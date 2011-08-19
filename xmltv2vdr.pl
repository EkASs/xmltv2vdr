#!/usr/bin/perl

# xmltv2vdr.pl
#
# Converts data from an xmltv output file to VDR - tested with 1.7.19
#
# This script requires:
#   The PERL module date::manip
#   The PERL module XML::Parser
#   xmllint utility (Check the validity of the xmltv file)
#
# The files containing genres and ratings MUST be in UTF-8 charset.
# To convert: iconv --from-code=<source_charset> --to-code=UTF-8 genres.conf > genres.conf.utf8
#
# This software is released under the GNU GPL
#
# See the README file for copyright information and how to reach the author.

use strict;
use utf8;
use Encode;
use Getopt::Std;
use Time::Local;
use Date::Manip;
use XML::Parser;
use Socket;

my $localLang = "fr";
my $workDir = "/home/marc/epgvdr";
my $xmltvDtdFile = "file:$workDir/xmltv.dtd";
my $xmllintBin = "/usr/bin/xmllint";

my $Usage = qq{
Usage: $0 [options] -c <channels.conf file> -x <xmltv datafile> 
    
Options:
 -a (+,-) mins          Adjust the time from xmltv that is fed
                          into VDR (in minutes) (default: 0)
 -c channels.conf       File containing modified channels.conf info
 -d hostname            Destination hostname (default: localhost)
 -D                     Write debug log
 -h                     Show help text
 -g genres.conf         If xmltv source file contains genre information then add it
 -l description length  Length of the EPG description to use in char
                          (0: All the description, default: 0)
 -L credits length      Numbers of EPG credits to keep
                          (0: All credits, default: 0)
 -p port                SVDRP port number (default: 6419)
 -P priority            EPG priority in hex number (if multiple sources) (default: 0)
 -q                     Quiet mode
 -r ratings.conf        If xmltv source file contains ratings information then add it
 -s                     Simulation Mode (Print info to stdout)
 -t timeout             The time this program has to give all info to VDR
                          (default: 60s) 
 -v                     Show info messages
 -x xmltv output        File containing xmltv data
 -X                     Add extra attribute to the description
                          (currently episode-num & star-rating)
};

# getopts
our ($opt_a, $opt_c, $opt_d, $opt_D, $opt_h, $opt_g, $opt_l, $opt_L, $opt_p, $opt_P, $opt_q,
    $opt_r, $opt_s,$opt_t,$opt_v,$opt_x,$opt_X);
die $Usage if (!getopts('a:c:d:Dg:hl:L:p:qr:st:vx:X') || $opt_h);

# Options
my $adjust = $opt_a || 0;
my $channelsFile = $opt_c  || die "$Usage Need to specify a channels.conf file";
my $dest = $opt_d || "localhost";
my $debug = $opt_D;
my $genresFile = $opt_g if $opt_g;
my $descv = $opt_l || 0;
if ( $descv < 0 ) { die "$Usage Description lenght out of range"; }
my $creditsv = $opt_L || 0;
if ( $creditsv < 0 ) { die "$Usage Credits lenght out of range"; }
my $port = $opt_p || 6419;
if ( ( $port < 0 ) || ( $port > 65535 ) ) { die "$Usage Port out of range"; }
my $epgPrio = $opt_P || 0;
my $warn = 1 if !($opt_q);
my $ratingsFile = $opt_r if $opt_r;
my $sim = $opt_s;
my $timeout = $opt_t || 60; # max. seconds to wait for response
if ( $timeout < 0 ) { die "$Usage Timeout out of range"; }
my $verbose = $opt_v;
my $xmltvFile = $opt_x  || die "$Usage Need to specify an XMLTV file";
my $xAttr = $opt_X;

# Logs
$warn = 1 if $debug;
$verbose = 1 if $debug;
if ($debug) {
    my $debugFile = "$workDir/debug";
    open(DEBUG, ">$debugFile") || die "$!";
}

# Files
$channelsFile = "$workDir/$channelsFile" if ( $channelsFile !~ m:^/: );
$genresFile = "$workDir/$genresFile" if ( $genresFile !~ m:^/: );
$ratingsFile = "$workDir/$ratingsFile" if ( $ratingsFile !~ m:^/: );
$xmltvFile = "$workDir/$xmltvFile" if ( $xmltvFile !~ m:^/: );

# Configuration files data
my %genreLine;
my %ratingLine;
my %channelId;
my %channelName;

# XML parse
my %vdrText;
my $pivotTime = time () - 3600;
my $isProg = 0;
my $creditsCount = 0;
my $programChan = "";
my $programId = 0;
my $programStart = 0;
my $programDur = 0;
my $programTitle = "";
my $programShortdesc = "";
my $programDesc = "";
my $programDate = "";
my $currentCreditElement = "";
my $programCredits = "";
my $programRole = "";
my $programGenre = "";
my $programRating = "";
my $programStarRating = "";
my $programEpisode = "";
my $programEpisodeShort = "";
my %elementLang = ( element => "", value => "", currentLang => "", newLang => "" );

# Sometime, XML::Parser splits the data
my $xmlParserBuf = "";

# Translate
sub translate {
    my $line=shift;
    
    $line=~s/director/Réalisateur/;
    $line=~s/actor/Acteur/;
    $line=~s/writer/Scénariste/;
    $line=~s/adapter/Adapteur/;
    $line=~s/producer/Producteur/;
    $line=~s/presenter/Presentateur/;
    $line=~s/commentator/Commentateurr/;
    $line=~s/guest/Invité/;
    $line=~s/season/Saison/;
    $line=~s/episode/Episode/;
    $line=~s/part/Partie/;
    $line=~s/rating/Note/;

    return $line;
}

# Convert XMLTV time format (YYYYMMDDmmss ZZZ) into VDR (secs since epoch)
sub xmltime2vdr {
    my $xmlTime=shift;
    my $secs = &Date::Manip::UnixDate($xmlTime, "%s");
    return $secs + ( $adjust * 60 );
}

# Send info over SVDRP (thanks to Sky plugin)
sub SVDRPsend {
    my $s = shift;
    print DEBUG "Send : $s\n" if ($debug);
    if ( $sim == 0 ) {
        print SOCK "$s\r\n";
    }
    else {
        print "$s\n";
    } 
}

# Recv info over SVDRP (thanks to Sky plugin)
sub SVDRPreceive {
    my $expect = shift | 0;
    
    if ( $sim == 1 ) { return 0; }
    
    my @a = ();
    while (<SOCK>) {
        s/\s*$//; # 'chomp' wouldn't work with "\r\n"
        push(@a, $_);
        print DEBUG "Receive : $_\n" if ($debug);
        if (substr($_, 3, 1) ne "-") {
            my $code = substr($_, 0, 3);
            die("expected SVDRP code $expect, but received $code") if ($code != $expect);
            last;
        }
    }
    return @a;
}

# Get data in best language available ( lang=$localLang || no lang || first found )
sub getLang {
    my $newValue = shift;
    
    print DEBUG "element : *$elementLang{element}* new value : *$newValue* current value : *$elementLang{value}* ",
        "current lang : *$elementLang{currentLang}* new lang : *$elementLang{newLang}*\n" if $debug;

    if (!$elementLang{value}) {
        $elementLang{value} = $newValue;
        $elementLang{currentLang} = $elementLang{newLang};
        return $newValue;
    } elsif ( $elementLang{newLang} eq $localLang ) {
        $elementLang{value} = $newValue;
        $elementLang{currentLang} = $localLang;
        return $newValue;
    } elsif ( (!$elementLang{newLang}) && (!$elementLang{currentLang}) ) {
        $elementLang{value} = $newValue;
        return $newValue;
    }
    return $elementLang{value};
}


# Store configuration files data
sub parse_conf_files {

    # Genres
    if ($genresFile) {
        print "Parsing $genresFile...\n" if $verbose;
        # Read the genres stuff
        open(GENRES, "$genresFile") || die "cannot open $genresFile file";
        while ( <GENRES> ) {
            s/#.*//;            # ignore comments by erasing them
            next if /^(\s)*$/;  # skip blank lines

            # Split a Genre Line
            chomp;
            my ( $genreName, $genreCode ) = split(/:/, $_);
            $genreName = decode("UTF-8", $genreName);
            $genreLine { $genreName } = $genreCode;
            print DEBUG "Add genre $genreName with code ", $genreLine { $genreName } ,"\n" if $debug;
        }
        print scalar(keys %genreLine) ," genres found.\n" if $verbose;
        close GENRES;
    }

    # Ratings
    if ($ratingsFile) {
        print "Parsing $ratingsFile...\n" if $verbose;
        # Read the ratings stuff
        open(RATINGS, "$ratingsFile") || die "cannot open $ratingsFile file";
        while ( <RATINGS> ) {
            s/#.*//;            # ignore comments by erasing them
            next if /^(\s)*$/;  # skip blank lines

            # Split a Rating Line
            chomp;
            my ( $ratingName, $ratingAge ) = split(/:/, $_);
            $ratingName = decode("UTF-8", $ratingName);
            $ratingLine { $ratingName } = $ratingAge;
            print DEBUG "Add rating $ratingName with age ", $ratingLine { $ratingName } ,"\n" if $debug;
        }
        print scalar(keys %ratingLine) ," ratings found.\n" if $verbose;
        close RATINGS;
    }

    # Channels
    print "Parsing $channelsFile...\n" if $verbose;
    open(CHANNELS, "$channelsFile") || die "cannot open $channelsFile file";
    my $verboseMsg = "Channels with no xmltv info :" if ($verbose);
    my $count = 0;
    while ( <CHANNELS> ) {
        s/#.*//;            # ignore comments by erasing them
        next if /^(\s)*$/;  # skip blank lines

        # Split a Channel Line
        chomp;
        my ($channelName, $freq, $param, $source, $srate, $vpid, $apid, $tpid, $ca, $sid, $nid,
            $tid, $rid, $xmltvChannelName) = split(/:/, $_);
        
        if ( $source eq 'T' ) { 
            $freq=substr($freq, 0, 3);
        }
        
        if (!$xmltvChannelName) {
            if(!$channelName) {
                $_ =~ m/:(.*$)/;
                if ($warn == 1 ) { warn("\nIgnoring header: $1\n"); }
            }
            else {
                $verboseMsg .= " $channelName," if $verbose;
                $count++;
            }
            next;
        }
        my @channels = split ( /,/, $xmltvChannelName);
        foreach my $myChannel ( @channels ) {
            $channelName{$myChannel} = $channelName;
            # Save the Channel Entry
            if ($nid>0) {
                $channelId{$myChannel} = "C $source-$nid-$tid-$sid $channelName\r\n";
            }
            else {
                $channelId{$myChannel} = "C $source-$nid-$freq-$sid $channelName\r\n";
            }
            print DEBUG "Add channel $myChannel : $channelId{$myChannel}" if $debug;
            $vdrText{$myChannel} = "";
        }
    }
    print scalar(keys %channelId) ," channels found.\n" if $verbose;
    print "$verboseMsg * Total : $count *.\n" if $verbose;
}

#
# XML::Parser handlers
#

# process a XML::Parser default event
sub handle_def { }

# process a XML::Parser start-of-element event
sub handle_start {
    my ( $expat, $element, %attrs ) = @_;
 
    print DEBUG "<$element>\n" if $debug;
    if ( %attrs && $debug ) {
        print DEBUG "Attributes:\n";
        while( my( $key, $value ) = each( %attrs )) {
            print DEBUG "\t$key => $value\n";
        }
    }
    
    $xmlParserBuf = "";

    # New XML Program
    if ( $element eq "programme" ) {
        print DEBUG "Found programme\n" if $debug;
        # doesn't handle split programs yet (clumpidx)
        if ( $attrs{clumpidx} ) {
            warn "Found splitted programme for $channelName{$attrs{channel}}\n" if $warn;
            print DEBUG "Programme splitted, abort\n" if $debug;
            return 0;
        }
        $programStart = &xmltime2vdr( $attrs{start} );
        $programId = $programStart / 60 % 0xFFFF;
        my $vdrStop = &xmltime2vdr( $attrs{stop} );
        if ($vdrStop < $pivotTime) {
            warn "Found outdated programme for $channelName{$attrs{channel}}\n" if $warn;
            print DEBUG "Programme outdated, abort\n" if $debug;
            return 0;
        }
        $programDur = $vdrStop - $programStart;
        $programChan = $attrs{channel};
        $isProg = 1;
    # Existing Program
    } elsif ($isProg) {
        if ( $elementLang{element} ne $element ) {
            # New element
            %elementLang = ( element => $element, value => "", currentLang => "", newLang => "" );
        }
        # Get attributes when needed
        $elementLang{newLang} = "$attrs{lang}";
        if ( $element eq "actor" ) {
            $programRole = "$attrs{role}";
        } elsif ( ( $xAttr ) && ( $element eq "episode-num" ) && ( $attrs{system} ) ) {
            $programEpisode = $attrs{system};
        # Get value when needed
        } elsif ( ( $xAttr ) && ( $element eq "star-rating" ) ) {
            $programStarRating = "*nextvalue*";
        }
    }
}
 
# process a XML::Parser chars-of-element event
sub handle_char {
    my ($expat, $str) = @_;
    
    $xmlParserBuf .= $str;

    if ($debug) {
        ( $str =~ s:^[\s\n\r\t]*:: );
        print DEBUG "String:\n\t$str\n" if $str;
    }

}

# process an XML::Parser end-of-element event
sub handle_end {
    my( $expat, $element ) = @_;

    print DEBUG "</$element>\n" if $debug;
    print DEBUG "xmlParserBuf : $xmlParserBuf\n" if $debug;

    # elements
    if ($isProg) {
        if ( $element eq "title" ) {
            my $value = getLang ( $xmlParserBuf );
            $programTitle = $value;
        } elsif ( $element eq "sub-title" ) {
            my $value = getLang ( $xmlParserBuf );
            $programShortdesc = $value;
        } elsif ( $element eq "desc" ) {
            my $value = getLang ( $xmlParserBuf );
            $programDesc = $value;
            $programDesc = substr($programDesc, 0, $descv) if ($descv);
        } elsif ( $element eq "date" ) {
            $programDate = "( $xmlParserBuf )";
        } elsif ( $element =~ m/^(director|actor|writer|adapter|producer|presenter|commentator|guest)$/ ) {
            if ( !($creditsv) || ( $creditsCount < $creditsv ) ) {
                if ( $currentCreditElement eq $element ) {
                    $programCredits .=  ", $xmlParserBuf";
                    $programCredits .=  " \"$programRole\"" if $programRole;
                } else {
                    $currentCreditElement = $element;
                    $programCredits .= ".|" if $creditsCount;
                    $programCredits .= translate($element);
                    $programCredits .=  " : $xmlParserBuf";
                    $programCredits .=  " \"$programRole\"" if $programRole;
                }
                $creditsCount++;
            }
            $programRole = "";
        } elsif ( $element eq "category" ) {
            my $value = getLang ( $xmlParserBuf );
            if ($genreLine { $value }) {
                $programGenre = $genreLine { $value };
            } else {
                warn "Genre unknown : $value\n" if $warn;
                print DEBUG "Genre unknown : $value\n" if $debug;
            }
        } elsif ( $element eq "rating" ) {
            if ($ratingLine { $xmlParserBuf }) {
                $programRating .= $ratingLine { $xmlParserBuf };
            } else {
                warn "Rating unknown : $xmlParserBuf\n" if $warn;
                print DEBUG "Rating unknown : $xmlParserBuf\n" if $debug;
            }
        } elsif ( $element eq "episode-num" ) {
            if ( $programEpisode eq "xmltv_ns" ) {
                $programEpisode = "";
                $programEpisodeShort = "";
                my ($season, $episode, $part) = split(/\./, $xmlParserBuf);
                my ($number, $total) = split(/\//, $season);
                if ($number) {
                    $number++;
                    $programEpisode .= translate("season"). " $number";
                    $programEpisodeShort .= "s" .sprintf("%02d", $number);;
                    $programEpisode .= "/$total" if $total;
                    print DEBUG "Season : $programEpisode\n" if $debug;
                }
                my ($number, $total) = split(/\//, $episode);
                if ($number) {
                    $number++;
                    $programEpisode .= " - " if ($season);
                    $programEpisode .= translate("episode"). " $number";
                    $programEpisodeShort .= "e" .sprintf("%02d", $number);;
                    $programEpisode .= "/$total" if $total;
                    print DEBUG "Episode : $programEpisode\n" if $debug;
                }
                my ($number, $total) = split(/\//, $part);
                if ($number) {
                    $number++;
                    $programEpisode .= " - " if ($season || $episode);
                    $programEpisode .= translate("part"). " $number";
                    $programEpisode .= "/$total" if $total;
                    print DEBUG "Part : $programEpisode\n" if $debug;
                }
            } else {
                $programEpisode = translate("episode"). " $xmlParserBuf";
                print DEBUG "Raw : $programEpisode\n" if $debug;
            }
            $programEpisode .= " ";
        } elsif ( ( $element eq "value" ) && ( $programStarRating eq "*nextvalue*" ) ) {
            $programStarRating = translate("rating") . " : $xmlParserBuf";
        # Completed XML Program
        } elsif ( $element eq "programme" ) {
            # Infos
            my $epgEntry = "E $programId $programStart $programDur $epgPrio\r\n";
            # Title
            $epgEntry .= "T $programTitle\r\n" if ( $programTitle );
            # Short text
            if ( !$programShortdesc ) {
                $programShortdesc .= $programEpisodeShort;
                $epgEntry .= "S $programShortdesc\r\n";
                $programEpisode = "";
            }
            
            # description
            $programEpisode = "$programEpisode$programDate|" if ( $programEpisode || $programDate );
            $programDesc = "$programDesc|" if ( $programDesc );
            $programCredits = "$programCredits." if ( $programCredits );
            $programCredits = "$programCredits|" if ( $programCredits && $programStarRating );
            $epgEntry .= "D $programEpisode$programDesc$programCredits$programStarRating\r\n"
                if (  $programEpisode || $programDesc || $programCredits || $programStarRating);
            # genre
            $programGenre = "FF" if !( $programGenre );
            $epgEntry .= "G $programGenre\r\n";
            # end
            $epgEntry .= "e\r\n";
            
            $vdrText{$programChan} .= $epgEntry;
            print DEBUG "Add  programme :\n$epgEntry" if $debug;
            
            $isProg = 0;
            $creditsCount = 0;
            $programChan = "";
            $programId = 0;
            $programStart = 0;
            $programDur = 0;
            $programTitle = "";
            $programShortdesc = "";
            $programDesc = "";
            $programDate = "";
            $currentCreditElement = "";
            $programCredits = "";
            $programGenre = "";
            $programRating = "";
            $programEpisode = "";
            $programEpisodeShort = "";
            $programStarRating = "";
        }
    }
    $xmlParserBuf = "";
}

#
# Main
#

# parse configuration files
parse_conf_files;

# check xml file
print "Checking $xmltvFile...\n" if $verbose;
system( $xmllintBin, "--valid", "--dtdvalid", "$xmltvDtdFile", "--noout", $xmltvFile ) == 0 || die "Check failed\n";

# initialize the parser
my $parser = XML::Parser->new(
    Handlers => {
        Start => \&handle_start,
        End => \&handle_end,
        Char => \&handle_char,
        Default => \&handle_def,
    }
);

# Do the EPG stuff
print "Parsing $xmltvFile...\n" if $verbose;
$parser->parsefile( $xmltvFile );

# Connect to SVDRP socket (thanks to Sky plugin coders)
if ( $sim == 0 ) {
    $SIG{ALRM} = sub { die("timeout"); };
    alarm($timeout);
    
    my $iAddr = inet_aton($dest) || die("no host: $dest");
    my $pAddr = sockaddr_in($port, $iAddr);
    
    my $proto = getprotobyname('tcp');
    socket(SOCK, PF_INET, SOCK_STREAM, $proto)  || die("socket: $!");
    connect(SOCK, $pAddr)                       || die("connect: $!");
    select((select(SOCK), $| = 1)[0]);
}

print "Sending data...\n" if $verbose;

# Look for initial banner
SVDRPreceive(220);
SVDRPsend("CLRE");
SVDRPreceive(250);

# Send the data
while ( my ($key, $value) = each(%vdrText) ) {
    if ($value) {
        print "Send $key => $channelName{$key}\n" if $verbose;
        # Send VDR PUT EPG
        SVDRPsend("PUTE");
        SVDRPreceive(354);
        my $vdrEncoded = encode("UTF-8", $value);
        SVDRPsend($channelId{$key} . $vdrEncoded . "c\r\n" . ".");
        SVDRPreceive(250);
        print DEBUG "$channelId{$key}$value" if $debug;
    } else {
        print "No data for $key ($channelName{$key})\n" if $verbose;
    }
}

# Lets get out of here! :-)
SVDRPsend("QUIT");
SVDRPreceive(221);

close(SOCK) if ( $sim == 0 );
close(DEBUG) if $debug;

print "All done.\n" if $verbose;

exit;
