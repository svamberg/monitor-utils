#!/usr/bin/perl

#####################################
#####################################
### ______               _     =) ###
### | ___ \             | |       ###
### | |_/ / __ _  _ __  | |       ###
### |    / / _` || '_ \ | |       ###
### | |\ \| (_| || | | || |____   ###
### \_| \_|\__,_||_| |_|\_____/   ###
#####################################
#####################################
#####################################
## Original version written by
## ran.leibman@gmail.com
## Additionial checks code written
## by laurent.dufour@havas.com
## updated by X. Franco & A. Rigaud
## 20160211 : Added FSSTATUS/SNAPSHOTAGE
##
## the following parameters has
## been tested against a
## FAS2220
## FAS2240
## FAS3220
## FA2050, NetApp Release 7.3.1.1
## IBM System Storage N6240, Data ONTAP Release 8.1.4P4
##
## DISKSUMMARY|HA|CIFSSESSIONS|
## AUTOSUPPORTSTATUS|NFSOPS|
## CIFSOPS|SHELFINFO|...
##
#####################################
#####################################


use strict;
use POSIX;
use lib "/usr/lib/nagios/libexec";
use lib "/usr/lib/nagios/plugins";
use lib "/usr/lib64/nagios/libexec";
use lib "/usr/lib64/nagios/plugins";
use utils qw($TIMEOUT %ERRORS);
use Net::SNMP;
use File::Basename;
use Getopt::Long;
use Time::Local;
use IPC::Cmd qw(run_forked);
use Data::Dumper;

Getopt::Long::Configure('bundling');

my $stat = 0;
my $msg;
my $perf;
my $script_name = basename($0);
my $script_version = 1.3;

my $counterFilePath="/tmp";
my $counterFile;

my %opt;
my $elapsedtime = 1;

my %ERRORS = (
        'OK'       => '0',
        'WARNING'  => '1',
        'CRITICAL' => '2',
        'UNKNOWN'  => '3',
    );

# default return value is UNKNOWN
my $state = "UNKNOWN";
my $answer = "";

# time this script was run
my $runtime = time();

my $key;
our %snmpIndexes;


# file related variables
my $fileRuntime;
my $fileHostUptime;
my $fileNfsOps;
my $fileCifsOps;
my $fileIscsiOps;
my $fileIscsi64ReadBytes;
my $fileIscsi64WriteBytes;
my $fileFcpOps;
my $fileFcp64ReadBytes;
my $fileFcp64WriteBytes;
my $fileDisk64ReadBytes;
my $fileDisk64WriteBytes;

# performance variables from SNMP
my $total_nfs_ops;
my $total_cifs_ops;
my $total_disk_read;
my $total_disk_write;
my $blocks_iscsi_ops;
my $blocks_iscsi_read;
my $blocks_iscsi_write;
my $blocks_fcp_ops;
my $blocks_fcp_read;
my $blocks_fcp_write;

my $snmpHostUptime;

### SNMP OIDs
## You can browse at http://www.oidview.com/mibs/789/NETAPP-MIB.html
###############
my %oid = ();


# SNMP Status Codes
my %nvramBatteryStatus = (
        1 => 'ok',
        2 => 'partially discharged',
        3 => 'fully discharged',
        4 => 'not present',
        5 => 'near end of life',
        6 => 'at end of life',
        7 => 'unknown',
);
my %GlobalStatusIndex = (
        1 => 'other',
        2 => 'unknown',
        3 => 'ok',
        4 => 'nonCritical',
        5 => 'critical',
        6 => 'nonRecoverable',
);

my %AutoSupportStatusIndex = (
        1 => 'ok',
        2 => 'smtpFailure',
        3 => 'postFailure',
        4 => 'smtpPostFailure',
        5 => 'unknown',
);

my %cfSettingsIndex = (
        1 => 'notConfigured',
        2 => 'enabled',
        3 => 'disabled',
        4 => 'takeoverByPartnerDisabled',
        5 => 'thisNodeDead',
);

my %cfStateIndex = (
        1 => 'dead',
        2 => 'canTakeover',
        3 => 'cannotTakeover',
        4 => 'takeover',
);

my %cfCannotTakeoverCauseIndex = (
        1 => 'ok',
        2 => 'unknownReason',
        3 => 'disabledByOperator',
        4 => 'interconnectOffline',
        5 => 'disabledByPartner',
        6 => 'takeoverFailed',
        7 => 'mailboxDegraded',
        8 => 'partnerMailboxUninitialised',
        9 => 'mailboxVersionMismatch',
        10 => 'nvramSizeMismatch',
        11 => 'kernelVersionMismatch',
        12 => 'partnerBootingUp',
        13 => 'partnerPerformingRevert',
        14 => 'performingRevert',
        15 => 'partnerRequestedTakeover',
        16 => 'alreadyInTakenoverMode',
        17 => 'nvramLogUnsynchronized',
        18 => 'backupMailboxProblems',
);

my %cfPartnerStatusIndex = (
        1 => 'maybeDown',
        2 => 'ok',
        3 => 'dead',
);

my %cfInterconnectStatusIndex = (
        1 => 'notPresent',
        2 => 'down',
        3 => 'partialFailure',
        4 => 'up',
);

my %EcnlStatusIndex = (
        1 => 'initializing',
        2 => 'transitioning',
        3 => 'active',
        4 => 'inactive',
        5 => 'reconfiguring',
        6 => 'nonexistent',
);

my %fsOverallStatusIndex = (
        1 => 'ok',
        2 => 'Nearly Full',
        3 => 'Full',
);

### Functions
###############

sub uniq(@) {
        my @array = @_;
        my @unique = ();
        my %seen   = ();

        foreach my $elem ( @array ) {
                next if $seen{ $elem }++;
                push @unique, $elem;
        }
        return @unique;
}

sub _create_session(@) {
        my ($server, $comm, $version, $timeout) = @_;
        my ($sess, $err) = Net::SNMP->session( -hostname => $server, -version => $version, -community => $comm, -timeout => $timeout);
        if (!defined($sess)) {
                print "Can't create SNMP session to $server\n";
                exit(1);
        }
        return $sess;
}

sub _set_oid($) {
        my $version = shift;

        # DEFAULT VALUES (ONTAP 7.x, 8.x)
        $oid{SysUpTime} = '.1.3.6.1.2.1.1.3.0';
        $oid{FailedFanCount} = '.1.3.6.1.4.1.789.1.2.4.2.0';
        $oid{FailPowerSupplyCount} = '.1.3.6.1.4.1.789.1.2.4.4.0';
        $oid{cpuBusyTimePerCent} = '.1.3.6.1.4.1.789.1.2.1.3.0';
        $oid{envOverTemperature} = '.1.3.6.1.4.1.789.1.2.4.1.0';
        $oid{nvramBatteryStatus} = '.1.3.6.1.4.1.789.1.2.5.1.0';
        $oid{FailedDiskCount} = '.1.3.6.1.4.1.789.1.6.4.7.0';
        $oid{UpTime} = '.1.3.6.1.2.1.1.3.0';
        $oid{CacheAge} = '.1.3.6.1.4.1.789.1.2.2.23.0';
        $oid{GlobalStatus} = '.1.3.6.1.4.1.789.1.2.2.4.0';
        $oid{GlobalStatus_text} = '.1.3.6.1.4.1.789.1.2.2.25.0';
        $oid{NdmpSessions} = '.1.3.6.1.4.1.789.1.10.2.0';
        $oid{CifsSessions} = '.1.3.6.1.4.1.789.1.7.2.12.0';
        $oid{AutoSupportStatus} = '.1.3.6.1.4.1.789.1.2.7.1.0';
        $oid{AutoSupportStatus_text} = '.1.3.6.1.4.1.789.1.2.7.2.0';

        $oid{netapp_disksummary} = '.1.3.6.1.4.1.789.1.6.4';
        $oid{netapp_disksummary_diskTotalCount} = '.1.3.6.1.4.1.789.1.6.4.1.0';
        $oid{netapp_disksummary_diskActiveCount} = '.1.3.6.1.4.1.789.1.6.4.2.0';
        $oid{netapp_disksummary_diskFailedCount} = '.1.3.6.1.4.1.789.1.6.4.7.0';
        $oid{netapp_disksummary_diskSpareCount} = '.1.3.6.1.4.1.789.1.6.4.8.0';
        $oid{netapp_disksummary_diskReconstructingCount} = '.1.3.6.1.4.1.789.1.6.4.3.0';
        $oid{netapp_disksummary_diskFailedMessage} = '.1.3.6.1.4.1.789.1.6.4.10.0';

        $oid{netapp_cf} = '.1.3.6.1.4.1.789.1.2.3';
        $oid{netapp_cfSettings} = '.1.3.6.1.4.1.789.1.2.3.1.0';
        $oid{netapp_cfState} = '.1.3.6.1.4.1.789.1.2.3.2.0';
        $oid{netapp_cfCannotTakeoverCause} = '.1.3.6.1.4.1.789.1.2.3.3.0';
        $oid{netapp_cfPartnerStatus} = '.1.3.6.1.4.1.789.1.2.3.4.0';
        $oid{netapp_cfPartnerName} = '.1.3.6.1.4.1.789.1.2.3.6.0';
        $oid{netapp_cfInterconnectStatus} = '.1.3.6.1.4.1.789.1.2.3.8.0';

        $oid{filesysvolTable} = '.1.3.6.1.4.1.789.1.5.8';
        $oid{filesysvolTablevolEntryOptions} = "$oid{filesysvolTable}.1.7";
        $oid{filesysvolTablevolEntryvolName} = "$oid{filesysvolTable}.1.2";

        $oid{netapp_volume_id_table_df} = ".1.3.6.1.4.1.789.1.5.4.1";
        $oid{netapp_volume_id_table_df_name} = "$oid{netapp_volume_id_table_df}.2";
        $oid{netapp_volume_id_table_df_total} = "$oid{netapp_volume_id_table_df}.3";
        $oid{netapp_volume_id_table_df_used} = "$oid{netapp_volume_id_table_df}.4";
        $oid{netapp_volume_id_table_df_free} = "$oid{netapp_volume_id_table_df}.5";
        $oid{netapp_volume_id_table_df_used_prec} = "$oid{netapp_volume_id_table_df}.6";
        $oid{netapp_volume_id_table_df_used_high} = "$oid{netapp_volume_id_table_df}.16";
        $oid{netapp_volume_id_table_df_used_low} = "$oid{netapp_volume_id_table_df}.17";

        $oid{fsOverallStatus} = '1.3.6.1.4.1.789.1.5.7.1.0';
        $oid{fsOverallStatus_text} = '1.3.6.1.4.1.789.1.5.7.2.0';

        # 64bit values for SNMP v2c
        $oid{netapp_volume_id_table_df64_total} = "$oid{netapp_volume_id_table_df}.29";
        $oid{netapp_volume_id_table_df64_used} = "$oid{netapp_volume_id_table_df}.30";
        $oid{netapp_volume_id_table_df64_free} = "$oid{netapp_volume_id_table_df}.31";

        $oid{netapp_enclNumber} = '.1.3.6.1.4.1.789.1.21.1.1';
        $oid{EnclTable} = '.1.3.6.1.4.1.789.1.21.1.2.1';
        $oid{EnclTableIndex} = "$oid{EnclTable}.1";
        $oid{EnclTableState} = "$oid{EnclTable}.2";
        $oid{EnclTableShelfAddr} = "$oid{EnclTable}.3";
        $oid{EnclTableProductID} = "$oid{EnclTable}.5";
        $oid{EnclTableProductVendor} = "$oid{EnclTable}.6";
        $oid{EnclTableProductModel} = "$oid{EnclTable}.7";
        $oid{EnclTableProductRevision} = "$oid{EnclTable}.8";
        $oid{EnclTableProductSerial} = "$oid{EnclTable}.9";
        $oid{EnclTablePsFailed} = "$oid{EnclTable}.15";
        $oid{EnclTableFanFailed} = "$oid{EnclTable}.18";
        $oid{EnclTableTempOverFail} = "$oid{EnclTable}.21";
        $oid{EnclTableTempOverWarn} = "$oid{EnclTable}.22";
        $oid{EnclTableTempUnderFail} = "$oid{EnclTable}.23";
        $oid{EnclTableTempUnderWarn} = "$oid{EnclTable}.24";
        $oid{EnclTableCurrentTemp} = "$oid{EnclTable}.25";
        $oid{EnclTableElectronicFailed} = "$oid{EnclTable}.33";
        $oid{EnclTableVoltPresent} = "$oid{EnclTable}.35";
        $oid{EnclTableVoltOverFail} = "$oid{EnclTable}.36";
        $oid{EnclTableVoltOverWarn} = "$oid{EnclTable}.37";
        $oid{EnclTableVoltUnderFail} = "$oid{EnclTable}.38";
        $oid{EnclTableVoltUnderWarn} = "$oid{EnclTable}.39";

        $oid{netapp_misc} = '1.3.6.1.4.1.789.1.2.2';
        $oid{netapp_miscHighNfsOps} = "$oid{netapp_misc}.5.0";
        $oid{netapp_miscLowNfsOps} = "$oid{netapp_misc}.6.0";
        $oid{netapp_miscHighCifsOps} = "$oid{netapp_misc}.7.0";
        $oid{netapp_miscLowCifsOps} = "$oid{netapp_misc}.8.0";
        $oid{netapp_misc64DiskReadBytes} = "$oid{netapp_misc}.32.0";
        $oid{netapp_misc64DiskWriteBytes} = "$oid{netapp_misc}.33.0";

        $oid{netapp_blocks} = '.1.3.6.1.4.1.789.1.17';
        $oid{netapp_blocks_iscsi64Ops} = "$oid{netapp_blocks}.24.0";
        $oid{netapp_blocks_iscsi64ReadBytes} = "$oid{netapp_blocks}.22.0";
        $oid{netapp_blocks_iscsi64WriteBytes} = "$oid{netapp_blocks}.23.0";
        $oid{netapp_blocks_fcp64Ops} = "$oid{netapp_blocks}.25.0";
        $oid{netapp_blocks_fcp64ReadBytes} = "$oid{netapp_blocks}.20.0";
        $oid{netapp_blocks_fcp64WriteBytes} = "$oid{netapp_blocks}.21.0";

        ### SNAPSHOT OIDs
        ### You can browse at http://www.oidview.com/mibs/789/NETWORK-APPLIANCE-MIB.html
        ###############

        $oid{filesys_snapshot_slVTable_slVEntry} = '.1.3.6.1.4.1.789.1.5.5.2.1';
        $oid{filesys_snapshot_slVTable_slVEntry_index} = "$oid{filesys_snapshot_slVTable_slVEntry}.1";
        $oid{filesys_snapshot_slVTable_slVEntry_number} = "$oid{filesys_snapshot_slVTable_slVEntry}.8";
        $oid{filesys_snapshot_slVTable_slVEntry_Vname} = "$oid{filesys_snapshot_slVTable_slVEntry}.9";

        if ($version =~ /^9\.\d+$/) {
                $oid{envOverTemperature} = '.1.3.6.1.4.1.789.1.25.2.1.18';
                $oid{FailedFanCount} = '.1.3.6.1.4.1.789.1.25.2.1.19';
                $oid{FailPowerSupplyCount} = '.1.3.6.1.4.1.789.1.25.2.1.21';
                $oid{nvramBatteryStatus} = '.1.3.6.1.4.1.789.1.25.2.1.17';
                $oid{nodeHealth} = '.1.3.6.1.4.1.789.1.25.2.1.11';
        }
}

sub FSyntaxError($) {
        my $err = shift;
        print <<EOU;
$err

This is $script_name in version $script_version.

  Syntax:
    -H <IP_or_Hostname>     Ip/Dns Name of the Filer
    -C <community_name>     SNMP Community Name for read
    -V <1|2c>               SNMP version (default 1), some checks run only 2c
    -T <check_type>         Type of check, see bellow
    -t <seconds>            Timeout to SNMP session in seconds (default 5)
    -w <number>             Warning Value (default 500)
    -c <number>             Critical Value (default 500)
    -v <vol_path|aggr_name> Volume Name in format /vol/volname
                            or aggregate name (not available in 7.x ONTAP)
                            For available values use any word, such as \'-v whatever\'
    -e <vol1[,vol2[,...]]>  Exclude volumes from snap check (SNAPSHOT/SNAPSHOTAGE)
    -I                      Inform only, return OK every time (ignore -w and -c values)
    -h                      This help

  Available check types:
    TEMP              - Temperature
    FAN               - Fan Fail
    PS                - Power Supply Fail
    CPULOAD           - CPU Load (-w -c)
    NVRAM             - NVram Battery Status
    DISKUSED          - Usage Percentage of volume or aggregate (-w -c -v)
    SNAPSHOT          - Snapshot Config (-e volname,volname2,volname3)
    SNAPSHOTAGE       - Check the age of volume snapshot which are older than x days (-w -c -v -e)
    SHELF             - Shelf Health
    SHELFINFO         - Shelf Model & Temperature Information
    NFSOPS            - Nfs Ops per seconds (-w -c)
    CIFSOPS           - Cifs Ops per seconds (-w -c)
    ISCSIOPS          - iSCSI Ops per seconds, collect read/write performance data, using SNMPv2c (-w -c)
    FCPOPS            - FibreChannel Ops per seconds, collect read/write performance data, using SNMPv2c (-w -c)
    NDMPSESSIONS      - Number of ndmp sessions (-w -c)
    CIFSSESSIONS      - Number of cifs sessions (-w -c)
    GLOBALSTATUS      - Global Status of the filer
    AUTOSUPPORTSTATUS - Auto Support Status of the filer
    HA                - High Availability
    NODEHEALTH        - Node Health (only for Cluster mode)
    DISKSUMMARY       - Status of disks
    FAILEDDISK        - Number of failed disks
    UPTIME            - Only show\'s uptime
    CACHEAGE          - Cache Age (-w -c)
    FSSTATUS          - Overall file system health

  Examples:
    $script_name -H netapp.mydomain -C public -T UPTIME
      UPTIME: 2 days, 23:03:21.09 | uptime=255801s

    $script_name -H netapp.mydomain -C public -T DISKUSED -v /vol/data/ -w 90 -c 95 -V 2c
      OK: DISKUSED 79% | /vol/data/=8104595240k

    $script_name -H netapp.mydomain -C public -T GLOBALSTATUS
      CRIT: GLOBALSTATUS nonCritical 4 Disk on adapter 1a, shelf 1, bay 9, failed.   | globalstatus=4

    $script_name -H netapp.mydomain -C public -T DISKUSED -v wtf
      WARN: Unknown volume path or aggregate name 'wtf'. Available values: aggr_p1a_sas2_mirror /vol/vol0/ /vol/esx/ /vol/xen_a/

EOU
        exit($ERRORS{'UNKNOWN'});
}

sub _get_oid_value(@) {
        my $sess = shift;
        my $local_oid = shift;
        my $r_return = $sess->get_request(-varbindlist => [$local_oid]);
        #print ">>>$local_oid >>> $r_return->{$local_oid}\n";
        if ($r_return->{$local_oid} eq 'noSuchInstance' ) {
                #print Data::Dumper->Dump([$r_return]);
                $r_return = $sess->get_next_request(-varbindlist => [$local_oid]);
                #print Data::Dumper->Dump([$r_return]);
                return($r_return->{(keys %{$r_return})[0]}); # read first value from hash
        }
        else {
                #print Data::Dumper->Dump([$r_return]);
                return($r_return->{$local_oid});
        }
}

sub _clac_generic_err_stat(@) {
        my $value = shift;
        my $value_type = shift;
        my $tmp_warn = shift;
        my $tmp_crit = shift;
        my $scale = shift;
        my $r_msg;
        my $r_stat;
        if($opt{'inform'} or ($value <= $tmp_warn)) {
                $r_stat = $ERRORS{'OK'};
                $r_msg = "OK: $value_type $value $scale";
        }  elsif($value > $tmp_warn and $value < $tmp_crit) {
                $r_stat = $ERRORS{'WARNING'};
                $r_msg = "WARN: $value_type $value $scale";
        } elsif($value >= $tmp_crit) {
                $r_stat = $ERRORS{'CRITICAL'};
                $r_msg = "CRIT: $value_type $value $scale";
        }
        return($r_msg,$r_stat);
}


sub _clac_err_stat(@) {
        my $value = shift;
        my $value_type = shift;
        my $tmp_warn = shift;
        my $tmp_crit = shift;
        my $r_msg;
        my $r_stat;
        if($value <= $tmp_warn) {
                $r_stat = $ERRORS{'OK'};
                $r_msg = "OK: $value_type $value%";
        }  elsif($value > $tmp_warn and $value < $tmp_crit) {
                $r_stat = $ERRORS{'WARNING'};
                $r_msg = "WARN: $value_type $value%";
        } elsif($value >= $tmp_crit) {
                $r_stat = $ERRORS{'CRITICAL'};
                $r_msg = "CRIT: $value_type $value%";
        }
        return($r_msg,$r_stat);
}


sub _clac_absolute_err_stat(@) {
        my $value = shift;
        my $value_type = shift;
        my $tmp_warn = shift;
        my $tmp_crit = shift;
        my $r_msg;
        my $r_stat;
        ($r_msg,$r_stat) = _clac_generic_err_stat($value,$value_type,$tmp_warn,$tmp_crit,"");
        return($r_msg,$r_stat);
}

sub _clac_minutes_err_stat(@) {
        my $value = shift;
        my $value_type = shift;
        my $tmp_warn = shift;
        my $tmp_crit = shift;
        my $r_msg;
        my $r_stat;
        ($r_msg,$r_stat) = _clac_generic_err_stat($value,$value_type,$tmp_warn,$tmp_crit,"minutes");
        return($r_msg,$r_stat);
}

sub _ulong64(@) {
        my $high = shift;
        my $low = shift;
        if ($low < 0) {
                $low = $low & 0x00000000FFFFFFFF;
                $low = $low | 0x0000000080000000;
        }
        if ($high < 0) {
                $high = $high & 0x00000000FFFFFFFF;
                $high = $high | 0x0000000080000000;
        }
        return ($high<<32)|$low;
}


### Gather input from user
#############################
$opt{'crit'} = 500;
$opt{'warn'} = 500;
$opt{'version'} = 2;
$opt{'timeout'} = 60;
my $result = GetOptions(\%opt,
                                                'filer|H=s',
                                                'community|C=s',
                                                'version|V=s',
                                                'check_type|T=s',
                                                'warn|w=i',
                                                'crit|c=i',
                                                'vol|v=s',
                                                'exclude|e=s',
                                                'inform|I',
                                                'timeout|t=i',
                                                "help|h",
                                                );

FSyntaxError("") if defined $opt{'help'};
FSyntaxError("Missing -H")  unless defined $opt{'filer'};
FSyntaxError("Missing -C")  unless defined $opt{'community'};
FSyntaxError("Missing -T")  unless defined $opt{'check_type'};
if($opt{'vol'}) {
        if ( !( ($opt{'vol'} =~ m#^/vol/.*$#) or ($opt{'vol'} =~ m#^[^/]*$#) ) )  { 
                FSyntaxError("$opt{'vol'} format is '/vol/volname' or 'aggregate_name'! For listing available names use any text such as '-v whatever'.");
        }
}
if($opt{'crit'} and $opt{'warn'}) {
        if($opt{'warn'} > $opt{'crit'}) {
                FSyntaxError("Warning can't be larger then Critical: $opt{'warn'} > $opt{'crit'}");
        }
}

if( ($opt{'check_type'} eq 'ISCSIOPS') or ($opt{'check_type'} eq 'FCPOPS') ) {
        $opt{'version'} = '2c';
}

if (!defined($counterFilePath)) {
    $state = "UNKNOWN";
    $answer = "Filepath must be specified";
    print "$state: $answer\n";
    exit $ERRORS{$state};
} # end check for filepath





# Starting Alarm
alarm($TIMEOUT);

# Establish SNMP Session
our $snmp_session = _create_session($opt{'filer'},$opt{'community'},$opt{'version'},$opt{'timeout'});

# set OID table
my $productFirmwareVersion = "7.0"; # netapp 7.x, 8.x
$productFirmwareVersion = _get_oid_value($snmp_session,".1.3.6.1.4.1.789.1.1.6.0");
_set_oid($productFirmwareVersion);

# setup counterFile now that we have host IP and check type
$counterFile = $counterFilePath."/".$opt{'filer'}.".check-netapp-ng.$opt{'check_type'}.nagioscache";

# READ AND UPDATE CACHE FOR SPECIFIC TESTS FROM FILE
if (("$opt{'check_type'}" eq "CIFSOPS") or ("$opt{'check_type'}" eq "NFSOPS") or ("$opt{'check_type'}" eq "ISCSIOPS") or ("$opt{'check_type'}" eq "FCPOPS")) {
        $snmpHostUptime =  _get_oid_value($snmp_session,$oid{SysUpTime});
        
        # READ CACHE DATA FROM FILE IF IT EXISTS
        if (-e $counterFile) {
                open(FILE, "$counterFile");
                chomp($fileRuntime = <FILE>);
                chomp($fileHostUptime = <FILE>);
                chomp($fileNfsOps = <FILE>) if $opt{'check_type'} eq 'NFSOPS';
                chomp($fileCifsOps = <FILE>) if $opt{'check_type'} eq 'CIFSOPS';
                if ($opt{'check_type'} eq 'ISCSIOPS') {
                        chomp($fileIscsiOps = <FILE>);
                        chomp($fileIscsi64ReadBytes = <FILE>);
                        chomp($fileIscsi64WriteBytes = <FILE>);
                }
                if ($opt{'check_type'} eq 'FCPOPS') {
                        chomp($fileFcpOps = <FILE>);
                        chomp($fileFcp64ReadBytes = <FILE>);
                        chomp($fileFcp64WriteBytes = <FILE>);
                }
                if ( ($opt{'check_type'} eq 'ISCSIOPS') or ($opt{'check_type'} eq 'FCPOPS') ) {
                        chomp($fileDisk64ReadBytes = <FILE>);
                        chomp($fileDisk64WriteBytes = <FILE>);
                }
                close(FILE);
        } # end if file exists

        # POPULATE CACHE DATA TO FILE
        if ((-w $counterFile) || (-w dirname($counterFile))) {
                open(FILE, ">$counterFile");
                print FILE "$runtime\n";
                print FILE "$snmpHostUptime\n";

                if ($opt{'check_type'} eq 'NFSOPS') {
                        my $low_nfs_ops = _get_oid_value($snmp_session,$oid{netapp_miscLowNfsOps});
                        my $high_nfs_ops = _get_oid_value($snmp_session,$oid{netapp_miscHighNfsOps});
                        $total_nfs_ops = _ulong64($high_nfs_ops, $low_nfs_ops);
                        print FILE "$total_nfs_ops\n";
                }

                if ($opt{'check_type'} eq 'CIFSOPS') {
                        my $low_cifs_ops = _get_oid_value($snmp_session,$oid{netapp_miscLowCifsOps});
                        my $high_cifs_ops = _get_oid_value($snmp_session,$oid{_netapp_miscHighCifsOps});
                        $total_cifs_ops = _ulong64($high_cifs_ops, $low_cifs_ops);
                        print FILE "$total_cifs_ops\n";
                }

                if ($opt{'check_type'} eq 'ISCSIOPS') {
                        $blocks_iscsi_ops = _get_oid_value($snmp_session,$oid{netapp_blocks_iscsi64Ops});
                        $blocks_iscsi_read = _get_oid_value($snmp_session,$oid{netapp_blocks_iscsi64ReadBytes});
                        $blocks_iscsi_write = _get_oid_value($snmp_session,$oid{netapp_blocks_iscsi64WriteBytes});
                        print FILE "$blocks_iscsi_ops\n$blocks_iscsi_read\n$blocks_iscsi_write\n";
                }

                if ($opt{'check_type'} eq 'FCPOPS') {
                        $blocks_fcp_ops = _get_oid_value($snmp_session,$oid{netapp_blocks_fcp64Ops});
                        $blocks_fcp_read = _get_oid_value($snmp_session,$oid{netapp_blocks_fcp64ReadBytes});
                        $blocks_fcp_write = _get_oid_value($snmp_session,$oid{netapp_blocks_fcp64WriteBytes});
                        print FILE "$blocks_fcp_ops\n$blocks_fcp_read\n$blocks_fcp_write\n";
                }

                if ( ($opt{'check_type'} eq 'ISCSIOPS') or ($opt{'check_type'} eq 'FCPOPS') ) {
                        $total_disk_read = _get_oid_value($snmp_session,$oid{netapp_misc64DiskReadBytes});
                        $total_disk_write = _get_oid_value($snmp_session,$oid{netapp_misc64DiskWriteBytes});
                        print FILE "$total_disk_read\n$total_disk_write\n";
                }
                close(FILE);
            } else {
                $state = "WARNING";
                $answer = "file $counterFile is not writable\n";
                print ("$state: $answer\n");
                exit $ERRORS{$state};
        } # end if file is writable

        # check to see if we pulled data from the cache file or not
        if ( (!defined($fileRuntime)) ) {
            $state = "OK";
            $answer = "never cached - caching\n";
            print "$state: $answer\n";
            exit $ERRORS{$state};
        } # end if cache file didn't exist

        # check host's uptime to see if it goes backward
        if ($fileHostUptime > $snmpHostUptime) {
            $state = "WARNING";
            $answer = "uptime goes backward - recaching data\n";
            print "$state: $answer\n";
            exit $ERRORS{$state};
        } # end if host uptime goes backward

        $elapsedtime=$runtime-$fileRuntime;

        if ($elapsedtime<1){ $elapsedtime=1; }

} # end populate cache only for *OPS tests

#print "fileHostUptime : ".$fileHostUptime."\n";
#print "snmpeHostUptime : ".$snmpHostUptime."\n";
#print "elapsedTime : ".$elapsedtime."\n";



### Temperature ###
if("$opt{'check_type'}" eq "TEMP") {
        my $check = _get_oid_value($snmp_session,$oid{envOverTemperature});
        if($check == 1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} is ok";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: Over $opt{'check_type'} !";
        }
        $perf = "overtemperature=$check";
### Fan ###
} elsif("$opt{'check_type'}" eq "FAN") {
        my $check = _get_oid_value($snmp_session,$oid{FailedFanCount});
        if($check == 0) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $check";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $check !";
        }
        $perf = "failedfans=$check";
### PS ###
} elsif("$opt{'check_type'}" eq "PS") {
        my $check = _get_oid_value($snmp_session,$oid{FailPowerSupplyCount});
        if($check == 0) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} Fail $check";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} Fail $check !";
        }
        $perf = "failedpowersupplies=$check";
### CPULOAD ###
} elsif("$opt{'check_type'}" eq "CPULOAD") {
        my $check = _get_oid_value($snmp_session,$oid{cpuBusyTimePerCent});
        ($msg,$stat) = _clac_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "cpuload=$check\%;$opt{'warn'};$opt{'crit'};;";
### NFSOPS ###
} elsif("$opt{'check_type'}" eq "NFSOPS") {
        my $nfsops_per_seconds=floor ( ($total_nfs_ops-$fileNfsOps)/$elapsedtime );

        my $check=$nfsops_per_seconds;

        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "nfsops=$check";
### CIFSOPS ###
} elsif("$opt{'check_type'}" eq "CIFSOPS") {
        my $cifsops_per_seconds=floor ( ($total_cifs_ops-$fileCifsOps)/$elapsedtime );

        my $check=$cifsops_per_seconds;

        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "cifsops=$check";
### ISCSIOPS ###
} elsif("$opt{'check_type'}" eq "ISCSIOPS") {
        my $iscsiops_per_seconds=floor ( ($blocks_iscsi_ops-$fileIscsiOps)/$elapsedtime );
        my $iscsiread_per_seconds=floor ( ($blocks_iscsi_read-$fileIscsi64ReadBytes)/$elapsedtime );
        my $iscsiwrite_per_seconds=floor ( ($blocks_iscsi_write-$fileIscsi64WriteBytes)/$elapsedtime );
        my $diskread_per_seconds=floor ( ($total_disk_read-$fileDisk64ReadBytes)/$elapsedtime );
        my $diskwrite_per_seconds=floor ( ($total_disk_write-$fileDisk64WriteBytes)/$elapsedtime );
        my $check=$iscsiops_per_seconds;

        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $msg = "$msg ops/s (iscsi read=$iscsiread_per_seconds B/s, iscsi write=$iscsiwrite_per_seconds B/s, disk read=$diskread_per_seconds B/s, disk write=$diskwrite_per_seconds B/s)";
        $perf = "iscsiops=$check iscsiread=$iscsiread_per_seconds iscsiwrite=$iscsiwrite_per_seconds diskread=$diskread_per_seconds diskwrite=$diskwrite_per_seconds";
### FCPOPS ###
} elsif("$opt{'check_type'}" eq "FCPOPS") {
        my $fcpops_per_seconds=floor ( ($blocks_fcp_ops-$fileFcpOps)/$elapsedtime );
        my $fcpread_per_seconds=floor ( ($blocks_fcp_read-$fileFcp64ReadBytes)/$elapsedtime );
        my $fcpwrite_per_seconds=floor ( ($blocks_fcp_write-$fileFcp64WriteBytes)/$elapsedtime );
        my $diskread_per_seconds=floor ( ($total_disk_read-$fileDisk64ReadBytes)/$elapsedtime );
        my $diskwrite_per_seconds=floor ( ($total_disk_write-$fileDisk64WriteBytes)/$elapsedtime );

        my $check=$fcpops_per_seconds;

        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $msg = "$msg ops/s (fcp read=$fcpread_per_seconds B/s, fcp write=$fcpwrite_per_seconds B/s, disk read=$diskread_per_seconds B/s, disk write=$diskwrite_per_seconds B/s)";
        $perf = "fcpops=$check fcpread=$fcpread_per_seconds fcpwrite=$fcpwrite_per_seconds diskread=$diskread_per_seconds diskwrite=$diskwrite_per_seconds";
### NVRAM ###
} elsif("$opt{'check_type'}" eq "NVRAM") {
        my $check = _get_oid_value($snmp_session,$oid{nvramBatteryStatus});
        if($check == 1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $nvramBatteryStatus{$check}";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $nvramBatteryStatus{$check}";
        }
        $perf = "nvrambatterystatus=$check";
### DISKUSED ###
} elsif("$opt{'check_type'}" eq "DISKUSED") {

        FSyntaxError("Missing -v")  unless defined $opt{'vol'};

        my $r_vol_tbl = $snmp_session->get_table($oid{netapp_volume_id_table_df_name});
        foreach my $key ( keys %$r_vol_tbl) {
                if("$$r_vol_tbl{$key}" eq "$opt{'vol'}") {
                        my @tmp_arr = split(/\./, $key);
                        my $suboid = pop(@tmp_arr);
                        my $used = "";
                        my $capacity = "";
                        if ($opt{'version'} eq '2c') {
                                $used = _get_oid_value($snmp_session,"$oid{netapp_volume_id_table_df64_used}.$suboid");
                                $capacity = _get_oid_value($snmp_session,"$oid{netapp_volume_id_table_df64_total}.$suboid");
                        }
                        else {
                                my $used_high = _get_oid_value($snmp_session,"$oid{netapp_volume_id_table_df_used_high}.$suboid");
                                my $used_low  = _get_oid_value($snmp_session,"$oid{netapp_volume_id_table_df_used_low}.$suboid");
                                $used = _ulong64($used_high, $used_low);
                        }
                        my $used_prec = _get_oid_value($snmp_session,"$oid{netapp_volume_id_table_df_used_prec}.$suboid");

                        ($msg,$stat) = _clac_err_stat($used_prec,"$opt{'check_type'} $opt{'vol'}",$opt{'warn'},$opt{'crit'});

                        # https://nagios-plugins.org/doc/guidelines.html
                        # 'label'=value[UOM];[warn];[crit];[min];[max]
                        $perf =   "$$r_vol_tbl{$key}=$used\KB;" .floor($capacity*$opt{'warn'}/100) .";" .floor($capacity*$opt{'crit'}/100) .";;$capacity";
                        $perf .= " $$r_vol_tbl{$key}:perc=$used_prec\%;" .floor($opt{'warn'}) .";" .floor($opt{'crit'}) .";;100";
                }
        }
        if ($msg =~ /^$/) {
                $stat = $ERRORS{'WARNING'};
                $msg = "WARN: Unknown volume path or aggregate name '$opt{'vol'}'. Available values:";
                foreach my $key (sort keys %$r_vol_tbl) {
                        next if ( !( ($$r_vol_tbl{$key} =~ m#^/vol/.*$#) or ($$r_vol_tbl{$key} =~ m#^[^/]*$#) ) );
                        $msg .= " $$r_vol_tbl{$key}"
                }
                }
### SNAPSHOTAGE ###
} elsif("$opt{'check_type'}" eq "SNAPSHOTAGE") {

        my @exc_list = split(',',$opt{'exclude'});
        my @vol_list;
        my @vol_id;
        my @vol_err_ok;
        my @vol_err_war;
        my @vol_err_cri;
        my $loc_mon=(localtime(time()))[4]+1;
        my $loc_year=(localtime(time()))[5]+1900;
        my $loc_time = time();
        my $badcount = 0;
        my $r_snap_tbl = $snmp_session->get_table($oid{filesys_snapshot_slVTable_slVEntry});
        my $r_vol_tbl = $snmp_session->get_table($oid{filesys_snapshot_slVTable_slVEntry_number});
        foreach my $key ( keys %$r_vol_tbl) {
                my @tmp_oid = split(/\./, $key);
                my $nb_col = scalar @tmp_oid;
                push(@vol_list,"$tmp_oid[$nb_col-2]");
        }
        @vol_id = uniq(@vol_list);
        foreach my $vol_id (@vol_id) {
                my $Snap_year;
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry_number}.$vol_id.1";
                my $Nb_Snap = "$$r_vol_tbl{$key_tmp}";
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry}.9.$vol_id.$Nb_Snap";
                my $Vol_Name = "$$r_snap_tbl{$key_tmp}";
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry}.2.$vol_id.$Nb_Snap";
                my $Snap_mon = "$$r_snap_tbl{$key_tmp}";
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry}.3.$vol_id.$Nb_Snap";
                my $Snap_day = "$$r_snap_tbl{$key_tmp}";
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry}.4.$vol_id.$Nb_Snap";
                my $Snap_hour = "$$r_snap_tbl{$key_tmp}";
                my $key_tmp = "$oid{filesys_snapshot_slVTable_slVEntry}.5.$vol_id.$Nb_Snap";
                my $Snap_min = "$$r_snap_tbl{$key_tmp}";
                if ( $loc_mon >= $Snap_mon ) {
                        $Snap_year = $loc_year;
                } else {
                        $Snap_year = $loc_year-1;
                }
                my $Snap_time = timelocal(0,$Snap_min,$Snap_hour,$Snap_day,$Snap_mon-1,$Snap_year);
                my $Snap_delta = sprintf("%.2f", ($loc_time-$Snap_time)/86400);

                #print "Localtime : ".localtime($loc_time)." \n";
                #print "Localtime : ".localtime($Snap_time)." \n";
                #print "Vol_id=$vol_id Nb_Snap=$Nb_Snap Vol_Name=$Vol_Name Snap_mon=$Snap_mon Snap_day=$Snap_day Snap_hour=$Snap_hour Snap_min=$Snap_min localtime=$loc_time snap_time=$Snap_time Snap_delta=$Snap_delta War=$opt{'warn'} Crit=$opt{'crit'}\n";

                if (defined $opt{'vol'}) {
                        if ($opt{'vol'} eq "/vol/$Vol_Name/") {
                                if($Snap_delta > $opt{'warn'} and $Snap_delta < $opt{'crit'}) {
                                        push(@vol_err_war, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                } elsif($Snap_delta >= $opt{'crit'}) {
                                        push(@vol_err_cri, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                } else {
                                        push(@vol_err_ok, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                }
                        }
                } elsif (defined $opt{'exclude'}) {
                        my $volcheck = 0;
                        foreach my $exvol (@exc_list) {
                                if ($exvol eq "/vol/$Vol_Name/") {
                                        $volcheck++;
                                        #print "Exclude\n";
                                }
                        }
                        if($volcheck == 0) {
                                if($Snap_delta > $opt{'warn'} and $Snap_delta < $opt{'crit'}) {
                                        push(@vol_err_war, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                } elsif($Snap_delta >= $opt{'crit'}) {
                                        push(@vol_err_cri, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                } else {
                                        push(@vol_err_ok, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                                }
                        }
                } else {
                        if($Snap_delta > $opt{'warn'} and $Snap_delta < $opt{'crit'}) {
                                push(@vol_err_war, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                        } elsif($Snap_delta >= $opt{'crit'}) {
                                push(@vol_err_cri, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                        } else {
                                push(@vol_err_ok, "/vol/".$Vol_Name."/ : ".$Snap_delta."");
                        }
                }
        }
        my $err_ok = $#vol_err_ok + 1;
        my $err_war = $#vol_err_war + 1;
        my $err_cri = $#vol_err_cri + 1;
        $badcount += ($err_war+$err_cri);

        if (($err_cri == 0) && ($err_war == 0) && ($err_ok != 0)) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} @vol_err_ok ";
        } elsif ($err_cri != 0) {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT : $opt{'check_type'} $badcount outdated snapshots found, @vol_err_cri days old (> $opt{'crit'} d)";
        } elsif ($err_war != 0) {
                $stat = $ERRORS{'WARNING'};
                $msg = "WARN: $opt{'check_type'} $badcount outdated snapshots found, @vol_err_war days old (> $opt{'warn'} d)";
                } elsif (defined $opt{'vol'}) {
                $err_war = 1;
                $stat = $ERRORS{'WARNING'};
                $msg = "WARN: $opt{'check_type'} Unknown volume path name '$opt{'vol'}'. example \"/vol/vol0/\"";
        } else {
                $stat = $ERRORS{'UNKNOWN'};
                $msg = "UNKNOW Errors";
        }
$perf = "outdated_snapshots=$badcount";

### SNAPSHOT ###
} elsif("$opt{'check_type'}" eq "SNAPSHOT") {
        my @exc_list = split(',',$opt{'exclude'});
        my @vol_err;
        my $r_vol_tbl = $snmp_session->get_table($oid{filesysvolTablevolEntryvolName});
        foreach my $key ( keys %$r_vol_tbl) {
                my @tmp_arr = split(/\./, $key);
                my $suboid = pop(@tmp_arr);
                my $vol_tmp = "$$r_vol_tbl{$key}";

                my $volopt = _get_oid_value($snmp_session,"$oid{filesysvolTablevolEntryOptions}.$suboid");

                if($volopt !~ /nosnap=off/) {
                        my $volcheck = 0;
                        foreach my $exvol (@exc_list) {
                                if($exvol eq $vol_tmp) {
                                        $volcheck++;
                                        last;
                                }
                        }
                        if($volcheck == 0) {
                                push(@vol_err,"$vol_tmp");
                        }
                }
        }

        my $err_count = $#vol_err + 1;
        if($err_count == 0) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} all ok";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} @vol_err not configured";
        }
        $perf = "snapoff=$err_count";

### FAILEDDISK ###
} elsif("$opt{'check_type'}" eq "FAILEDDISK") {
        my $check = _get_oid_value($snmp_session,$oid{FailedDiskCount});
        if($check == 0) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $check";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $check";
        }
        $perf = "faileddisks=$check";

### DISKSUMMARY ###
} elsif("$opt{'check_type'}" eq "DISKSUMMARY") {
        my $diskTotal = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskTotalCount});
        my $diskActive = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskActiveCount});
        my $diskFailed = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskFailedCount});
        my $diskReconstructing = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskReconstructingCount});
        my $diskSpare = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskSpareCount});
        my $diskMessage = _get_oid_value($snmp_session,$oid{netapp_disksummary_diskFailedMessage});

        my $check=$diskFailed;

        if($check == 0) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} (".$diskMessage.") Disk Summary : Total->".$diskTotal." Active->".$diskActive." Spare->".$diskSpare." Failed ->".$diskFailed. " Reconstructing ->".$diskReconstructing;
        } elsif ($diskSpare>0) {
                $stat = $ERRORS{'WARNING'};
                $msg = "WARN: $opt{'check_type'} (".$diskMessage.") Disk Summary : Total->".$diskTotal." Active->".$diskActive." Spare->".$diskSpare." Failed ->".$diskFailed. " Reconstructing ->".$diskReconstructing;
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} (".$diskMessage.") Disk Summary : Total->".$diskTotal." Active->".$diskActive." Spare->".$diskSpare." Failed ->".$diskFailed. " Reconstructing ->".$diskReconstructing;
        }
        $perf = "faileddisks=$check total=$diskTotal active=$diskActive spare=$diskSpare reconstructing=$diskReconstructing";

### HA ###
} elsif("$opt{'check_type'}" eq "HA") {

        my $cfSettings = _get_oid_value($snmp_session,$oid{netapp_cfSettings});
        my $cfState = _get_oid_value($snmp_session,$oid{netapp_cfState});
        my $cfCannotTakeoverCause = _get_oid_value($snmp_session,$oid{netapp_cfCannotTakeoverCause});
        my $cfPartnerStatus = _get_oid_value($snmp_session,$oid{netapp_cfPartnerStatus});
        my $cfPartnerName = _get_oid_value($snmp_session,$oid{netapp_cfPartnerName});
        my $cfInterconnectStatus = _get_oid_value($snmp_session,$oid{netapp_cfInterconnectStatus});

        my $check=$cfSettings;

        if($cfSettings == 2) {


            if ( ($cfPartnerStatus != 2) or ($cfState != 2) or ($cfInterconnectStatus != 4) ) {
                    $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} HA Summary : Settings->".$cfSettingsIndex{$cfSettings}." State->".$cfStateIndex{$cfState}." Cannot Takeover Cause->".$cfCannotTakeoverCauseIndex{$cfCannotTakeoverCause}." Partner->".$cfPartnerName." Partner Status ->".$cfPartnerStatusIndex{$cfPartnerStatus}." Interconnection State->".$cfInterconnectStatusIndex{$cfInterconnectStatus};
            } else {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} HA Summary : Settings->".$cfSettingsIndex{$cfSettings}." State->".$cfStateIndex{$cfState}." Partner->".$cfPartnerName." Partner Status ->".$cfPartnerStatusIndex{$cfPartnerStatus}." Interconnection State->".$cfInterconnectStatusIndex{$cfInterconnectStatus};
            }

        } elsif ( ($cfSettings == 3) or ($cfSettings == 1) ) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} HA Summary : Settings ->".$cfSettingsIndex{$cfSettings};
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} HA Summary : Settings->".$cfSettingsIndex{$cfSettings}." State->".$cfStateIndex{$cfState}." Partner->".$cfPartnerName." Partner Status ->".$cfPartnerStatusIndex{$cfPartnerStatus}." Interconnection State->".$cfInterconnectStatusIndex{$cfInterconnectStatus};
        }
        $perf = "hasettings=$check";


### UPTIME ###
} elsif("$opt{'check_type'}" eq "UPTIME") {
        my $check = _get_oid_value($snmp_session,$oid{UpTime});
        $msg = "$opt{'check_type'}: $check";
        $check =~ m/^\s*(\d+)\s+days,\s+(\d+):(\d+):(\d+).*$/;
        $perf = "uptime=" . ($1*86400 + $2*3600 + $3*60 + $4) . "s";
### CACHEAGE ###
} elsif("$opt{'check_type'}" eq "CACHEAGE") {
        my $check = _get_oid_value($snmp_session,$oid{CacheAge});
        ($msg,$stat) = _clac_minutes_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "cache_age=$check";
### GLOBALSTATUS ###
} elsif("$opt{'check_type'}" eq "GLOBALSTATUS") {
        my $check = _get_oid_value($snmp_session,$oid{GlobalStatus});
        my $global_stat_txt = _get_oid_value($snmp_session,$oid{GlobalStatus_text});
        if($check == 3) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $GlobalStatusIndex{$check} $check $global_stat_txt";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $GlobalStatusIndex{$check} $check $global_stat_txt";
        }
        $perf = "globalstatus=$check";
### NODEHEALTH ###
} elsif("$opt{'check_type'}" eq "NODEHEALTH") {
        my $check = _get_oid_value($snmp_session,$oid{nodeHealth});
        if($check == 1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} Node can communicate with the cluster.";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} Node cannot communicate with the cluster.";
        }
        $perf = "nodehealth=$check";
### AUTOSUPPORTSTATUS ###
} elsif("$opt{'check_type'}" eq "AUTOSUPPORTSTATUS") {
        my $check = _get_oid_value($snmp_session,$oid{AutoSupportStatus});
        my $autosupport_stat_txt = _get_oid_value($snmp_session,$oid{AutoSupportStatus_text});
        if($check == 1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $AutoSupportStatusIndex{$check} $check $autosupport_stat_txt";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $AutoSupportStatusIndex{$check} $check $autosupport_stat_txt";
        }
        $perf = "autosupportstatus=$check";
### NDMPSESSIONS ###
} elsif("$opt{'check_type'}" eq "NDMPSESSIONS") {
        my $check = _get_oid_value($snmp_session,$oid{NdmpSessions});
        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "ndmpsess=$check";
### CIFSSESSIONS ###
} elsif("$opt{'check_type'}" eq "CIFSSESSIONS") {
        my $check = _get_oid_value($snmp_session,$oid{CifsSessions});
        ($msg,$stat) = _clac_absolute_err_stat($check,$opt{'check_type'},$opt{'warn'},$opt{'crit'});
        $perf = "cifssess=$check";
### SHELF ###
} elsif ( ("$opt{'check_type'}" eq "SHELF") or ("$opt{'check_type'}" eq "SHELFINFO") ) {
        my @errs;
        my $r_shelf = $snmp_session->get_table($oid{EnclTableIndex});
        my $r_volt  = $snmp_session->get_table($oid{EnclTableVoltPresent});
        my $r_volt_count = scalar (keys %$r_volt);
        #print Data::Dumper->Dump([$oid{EnclTableIndex},$r_shelf, $r_volt]);
        my $perf_temp = "";
        foreach my $key ( sort keys %$r_shelf) {
                my @tmp_arr = split(/\./, $key);
                my $suboid = pop(@tmp_arr);

                my %shelf;
                my @shelf_err;
                my $addr = _get_oid_value($snmp_session,"$oid{EnclTableShelfAddr}.$suboid");

                my $shelf_state = _get_oid_value($snmp_session,"$oid{EnclTableState}.$suboid");

                if($shelf_state != 3) {
                        push(@shelf_err,"$addr state $EcnlStatusIndex{$shelf_state},");
                }

                if ("$opt{'check_type'}" eq "SHELFINFO") {
                        my $shelf_temp =  _get_oid_value($snmp_session,"$oid{EnclTableCurrentTemp}.$suboid");
                        my @current_temp = split(/\,/, $shelf_temp );

                        $shelf{'ShelfNumber'} = $suboid;
                        $shelf{'CurrentTemp'} = shift(@current_temp);
                        $shelf{'ProductID'} = _get_oid_value($snmp_session,"$oid{EnclTableProductID}.$suboid");
                        $shelf{'ProductVendor'} = _get_oid_value($snmp_session,"$oid{EnclTableProductVendor}.$suboid");
                        $shelf{'ProductModel'} = _get_oid_value($snmp_session,"$oid{EnclTableProductModel}.$suboid");
                        $shelf{'ProductRevision'} = _get_oid_value($snmp_session,"$oid{EnclTableProductRevision}.$suboid");
                        $shelf{'ProductSerial'} = _get_oid_value($snmp_session,"$oid{EnclTableProductSerial}.$suboid");
                } else {
                        $shelf{'PsFail'} = _get_oid_value($snmp_session,"$oid{EnclTablePsFailed}.$suboid");
                        $shelf{'FanFail'} = _get_oid_value($snmp_session,"$oid{EnclTableFanFailed}.$suboid");
                        $shelf{'ElectFail'} = _get_oid_value($snmp_session,"$oid{EnclTableElectronicFailed}.$suboid");
                        $shelf{'TempOverFail'} = _get_oid_value($snmp_session,"$oid{EnclTableTempOverFail}.$suboid");
                        $shelf{'TempOver'} = _get_oid_value($snmp_session,"$oid{EnclTableTempOverWarn}.$suboid");
                        $shelf{'TempUnderFail'} = _get_oid_value($snmp_session,"$oid{EnclTableTempUnderFail}.$suboid");
                        $shelf{'TempUnderWarn'} = _get_oid_value($snmp_session,"$oid{EnclTableTempUnderWarn}.$suboid");
                        $shelf{'VoltOverFail'} = _get_oid_value($snmp_session,"$oid{EnclTableVoltOverFail}.$suboid") if $suboid <= $r_volt_count;
                        $shelf{'VoltOverWarn'} = _get_oid_value($snmp_session,"$oid{EnclTableVoltOverWarn}.$suboid") if $suboid <= $r_volt_count;
                        $shelf{'VoltUnderFail'} = _get_oid_value($snmp_session,"$oid{EnclTableVoltUnderFail}.$suboid") if $suboid <= $r_volt_count;
                        $shelf{'VoltUnderWarn'} = _get_oid_value($snmp_session,"$oid{EnclTableVoltUnderWarn}.$suboid") if $suboid <= $r_volt_count;
                }


                foreach my $subkey ( keys %shelf) {
                    if ( ($shelf{$subkey} ne "") and ($shelf{$subkey} ne "noSuchInstance") ) {
                        if ( "$subkey" eq "CurrentTemp" ) {
                                $shelf{$subkey} =~ m/^([0-9]+)C.*$/;
                                $perf_temp = "$perf_temp, temp_$shelf{'ShelfNumber'}=$1";
                        }
                    }
                    #else { print "$subkey->"; print "None "; }
                        if ("$opt{'check_type'}" eq "SHELF") {
                        if(($shelf{$subkey} ne "") and ($shelf{$subkey} ne "noSuchInstance")) { push(@shelf_err,"$addr $subkey,") }
                        }
                }

                #{ print "\n"; }
                #if ("$opt{'check_type'}" eq "SHELF") { print "\n"; }

                if($#shelf_err != -1) {
                        push(@errs,@shelf_err)
                }
        }

        if($#errs == -1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} ok";
                if ("$opt{'check_type'}" eq "SHELFINFO")
                { $perf = "shelfinfo=0$perf_temp"; }
                else
                { $perf = "shelf=0"; }
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} Errors -";
                foreach(@errs) {
                        $msg = "$msg $_";
                }
                if ("$opt{'check_type'}" eq "SHELFINFO")
                { $perf = "shelfinfo=1$perf_temp"; }
                else
                { $perf = "shelf=1"; }
        }
### FSSTATUS ###
} elsif("$opt{'check_type'}" eq "FSSTATUS") {
        my $check = _get_oid_value($snmp_session,$oid{fsOverallStatus});
        my $global_stat_txt = _get_oid_value($snmp_session,$oid{fsOverallStatus_text});
        if($check == 1) {
                $stat = $ERRORS{'OK'};
                $msg = "OK: $opt{'check_type'} $fsOverallStatusIndex{$check} $check $global_stat_txt";
        }elsif($check == 2) {
                $stat = $ERRORS{'WARNING'};
                $msg = "WARN: $opt{'check_type'} $fsOverallStatusIndex{$check} $check $global_stat_txt";
        } else {
                $stat = $ERRORS{'CRITICAL'};
                $msg = "CRIT: $opt{'check_type'} $fsOverallStatusIndex{$check} $check $global_stat_txt";
        }
        $perf = "fsstatus=$check";

### Syntax Error ###
} else {
        FSyntaxError("$opt{'check_type'} invalid parameter !");
}

$msg =~ s/\n//g;
$perf ? print "$msg | $perf\n" : print "$msg\n";

exit($stat);
