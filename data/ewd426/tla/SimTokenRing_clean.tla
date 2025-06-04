-------------------------------- MODULE SimTokenRing -------------------------------
EXTENDS TokenRing, TLC, CSV, IOUtils

ASSUME TLCGet("config").mode = "generate"

CSVFile ==
"SimTokenRing.csv"

ASSUME

/\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization ==

UniqueToken =>
/\ CSVWrite("%1$s", <<TLCGet("level")>>,CSVFile)
/\ TLCGet("stats").traces % 250 = 0 =>
/\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0
/\ FALSE

=======================================================================================
$ rm -rf states/ ; rm *.csv ; tlc SimTokenRing -note -generate -depth -1

$ alias tlc
tlc='java -cp /path/to/tla2tools.jar tlc2.TLC'
