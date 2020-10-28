<?

/* ---- timed log of hits with IPs ---- */

$timed_log_name = "hitlog.txt";

// define log file path
$timed_log_file = dirname(__FILE__) . '/' . $timed_log_name;
//echo $timed_log_file, "<br>";

// append date/time to message
$timed_line = date(DATE_ATOM) . "," . $_SERVER['REMOTE_ADDR'] . "," . $_SERVER['QUERY_STRING'] . "\n";
//echo $timed_line, "<br>";

// add line to log file
file_put_contents($timed_log_file, $timed_line, FILE_APPEND);


/*----------------------------

-------- ++ simPHP ++ --------
A simple PHP hit counter.

Description:
   simPHP counts both regular and unique views on multiple
   webpages. The stats can be displayed on any PHP-enabled
   webpage. You MUST have read/write permissions on files.

Script by Ajay: ajay@scyberia.org
http://scyberia.org

----------------------------*/



/*----------CONFIG----------*/

// NOTE: If you change any config after using simphp,
// remove the old files.

// Relative URL of text file that holds hit info:
$lf_name = "hits.txt";

// Save new log file each month
//   0 = No
//   1 = Yes
$monthly = 1;

// Path to store old files:
// Default for June, 2012:
//   oldfiles/6-12.txt
$monthly_path = "oldfiles";

// Count unique hits or all hits:
//   0 = All hits
//   1 = Unique hits
//   2 = Both
$type = 2;

// Text to display
// before all hits.
$beforeAllText = "Hits: ";

// Before unique hits.
$beforeUniqueText = "Unique Visits: ";

// Display hits on this page:
//   0 = No
//   1 = Yes
$display = 1;

// Only change this if you are recording both values.
// Separator for unique and all hits display - use HTML tags! (line break is default)
$separator = "<br \>";

// Default would output:
//   Visits: 10
//   Unique Visits: 10
/*--------------------------*/






/*--------BEGIN CODE--------*/

$log_file = dirname(__FILE__) . '/' . $lf_name;

//Check for "?display=true" in URL.
if ($_GET['display'] == "true") {
	//Show include() info.
	die("<pre>&#60;? include(\"" . dirname(__FILE__) . '/' . basename(__FILE__) . "\"); ?&#62;</pre>");
} else {
	//Visit or IP.
	$uIP = $_SERVER['REMOTE_ADDR'];

	//Check for "hits.txt" file.
	if (file_exists($log_file)) {
		//Check if today is first day of month
		if (date('j') == 10) {
			//Ensure that monthly dir exists
			if (!file_exists($monthly_path)) {
				mkdir($monthly_path);
			}

			//Check if prev month log file exists already
			$prev_name = $monthly_path . '/' . date("n-Y", strtotime("-1 month"));
			if (!file_exists($prev_name)) {
				//If not, move/rename current file
				copy($log_file, $prev_name);

				//Create new $toWrite based on CONFIG
				//Write file according to CONFIG above.
				if ($type == 0) {
					$toWrite = "1";
					$info = $beforeAllText . "1";
				} else if ($type == 1) {
					$toWrite = "1;" . $uIP . ",";
					$info = $beforeUniqueText . "1";
				} else if ($type == 2) {
					$toWrite = "1;1;" . $uIP . ",";
					$info = $beforeAllText . "1" . $separator . $beforeUniqueText . "1";
				}
				goto write_logfile;
			}
		}

		//Get contents of "hits.txt" file.
		$log = file_get_contents($log_file);

		//Get type from CONFIG above.
		if ($type == 0) {

			//Create info to write to log file and info to show.
			$toWrite = intval($log) + 1;
			$info = $beforeAllText . $toWrite;

		} else if ($type == 1) {

			//Separate log file into hits and IPs.
			$hits = reset(explode(";", $log));
			$IPs = end(explode(";", $log));
			$IPArray = explode(",", $IPs);

			//Check for visitor IP in list of IPs.
			if (array_search($uIP, $IPArray, true) === false) {
				//If doesnt' exist increase hits and include IP.
				$hits = intval($hits) + 1;
				$toWrite = $hits . ";" . $IPs . $uIP . ",";
			} else {
				//Otherwise nothing.
				$toWrite = $log;
			}
			//Info to show.
			$info = $beforeUniqueText . $hits;

		} else if ($type == 2) {

			//Position of separators.
			$c1Pos = strpos($log, ";");
			$c2Pos = strrpos($log, ";");

			//Separate log file into regular hits, unique hits, and IPs.
			$pieces = explode(";", $log);
			$allHits = $pieces[0];
			$uniqueHits = $pieces[1];
			$IPs = $pieces[2];
			$IPArray = explode(",", $IPs);

			//Increase regular hits.
			$allHits = intval($allHits) + 1;

			//Search for visitor IP in list of IPs.
			if (array_search($uIP, $IPArray, true) === false) {
				//Increase ONLY unique hits and append IP.
				$uniqueHits = intval($uniqueHits) + 1;
				$toWrite = $allHits . ";" . $uniqueHits . ";" . $IPs . $uIP . ",";
			} else {
				//Else just include regular hits.
				$toWrite = $allHits . ";" . $uniqueHits . ";" . $IPs;
			}
			//Info to show.
			$info = $beforeAllText . $allHits . $separator . $beforeUniqueText . $uniqueHits;
		}
	} else {
		//If "hits.txt" doesn't exist, create it.
		$fp = fopen($log_file ,"w");
		fclose($fp);

		//Write file according to CONFIG above.
		if ($type == 0) {
			$toWrite = "1";
			$info = $beforeAllText . "1";
		} else if ($type == 1) {
			$toWrite = "1;" . $uIP . ",";
			$info = $beforeUniqueText . "1";
		} else if ($type == 2) {
			$toWrite = "1;1;" . $uIP . ",";
			$info = $beforeAllText . "1" . $separator . $beforeUniqueText . "1";
		}
	}

	write_logfile:
	//Put $toWrite in log file
	file_put_contents($log_file, $toWrite);

	//Display info if is set in CONFIG.
	if ($display == 1) {
		echo $info;
	}
}
?>
