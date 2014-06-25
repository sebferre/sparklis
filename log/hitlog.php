<?

$log_name = "hitlog.txt";

// define log file path
$log_file = dirname(__FILE__) . '/' . $log_name;
echo $log_file, "<br>";

// append date/time to message
$line = date(DATE_ATOM) . "," . $_SERVER['REMOTE_ADDR'] . "," . $_SERVER['QUERY_STRING'] . "\n";
echo $line, "<br>";

// add line to log file
file_put_contents($log_file, $line, FILE_APPEND);

// display message
echo "Done";

?>
