<?

/* ---- timed log of queries ---- */
/* date/time, IP#session, endpoint, query */

$query_log_name = "querylog.txt";

// define log file path
$query_log_file = dirname(__FILE__) . '/' . $query_log_name;
//echo $query_log_file, "<br>";

// define line
parse_str($_SERVER['QUERY_STRING']); // extracting GET variables 'endpoint' and 'query'
$query_line = date(DATE_ATOM) . "," . $_SERVER['REMOTE_ADDR'] . "#" . $session . "," . $endpoint . "," . $query . "\n";

// add line to querylog file
file_put_contents($query_log_file, $query_line, FILE_APPEND);

?>
