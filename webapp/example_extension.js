// reporting that this extension is active
console.log("example extension active");
// defining a fixed suggestion
const sugg_a_city = {
  "type": "IncrType",
  "uri": "http://www.semwebtech.org/mondial/10/meta#City"
};
window.addEventListener(
    'load',
    function(ev) {
	// inserting a new button
	document
	    .getElementById("increments")
	    .insertAdjacentHTML('beforeend', "<button id=\"a-city\">a city</button>");
	var button = document.getElementById("a-city");
	// and using it to activate the fixed suggestion
	button.onclick =
	    function() {
		sparklis.activateSuggestion(sugg_a_city);
		//var p = sparklis.currentPlace().applySuggestion(sugg_a_city);
		//window.alert("The new place has been computed and will now be displayed");
		//sparklis.setCurrentPlace(p);
	    };
	// inserting a text field above query
	document.
	    getElementById("query").
	    insertAdjacentHTML('beforebegin', '<input id="qa" class="form-control" type="text">');
	var qa = document.getElementById("qa");
	qa.addEventListener("keyup", function(event) {
	    if (event.keyCode == 13) { // ENTER
		console.log("qa kwd entered: [" + qa.value + "]");
		var constr = { type: "MatchesAll", kwds: [qa.value] };
		function select_sugg(suggs) {
		    var best_item = suggs[0].item;
		    suggs.forEach(function(sugg) {
			if (best_item.frequency == null || sugg.item.frequency != null && sugg.item.frequency.value > best_item.frequency.value) {
			    best_item = sugg.item;
			}
		    });
		    return best_item.suggestion;
		};
		var char0 = qa.value.charAt(0);
		if (char0 === char0.toUpperCase()) {
		    //sparklis.setTermConstr(constr);
		    sparklis
			.currentPlace()
			.getTermSuggestions(false, constr, function(partial,suggs) {
			    console.log("got suggestions for constraint");
			    console.log(suggs);
			    let best_sugg = select_sugg(suggs);
			    //var fst_sugg = suggs[0].item.suggestion;
			    let labels = sparklis.termLabels();
			    console.log("choosing suggestion: " + best_sugg + " => " + labels.info(best_sugg.term.uri));
			    sparklis.activateSuggestion(best_sugg);
			})
		} else {
		    //sparklis.setConceptConstr(constr);
		    sparklis
			.currentPlace()
			.getConceptSuggestions(false, constr, function(partial,suggs) {
			    console.log("got suggestions for constraint");
			    console.log(suggs);
			    //var fst_sugg = suggs[0].item.suggestion;
			    let best_sugg = select_sugg(suggs);
			    console.log("choosing suggestion: " + best_sugg);
			    sparklis.activateSuggestion(best_sugg);
			})
		};
		qa.value = "";
	    }});
	
    });
// example SPARQL hook: adding a dummy PREFIX
sparklis_extension.hookSparql =
    function(sparql) {
	console.log("endpoint:", sparklis.endpoint());
	console.log("query:", sparklis.currentPlace().query());
	console.log("delta: ", sparklis.currentPlace().delta());
	console.log("permalink:", sparklis.currentPlace().permalink());
	console.log("SPARQL query:", sparql);
	return sparql
	//console.log("Here a dummy PREFIX is added.");
	//return "PREFIX foo: <http://foo.com/>\n" + sparql
    };
// example results hook: keeping only the two first results
sparklis_extension.hookResults =
    function(results) {
	console.log("results", results);
	// testing direct SPARQL call to the endpoint
	sparklis.evalSparql("SELECT * WHERE { ?x a ?c } LIMIT 10",
			    function(res) { console.log("other results:", res); },
			    function(code) { console.log("failed to get the other results, error", code); });
	console.log("Here the first two rows of the results will be selected.");
	//results.rows = results.rows.slice(0,2);
	return results
    };
// example suggestions hook: looking for suggestions matching 'city'
flag = true;
sparklis_extension.hookSuggestions =
    function(suggestions) {
	console.log("2 suggestions", suggestions.type, suggestions.forest.slice(0,2));
	if (suggestions.type == "Concepts" && flag) {
	    flag = false;
	    constr = { "type": "MatchesAll", "kwds": ["city"] };
	    sparklis.currentPlace().getConceptSuggestions(
		false, constr,
		function(partial,suggs) {
		    console.log("all suggestions matching 'city'", suggs);
		    flag = true;
		})
	}
    };
// example apply-suggestion hook: just logging and applying the suggestion
sparklis_extension.hookApplySuggestion =
    function(place,sugg) {
	console.log("applied suggestion", sugg);
	new_place = place.applySuggestion(sugg);
	//console.log("new place", new_place);
	return new_place
    };
