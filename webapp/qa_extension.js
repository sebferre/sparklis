// reporting that this extension is active
console.log("QA extension active");

// upon window load... create text field and ENTER handler
window.addEventListener(
    'load',
    function(ev) {
	let qa = document.getElementById("qa");
	qa.addEventListener("keyup", function(event) {
	    if (event.keyCode == 13) { // ENTER
		event.stopPropagation();
		process_question(qa);
	    }
	})
    });

/* processing a question, i.e. a sequence of steps */

// process user question, available in qa HTML element
function process_question(qa) {
    let question = qa.value;
    console.log("Question: " + question);
    let steps = question.split(/\s*;\s*/).filter(s => s !== '');
    console.log("Steps: " + steps);
    let place = sparklis.currentPlace();
    process_steps(qa, place, steps);
}

// starting from place, apply sequence of steps as far as possible
function process_steps(qa, place, steps) {
    if (steps.length === 0) {
	console.log("QA search completed");
    } else {
	let first_step = steps[0];
	process_step(place, first_step)
	    .then(next_place => {
		let next_steps = steps.slice(1);
		qa.value = next_steps.join(" ; "); // update qa field
		sparklis.setCurrentPlace(next_place); // update Sparklis view
		process_steps(qa, next_place, next_steps); // continue with next steps from there
	    })
	    .catch(msg => {
		console.log("QA search halted because " + msg);
	    })
    }
}

/* processing a single step */

// applying step to place, returning a promise of the next place
function process_step(place, step) {
    console.log("Step: ", step);
    let match;
    if (step === "up") {
	return move_focus(place, move_up)
    } else if (step === "down") {
	return move_focus(place, move_down)
    } else if (step === "and") {
	return apply_suggestion(place, "and", "IncrAnd")
    } else if (step === "or") {
	return apply_suggestion(place, "or", "IncrOr")
    } else if (step === "not") {
	return apply_suggestion(place, "not", "IncrNot")
    } else if (step === "maybe") {
	return apply_suggestion(place, "maybe", "IncrMaybe")
    } else if (step === "asc") {
	let sugg = { type: "IncrOrder", order: { type: "ASC", conv: { targetType: "Double", forgetOriginalDatatype: false } } };
	return apply_suggestion(place, "asc-order", sugg)
    } else if (step === "desc") {
	let sugg = { type: "IncrOrder", order: { type: "DESC", conv: { targetType: "Double", forgetOriginalDatatype: false } } };
	return apply_suggestion(place, "desc-order", sugg)
    } else if ((match = /^after\s+(.+)$/.exec(step))) {
	let constr = { type: "After", kwd: match[1] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "after", sugg)
    } else if ((match = /^before\s+(.+)$/.exec(step))) {
	let constr = { type: "Before", kwd: match[1] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "before", sugg)
    } else if ((match = /^from\s+(.+)\s+to\s+(.+)$/.exec(step))) {
	let constr = { type: "FromTo", kwdFrom: match[1], kwdTo: match[2] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "from-to", sugg)
    } else if ((match = /^>\s*(.+)$/.exec(step))) {
	let constr = { type: "HigherThan", value: match[1] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "higher-than", sugg)
    } else if ((match = /^<\s*(.+)$/.exec(step))) {
	let constr = { type: "LowerThan", value: match[1] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "lower-than", sugg)
    } else if ((match = /^between\s+(.+)\s+and\s+(.+)$/.exec(step))) {
	let constr = { type: "Between", valueFrom: match[1], valueTo: match[2] };
	let sugg = {type: "IncrConstr", constr: constr, filterType: "OnlyLiterals"};
	return apply_suggestion(place, "between", sugg)
    } else if ((match = /^a\s+(.+)\s*$/.exec(step))) {
	return search_and_apply_suggestion(
	    place, "class", match[1],
	    (place,constr) => place.getConceptSuggestions(false,constr),
	    sugg => suggestion_type(sugg) === "IncrType",
	    sparklis.classLabels())
    } else if ((match = /^has\s+(.+)$/.exec(step))) {
	return search_and_apply_suggestion(
	    place, "fwd property", match[1],
	    (place,constr) => place.getConceptSuggestions(false,constr),
	    sugg =>
	    suggestion_type(sugg) === "IncrRel" && sugg.orientation === "Fwd"
		|| suggestion_type(sugg) === "IncrPred" && sugg.arg === "S",
	    sparklis.propertyLabels())
    } else if ((match = /^is\s+(.+)\s+of$/.exec(step))) {
	return search_and_apply_suggestion(
	    place, "bwd property", match[1],
	    (place,constr) => place.getConceptSuggestions(false,constr),
	    sugg =>
	    suggestion_type(sugg) === "IncrRel" && sugg.orientation === "Bwd"
		|| suggestion_type(sugg) === "IncrPred" && sugg.arg === "O",
	    sparklis.propertyLabels())
    } else {
	return search_and_apply_suggestion(
	    place, "term", step,
	    (place,constr) => place.getTermSuggestions(false,constr),
	    sugg => suggestion_type(sugg) === "IncrTerm" && sugg.term.type === "uri",
	    sparklis.termLabels())
    }
}

function move_focus(place, move) {
    return new Promise((resolve, reject) => {
	let path = place.focusPath();
	let next_path = move(path);
	let next_place = place.focusAtPath(next_path);
	resolve(next_place)
    })
}

function apply_suggestion(place, kind, sugg) {
    return new Promise((resolve, reject) => {
	let next_place = place.applySuggestion(sugg);
	resolve(next_place);
    })
}
    
function search_and_apply_suggestion(place, kind, query, getSuggestions, filterSuggestion, lexicon) {
    return new Promise((resolve, reject) => {
	get_constr(kind, query)
	    .then(constr => {
		console.log(kind, "constr : ", constr);
		place.onEvaluated(() => {
		    getSuggestions(place, constr)
			.then(res => {
			    let forest = res.forest;
			    console.log("got suggestions for constraint");
			    //console.log(forest);
			    let best_sugg = select_sugg(kind, query, forest, filterSuggestion, lexicon);
			    if (!best_sugg) {
				reject("no suggestion found");
			    } else {
				console.log("choosing suggestion:");
				console.log(best_sugg);
				let next_place = place.applySuggestion(best_sugg);
				resolve(next_place);
			    }
			})
			.catch(() => {
			    reject(kind + " not found");
			})
		})
	    })
	    .catch(error => {
		reject(kind + " search failed");
	    })
    })
}		       

// defining a constraint promise from kind and query
function get_constr(kind, query) {
    return new Promise((resolve, reject) => {
	let input_wikidata = document.getElementById("input-wikidata-mode");
	if (input_wikidata.checked) {
	    let search =
		{ type: "WikidataSearch",
		  kwds: query.split(/\s+/) };
	    sparklis.externalSearchConstr(search)
		.then(constr => resolve(constr))
		.catch(reject);
	} else {
	    let constr =
		{ type: "MatchesAll",
		  kwds: query.split(/\s+/) };
	    resolve(constr);
	}
    })
}

// selecting the most frequent suggestion satisfying pred
function select_sugg(kind, query, forest, pred, lexicon) {
    var best_item = null;
    var best_score = null;
    forest.forEach(function(tree) {
	let item = tree.item;
	if (pred(item.suggestion)) {
	    let score = get_score(lexicon, kind, query, item);
	    if (best_item === null
		|| best_score === null
		|| (score !== null && best_score !== null
		    && score > best_score)) {
		best_item = item;
		best_score = score;
	    }
	}
    });
    return best_item.suggestion;
}

// computing score of item for suggestion choice
function get_score(lexicon, kind, query, item) {
    let freq = item_frequency(item);
    let uri = suggestion_uri(item.suggestion);
    if (uri === null) {
	return 0;
    } else {
	let label = lexicon.info(uri);
	if (typeof label !== "string") {
	    label = label.label;
	};
	let dist = editDistance(query,label);
	let score = freq * (1 / (1 + dist));
	console.log("score=", score, ", freq=", freq, ", dist=", dist, ", label=", label, ", uri=", uri);
	return score;
    }
}

/* utility functions */

function move_up(path) {
    let lastDownIndex = path.lastIndexOf("DOWN");
    if (lastDownIndex === -1) {
	return path;
    } else {
	return path.slice(0, lastDownIndex);
    }
}

function move_down(path) {
    return [...path, "DOWN"];
}

function item_frequency(item) {
    if (item.frequency === null) {
	return 0;
    } else {
	return item.frequency.value;
    }
}

function suggestion_type(sugg) {
    if (typeof sugg === "string") {
	return sugg;
    } else {
	return sugg.type;
    }
}

function suggestion_uri(sugg) {
    switch (sugg.type) {
    case "IncrType":
	return sugg.uri;
    case "IncrRel":
	return sugg.uri;
    case "IncrPred":
	let pred = sugg.pred;
	switch (pred.type) {
	case "Class":
	    return pred.uri;
	case "Prop":
	    return pred.uri;
	case "SO":
	    return pred.uriO;
	case "EO":
	    return pred.uriE;
	default:
	    return null;
	}
    case "IncrTerm":
	let term = sugg.term;
	switch (term.type) {
	case "uri":
	    return term.uri;
	default:
	    return null;
	}
    }
}

function editDistance(str1, str2) {
    const len1 = str1.length;
    const len2 = str2.length;
    
    // Create a 2D array to store distances
    const dp = Array(len1 + 1).fill(null).map(() => Array(len2 + 1).fill(null));

    // Initialize base cases
    for (let i = 0; i <= len1; i++) dp[i][0] = i;
    for (let j = 0; j <= len2; j++) dp[0][j] = j;

    // Compute distances
    for (let i = 1; i <= len1; i++) {
        for (let j = 1; j <= len2; j++) {
            const cost = str1[i - 1] === str2[j - 1] ? 0 : 1;
            dp[i][j] = Math.min(
                dp[i - 1][j] + 1,    // Deletion
                dp[i][j - 1] + 1,    // Insertion
                dp[i - 1][j - 1] + cost // Substitution
            );
        }
    }

    return dp[len1][len2];
}

// example steps
// on DBpedia Core: a film; has director; Tim Burton; down; or; Spielberg; up; up; has starring ; has birthdate ; after 1980
// on DBpedia Core: a film ; has budget ; desc ; > 1e7

