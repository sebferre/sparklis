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

// process user question, available qa HTML element
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

// applying step to place, returning a promise of the next place
function process_step(place, step) {
    return new Promise((resolve, reject) => {
	console.log("Step: ", step);
	let step_kwds = step.split(/\s+/);
	console.log("Kwds: ", step_kwds);
	let constr = { type: "MatchesAll", kwds: step_kwds };
	let char0 = step.charAt(0);
	if (char0 === char0.toUpperCase()) {
	    place.onEvaluated(() => {
		place
		    .getTermSuggestions(false, constr)
		    .then(suggs => {
			console.log("got term suggestions for constraint");
			//console.log(suggs);
			let best_sugg = select_sugg(suggs);
			let labels = sparklis.termLabels();
			console.log("choosing suggestion: " + labels.info(best_sugg.term.uri));
			let next_place = place.applySuggestion(best_sugg);
			resolve(next_place);
		    })
		    .catch(() => {
			reject("Term not found");
		    })
	    })
	} else {
	    place.onEvaluated(() => {
		place
		    .getConceptSuggestions(false, constr)
		    .then(suggs => {
			console.log("got concept suggestions for constraint");
			//console.log(suggs);
			let best_sugg = select_sugg(suggs);
			console.log("choosing suggestion:");
			console.log(best_sugg);
			let next_place = place.applySuggestion(best_sugg);
			resolve(next_place);
		    })
		    .catch(() => {
			reject("Concept not found");
		    })
	    })
	};
    })
}

// selecting the most frequent suggestion
function select_sugg(suggs) {
    let forest = suggs.forest;
    var best_item = forest[0].item;
    forest.forEach(function(sugg) {
	if (best_item.frequency == null
	    || (sugg.item.frequency != null
		&& (sugg.item.frequency.value > best_item.frequency.value))) {
	    best_item = sugg.item;
	}
    });
    return best_item.suggestion;
}
