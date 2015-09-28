
class virtual grammar =
object
  method virtual adjective_before_noun : bool

  method virtual thing : string
  method virtual relation : string
  method virtual is : string
  method virtual has : string
  method virtual has_as_a : string
  method virtual relative_that : string
  method virtual whose : string

  method virtual and_ : string
  method virtual or_ : string
  method virtual not_ : string
  method virtual optionally : string
  method virtual optional : string

  method virtual of_ : string
  method virtual genetive_suffix : string option
  method virtual rel_to : string
  method virtual rel_from : string

  method virtual a_an : following:string -> string
  method virtual the : string
  method virtual each : string
  method virtual all : string
  method virtual no : string
  method virtual any : string
  method virtual quantif_one : string
  method virtual quantif_of : string
  method virtual something : string
  method virtual anything : string
  method virtual everything : string
  method virtual nothing : string
  method virtual for_ : string

  method virtual n_th : int -> string

  method virtual aggreg_number : string * [`Noun | `Adjective]
  method virtual aggreg_list : string * [`Noun | `Adjective]
  method virtual aggreg_total : string * [`Noun | `Adjective]
  method virtual aggreg_average : string * [`Noun | `Adjective]
  method virtual aggreg_maximum : string * [`Noun | `Adjective]
  method virtual aggreg_minimum : string * [`Noun | `Adjective]
  method virtual aggreg_sample : string * [`Noun | `Adjective ]
  method virtual aggreg_given : string * [`Noun | `Adjective]

  method virtual order_highest : string
  method virtual order_lowest : string

  method virtual matches : string
  method virtual after : string
  method virtual before : string
  method virtual interval_from : string
  method virtual interval_to : string
  method virtual higher_or_equal_to : string
  method virtual lower_or_equal_to : string
  method virtual interval_between : string
  method virtual interval_and : string
  method virtual language : string
  method virtual datatype : string
  method virtual matching : string

  method virtual give_me : string
  method virtual there_is : string
  method virtual it_is_true_that : string

  method virtual tooltip_open_resource : string
  method virtual tooltip_delete_current_focus : string
  method virtual tooltip_remove_element_at_focus : string
  method virtual tooltip_focus_on_property : string
  method virtual tooltip_or : string
  method virtual tooltip_optionally : string
  method virtual tooltip_not : string
  method virtual tooltip_any : string
  method virtual tooltip_aggreg : string
  method virtual tooltip_foreach : string
  method virtual tooltip_highest : string
  method virtual tooltip_lowest : string
  method virtual tooltip_header_hide_focus : string
  method virtual tooltip_header_set_focus : string

  method virtual msg_permalink : string
  method virtual result_results : string * string
  method virtual entity_entities : string * string
  method virtual concept_concepts : string * string
  method virtual modifier_modifiers : string * string
end

let english =
object
  inherit grammar

  method adjective_before_noun = true

  method thing = "thing"
  method relation = "relation"
  method is = "is"
  method has = "has"
  method has_as_a = "has as a"
  method relative_that = "that"
  method whose = "whose"

  method and_ = "and"
  method or_ = "or"
  method not_ = "not"
  method optionally = "optionally"
  method optional = "optional"

  method of_ = "of"
  method genetive_suffix = Some "'s"
  method rel_to = "to"
  method rel_from = "from"

  method a_an ~following =
    let starts_with_vowel =
      try
	let c = Char.lowercase following.[0] in
	c = 'a' || c = 'e' || c = 'i' || c = 'o' (* || c = 'u' : 'u' is more often pronounced [y] *)
      with _ -> false in
    if starts_with_vowel
    then "an"
    else "a"
  method the = "the"
  method each = "each"
  method all = "all"
  method no = "no"
  method any = "any"
  method quantif_one = "one"
  method quantif_of = "of"
  method something = "something"
  method anything = "anything"
  method everything = "everything"
  method nothing = "nothing"
  method for_ = "for"

  method n_th n =
    let suffix =
      if n mod 10 = 1 && not (n mod 100 = 11) then "st"
      else if n mod 10 = 2 && not (n mod 100 = 12) then "nd"
      else if n mod 10 = 3 && not (n mod 100 = 13) then "rd"
      else "th" in
    string_of_int n ^ suffix

  method aggreg_number = "number", `Noun
  method aggreg_list = "list", `Noun
  method aggreg_total = "total", `Adjective
  method aggreg_average = "average", `Adjective
  method aggreg_maximum = "maximum", `Adjective
  method aggreg_minimum = "minimum", `Adjective
  method aggreg_sample = "sample", `Adjective
  method aggreg_given = "given", `Adjective

  method order_highest = "highest-to-lowest"
  method order_lowest = "lowest-to-highest"

  method matches = "matches"
  method after = "after"
  method before = "before"
  method interval_from = "from"
  method interval_to = "to"
  method higher_or_equal_to = "higher or equal to"
  method lower_or_equal_to = "lower or equal to"
  method interval_between = "between"
  method interval_and = "and"
  method language = "language"
  method datatype = "datatype"
  method matching = "matching"

  method give_me = "give me"
  method there_is = "there is"
  method it_is_true_that = "it is true that"

  method tooltip_open_resource = "Open resource in new window"
  method tooltip_delete_current_focus = "Click on this red cross to delete the current focus"
  method tooltip_remove_element_at_focus = "Remove this query element at the query focus"
  method tooltip_focus_on_property = "Adds a focus on the property to refine it"
  method tooltip_or = "Insert an alternative to the current focus"
  method tooltip_optionally = "Make the current focus optional"
  method tooltip_not = "Apply negation to the current focus"
  method tooltip_any = "Hide the focus column in the table of results"
  method tooltip_aggreg = "Aggregate the focus column in the table of results" (*, for each solution on other columns *)
  method tooltip_foreach = "Compute the aggregation for each value of this entity"
  method tooltip_highest = "Sort the focus column in decreasing order"
  method tooltip_lowest = "Sort the focus column in increasing order"
  method tooltip_header_hide_focus = "Click on this column header to hide the focus"
  method tooltip_header_set_focus = "Click on this column header to set the focus on it"

  method msg_permalink = "The following URL points to the current endpoint and query (Ctrl+C, Enter to copy to clipboard)."
  method result_results = "result", "results"
  method entity_entities = "entity", "entities"
  method concept_concepts = "concept", "concepts"
  method modifier_modifiers = "modifier", "modifiers"
end

let french =
object
  inherit grammar

  method adjective_before_noun = false

  method thing = "chose"
  method relation = "relation"
  method is = "est"
  method has = "a"
  method has_as_a = "a pour"
  method relative_that = "qui"
  method whose = "dont l'"

  method and_ = "et"
  method or_ = "ou"
  method not_ = "pas"
  method optionally = "optionellement"
  method optional = "optionel(le)"

  method of_ = "de"
  method genetive_suffix = None
  method rel_from = "de"
  method rel_to = "à"

  method a_an ~following = "un(e)"
  method the = "l'"
  method each = "chaque"
  method no = "aucun(e)"
  method any = "n'importe quel(le)"
  method all = "tous"
  method quantif_one = "un(e)"
  method quantif_of = "parmi"
  method something = "quelque chose"
  method anything = "n'importe quoi"
  method everything = "tout"
  method nothing = "rien"
  method for_ = "pour"

  method n_th n =
    let suffix =
      if n = 1 then "er"
      else "ième" in
    string_of_int n ^ suffix

  method aggreg_number = "nombre", `Noun
  method aggreg_list = "liste", `Noun
  method aggreg_total = "total(e)", `Adjective
  method aggreg_average = "moyen(ne)", `Adjective
  method aggreg_maximum = "maximal(e)", `Adjective
  method aggreg_minimum = "minimal(e)", `Adjective
  method aggreg_sample = "échantillon", `Noun
  method aggreg_given = "donné(e)", `Adjective

  method order_highest = "en ordre décroissant"
  method order_lowest = "en ordre croissant"

  method matches = "contient"
  method after = "après"
  method before = "avant"
  method interval_from = "de"
  method interval_to = "à"
  method higher_or_equal_to = "supérieur(e) ou égal à"
  method lower_or_equal_to = "inférieur(e) ou égal à"
  method interval_between = "entre"
  method interval_and = "et"
  method language = "langage"
  method datatype = "type de donnée"
  method matching = "contenant"

  method give_me = "donne moi"
  method there_is = "il y a"
  method it_is_true_that = "il est vrai que"

  method tooltip_open_resource = "Ouvrir la ressource dans une nouvelle fenêtre"
  method tooltip_delete_current_focus = "Cliquer sur la croix rouge pour supprimer le focus actuel"
  method tooltip_remove_element_at_focus = "Supprimer cet élément de requête au focus actuel"
  method tooltip_focus_on_property = "Insérer un focus sur la propriété pour la raffiner"
  method tooltip_or = "Insérer une alternative au focus actuel"
  method tooltip_optionally = "Rendre le focus actuel optionnel"
  method tooltip_not = "Appliquer une négation au focus actuel"
  method tooltip_any = "Cacher la colonne du focus actuel dans la table des résultats"
  method tooltip_aggreg = "Agréger la colonne du focus actuel dans la table des résultats" (* , pour chaque valuation des autres colonnes *)
  method tooltip_foreach = "Calculer l'agrégation pour chaque valeur de cette entité"
  method tooltip_highest = "Trier la colonne du focus actuel en ordre décroissant"
  method tooltip_lowest = "Trier la colonne du focus actuel en ordre croissant"
  method tooltip_header_hide_focus = "Cliquer sur cet entête de colonne pour cacher le focus"
  method tooltip_header_set_focus = "Cliquer sur cet entête de colonne pour mettre le focus dessus"

  method msg_permalink = "L'URL suivante pointe sur le point d'accès et la requête actuelles (Ctrl+C, Entrée pour copier)."
  method result_results = "résultat", "résultats"
  method entity_entities = "entité", "entités"
  method concept_concepts = "concept", "concepts"
  method modifier_modifiers = "modifieur", "modifieurs"
end
