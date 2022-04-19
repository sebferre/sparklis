(*
   Copyright 2013 Sébastien Ferré, IRISA, Université de Rennes 1, ferre@irisa.fr

   This file is part of Sparklis.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

type aggreg_syntax = [`A | `The] * string * string option (* quantifier, noun, adj_opt : adjective form is preferred *)

type func_syntax =
[ `Noun of string
| `Prefix of string
| `Infix of string
| `Brackets of string * string
| `Pattern of [`Kwd of string | `Func of string | `Arg of int] list ]

class virtual grammar =
object (self)
  method virtual adjective_before_noun : bool

  method virtual thing : string
  method virtual relation : string
  method virtual value_ : string
  method virtual result : string
  method virtual geolocation : string
  method virtual latitude : string
  method virtual longitude : string
  method virtual is : string
  method virtual has : string
  method virtual has_as_a : following:string -> string
  method virtual relative_that : string
  method virtual relative_that_object : string
  method virtual whose : string
  method virtual according_to : string
  method virtual which : string
  method virtual hierarchy : string
  method virtual in_ : string
  method virtual rank : string

  method virtual and_ : string
  method virtual or_ : string
  method virtual not_ : string
  method virtual optionally : string
  method virtual optional : string
  method virtual choice : string
  method virtual between : string

  method virtual of_ : string
  method virtual genetive_suffix : string option
  method virtual rel_to : string
  method virtual rel_from : string
  method virtual with_ : string

  method virtual a_an : following:string -> string
  method virtual the : string
  method virtual every : string
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
  method virtual this : string

  method virtual n_th : int -> string

  method virtual string : string
  method virtual integer : string
  method virtual number : string
  method virtual date : string
  method virtual time : string
  method virtual date_and_time : string
  method virtual duration : string
  method virtual uri : string

  method virtual aggreg_syntax : Lisql.aggreg -> aggreg_syntax
  method virtual func_syntax : Lisql.func -> func_syntax
      
  method virtual order_highest : string
  method virtual order_lowest : string

  method virtual matches : string
  method virtual is_exactly : string
  method virtual starts_with : string
  method virtual ends_with : string
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
  method virtual the_fact_that : string
  method virtual where : string
  method virtual undefined : string

  method virtual selected_item_s : string

  method virtual tooltip_open_resource : string
  method virtual tooltip_delete_current_focus : string
  method virtual tooltip_remove_element_at_focus : string
  method virtual tooltip_focus_on_property : string
  method virtual tooltip_duplicate_focus : string
  method virtual tooltip_or : string
  method virtual tooltip_optionally : string
  method virtual tooltip_not : string
  method virtual tooltip_any : string
  method virtual tooltip_sample : string
  method virtual tooltip_aggreg : string
  method virtual tooltip_func : string
  method virtual tooltip_input_name : string
  method virtual tooltip_foreach : string
  method virtual tooltip_foreach_result : string
  method virtual tooltip_foreach_id : string
  method virtual tooltip_aggreg_id : string
  method virtual tooltip_highest : string
  method virtual tooltip_lowest : string
  method virtual tooltip_header_hide_focus : string
  method virtual tooltip_header_set_focus : string
  method virtual tooltip_header_exact_count : string
  method virtual tooltip_geolocation : string
  method virtual tooltip_hierarchy : string

  method virtual msg_permalink : string
  method virtual msg_clear_log : string
  method virtual msg_full_log : string
  method virtual result_results : string * string
  method virtual item_items : string * string
  method entity_entities : string * string = self#item_items
  method concept_concepts : string * string = self#item_items
  method modifier_modifiers : string * string = self#item_items
  method virtual sorting_frequency : string
  method virtual sorting_alphanum : string
end

let english =
  let starts_with_vowel following =
    try
      let c = Char.lowercase_ascii following.[0] in
      c = 'a' || c = 'e' || c = 'i' || c = 'o' (* || c = 'u' : 'u' is more often pronounced [y] *)
    with _ -> false in
object
  inherit grammar

  method adjective_before_noun = true

  method thing = "thing"
  method relation = "relation"
  method value_ = "value"
  method result = "result"
  method geolocation = "geolocation"
  method latitude = "latitude"
  method longitude = "longitude"
  method is = "is"
  method has = "has"
  method has_as_a ~following = if starts_with_vowel following then "has as an" else "has as a"
  method relative_that = "that"
  method relative_that_object = "that"
  method whose = "whose"
  method according_to = "according to" (* "from" *)
  method which = "which"
  method hierarchy = "(hierarchy)"
  method in_ = "in"
  method rank = "rank"

  method and_ = "and"
  method or_ = "or"
  method not_ = "not"
  method optionally = "optionally"
  method optional = "optional"

  method of_ = "of"
  method genetive_suffix = Some "'s"
  method rel_to = "to"
  method rel_from = "from"
  method with_ = "with"

  method a_an ~following = if starts_with_vowel following then "an" else "a"
  method the = "the"
  method every = "every"
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
  method this = "this"
  method choice = "choice"
  method between = "between"

  method n_th n =
    let suffix =
      if n mod 10 = 1 && not (n mod 100 = 11) then "st"
      else if n mod 10 = 2 && not (n mod 100 = 12) then "nd"
      else if n mod 10 = 3 && not (n mod 100 = 13) then "rd"
      else "th" in
    string_of_int n ^ suffix

  method string = "string"
  method integer = "integer"
  method number = "number"
  method date = "date"
  method time = "time"
  method date_and_time = "date and time"
  method duration = "duration"
  method uri = "URI"

  method aggreg_syntax = function
  | Lisql.NumberOf -> `The, "number", None
  | Lisql.ListOf -> `The, "list", None
  | Lisql.Sample -> `A, "sample", None
  | Lisql.Total _ -> `The, "sum", Some "total"
  | Lisql.Average _ -> `The, "average", Some "average"
  | Lisql.Maximum _ -> `The, "maximum", Some "maximal"
  | Lisql.Minimum _ -> `The, "minimum", Some "minimal"

  method func_syntax = function
  | Str -> `Noun "string"
  | Lang -> `Noun "language"
  | Datatype -> `Noun "datatype"
  | IRI -> `Pattern [`Kwd "the"; `Func "IRI"; `Arg 1]
  | STRDT -> `Pattern [`Kwd "the"; `Func "literal"; `Arg 1; `Kwd "with"; `Func "datatype"; `Arg 2]
  | STRLANG -> `Pattern [`Kwd "the"; `Func "literal"; `Arg 1; `Kwd "with";  `Func "language tag"; `Arg 2]
  | Strlen -> `Noun "length"
  | Substr2 -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Kwd "from position"; `Arg 2]
  | Substr3 -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Kwd "from position"; `Arg 2; `Kwd "having length"; `Arg 3]
  | Strbefore -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Func "before"; `Arg 2]
  | Strafter -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Func "after"; `Arg 2]
  | Concat -> `Infix " ++ "
  | UCase -> `Noun "uppercase"
  | LCase -> `Noun "lowercase"
  | Encode_for_URI -> `Noun "URI encoding"
  | Replace -> `Pattern [`Kwd "the"; `Func "replacement"; `Kwd "in"; `Arg 1; `Kwd "of"; `Arg 2; `Kwd "by"; `Arg 3]
  | Integer -> `Pattern [`Arg 1; `Kwd "as"; `Func "integer"]
  | Decimal -> `Pattern [`Arg 1; `Kwd "as"; `Func "decimal"]
  | Double -> `Pattern [`Arg 1; `Kwd "as"; `Func "float"]
  | Indicator -> `Pattern [`Kwd "1 or 0"; `Kwd "whether"; `Arg 1]
  | Add -> `Infix " + "
  | Sub -> `Infix " - "
  | Mul -> `Infix " * "
  | Div -> `Infix " / "
  | Neg -> `Prefix "- "
  | Abs -> `Brackets ("|","|")
  | Round -> `Noun "rounding"
  | Ceil -> `Noun "ceiling"
  | Floor -> `Noun "floor"
  | Random2 -> `Pattern [`Kwd "a"; `Func "random number"; `Kwd "between"; `Arg 1; `Kwd "and"; `Arg 2]
  | Date -> `Noun "date"
  | Time -> `Noun "time"
  | Year -> `Noun "year"
  | Month -> `Noun "month"
  | Day -> `Noun "day"
  | Hours -> `Noun "hours"
  | Minutes -> `Noun "minutes"
  | Seconds -> `Noun "seconds"
  | TODAY -> `Pattern [`Func "today"]
  | NOW -> `Pattern [`Func "now"]
  | And -> `Infix " and "
  | Or -> `Infix " or "
  | Not -> `Prefix "it is not true that "
  | EQ -> `Infix " = "
  | NEQ -> `Infix " ≠ "
  | GT -> `Infix " > "
  | GEQ -> `Infix " ≥ "
  | LT -> `Infix " < "
  | LEQ -> `Infix " ≤ "
  | BOUND -> `Pattern [`Arg 1; `Kwd "is"; `Func "bound"]
  | IF -> `Pattern [`Arg 2; `Func "if"; `Arg 1; `Func "else"; `Arg 3]
  | IsIRI -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "IRI"]
  | IsBlank -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "blank node"]
  | IsLiteral -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "literal"]
  | IsNumeric -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "number"]
  | StrStarts -> `Pattern [`Arg 1; `Func "starts with"; `Arg 2]
  | StrEnds -> `Pattern [`Arg 1; `Func "ends with"; `Arg 2]
  | Contains -> `Pattern [`Arg 1; `Func "contains"; `Arg 2]
  | REGEX -> `Pattern [`Arg 1; `Func "matches regexp"; `Arg 2]
  | REGEX_i -> `Pattern [`Arg 1; `Func "matches regexp (case insensitive)"; `Arg 2]
  | LangMatches -> `Pattern [`Arg 1; `Kwd "has"; `Kwd "a"; `Func "language"; `Kwd "that"; `Func "matches"; `Arg 2]
 
  method order_highest = "highest-to-lowest"
  method order_lowest = "lowest-to-highest"

  method matches = "matches"
  method is_exactly = "is exactly"
  method starts_with = "starts with"
  method ends_with = "ends with"
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
  method the_fact_that = "the fact that"
  method where = "where"
  method undefined = "undefined"

  method selected_item_s = "selected items"

  method tooltip_open_resource = "Open resource in new window"
  method tooltip_delete_current_focus = "Click on this cross to delete the current focus"
  method tooltip_remove_element_at_focus = "Remove this query element at the query focus"
  method tooltip_focus_on_property = "Adds a focus on the property to refine it"
  method tooltip_duplicate_focus = "Insert a copy of the current focus"
  method tooltip_or = "Insert an alternative to the current focus"
  method tooltip_optionally = "Make the current focus optional"
  method tooltip_not = "Apply negation to the current focus"
  method tooltip_any = "Hide the focus column in the table of results"
  method tooltip_sample = "Replace the aggregation by a sample in order to select another aggregation operator"
  method tooltip_aggreg = "Aggregate the focus column in the table of results" (*, for each solution on other columns *)
  method tooltip_func = "Apply the function to the current focus"
  method tooltip_input_name = "Input a (new) name for the expression result"
  method tooltip_foreach = "Group results for each value of this entity"
  method tooltip_foreach_result = "Compute the aggregation for each result of the related query"
  method tooltip_foreach_id = "Compute the aggregation for each value of this entity"
  method tooltip_aggreg_id = "Insert a new aggregation column for this entity"
  method tooltip_highest = "Sort the focus column in decreasing order"
  method tooltip_lowest = "Sort the focus column in increasing order"
  method tooltip_header_hide_focus = "Click on this column header to hide the focus"
  method tooltip_header_set_focus = "Click on this column header to set the focus on it"
  method tooltip_header_exact_count = "Click to get exact count"
  method tooltip_geolocation = "Retrieve geolocations to show entities on a map"
  method tooltip_hierarchy = "Show a hierarchy of entities according to the property at the left"

  method msg_permalink = "The following URL points to the current endpoint and query (Ctrl+C, Enter to copy to clipboard)."
  method msg_clear_log = "Are you sure that you want to clear the navigation history? (This action cannot be undone.)"
  method msg_full_log = "The local storage is full. Do you want to clear the navigation history for this endpoint to enable the recording of future navigation ? (This action cannot be undone.) If you click 'Cancel', the recording will stop until the history is cleared."
  method result_results = "result", "results"
  method item_items = "item", "items"
  (*method entity_entities = "entity", "entities"
  method concept_concepts = "concept", "concepts"
  method modifier_modifiers = "modifier", "modifiers"*)
  method sorting_frequency = "decreasing frequency"
  method sorting_alphanum = "alphanumeric order"
end

let french =
object
  inherit grammar

  method adjective_before_noun = false

  method thing = "chose"
  method relation = "relation"
  method value_ = "valeur"
  method result = "résultat"
  method geolocation = "géolocalisation"
  method latitude = "latitude"
  method longitude = "longitude"
  method is = "est"
  method has = "a"
  method has_as_a ~following = "a pour"
  method relative_that = "qui"
  method relative_that_object = "que"
  method whose = "dont le·a"
  method according_to = "selon"
  method which = "lequel"
  method hierarchy = "(hiérarchie)"
  method in_ = "dans"
  method rank = "rang"

  method and_ = "et"
  method or_ = "ou"
  method not_ = "pas"
  method optionally = "optionnellement"
  method optional = "optionnel·le"

  method of_ = "de"
  method genetive_suffix = None
  method rel_from = "de"
  method rel_to = "à"
  method with_ = "avec"

  method a_an ~following = "un·e"
  method the = "le·a"
  method every = "chaque"
  method each = "chaque"
  method no = "aucun·e"
  method any = "n'importe quel·le"
  method all = "tous"
  method quantif_one = "un·e"
  method quantif_of = "parmi"
  method something = "quelque chose"
  method anything = "n'importe lequel"
  method everything = "tout"
  method nothing = "rien"
  method for_ = "pour"
  method this = "ceci"
  method choice = "choix"
  method between = "entre"

  method n_th n =
    let suffix =
      if n = 1 then "er"
      else "e" in
    string_of_int n ^ suffix

  method string = "chaine"
  method integer = "entier"
  method number = "nombre"
  method date = "date"
  method time = "heure"
  method date_and_time = "date et heure"
  method duration = "durée"
  method uri = "URI"

  method aggreg_syntax = function
  | Lisql.NumberOf -> `The, "nombre", None
  | Lisql.ListOf -> `The, "liste", None
  | Lisql.Sample -> `A, "échantillon", None
  | Lisql.Total _ -> `The, "somme", Some "total·e"
  | Lisql.Average _ -> `The, "moyenne", Some "moyen·ne"
  | Lisql.Maximum _ -> `The, "maximum", Some "maximal·e"
  | Lisql.Minimum _ -> `The, "minimum", Some "minimal·e"

  method func_syntax = function
  | Str -> `Pattern [`Kwd "la"; `Func "chaine"; `Kwd "de"; `Arg 1]
  | Lang -> `Pattern [`Kwd "la"; `Func "langue"; `Kwd "de"; `Arg 1]
  | Datatype -> `Pattern [`Kwd "le"; `Func "type"; `Kwd "de"; `Arg 1]
  | IRI -> `Pattern [`Kwd "l'"; `Func "IRI"; `Arg 1]
  | STRDT -> `Pattern [`Kwd "le"; `Func "littéral"; `Arg 1; `Kwd "de";  `Func "type"; `Arg 2]
  | STRLANG -> `Pattern [`Kwd "le"; `Func "littéral"; `Arg 1; `Kwd "de"; `Func "langue"; `Arg 2]
  | Strlen -> `Pattern [`Kwd "la"; `Func "longueur"; `Kwd "de"; `Arg 1]
  | Substr2 -> `Pattern [`Kwd "la"; `Func "sous-chaine"; `Kwd "de"; `Arg 1; `Kwd "partant de la position"; `Arg 2]
  | Substr3 -> `Pattern [`Kwd "la"; `Func "sous-chaine"; `Kwd "de"; `Arg 1; `Kwd "partant de la position"; `Arg 2; `Kwd "et de longueur"; `Arg 3]
  | Strbefore -> `Pattern [`Kwd "la"; `Func "sous-chaine"; `Kwd "de"; `Arg 1; `Func "avant"; `Arg 2]
  | Strafter -> `Pattern [`Kwd "la"; `Func "sous-chaine"; `Kwd "de"; `Arg 1; `Func "après"; `Arg 2]
  | Concat -> `Infix " ++ "
  | UCase -> `Pattern [`Arg 1; `Kwd "en"; `Func "majuscules"]
  | LCase -> `Pattern [`Arg 1; `Kwd "en"; `Func "minuscules"]
  | Encode_for_URI -> `Pattern [`Kwd "l'"; `Func "encodage URI"; `Kwd "de"; `Arg 1]
  | Replace -> `Pattern [`Kwd "le"; `Func "remplacement"; `Kwd "dans"; `Arg 1; `Kwd "de"; `Arg 2; `Kwd "par"; `Arg 3]
  | Integer -> `Pattern [`Arg 1; `Kwd "comme"; `Func "entier"]
  | Decimal -> `Pattern [`Arg 1; `Kwd "comme"; `Func "décimal"]
  | Double -> `Pattern [`Arg 1; `Kwd "comme"; `Func "flottant"]
  | Indicator -> `Pattern [`Kwd "1 ou 0"; `Kwd "selon"; `Kwd "que"; `Arg 1]
  | Add -> `Infix " + "
  | Sub -> `Infix " - "
  | Mul -> `Infix " * "
  | Div -> `Infix " / "
  | Neg -> `Prefix "- "
  | Abs -> `Brackets ("|","|")
  | Round -> `Pattern [`Kwd "l'"; `Func "arrondi"; `Kwd "de"; `Arg 1]
  | Ceil -> `Pattern [`Kwd "la"; `Func "partie entière par excès"; `Kwd "de"; `Arg 1]
  | Floor -> `Pattern [`Kwd "la"; `Func "partie entière par défaut"; `Kwd "de"; `Arg 1]
  | Random2 -> `Pattern [`Kwd "un"; `Func "nombre aléatoire"; `Kwd "entre"; `Arg 1; `Kwd "et"; `Arg 2]
  | Date -> `Pattern [`Kwd "la"; `Func "date"; `Kwd "de"; `Arg 1]
  | Time -> `Pattern [`Kwd "l'"; `Func "heure"; `Kwd "de"; `Arg 1]
  | Year -> `Pattern [`Kwd "l'"; `Func "année"; `Kwd "de"; `Arg 1]
  | Month -> `Pattern [`Kwd "le"; `Func "mois"; `Kwd "de"; `Arg 1]
  | Day -> `Pattern [`Kwd "le"; `Func "jour"; `Kwd "de"; `Arg 1]
  | Hours -> `Pattern [`Kwd "les"; `Func "heures"; `Kwd "de"; `Arg 1]
  | Minutes -> `Pattern [`Kwd "les"; `Func "minutes"; `Kwd "de"; `Arg 1]
  | Seconds -> `Pattern [`Kwd "les"; `Func "secondes"; `Kwd "de"; `Arg 1]
  | TODAY -> `Pattern [`Func "aujourd'hui"]
  | NOW -> `Pattern [`Func "maintenant"]
  | And -> `Infix " et "
  | Or -> `Infix " ou "
  | Not -> `Prefix "il n'est pas vrai que "
  | EQ -> `Infix " = "
  | NEQ -> `Infix " ≠ "
  | GT -> `Infix " > "
  | GEQ -> `Infix " ≥ "
  | LT -> `Infix " < "
  | LEQ -> `Infix " ≤ "
  | BOUND -> `Pattern [`Arg 1; `Kwd "a"; `Kwd "une"; `Func "valeur"]
  | IF -> `Pattern [`Arg 2; `Func "si"; `Arg 1; `Func "sinon"; `Arg 3]
  | IsIRI -> `Pattern [`Arg 1; `Kwd "est"; `Kwd "une"; `Func "IRI"]
  | IsBlank -> `Pattern [`Arg 1; `Kwd "est"; `Kwd "un"; `Func "noeud anonyme"]
  | IsLiteral -> `Pattern [`Arg 1; `Kwd "est"; `Kwd "un"; `Func "litéral"]
  | IsNumeric -> `Pattern [`Arg 1; `Kwd "est"; `Kwd "un"; `Func "nombre"]
  | StrStarts -> `Pattern [`Arg 1; `Func "commence par"; `Arg 2]
  | StrEnds -> `Pattern [`Arg 1; `Func "termine par"; `Arg 2]
  | Contains -> `Pattern [`Arg 1; `Func "contient"; `Arg 2]
  | REGEX -> `Pattern [`Arg 1; `Func "matche la regexp"; `Arg 2]
  | REGEX_i -> `Pattern [`Arg 1; `Func "matche la regexp (insensible à la casse)"; `Arg 2]
  | LangMatches -> `Pattern [`Arg 1; `Kwd "a"; `Kwd "une"; `Func "langue"; `Kwd "qui"; `Func "matche"; `Arg 2]
 
  method order_highest = "en ordre décroissant"
  method order_lowest = "en ordre croissant"

  method matches = "contient"
  method is_exactly = "est exactement"
  method starts_with = "commence par"
  method ends_with = "termine par"
  method after = "après"
  method before = "avant"
  method interval_from = "de"
  method interval_to = "à"
  method higher_or_equal_to = "supérieur·e ou égal·e à"
  method lower_or_equal_to = "inférieur·e ou égal·e à"
  method interval_between = "entre"
  method interval_and = "et"
  method language = "langage"
  method datatype = "type de donnée"
  method matching = "contenant"

  method give_me = "donne moi"
  method there_is = "il y a"
  method it_is_true_that = "il est vrai que"
  method the_fact_that = "le fait que"
  method where = "où"
  method undefined = "indéfini"

  method selected_item_s = "éléments sélectionnés"

  method tooltip_open_resource = "Ouvrir la ressource dans une nouvelle fenêtre"
  method tooltip_delete_current_focus = "Cliquer sur la croix pour supprimer le focus actuel"
  method tooltip_remove_element_at_focus = "Supprimer cet élément de requête au focus actuel"
  method tooltip_focus_on_property = "Insérer un focus sur la propriété pour la raffiner"
  method tooltip_or = "Insérer une alternative au focus actuel"
  method tooltip_duplicate_focus = "Insérer une copie du focus actuel"
  method tooltip_optionally = "Rendre le focus actuel optionnel"
  method tooltip_not = "Appliquer une négation au focus actuel"
  method tooltip_any = "Cacher la colonne du focus actuel dans la table des résultats"
  method tooltip_sample = "Remplacer l'agrégation par un échantillon afin de pouvoir sélectionner un autre opérateur d'agrégation"
  method tooltip_aggreg = "Agréger la colonne du focus actuel dans la table des résultats" (* pour chaque valuation des autres colonnes *)
  method tooltip_func = "Appliquer cette fonction au focus actuel"
  method tooltip_input_name = "Entrer un (nouveau) nom pour le résultat de l'expression"
  method tooltip_foreach = "Grouper les résultats pour chaque valeur de cette entité"
  method tooltip_foreach_result = "Calculer l'agrégation pour chaque résultat de la requête associée"
  method tooltip_foreach_id = "Calculer l'agrégation pour chaque valeur de cette entité"
  method tooltip_aggreg_id = "Insérer une nouvelle colonne d'agrégation pour cette entité"
  method tooltip_highest = "Trier la colonne du focus actuel en ordre décroissant"
  method tooltip_lowest = "Trier la colonne du focus actuel en ordre croissant"
  method tooltip_header_hide_focus = "Cliquer sur cet entête de colonne pour cacher le focus"
  method tooltip_header_set_focus = "Cliquer sur cet entête de colonne pour mettre le focus dessus"
  method tooltip_header_exact_count = "Cliquer pour obtenir le nombre exact"
  method tooltip_geolocation = "Récupérer les géolocalisations pour montrer les entités sur une carte"
  method tooltip_hierarchy = "Montrer une hiérarchie d'entités selon la propriété à gauche"

  method msg_permalink = "L'URL suivante pointe sur le point d'accès et la requête actuelles (Ctrl+C, Entrée pour copier)."
  method msg_clear_log = "Êtes-vous sûr de vouloir effacer l'historique de navigation ? (Cette action ne peut être annulée)."
  method msg_full_log = "Le stockage local est plein. Voulez-vous effacer l'historique de navigation pour ce point d'accès afin de permettre l'enregistrement de la navigation future ? (Cette action ne peut pas être annulée.) Si vous cliquez sur 'Annuler', l'enregistrement s'arrêtera jusqu'à ce que l'historique soit effacé."
  method result_results = "résultat", "résultats"
  method item_items = "élément", "éléments"
  (*method entity_entities = "entité", "entités"
  method concept_concepts = "concept", "concepts"
  method modifier_modifiers = "modifieur", "modifieurs"*)
  method sorting_frequency = "fréquence décroissante"
  method sorting_alphanum = "ordre alphanumérique"
end


let spanish =
object
  inherit grammar

  method adjective_before_noun = false

  method thing = "cosa"
  method relation = "relación"
  method value_ = "valor"
  method result = "resultado"
  method geolocation = "geolocalización"
  method latitude = "latitud"
  method longitude = "longitud"
  method is = "es"
  method has = "tiene"
  method has_as_a ~following = "tiene como"
  method relative_that = "que"
  method relative_that_object = "que"
  method whose = "cuyo"
  method according_to = "según"
  method which = "el/la cual"
  method hierarchy = "(jerarquía)"
  method in_ = "en"
  method rank = "rango"

  method and_ = "y"
  method or_ = "o"
  method not_ = "no"
  method optionally = "opcionalmente"
  method optional = "opcional"

  method of_ = "de"
  method genetive_suffix = None
  method rel_from = "de"
  method rel_to = "a"
  method with_ = "con"

  method a_an ~following = "un(a)"
  method the = "la"
  method every = "cada"
  method each = "cada"
  method no = "no"
  method any = "cualquier"
  method all = "todos"
  method quantif_one = "un(a)"
  method quantif_of = "de"
  method something = "algo"
  method anything = "cualquier cosa"
  method everything = "todo"
  method nothing = "nada"
  method for_ = "para"
  method this = "este"
  method choice = "elección"
  method between = "entre"

  method n_th n =
    let suffix =
      if n = 1 then "o/a"
      else "o" in
    string_of_int n ^ suffix

  method string = "cadena"
  method integer = "entero"
  method number = "número"
  method date = "fecha"
  method time = "hora"
  method date_and_time = "fecha y hora"
  method duration = "duración"
  method uri = "URI"

  method aggreg_syntax = function
  | Lisql.NumberOf -> `The, "número", None
  | Lisql.ListOf -> `The, "lista", None
  | Lisql.Sample -> `A, "muestra", None
  | Lisql.Total _ -> `The, "suma", Some "total"
  | Lisql.Average _ -> `The, "promedio", Some "promedio"
  | Lisql.Maximum _ -> `The, "máximo", Some "máximo"
  | Lisql.Minimum _ -> `The, "mínimo", Some "mínimo"

  method func_syntax = function
  | Str -> `Pattern [`Kwd "la"; `Func "cadena"; `Kwd "de"; `Arg 1]
  | Lang -> `Pattern [`Kwd "el"; `Func "idioma"; `Kwd "de"; `Arg 1]
  | Datatype -> `Pattern [`Kwd "el"; `Func "tipo"; `Kwd "de"; `Arg 1]
  | IRI -> `Pattern [`Kwd "la"; `Func "IRI"; `Arg 1]
  | STRDT -> `Pattern [`Kwd "el"; `Func "literal"; `Arg 1; `Kwd "de";  `Func "tipo"; `Arg 2]
  | STRLANG -> `Pattern [`Kwd "el"; `Func "literal"; `Arg 1; `Kwd "de"; `Func "idioma"; `Arg 2]
  | Strlen -> `Pattern [`Kwd "la"; `Func "longitud"; `Kwd "de"; `Arg 1]
  | Substr2 -> `Pattern [`Kwd "la"; `Func "subcadena"; `Kwd "de"; `Arg 1; `Kwd "partiendo de la posición"; `Arg 2]
  | Substr3 -> `Pattern [`Kwd "la"; `Func "subcadena"; `Kwd "de"; `Arg 1; `Kwd "partiendo de la posición"; `Arg 2; `Kwd "y de longitud"; `Arg 3]
  | Strbefore -> `Pattern [`Kwd "la"; `Func "subcadena"; `Kwd "de"; `Arg 1; `Func "antes"; `Arg 2]
  | Strafter -> `Pattern [`Kwd "la"; `Func "subcadena"; `Kwd "de"; `Arg 1; `Func "depués"; `Arg 2]
  | Concat -> `Infix " ++ "
  | UCase -> `Pattern [`Arg 1; `Kwd "en"; `Func "mayúsculas"]
  | LCase -> `Pattern [`Arg 1; `Kwd "en"; `Func "minúsculas"]
  | Encode_for_URI -> `Pattern [`Kwd "la"; `Func "codificación de la URI"; `Kwd "de"; `Arg 1]
  | Replace -> `Pattern [`Kwd "el"; `Func "reemplazo"; `Kwd "en"; `Arg 1; `Kwd "de"; `Arg 2; `Kwd "por"; `Arg 3]
  | Integer -> `Pattern [`Arg 1; `Kwd "como"; `Func "entero"]
  | Decimal -> `Pattern [`Arg 1; `Kwd "como"; `Func "decimal"]
  | Double -> `Pattern [`Arg 1; `Kwd "como"; `Func "flotante"]
  | Indicator -> `Pattern [`Kwd "1 o 0"; `Kwd "dependiendo"; `Kwd "de"; `Kwd "si"; `Arg 1]
  | Add -> `Infix " + "
  | Sub -> `Infix " - "
  | Mul -> `Infix " * "
  | Div -> `Infix " / "
  | Neg -> `Prefix "- "
  | Abs -> `Brackets ("|","|")
  | Round -> `Pattern [`Kwd "el"; `Func "redondeo"; `Kwd "de"; `Arg 1]
  | Ceil -> `Pattern [`Kwd "la"; `Func "parte entera por exceso"; `Kwd "de"; `Arg 1]
  | Floor -> `Pattern [`Kwd "la"; `Func "parte entera por defecto"; `Kwd "de"; `Arg 1]
  | Random2 -> `Pattern [`Kwd "un"; `Func "número aleatorio"; `Kwd "entre"; `Arg 1; `Kwd "y"; `Arg 2]
  | Date -> `Pattern [`Kwd "la"; `Func "fecha"; `Kwd "de"; `Arg 1]
  | Time -> `Pattern [`Kwd "la"; `Func "hora"; `Kwd "de"; `Arg 1]
  | Year -> `Pattern [`Kwd "el"; `Func "año"; `Kwd "de"; `Arg 1]
  | Month -> `Pattern [`Kwd "el"; `Func "mes"; `Kwd "de"; `Arg 1]
  | Day -> `Pattern [`Kwd "el"; `Func "día"; `Kwd "de"; `Arg 1]
  | Hours -> `Pattern [`Kwd "las"; `Func "horas"; `Kwd "de"; `Arg 1]
  | Minutes -> `Pattern [`Kwd "los"; `Func "minutos"; `Kwd "de"; `Arg 1]
  | Seconds -> `Pattern [`Kwd "los"; `Func "segundos"; `Kwd "de"; `Arg 1]
  | TODAY -> `Pattern [`Func "hoy"]
  | NOW -> `Pattern [`Func "ahora"]
  | And -> `Infix " y "
  | Or -> `Infix " o "
  | Not -> `Prefix " no es verdad que "
  | EQ -> `Infix " = "
  | NEQ -> `Infix " ≠ "
  | GT -> `Infix " > "
  | GEQ -> `Infix " ≥ "
  | LT -> `Infix " < "
  | LEQ -> `Infix " ≤ "
  | BOUND -> `Pattern [`Arg 1; `Kwd "tiene"; `Kwd "un"; `Func "valor"]
  | IF -> `Pattern [`Arg 2; `Func "si"; `Arg 1; `Func "en caso contrario"; `Arg 3]
  | IsIRI -> `Pattern [`Arg 1; `Kwd "es"; `Kwd "una"; `Func "IRI"]
  | IsBlank -> `Pattern [`Arg 1; `Kwd "es"; `Kwd "un"; `Func "nodo anónimo"]
  | IsLiteral -> `Pattern [`Arg 1; `Kwd "es"; `Kwd "un"; `Func "literal"]
  | IsNumeric -> `Pattern [`Arg 1; `Kwd "es"; `Kwd "un"; `Func "número"]
  | StrStarts -> `Pattern [`Arg 1; `Func "comienza por"; `Arg 2]
  | StrEnds -> `Pattern [`Arg 1; `Func "termina en"; `Arg 2]
  | Contains -> `Pattern [`Arg 1; `Func "contiene"; `Arg 2]
  | REGEX -> `Pattern [`Arg 1; `Func "coincide con la expresión regular"; `Arg 2]
  | REGEX_i -> `Pattern [`Arg 1; `Func "coincide con la expresión regular (ignora mayús./minús.)"; `Arg 2]
  | LangMatches -> `Pattern [`Arg 1; `Kwd "tiene"; `Kwd "un"; `Func "idioma"; `Kwd "que"; `Func "coincide con"; `Arg 2]
 
  method order_highest = "en orden descendente"
  method order_lowest = "en orden ascendente"

  method matches = "contiene"
  method is_exactly = "es exactamente"
  method starts_with = "comienza por"
  method ends_with = "termina en"
  method after = "después"
  method before = "antes"
  method interval_from = "desde"
  method interval_to = "hasta"
  method higher_or_equal_to = "mayor o igual a"
  method lower_or_equal_to = "menor o igual a"
  method interval_between = "entre"
  method interval_and = "y"
  method language = "idioma"
  method datatype = "tipo de datos"
  method matching = "que contiene"

  method give_me = "dame"
  method there_is = "hay"
  method it_is_true_that = "es verdad que"
  method the_fact_that = "el hecho de que"
  method where = "donde"
  method undefined = "indefinido"

  method selected_item_s = "artículos seleccionados"

  method tooltip_open_resource = "Abrir el recurso en una nueva ventana"
  method tooltip_delete_current_focus = "Haga clic en la X para eliminar el foco actual"
  method tooltip_remove_element_at_focus = "Eliminar el elemento en el foco actual de consulta"
  method tooltip_focus_on_property = "Insertar un foco sobre la propiedad para refinarla"
  method tooltip_duplicate_focus = "Insertar una copia del foco actual"
  method tooltip_or = "Insertar una alternativa en el foco actual"
  method tooltip_optionally = "Hacer opcional el foco actual"
  method tooltip_not = "Aplicar una negación al foco actual"
  method tooltip_any = "Ocultar la columna del foco actual en la tabla de resultados"
  method tooltip_sample = "Reemplazar la agregación por una muestra para poder seleccionar otro agregador"
  method tooltip_aggreg = "Agregar la columna del foco actual en la tabla de resultados" (* pour chaque valuation des autres colonnes *)
  method tooltip_func = "Aplicar esta función en el foco actual"
  method tooltip_input_name = "Introducir un nombre (nuevo) para el resultado de la expresión"
  method tooltip_foreach = "Agrupar los resultados para cada valor de esta entidad"
  method tooltip_foreach_result = "Calcular la agregación para cada resultado de la consulta asociada"
  method tooltip_foreach_id = "Calcular la agregación para cada valor de esta entidad"
  method tooltip_aggreg_id = "Insertar una nueva columna de agregación para esta entidad"
  method tooltip_highest = "Ordenar la columna del foco actual en orden descendente"
  method tooltip_lowest = "Ordenar la columna del foco actual en orden ascendente"
  method tooltip_header_hide_focus = "Haga clic en el encabezado de la columna para ocultar el foco"
  method tooltip_header_set_focus = "Haga clic en el encabezado de la columna para poner el foco en él"
  method tooltip_header_exact_count = "Haga clic para obtener el número exacto"
  method tooltip_geolocation = "Recuperar geolocaciones para mostrar entidades en un mapa"
  method tooltip_hierarchy = "Mostrar una jerarquía de entidades de acuerdo a la propiedad de la izquierda"

  method msg_permalink = "La siguiente URL apunta al Endpoint y consulta actuales (Ctrl+C, Enter para copiar)."
  method msg_clear_log = "¿Está seguro de que quiere borrar el historial de navegación? (Esta acción no se puede deshacer)."
  method msg_full_log = "El almacenamiento local está lleno. ¿Desea borrar el historial de navegación de este Endpoint para permitir la grabación de futuras navegaciones? (Esta acción no se puede deshacer.) Si hace clic en 'Cancelar', la grabación se detendrá hasta que se borre el historial."
  method result_results = "resultado", "resultados"
  method item_items = "elemento", "elementos"
  (*method entity_entities = "entidad", "entidades"
  method concept_concepts = "concepto", "conceptos"
  method modifier_modifiers = "modificador", "modificadores"*)
  method sorting_frequency = "frecuencia decreciente"
  method sorting_alphanum = "orden alfanumérico"
end



let dutch =
object
  inherit grammar

  method adjective_before_noun = true

  method thing = "object"
  method relation = "relatie"
  method value_ = "value"
  method result = "resultaat"
  method geolocation = "geolocatie"
  method latitude = "breedtegraad"
  method longitude = "lengtegraad"
  method is = "is"
  method has = "heeft"
  method has_as_a ~following = "heeft als een"
  method relative_that = "dat"
  method relative_that_object = "dat"
  method whose = "van wie"
  method according_to = "volgens" (* "from" *)
  method which = "welke"
  method hierarchy = "(hiërarchie)"
  method in_ = "in"
  method rank = "rang"

  method and_ = "en"
  method or_ = "of"
  method not_ = "niet"
  method optionally = "optioneel"
  method optional = "optioneel"

  method of_ = "van"
  method genetive_suffix = Some "'s"
  method rel_to = "naar"
  method rel_from = "van"
  method with_ = "met"

  method a_an ~following = "een"
  method the = "de"
  method every = "iedere"
  method each = "ieder"
  method all = "alle"
  method no = "nee"
  method any = "elke"
  method quantif_one = "een"
  method quantif_of = "van"
  method something = "iets"
  method anything = "iets"
  method everything = "alles"
  method nothing = "niets"
  method for_ = "voor"
  method this = "dit"
  method choice = "keuze"
  method between = "tussen"

  method n_th n =
    let suffix = "e" in
    string_of_int n ^ suffix

  method string = "string"
  method integer = "integer"
  method number = "nummer"
  method date = "datum"
  method time = "tijd"
  method date_and_time = "datum en tijd"
  method duration = "duur"
  method uri = "URI"

  method aggreg_syntax = function
  | Lisql.NumberOf -> `The, "nummer", None
  | Lisql.ListOf -> `The, "lijst", None
  | Lisql.Sample -> `A, "voorbeeld", None
  | Lisql.Total _ -> `The, "som", Some "totaal"
  | Lisql.Average _ -> `The, "gemiddelde", Some "gemiddelde"
  | Lisql.Maximum _ -> `The, "maximum", Some "maximaal"
  | Lisql.Minimum _ -> `The, "minimum", Some "minimaal"

  method func_syntax = function
  | Str -> `Noun "string"
  | Lang -> `Noun "language"
  | Datatype -> `Noun "datatype"
  | IRI -> `Pattern [`Kwd "the"; `Func "IRI"; `Arg 1]
  | STRDT -> `Pattern [`Kwd "the"; `Func "literal"; `Arg 1; `Kwd "with"; `Func "datatype"; `Arg 2]
  | STRLANG -> `Pattern [`Kwd "the"; `Func "literal"; `Arg 1; `Kwd "with";  `Func "language tag"; `Arg 2]
  | Strlen -> `Noun "length"
  | Substr2 -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Kwd "from position"; `Arg 2]
  | Substr3 -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Kwd "from position"; `Arg 2; `Kwd "having length"; `Arg 3]
  | Strbefore -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Func "before"; `Arg 2]
  | Strafter -> `Pattern [`Kwd "the"; `Func "substring"; `Kwd "of"; `Arg 1; `Func "after"; `Arg 2]
  | Concat -> `Infix " ++ "
  | UCase -> `Noun "uppercase"
  | LCase -> `Noun "lowercase"
  | Encode_for_URI -> `Noun "URI encoding"
  | Replace -> `Pattern [`Kwd "the"; `Func "replacement"; `Kwd "in"; `Arg 1; `Kwd "of"; `Arg 2; `Kwd "by"; `Arg 3]
  | Integer -> `Pattern [`Arg 1; `Kwd "as"; `Func "integer"]
  | Decimal -> `Pattern [`Arg 1; `Kwd "as"; `Func "decimal"]
  | Double -> `Pattern [`Arg 1; `Kwd "as"; `Func "float"]
  | Indicator -> `Pattern [`Kwd "1 or 0"; `Kwd "whether"; `Arg 1]
  | Add -> `Infix " + "
  | Sub -> `Infix " - "
  | Mul -> `Infix " * "
  | Div -> `Infix " / "
  | Neg -> `Prefix "- "
  | Abs -> `Brackets ("|","|")
  | Round -> `Noun "rounding"
  | Ceil -> `Noun "ceiling"
  | Floor -> `Noun "floor"
  | Random2 -> `Pattern [`Kwd "a"; `Func "random number"; `Kwd "between"; `Arg 1; `Kwd "and"; `Arg 2]
  | Date -> `Noun "date"
  | Time -> `Noun "time"
  | Year -> `Noun "year"
  | Month -> `Noun "month"
  | Day -> `Noun "day"
  | Hours -> `Noun "hours"
  | Minutes -> `Noun "minutes"
  | Seconds -> `Noun "seconds"
  | TODAY -> `Pattern [`Func "today"]
  | NOW -> `Pattern [`Func "now"]
  | And -> `Infix " and "
  | Or -> `Infix " or "
  | Not -> `Prefix "it is not true that "
  | EQ -> `Infix " = "
  | NEQ -> `Infix " ≠ "
  | GT -> `Infix " > "
  | GEQ -> `Infix " ≥ "
  | LT -> `Infix " < "
  | LEQ -> `Infix " ≤ "
  | BOUND -> `Pattern [`Arg 1; `Kwd "is"; `Func "bound"]
  | IF -> `Pattern [`Arg 2; `Func "if"; `Arg 1; `Func "else"; `Arg 3]
  | IsIRI -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "IRI"]
  | IsBlank -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "blank node"]
  | IsLiteral -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "literal"]
  | IsNumeric -> `Pattern [`Arg 1; `Kwd "is"; `Kwd "a"; `Func "number"]
  | StrStarts -> `Pattern [`Arg 1; `Func "starts with"; `Arg 2]
  | StrEnds -> `Pattern [`Arg 1; `Func "ends with"; `Arg 2]
  | Contains -> `Pattern [`Arg 1; `Func "contains"; `Arg 2]
  | REGEX -> `Pattern [`Arg 1; `Func "matches regexp"; `Arg 2]
  | REGEX_i -> `Pattern [`Arg 1; `Func "matches regexp (case insensitive)"; `Arg 2]
  | LangMatches -> `Pattern [`Arg 1; `Kwd "has"; `Kwd "a"; `Func "language"; `Kwd "that"; `Func "matches"; `Arg 2]
 
  method order_highest = "hoogste-naar-laagste"
  method order_lowest = "laagste-naar-hoogste"

  method matches = "komt overeen"
  method is_exactly = "is precies"
  method starts_with = "begint met"
  method ends_with = "eindigt met"
  method after = "na"
  method before = "voor"
  method interval_from = "van"
  method interval_to = "tot"
  method higher_or_equal_to = "hoger of gelijk aan"
  method lower_or_equal_to = "lager of gelijk aan"
  method interval_between = "tussen"
  method interval_and = "en"
  method language = "taal"
  method datatype = "datatype"
  method matching = "overeenkomstig"

  method give_me = "geef mij"
  method there_is = "er is "
  method it_is_true_that = "het klopt dat"
  method the_fact_that = "het feit dat"
  method where = "waar"
  method undefined = "onbepaald"

  method selected_item_s = "geselecteerde items"

  method tooltip_open_resource = "Open bron in een nieuw venster"
  method tooltip_delete_current_focus = "Klik op dit kruis om de huidige focus te verwijderen"
  method tooltip_remove_element_at_focus = "Verwijder dit query element bij de query focus"
  method tooltip_focus_on_property = "Voegt een focus toe op de eigenschap om deze te verfijnen"
  method tooltip_duplicate_focus = "Voeg een kopie van de huidige focus toe"
  method tooltip_or = "Voeg een alternatief voor de huidige focus toe"
  method tooltip_optionally = "Maak de huidige focus optioneel"
  method tooltip_not = "Pas negatie toe op de huidige focus"
  method tooltip_any = "Verberg de focus kolom in de tabel met resultaten"
  method tooltip_sample = "Vervang de aggregatie door een voorbeeld om een andere aggregatie-operator te selecteten "
  method tooltip_aggreg = "Aggregeer de focus kolom in de tabel met resultaten" (*, for each solution on other columns *)
  method tooltip_func = "Pas de functie toe op de huidige focus"
  method tooltip_input_name = "Voer een (nieuwe) naam in voor het resultaat van de expressie"
  method tooltip_foreach = "Groepeer resultaten voor elke waarde van deze entiteit"
  method tooltip_foreach_result = "Bereken de aggregatie voor elk resultaat van de verwante query"
  method tooltip_foreach_id = "Bereken de aggregatie voor elke waarde van deze entiteit"
  method tooltip_aggreg_id = "Voeg een nieuwe aggregatiekolom toe voor deze entiteit"
  method tooltip_highest = "Sorteer de focus kolom in aflopende volgorde"
  method tooltip_lowest = "Sorteer de focus kolom in oplopende volgorde"
  method tooltip_header_hide_focus = "Klik op deze kolom header om de focus te verbergen"
  method tooltip_header_set_focus = "Klik op deze kolom header om de focus daar op te zetten"
  method tooltip_header_exact_count = "Klik om de exacte telling te krijgen"
  method tooltip_geolocation = "Haal geolocatie op om entiteiten op een kaart te tonen"
  method tooltip_hierarchy = "Geef een hiërarchie weer van entiteiten volgende de eigenschap aan de linkerkant"

  method msg_permalink = "De volgende URL verwijst naar het huidige endpoint en de query (CTRL+C, Enter om naar het klembord te kopiëren"
  method msg_clear_log = "Weet u zeker dat u de navigatiegeschiedenis wilt wissen? (Deze actie kan niet ongedaan worden gemaakt.)"
  method msg_full_log = "De lokale opslag is vol. Wilt u de navigatiegeschiedenis voor dit endpoint wissen om de opname van toekomstige navigatie mogelijk te maken ? (Deze actie kan niet ongedaan worden gemaakt.) Als u op 'Annuleren' klikt, zal de opname stoppen totdat de geschiedenis is gewist."
  method result_results = "resultaat", "resultaten"
  method item_items = "item", "items"
  (*method entity_entities = "entiteit", "entiteiten"
  method concept_concepts = "concept", "concepten"
  method modifier_modifiers = "modifier", "modifiers"*)
  method sorting_frequency = "afnemende frequentie"
  method sorting_alphanum = "alfanumerieke volgorde"
end
