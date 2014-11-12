
(* configuration *)

type config =
    { mutable max_results : int;
      mutable max_classes : int;
      mutable max_properties : int;
      mutable logging : bool;
      mutable entity_lexicon : Lexicon.entity_lexicon;
      mutable class_lexicon : Lexicon.class_lexicon;
      mutable property_lexicon : Lexicon.property_lexicon;
    }

let config =
  { max_results = 200;
    max_classes = 200;
    max_properties = 1000;
    logging = true;
    entity_lexicon = Lexicon.default_entity_lexicon;
    class_lexicon = Lexicon.default_class_lexicon;
    property_lexicon = Lexicon.default_property_lexicon;
  }
