  empty
, 'A : typeK
, 'Bool : typeK
, 'tt : 'Bool
, 'ff : 'Bool
, 'EqBool : Pi 'Bool . ( Pi 'Bool . typeK )
, 'refl : Pi 'Bool . ( 'EqBool 0 0 )
, 'elimEqBool : Pi ('EqBool 'tt 'ff) . 'A
, 'MaybeA : Pi 'Bool . typeK
, 'nothing : 'MaybeA 'ff
, 'just : Pi 'A . 'MaybeA 'tt
, 'elimMaybeA : Pi 'Bool . (Pi 'MaybeA 0 .
    Pi ( Pi 'EqBool 1 'ff . 'A ) .
    Pi ( Pi 'EqBool 2 'tt . (Pi 'A . 'A )) . 'A)

