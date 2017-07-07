module Main

import Data.List

%default total

data RegExp: Type -> Type where
  Atom: a -> RegExp a
  Disj: RegExp a -> RegExp a -> RegExp a
  Seq: RegExp a -> RegExp a -> RegExp a
  Star: RegExp a -> RegExp a
  Empty: RegExp a
  Nothing: RegExp a

data RegExpSpec: (a: Type) -> (RegExp a) -> (xs: List a) -> Type where
  AtomSpec: (a : Type) -> (x : a) ->
             RegExpSpec a (Atom x) [x]
  DisjSpec1: (a : Type) -> (r1 : RegExp a) ->
             (r2: RegExp a) -> (xs : List a) ->
             (RegExpSpec a r1 xs) ->
             RegExpSpec a (Disj r1 r2) xs
  DisjSpec2: (a : Type) -> (r1 : RegExp a) ->
             (r2: RegExp a) -> (xs : List a) ->
             (RegExpSpec a r2 xs) ->
             RegExpSpec a (Disj r1 r2) xs
  SeqSpec: (a: Type) ->
           (xs : List a) -> (ys : List a) -> (zs : List a) ->
           (r1 : RegExp a) -> (r2 : RegExp a) ->
           RegExpSpec a r1 xs ->
           RegExpSpec a r2 ys ->
           zs = xs ++ ys ->
           RegExpSpec a (Seq r1 r2) zs
  StarSpec0: (a: Type) ->
             (r: RegExp a) ->
             RegExpSpec a (Star r) []
  StarSpecS: (a: Type) ->
             (xs : List a) -> (ys : List a) ->
             (zs : List a) ->
             (r : RegExp a) ->
             RegExpSpec a r xs ->
             RegExpSpec a (Star r) ys ->
             (zs = xs ++ ys) ->
             RegExpSpec a (Star r) zs
  EmptySpec: (a: Type) -> RegExpSpec a Empty []

isEmpty : (r : RegExp a) -> RegExp a
isEmpty (Atom x) = Nothing
isEmpty (Disj x y) = Disj (isEmpty x) (isEmpty y)
isEmpty (Seq x y) = Seq (isEmpty x) (isEmpty y)
isEmpty (Star x) = Empty
isEmpty Empty = Empty
isEmpty Nothing = Nothing

atom_case : (a : Type) -> (x : a) -> RegExpSpec a (Atom x) [] -> Void
atom_case _ _ (AtomSpec _ _) impossible
atom_case _ _ (DisjSpec1 _ _ _ _ _) impossible
atom_case _ _ (DisjSpec2 _ _ _ _ _) impossible
atom_case _ _ (SeqSpec _ _ _ _ _ _ _ _ _) impossible
atom_case _ _ (StarSpec0 _ _) impossible
atom_case _ _ (StarSpecS _ _ _ _ _ _ _ _) impossible
atom_case _ _ (EmptySpec _) impossible

disj_case : (a: Type) -> (x: RegExp a) -> (y: RegExp a) ->
            (contra1: RegExpSpec a x [] -> Void) ->
            (contra2: RegExpSpec a y [] -> Void) ->
            RegExpSpec a (Disj x y) [] -> Void
disj_case a x y contra1 contra2 (DisjSpec1 a x y [] z) = contra1 z
disj_case a x y contra1 contra2 (DisjSpec2 a x y [] z) = contra2 z

seq_yes_case : (a: Type) -> (x : RegExp a) -> (y : RegExp a) ->
               RegExpSpec a x [] -> RegExpSpec a y [] ->
               RegExpSpec a (Seq x y) []
seq_yes_case a x y prf1 prf2 = SeqSpec a [] [] [] x y prf1 prf2 Refl

about_list1 : (a : Type) -> (xs : List a) -> (ys : List a) ->
              [] = xs ++ ys -> [] = xs
about_list1 a [] ys prf = Refl
about_list1 _ (_ :: _) _ Refl impossible

about_list2 : (a : Type) -> (xs : List a) -> (ys : List a) ->
              [] = xs ++ ys -> [] = ys
about_list2 a [] [] Refl = Refl
about_list2 _ (_ :: _) _ Refl impossible

about_list3 : (a : Type) -> (x : a) -> (y : a) -> (xs : List a) ->
              (ys : List a) -> (zs : List a) -> x :: xs = (y :: ys) ++ zs ->
              (x = y, xs = ys ++ zs)
about_list3 a y y (ys ++ zs) ys zs Refl = (Refl, Refl)

about_list4 : (a : Type) -> (x : a) -> (xs : List a) -> (ys : List a) ->
              (zs : List a) -> x :: xs = ys ++ zs ->
                Either (DPair (List a) (\ys' => (ys = x :: ys', xs = ys' ++ zs)))
                       (ys = [], zs = x :: xs)
about_list4 a x xs [] zs prf = Right (Refl, sym prf)
about_list4 a x xs (y :: ys) zs prf =
  let (Refl, h2) = about_list3 a x y xs ys zs prf in (Left (MkDPair ys (Refl, h2)))

seq_no_case1: (a : Type) -> (x : RegExp a) -> (y : RegExp a) ->
              (RegExpSpec a x [] -> Void) -> RegExpSpec a (Seq x y) [] -> Void
seq_no_case1 a x y f (SeqSpec a xs ys [] x y z w prf) =
  let h = about_list1 a xs ys prf in
  f (rewrite h in z)

seq_no_case2: (a : Type) -> (x : RegExp a) -> (y : RegExp a) ->
              (RegExpSpec a y [] -> Void) -> RegExpSpec a (Seq x y) [] -> Void
seq_no_case2 a x y f (SeqSpec a xs ys [] x y z w prf) =
  let h = about_list2 a xs ys prf in
  f (rewrite h in w)

match_nothing_is_false : (a : Type) -> (xs : List a) ->
                         RegExpSpec a Nothing xs -> Void
match_nothing_is_false _ _ (AtomSpec _ _) impossible
match_nothing_is_false _ _ (DisjSpec1 _ _ _ _ _) impossible
match_nothing_is_false _ _ (DisjSpec2 _ _ _ _ _) impossible
match_nothing_is_false _ _ (SeqSpec _ _ _ _ _ _ _ _ _) impossible
match_nothing_is_false _ _ (StarSpec0 _ _) impossible
match_nothing_is_false _ _ (StarSpecS _ _ _ _ _ _ _ _) impossible
match_nothing_is_false _ _ (EmptySpec _) impossible

decEmpty : (a : Type) -> (r : RegExp a) -> Dec (RegExpSpec a r [])
decEmpty a (Atom x) = No (atom_case a x)
decEmpty a (Disj x y) =
  case (decEmpty a x, decEmpty a y) of
    (Yes prf, _) => Yes (DisjSpec1 a x y [] prf)
    (_, Yes prf) => Yes (DisjSpec2 a x y [] prf)
    (No contra1, No contra2) => No (disj_case a x y contra1 contra2)
decEmpty a (Seq x y) =
  case (decEmpty a x, decEmpty a y) of
    (Yes prf1, Yes prf2) => Yes (seq_yes_case a x y prf1 prf2)
    (No contra, _) => No (seq_no_case1 a x y contra)
    (_, No contra) =>  No (seq_no_case2 a x y contra)
decEmpty a (Star x) = Yes (StarSpec0 a x)
decEmpty a Empty = Yes (EmptySpec a)
decEmpty a Nothing = No (match_nothing_is_false a [])

derive : DecEq a => (r : RegExp a) -> (x : a) -> RegExp a
derive (Atom y) x = case decEq y x of
                      Yes _ => Empty
                      No _ => Nothing
derive (Disj y z) x = Disj (derive y x) (derive z x)
derive (Seq y z) x = Disj (Seq (derive y x) z) (Seq (isEmpty y) (derive z x))
derive (Star y) x = Seq (derive y x) (Star y)
derive Empty x = Nothing
derive Nothing x = Nothing

empty_match_implies_empty_list : RegExpSpec a Empty xs -> xs = []
empty_match_implies_empty_list (EmptySpec a) = Refl

is_empty_match_implies_empty_list :
  (a : Type) -> (r : RegExp a) ->
  (xs : List a) -> RegExpSpec a (isEmpty r) xs -> xs = []
is_empty_match_implies_empty_list a (Atom y) xs x =
  void (match_nothing_is_false a xs x)
is_empty_match_implies_empty_list a (Disj y z) xs (DisjSpec1 a (isEmpty y) (isEmpty z) xs x) =
  is_empty_match_implies_empty_list a y xs x
is_empty_match_implies_empty_list a (Disj y z) xs (DisjSpec2 a (isEmpty y) (isEmpty z) xs x) =
  is_empty_match_implies_empty_list a z xs x
is_empty_match_implies_empty_list a (Seq y z) xs (SeqSpec a ys zs xs (isEmpty y) (isEmpty z) x w prf) =
  rewrite prf in
    (let h1 = is_empty_match_implies_empty_list a y ys x
         h2 = is_empty_match_implies_empty_list a z zs w
     in rewrite h1 in rewrite h2 in Refl)
is_empty_match_implies_empty_list a (Star y) xs x = empty_match_implies_empty_list x
is_empty_match_implies_empty_list a Empty xs x = empty_match_implies_empty_list x
is_empty_match_implies_empty_list a Nothing xs x = void (match_nothing_is_false a xs x)

is_empty_is_sound : (a : Type) -> (r : RegExp a) -> (xs : List a) ->
         RegExpSpec a (isEmpty r) xs -> RegExpSpec a r []
is_empty_is_sound a (Atom y) xs x = void (match_nothing_is_false a xs x)
is_empty_is_sound a (Disj y z) xs (DisjSpec1 a (isEmpty y) (isEmpty z) xs x) =
  let h = is_empty_is_sound a y xs x in (DisjSpec1 a y z [] h)
is_empty_is_sound a (Disj y z) xs (DisjSpec2 a (isEmpty y) (isEmpty z) xs x) =
  let h = is_empty_is_sound a z xs x in (DisjSpec2 a y z [] h)
is_empty_is_sound a (Seq y z) xs (SeqSpec a ys zs xs (isEmpty y) (isEmpty z) x w prf) =
    let h1 = is_empty_is_sound a y ys x in
    let h2 = is_empty_is_sound a z zs w in SeqSpec a [] [] [] y z h1 h2 Refl
is_empty_is_sound a (Star y) xs x = StarSpec0 a y
is_empty_is_sound a Empty xs x = EmptySpec a
is_empty_is_sound a Nothing xs x = void (match_nothing_is_false a xs x)

seq_nothing_match_is_false : (a : Type) -> (r : RegExp a) -> (xs : List a) ->
                             RegExpSpec a (Seq Nothing r) xs -> Void
seq_nothing_match_is_false a r xs (SeqSpec a ys zs xs Nothing r x y prf) =
  void (match_nothing_is_false a ys x)

derivative_is_sound: (a : Type) -> DecEq a => (r : RegExp a) ->
                     (x : a) -> (xs : List a) ->
                     RegExpSpec a (derive r x) xs -> RegExpSpec a r (x :: xs)
derivative_is_sound a (Atom z) x xs y with (decEq z x)
  derivative_is_sound a (Atom x) x xs y | (Yes Refl) =
    rewrite (empty_match_implies_empty_list y) in AtomSpec a x
  derivative_is_sound a (Atom z) x xs y | (No contra) =
    void (match_nothing_is_false a xs y)
derivative_is_sound a (Disj z w) x xs y =
  case y of
    (DisjSpec1 a (derive z x) _ xs y) =>
      let z' = (derivative_is_sound a z x xs y)
      in DisjSpec1 a z w (x :: xs) z'
    (DisjSpec2 a _ (derive w x) xs y) =>
      let z' = (derivative_is_sound a w x xs y)
      in DisjSpec2 a z w (x :: xs) z'
derivative_is_sound a (Seq r1 r2) x xs (DisjSpec1 a (Seq _ _) (Seq _ _) xs (SeqSpec a ys zs xs _ r2 y z prf)) =
  let h' = derivative_is_sound a r1 x ys y
  in rewrite prf in
  SeqSpec a (x :: ys) zs (x :: ys ++ zs) r1 r2 h' z Refl
derivative_is_sound a (Seq r1 r2) x xs (DisjSpec2 a (Seq _ r2) (Seq _ _) xs (SeqSpec a ys zs xs (isEmpty r1) (derive r2 x) y s prf)) =
  rewrite prf in
  rewrite (is_empty_match_implies_empty_list a r1 ys y) in
  let h1 = derivative_is_sound a r2 x zs s in
  let h2 = is_empty_is_sound a r1 ys y in
  SeqSpec a [] (x :: zs) (x :: zs) r1 r2 h2 h1 Refl
derivative_is_sound a (Star z) x _ (SeqSpec a xs ys zs _ (Star z) y w prf) =
  rewrite prf in
  let h = derivative_is_sound a z x xs y in
  StarSpecS a (x :: xs) ys (x :: xs ++ ys) z h w Refl
derivative_is_sound _ Empty _ _ (AtomSpec _ _) impossible
derivative_is_sound _ Empty _ _ (DisjSpec1 _ _ _ _ _) impossible
derivative_is_sound _ Empty _ _ (DisjSpec2 _ _ _ _ _) impossible
derivative_is_sound _ Empty _ _ (SeqSpec _ _ _ _ _ _ _ _ _) impossible
derivative_is_sound _ Empty _ _ (StarSpec0 _ _) impossible
derivative_is_sound _ Empty _ _ (StarSpecS _ _ _ _ _ _ _ _) impossible
derivative_is_sound _ Empty _ _ (EmptySpec _) impossible
derivative_is_sound _ Nothing _ _ (AtomSpec _ _) impossible
derivative_is_sound _ Nothing _ _ (DisjSpec1 _ _ _ _ _) impossible
derivative_is_sound _ Nothing _ _ (DisjSpec2 _ _ _ _ _) impossible
derivative_is_sound _ Nothing _ _ (SeqSpec _ _ _ _ _ _ _ _ _) impossible
derivative_is_sound _ Nothing _ _ (StarSpec0 _ _) impossible
derivative_is_sound _ Nothing _ _ (StarSpecS _ _ _ _ _ _ _ _) impossible
derivative_is_sound _ Nothing _ _ (EmptySpec _) impossible

atom_match_implies: (a : Type) -> (x : a) -> (xs : List a) ->
                    RegExpSpec a (Atom x) (x :: xs) -> xs = []
atom_match_implies a x [] (AtomSpec a x) = Refl

atom_match_implies2: (a : Type) -> (x : a) -> (y : a) -> (xs : List a) ->
                     RegExpSpec a (Atom x) (y :: xs) -> x = y
atom_match_implies2 a y y [] (AtomSpec a y) = Refl

cons_is_not_nil : (a : Type) -> (x : a) -> (xs : List a) -> x :: xs = [] -> Void
cons_is_not_nil _ _ _ Refl impossible

is_empty_is_complete : (a : Type) -> (r : RegExp a) -> RegExpSpec a r [] ->
                       RegExpSpec a (isEmpty r) []
is_empty_is_complete _ (Atom _) (AtomSpec _ _) impossible
is_empty_is_complete _ (Atom _) (DisjSpec1 _ _ _ _ _) impossible
is_empty_is_complete _ (Atom _) (DisjSpec2 _ _ _ _ _) impossible
is_empty_is_complete _ (Atom _) (SeqSpec _ _ _ _ _ _ _ _ _) impossible
is_empty_is_complete _ (Atom _) (StarSpec0 _ _) impossible
is_empty_is_complete _ (Atom _) (StarSpecS _ _ _ _ _ _ _ _) impossible
is_empty_is_complete _ (Atom _) (EmptySpec _) impossible
is_empty_is_complete a (Disj y z) (DisjSpec1 a y z [] x) =
  let h = is_empty_is_complete a y x in
  DisjSpec1 a (isEmpty y) (isEmpty z) [] h
is_empty_is_complete a (Disj y z) (DisjSpec2 a y z [] x) =
  let h = is_empty_is_complete a z x in
  DisjSpec2 a (isEmpty y) (isEmpty z) [] h
is_empty_is_complete a (Seq y z) (SeqSpec a xs ys [] y z x w prf) =
  let h1 = about_list1 a xs ys prf in
  let h2 = about_list2 a xs ys prf in
  let ih1 = is_empty_is_complete a y (rewrite h1 in x) in
  let ih2 = is_empty_is_complete a z (rewrite h2 in w) in
  SeqSpec a [] [] [] (isEmpty y) (isEmpty z) ih1 ih2 Refl
is_empty_is_complete a (Star y) x = EmptySpec a
is_empty_is_complete a Empty x = x
is_empty_is_complete a Nothing x = x

append_nil_neutral : (a : Type) -> (xs : List a) -> xs ++ [] = xs
append_nil_neutral a [] = Refl
append_nil_neutral a (x :: xs) =
  let h = append_nil_neutral a xs in
  rewrite h in Refl

about_list5 : (x : a) -> (y : a) -> (xs : List a) -> (ys : List a) -> (zs : List a) ->
              x :: xs = (y :: ys) ++ zs -> (x = y, xs = ys ++ zs)
about_list5 x _ (ys ++ zs) ys zs Refl = (Refl, Refl)

mutual {
star_case : (a : Type) -> DecEq a => (r : RegExp a) -> (x : a) ->
            (xs : List a) -> RegExpSpec a (Star r) xs ->
            (xs' : List a) ->
            xs = x :: xs' ->
            RegExpSpec a (Seq (derive r x) (Star r)) xs'
star_case a r x [] (StarSpec0 a r) = \xs', contra => void (cons_is_not_nil a x xs' (sym contra))
star_case a r x _ (StarSpecS a [] zs _ r y z Refl) = \xs', Refl =>
  star_case a r x (x :: xs') z xs' Refl
star_case a r x xs (StarSpecS a (w :: ys) zs xs r y z prf) = \xs', Refl =>
  let (Refl, Refl) = about_list5 x w xs' ys zs prf in
  let h = derivative_is_complete a r x ys y in
  SeqSpec a ys zs (ys ++ zs) (derive r x) (Star r) h z Refl

derivative_is_complete : (a : Type) -> (DecEq a) => (r : RegExp a) -> (x : a) -> (xs : List a) -> RegExpSpec a r (x :: xs) -> RegExpSpec a (derive r x) xs
derivative_is_complete a (Atom z) x xs y with (decEq z x)
  derivative_is_complete a (Atom x) x xs y | (Yes Refl) =
    rewrite (atom_match_implies a x xs y) in (EmptySpec a)
  derivative_is_complete a (Atom z) x xs y | (No contra) =
   void (contra (atom_match_implies2 a z x xs y))
derivative_is_complete a (Disj z w) x xs (DisjSpec1 a z w (x :: xs) y) =
  let h = derivative_is_complete a z x xs y in
  DisjSpec1 a (derive z x) (derive w x) xs h
derivative_is_complete a (Disj z w) x xs (DisjSpec2 a z w (x :: xs) y) =
  let h = derivative_is_complete a w x xs y in
  DisjSpec2 a (derive z x) (derive w x) xs h
derivative_is_complete a (Seq z w) x xs (SeqSpec a ys zs (x :: xs) z w y s prf) =
  case about_list4 a x xs ys zs prf of
    Left (ys' ** (h1, h2)) =>
      rewrite h2 in
      let h = derivative_is_complete a z x ys' (rewrite sym h1 in y) in
      DisjSpec1 a (Seq (derive z x) w) (Seq (isEmpty z) (derive w x)) (ys' ++ zs)
        (SeqSpec a ys' zs (ys' ++ zs) (derive z x) w h s Refl)
    Right (h1, h2) =>
      let h = derivative_is_complete a w x xs (rewrite sym h2 in s) in
      DisjSpec2 a (Seq (derive z x) w) (Seq (isEmpty z) (derive w x)) xs
        (SeqSpec a [] xs xs (isEmpty z) (derive w x) (is_empty_is_complete a z (rewrite sym h1 in y)) h Refl)
derivative_is_complete a (Star r) x xs prf =
  star_case a r x (x :: xs) prf xs Refl
derivative_is_complete a Empty x xs y =
  let h = empty_match_implies_empty_list y in void (cons_is_not_nil a x xs h)
derivative_is_complete a Nothing x xs y = void (match_nothing_is_false a (x :: xs) y)
}

match : DecEq a => (xs : List a) -> (r : RegExp a) -> Dec (RegExpSpec a r xs)
match {a} [] r = decEmpty a r
match {a} (x :: xs) r =
  case match xs (derive r x) of
    Yes prf => Yes (derivative_is_sound a r x xs prf)
    No contra => No (contra . (derivative_is_complete a r x xs))
