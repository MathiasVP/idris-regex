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

data RegExpSpec: (RegExp a) -> (xs: List a) -> Type where
  AtomSpec: (x : a) -> RegExpSpec (Atom x) [x]
  DisjSpec1: (r1 : RegExp a) ->
             (r2: RegExp a) -> (xs : List a) ->
             (RegExpSpec r1 xs) ->
             RegExpSpec (Disj r1 r2) xs
  DisjSpec2: (r1 : RegExp a) ->
             (r2: RegExp a) -> (xs : List a) ->
             (RegExpSpec r2 xs) ->
             RegExpSpec (Disj r1 r2) xs
  SeqSpec: (xs : List a) -> (ys : List a) -> (zs : List a) ->
           (r1 : RegExp a) -> (r2 : RegExp a) ->
           RegExpSpec r1 xs ->
           RegExpSpec r2 ys ->
           zs = xs ++ ys ->
           RegExpSpec (Seq r1 r2) zs
  StarSpec0: (r: RegExp a) ->
             RegExpSpec (Star r) []
  StarSpecS: (xs : List a) -> (ys : List a) ->
             (zs : List a) ->
             (r : RegExp a) ->
             RegExpSpec r xs ->
             RegExpSpec (Star r) ys ->
             (zs = xs ++ ys) ->
             RegExpSpec (Star r) zs
  EmptySpec: RegExpSpec Empty []

isEmpty : (r : RegExp a) -> RegExp a
isEmpty (Atom x) = Nothing
isEmpty (Disj x y) = Disj (isEmpty x) (isEmpty y)
isEmpty (Seq x y) = Seq (isEmpty x) (isEmpty y)
isEmpty (Star x) = Empty
isEmpty Empty = Empty
isEmpty Nothing = Nothing

atom_case : (x : a) -> RegExpSpec (Atom x) [] -> Void
atom_case _ (AtomSpec _) impossible
atom_case _ (DisjSpec1 _ _ _ _) impossible
atom_case _ (DisjSpec2 _ _ _ _) impossible
atom_case _ (SeqSpec _ _ _ _ _ _ _ _) impossible
atom_case _ (StarSpec0 _) impossible
atom_case _ (StarSpecS _ _ _ _ _ _ _) impossible
atom_case _ EmptySpec impossible


disj_case : (x: RegExp a) -> (y: RegExp a) ->
            (contra1: RegExpSpec x [] -> Void) ->
            (contra2: RegExpSpec y [] -> Void) ->
            RegExpSpec (Disj x y) [] -> Void
disj_case x y contra1 contra2 (DisjSpec1 x y [] z) = contra1 z
disj_case x y contra1 contra2 (DisjSpec2 x y [] z) = contra2 z

seq_yes_case : (x : RegExp a) -> (y : RegExp a) ->
               RegExpSpec x [] -> RegExpSpec y [] ->
               RegExpSpec (Seq x y) []
seq_yes_case x y prf1 prf2 = SeqSpec [] [] [] x y prf1 prf2 Refl

about_list1 : (xs : List a) -> (ys : List a) ->
              [] = xs ++ ys -> [] = xs
about_list1 [] ys prf = Refl
about_list1 (_ :: _) _ Refl impossible

about_list2 : (xs : List a) -> (ys : List a) ->
              [] = xs ++ ys -> [] = ys
about_list2 [] [] Refl = Refl
about_list2 (_ :: _) _ Refl impossible

about_list3 : (x : a) -> (y : a) -> (xs : List a) ->
              (ys : List a) -> (zs : List a) -> x :: xs = (y :: ys) ++ zs ->
              (x = y, xs = ys ++ zs)
about_list3 y y (ys ++ zs) ys zs Refl = (Refl, Refl)

about_list4 : (x : a) -> (xs : List a) -> (ys : List a) ->
              (zs : List a) -> x :: xs = ys ++ zs ->
                Either (DPair (List a) (\ys' => (ys = x :: ys', xs = ys' ++ zs)))
                       (ys = [], zs = x :: xs)
about_list4 x xs [] zs prf = Right (Refl, sym prf)
about_list4 x xs (y :: ys) zs prf =
  let (Refl, h2) = about_list3 x y xs ys zs prf in (Left (MkDPair ys (Refl, h2)))

seq_no_case1: (x : RegExp a) -> (y : RegExp a) ->
              (RegExpSpec x [] -> Void) -> RegExpSpec (Seq x y) [] -> Void
seq_no_case1 x y f (SeqSpec xs ys [] x y z w prf) =
  let h = about_list1 xs ys prf in
  f (rewrite h in z)

seq_no_case2: (x : RegExp a) -> (y : RegExp a) ->
              (RegExpSpec y [] -> Void) -> RegExpSpec (Seq x y) [] -> Void
seq_no_case2 x y f (SeqSpec xs ys [] x y z w prf) =
  let h = about_list2 xs ys prf in
  f (rewrite h in w)

match_nothing_is_false : (xs : List a) ->
                         RegExpSpec Nothing xs -> Void
match_nothing_is_false _ (AtomSpec _) impossible
match_nothing_is_false _ (DisjSpec1 _ _ _ _) impossible
match_nothing_is_false _ (DisjSpec2 _ _ _ _) impossible
match_nothing_is_false _ (SeqSpec _ _ _ _ _ _ _ _) impossible
match_nothing_is_false _ (StarSpec0 _) impossible
match_nothing_is_false _ (StarSpecS _ _ _ _ _ _ _) impossible
match_nothing_is_false _ EmptySpec impossible

decEmpty : (r : RegExp a) -> Dec (RegExpSpec r [])
decEmpty (Atom x) = No (atom_case x)
decEmpty (Disj x y) =
  case (decEmpty x, decEmpty y) of
    (Yes prf, _) => Yes (DisjSpec1 x y [] prf)
    (_, Yes prf) => Yes (DisjSpec2 x y [] prf)
    (No contra1, No contra2) => No (disj_case x y contra1 contra2)
decEmpty (Seq x y) =
  case (decEmpty x, decEmpty y) of
    (Yes prf1, Yes prf2) => Yes (seq_yes_case x y prf1 prf2)
    (No contra, _) => No (seq_no_case1 x y contra)
    (_, No contra) =>  No (seq_no_case2 x y contra)
decEmpty (Star x) = Yes (StarSpec0 x)
decEmpty Empty = Yes EmptySpec
decEmpty Nothing = No (match_nothing_is_false [])

derive : DecEq a => (r : RegExp a) -> (x : a) -> RegExp a
derive (Atom y) x = case decEq y x of
                      Yes _ => Empty
                      No _ => Nothing
derive (Disj y z) x = Disj (derive y x) (derive z x)
derive (Seq y z) x = Disj (Seq (derive y x) z) (Seq (isEmpty y) (derive z x))
derive (Star y) x = Seq (derive y x) (Star y)
derive Empty x = Nothing
derive Nothing x = Nothing

empty_match_implies_empty_list : RegExpSpec Empty xs -> xs = []
empty_match_implies_empty_list EmptySpec = Refl

is_empty_match_implies_empty_list :
  (r : RegExp a) ->
  (xs : List a) -> RegExpSpec (isEmpty r) xs -> xs = []
is_empty_match_implies_empty_list (Atom y) xs x =
  void (match_nothing_is_false xs x)
is_empty_match_implies_empty_list (Disj y z) xs (DisjSpec1 (isEmpty y) (isEmpty z) xs x) =
  is_empty_match_implies_empty_list y xs x
is_empty_match_implies_empty_list (Disj y z) xs (DisjSpec2 (isEmpty y) (isEmpty z) xs x) =
  is_empty_match_implies_empty_list z xs x
is_empty_match_implies_empty_list (Seq y z) xs (SeqSpec ys zs xs (isEmpty y) (isEmpty z) x w prf) =
  rewrite prf in
    (let h1 = is_empty_match_implies_empty_list y ys x
         h2 = is_empty_match_implies_empty_list z zs w
     in rewrite h1 in rewrite h2 in Refl)
is_empty_match_implies_empty_list (Star y) xs x = empty_match_implies_empty_list x
is_empty_match_implies_empty_list Empty xs x = empty_match_implies_empty_list x
is_empty_match_implies_empty_list Nothing xs x = void (match_nothing_is_false xs x)


is_empty_is_sound : (r : RegExp a) -> (xs : List a) ->
         RegExpSpec (isEmpty r) xs -> RegExpSpec r []
is_empty_is_sound (Atom y) xs x = void (match_nothing_is_false xs x)
is_empty_is_sound (Disj y z) xs (DisjSpec1 (isEmpty y) (isEmpty z) xs x) =
  let h = is_empty_is_sound y xs x in (DisjSpec1 y z [] h)
is_empty_is_sound (Disj y z) xs (DisjSpec2 (isEmpty y) (isEmpty z) xs x) =
  let h = is_empty_is_sound z xs x in (DisjSpec2 y z [] h)
is_empty_is_sound (Seq y z) xs (SeqSpec ys zs xs (isEmpty y) (isEmpty z) x w prf) =
    let h1 = is_empty_is_sound y ys x in
    let h2 = is_empty_is_sound z zs w in SeqSpec [] [] [] y z h1 h2 Refl
is_empty_is_sound (Star y) xs x = StarSpec0 y
is_empty_is_sound Empty xs x = EmptySpec
is_empty_is_sound Nothing xs x = void (match_nothing_is_false xs x)

seq_nothing_match_is_false : (r : RegExp a) -> (xs : List a) ->
                             RegExpSpec (Seq Nothing r) xs -> Void
seq_nothing_match_is_false r xs (SeqSpec ys zs xs Nothing r x y prf) =
  void (match_nothing_is_false ys x)

derivative_is_sound: DecEq a => (r : RegExp a) ->
                     (x : a) -> (xs : List a) ->
                     RegExpSpec (derive r x) xs -> RegExpSpec r (x :: xs)
derivative_is_sound (Atom z) x xs y with (decEq z x)
  derivative_is_sound (Atom x) x xs y | (Yes Refl) =
    rewrite (empty_match_implies_empty_list y) in AtomSpec x
  derivative_is_sound (Atom z) x xs y | (No contra) =
    void (match_nothing_is_false xs y)
derivative_is_sound (Disj z w) x xs y =
  case y of
    (DisjSpec1 (derive z x) _ xs y) =>
      let z' = (derivative_is_sound z x xs y)
      in DisjSpec1 z w (x :: xs) z'
    (DisjSpec2 _ (derive w x) xs y) =>
      let z' = (derivative_is_sound w x xs y)
      in DisjSpec2 z w (x :: xs) z'
derivative_is_sound (Seq r1 r2) x xs (DisjSpec1 (Seq _ _) (Seq _ _) xs (SeqSpec ys zs xs _ r2 y z prf)) =
  let h' = derivative_is_sound r1 x ys y
  in rewrite prf in
  SeqSpec (x :: ys) zs (x :: ys ++ zs) r1 r2 h' z Refl
derivative_is_sound (Seq r1 r2) x xs (DisjSpec2 (Seq _ r2) (Seq _ _) xs (SeqSpec ys zs xs (isEmpty r1) _ y s prf)) =
  rewrite prf in
  rewrite (is_empty_match_implies_empty_list r1 ys y) in
  let h1 = derivative_is_sound r2 x zs s in
  let h2 = is_empty_is_sound r1 ys y in
  SeqSpec [] (x :: zs) (x :: zs) r1 r2 h2 h1 Refl
derivative_is_sound (Star z) x _ (SeqSpec xs ys zs _ (Star z) y w prf) =
  rewrite prf in
  let h = derivative_is_sound z x xs y in
  StarSpecS (x :: xs) ys (x :: xs ++ ys) z h w Refl
derivative_is_sound Empty _ _ (AtomSpec _) impossible
derivative_is_sound Empty _ _ (DisjSpec1 _ _ _ _) impossible
derivative_is_sound Empty _ _ (DisjSpec2 _ _ _ _) impossible
derivative_is_sound Empty _ _ (SeqSpec _ _ _ _ _ _ _ _) impossible
derivative_is_sound Empty _ _ (StarSpec0 _) impossible
derivative_is_sound Empty _ _ (StarSpecS _ _ _ _ _ _ _) impossible
derivative_is_sound Empty _ _ EmptySpec impossible
derivative_is_sound Nothing _ _ (AtomSpec _) impossible
derivative_is_sound Nothing _ _ (DisjSpec1 _ _ _ _) impossible
derivative_is_sound Nothing _ _ (DisjSpec2 _ _ _ _) impossible
derivative_is_sound Nothing _ _ (SeqSpec _ _ _ _ _ _ _ _) impossible
derivative_is_sound Nothing _ _ (StarSpec0 _) impossible
derivative_is_sound Nothing _ _ (StarSpecS _ _ _ _ _ _ _) impossible
derivative_is_sound Nothing _ _ EmptySpec impossible

atom_match_implies: (x : a) -> (xs : List a) ->
                    RegExpSpec (Atom x) (x :: xs) -> xs = []
atom_match_implies x [] (AtomSpec x) = Refl

atom_match_implies2: (x : a) -> (y : a) -> (xs : List a) ->
                     RegExpSpec (Atom x) (y :: xs) -> x = y
atom_match_implies2 y y [] (AtomSpec y) = Refl

cons_is_not_nil : (x : a) -> (xs : List a) -> x :: xs = [] -> Void
cons_is_not_nil _ _ Refl impossible

is_empty_is_complete : (r : RegExp a) -> RegExpSpec r [] ->
                       RegExpSpec (isEmpty r) []
is_empty_is_complete (Atom _) (AtomSpec _) impossible
is_empty_is_complete (Atom _) (DisjSpec1 _ _ _ _) impossible
is_empty_is_complete (Atom _) (DisjSpec2 _ _ _ _) impossible
is_empty_is_complete (Atom _) (SeqSpec _ _ _ _ _ _ _ _) impossible
is_empty_is_complete (Atom _) (StarSpec0 _) impossible
is_empty_is_complete (Atom _) (StarSpecS _ _ _ _ _ _ _) impossible
is_empty_is_complete (Atom _) EmptySpec impossible
is_empty_is_complete (Disj y z) (DisjSpec1 y z [] x) =
  let h = is_empty_is_complete y x in
  DisjSpec1 (isEmpty y) (isEmpty z) [] h
is_empty_is_complete (Disj y z) (DisjSpec2 y z [] x) =
  let h = is_empty_is_complete z x in
  DisjSpec2 (isEmpty y) (isEmpty z) [] h
is_empty_is_complete (Seq y z) (SeqSpec xs ys [] y z x w prf) =
  let h1 = about_list1 xs ys prf in
  let h2 = about_list2 xs ys prf in
  let ih1 = is_empty_is_complete y (rewrite h1 in x) in
  let ih2 = is_empty_is_complete z (rewrite h2 in w) in
  SeqSpec [] [] [] (isEmpty y) (isEmpty z) ih1 ih2 Refl
is_empty_is_complete (Star y) x = EmptySpec
is_empty_is_complete Empty x = x
is_empty_is_complete Nothing x = x

append_nil_neutral : (xs : List a) -> xs ++ [] = xs
append_nil_neutral [] = Refl
append_nil_neutral (x :: xs) =
  let h = append_nil_neutral xs in
  rewrite h in Refl

about_list5 : (x : a) -> (y : a) -> (xs : List a) -> (ys : List a) -> (zs : List a) ->
              x :: xs = (y :: ys) ++ zs -> (x = y, xs = ys ++ zs)
about_list5 x _ (ys ++ zs) ys zs Refl = (Refl, Refl)

mutual {
star_case : DecEq a => (r : RegExp a) -> (x : a) ->
            (xs : List a) -> RegExpSpec (Star r) xs ->
            (xs' : List a) ->
            xs = x :: xs' ->
            RegExpSpec (Seq (derive r x) (Star r)) xs'
star_case r x [] (StarSpec0 r) = \xs', contra => void (cons_is_not_nil x xs' (sym contra))
star_case r x _ (StarSpecS [] zs _ r y z Refl) = \xs', Refl =>
  star_case r x (x :: xs') z xs' Refl
star_case r x xs (StarSpecS (w :: ys) zs xs r y z prf) = \xs', Refl =>
  let (Refl, Refl) = about_list5 x w xs' ys zs prf in
  let h = derivative_is_complete r x ys y in
  SeqSpec ys zs (ys ++ zs) (derive r x) (Star r) h z Refl

derivative_is_complete : (DecEq a) => (r : RegExp a) -> (x : a) -> (xs : List a) -> RegExpSpec r (x :: xs) -> RegExpSpec (derive r x) xs
derivative_is_complete (Atom z) x xs y with (decEq z x)
  derivative_is_complete (Atom x) x xs y | (Yes Refl) =
    rewrite (atom_match_implies x xs y) in EmptySpec
  derivative_is_complete (Atom z) x xs y | (No contra) =
   void (contra (atom_match_implies2 z x xs y))
derivative_is_complete (Disj z w) x xs (DisjSpec1 z w (x :: xs) y) =
  let h = derivative_is_complete z x xs y in
  DisjSpec1 (derive z x) (derive w x) xs h
derivative_is_complete (Disj z w) x xs (DisjSpec2 z w (x :: xs) y) =
  let h = derivative_is_complete w x xs y in
  DisjSpec2 (derive z x) (derive w x) xs h
derivative_is_complete (Seq z w) x xs (SeqSpec ys zs (x :: xs) z w y s prf) =
  case about_list4 x xs ys zs prf of
    Left (ys' ** (h1, h2)) =>
      rewrite h2 in
      let h = derivative_is_complete z x ys' (rewrite sym h1 in y) in
      DisjSpec1 (Seq (derive z x) w) (Seq (isEmpty z) (derive w x)) (ys' ++ zs)
        (SeqSpec ys' zs (ys' ++ zs) (derive z x) w h s Refl)
    Right (h1, h2) =>
      let h = derivative_is_complete w x xs (rewrite sym h2 in s) in
      DisjSpec2 (Seq (derive z x) w) (Seq (isEmpty z) (derive w x)) xs
        (SeqSpec [] xs xs (isEmpty z) (derive w x) (is_empty_is_complete z (rewrite sym h1 in y)) h Refl)
derivative_is_complete (Star r) x xs prf =
  star_case r x (x :: xs) prf xs Refl
derivative_is_complete Empty x xs y =
  let h = empty_match_implies_empty_list y in void (cons_is_not_nil x xs h)
derivative_is_complete Nothing x xs y = void (match_nothing_is_false (x :: xs) y)
}

match : DecEq a => (xs : List a) -> (r : RegExp a) -> Dec (RegExpSpec r xs)
match [] r = decEmpty r
match (x :: xs) r =
  case match xs (derive r x) of
    Yes prf => Yes (derivative_is_sound r x xs prf)
    No contra => No (contra . (derivative_is_complete r x xs))
