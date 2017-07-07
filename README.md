# idris-regex
Verified implementation of Brzozowski derivatives in Idris

The grammar is given by `RegExp: Type -> Type`.
The semantics of regular expressions is specified by

```idris
RegExpSpec: (a: Type) -> (RegExp a) -> (xs: List a) -> Type
```

Finally the file contains a verified matching procedure for deciding regular language membership

```idris
match : DecEq a => (xs : List a) -> (r : RegExp a) -> Dec (RegExpSpec a r xs)
```
