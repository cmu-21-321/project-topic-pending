/-! # Programs with authorization checks -/

namespace TypedAuthz

variable {User Input Location : Type} {Value : Location -> Type}

inductive Program (Value : Location -> Type) : List Location -> Type -> Type 1 where
  | pure {checked : List Location} {Result : Type} (r : Result) : Program Value checked Result
  | read {checked : List Location} {Result : Type} (loc : Location) (h : List.Mem loc checked)
      (k : Value loc -> Program Value checked Result) : Program Value checked Result
  | check {checked : List Location} {Result : Type} (loc : Location)
      (yes : Program Value (loc :: checked) Result) (no : Program Value checked Result) :
      Program Value checked Result

inductive Event (Location : Type) where
  | query (loc : Location) (ok : Bool)
  | access (loc : Location)

def Program.run (policy : User -> Input -> Location -> Bool) (u : User) (i : Input)
    (db : (loc : Location) -> Value loc) {checked : List Location} {Result : Type} :
    Program Value checked Result -> Prod Result (List (Event Location))
  | .pure r => (r, [])
  | .read loc _ k =>
      let rest := run policy u i db (k (db loc))
      (rest.1, .access loc :: rest.2)
  | .check loc yes no =>
      let ok := policy u i loc
      let rest := if ok then run policy u i db yes else run policy u i db no
      (rest.1, .query loc ok :: rest.2)

end TypedAuthz
