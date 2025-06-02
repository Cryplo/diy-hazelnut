open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch(t){
    | Cursor(htyp: Htyp.t) => htyp
    | LArrow(ztyp: Ztyp.t, htyp:Htyp.t) => Arrow(erase_typ(ztyp), htyp)
    | RArrow(htyp:Htyp.t, ztyp:Ztyp.t) => Arrow(htyp, erase_typ(ztyp))
  }
}

let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(hexp: Hexp.t) => hexp
  | Lam(str: string, zexp: Zexp.t) => Lam(str, erase_exp(zexp))
  | LAp(zexp: Zexp.t, hexp: Hexp.t) => Ap(erase_exp(zexp), hexp)
  | RAp(hexp: Hexp.t, zexp: Zexp.t) => Ap(hexp, erase_exp(zexp))
  | LPlus(zexp: Zexp.t, hexp: Hexp.t) => Plus(erase_exp(zexp), hexp)
  | RPlus(hexp: Hexp.t, zexp: Zexp.t) => Plus(hexp, erase_exp(zexp))
  | LAsc(zexp: Zexp.t, htyp: Htyp.t) => Asc(erase_exp(zexp), htyp) 
  | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) => Asc(hexp, erase_typ(ztyp))
  | NEHole(zexp: Zexp.t) => erase_exp(zexp)
  };
};

let syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;

  raise(Unimplemented);
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;

  raise(Unimplemented);
};

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
