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
  switch (t) {
  | Cursor(htyp: Htyp.t) => htyp
  | LArrow(ztyp: Ztyp.t, htyp: Htyp.t) => Arrow(erase_typ(ztyp), htyp)
  | RArrow(htyp: Htyp.t, ztyp: Ztyp.t) => Arrow(htyp, erase_typ(ztyp))
  };
};

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
  | NEHole(zexp: Zexp.t) => NEHole(erase_exp(zexp))
  };
};


let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(str: string) => TypCtx.find_opt(str, ctx) //Implement rule 1a
  | Lam(_, hexp: Hexp.t) => syn(ctx, hexp)
  // Implement rule 1b
  | Ap(hexp1: Hexp.t, hexp2: Hexp.t) =>
    switch (syn(ctx, hexp1)) {
    | Some(t1: Htyp.t) =>
      switch (match_arrow(t1)) {
      | Arrow(t2: Htyp.t, t3: Htyp.t) =>
        ana(ctx, hexp2, t2) ? Some(t3) : None
      | _ => None
      }
    | None => None
    }
  | Lit(_) => Some(Num) //Implement rule 1c
  | Plus(hexp1: Hexp.t, hexp2: Hexp.t) =>
    ana(ctx, hexp1, Num: Htyp.t) && ana(ctx, hexp2, Num: Htyp.t)
      ? Some(Num) : None // Implement rule 1d
  | Asc(hexp: Hexp.t, htyp: Htyp.t) =>
    ana(ctx, hexp, htyp) ? Some(htyp) : None //Implement rule 1e
  | EHole => Some(Hole) //Implement rule 1f
  | NEHole(hexp: Hexp.t) =>
    switch (syn(ctx, hexp)) {
    //Implement rule 1g
    | Some(_) => Some(Hole)
    | None => None
    }
  };
}

and consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  // Implement 3a-d
  | (Hole, _) => true
  | (_, Hole) => true
  | (Num, Num) => true
  | (Arrow(a, b), Arrow(c, d)) => consistent(a, b) && consistent(c, d)
  | _ => false
  };
}

and match_arrow = (t: Htyp.t): Htyp.t => {
  switch (t) {
  | Arrow(t1: Htyp.t, t2: Htyp.t) => Arrow(t1, t2)
  | Hole => Arrow(Hole, Hole)
  | _ => raise(Unimplemented)
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  //Implement 2a
  | Lam(str: string, hexp: Hexp.t) =>
    switch (match_arrow(t)) {
    | Arrow(t1: Htyp.t, t2: Htyp.t) =>
      let newctx = TypCtx.add(str, t1, ctx);
      ana(newctx, hexp, t2);
    | _ => raise(Unimplemented)
    }
  | _ =>
    switch (syn(ctx, e)) {
    // Implement 2b
    | Some(t1) => consistent(t1, t)
    | None => false
    }
  };
};

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  ignore(t);
  switch(a){
    | Move(d: Dir.t) => switch(d){
      | Child(_) => {
        let new_zexp = move_child(ctx, e, d);
        let syn_typ = syn(ctx, erase_exp(e));
        switch(syn_typ){
          | Some(contents) => Some((new_zexp, contents))
          | None => None
        }
        /*
        let htyp = cursor_htyp_from_zexp(ctx, new_zexp);
        switch(htyp){
          | Some(content) => Some((new_zexp, content))
          | None => raise(Unimplemented)
        }*/
      };
      | _ => raise(Unimplemented)
    };
    | _ => raise(Unimplemented)
  };
}

// Need to keep the action argument to keep track of first or second child
and move_child = (ctx: typctx, e: Zexp.t, d: Dir.t) : Zexp.t => {
  switch(d){
    | Child(c: Child.t) => switch(e){
      //Move cursor down at cursor spot
      | Cursor(hexp: Hexp.t) =>
        switch (hexp) {
        | Var(_) => raise(Unimplemented) // cant return a child if cursor is on the variable
        | Lam(str: string, hexp: Hexp.t) => Lam(str, Cursor(hexp))
        | Ap(hexp1: Hexp.t, hexp2: Hexp.t) => 
          switch (c) {
          | One => LAp(Cursor(hexp1), hexp2)
          | Two => RAp(hexp1, Cursor(hexp2))
          }
        | Lit(_) => raise(Unimplemented)
        | Plus(hexp1: Hexp.t, hexp2: Hexp.t) =>
          switch (c) {
          | One => LPlus(Cursor(hexp1), hexp2)
          | Two => RPlus(hexp1, Cursor(hexp2))
          }
        | Asc(hexp: Hexp.t, htyp: Htyp.t) =>
          switch (c) {
          | One => LAsc(Cursor(hexp), htyp)
          | Two => RAsc(hexp, Cursor(htyp))
          }
        | EHole => raise(Unimplemented)
        | NEHole(hexp: Hexp.t) => NEHole(Cursor(hexp))
        }
      //recursively move down until reaching cursor
      | Lam(str: string, zexp: Zexp.t) =>
        Lam(str, move_child(ctx, zexp, d))
      | LAp(zexp: Zexp.t, hexp: Hexp.t) =>
        LAp(move_child(ctx, zexp, d), hexp)
      | RAp(hexp: Hexp.t, zexp: Zexp.t) =>
        RAp(hexp, move_child(ctx, zexp, d))
      | LPlus(zexp: Zexp.t, hexp: Hexp.t) =>
        LPlus(move_child(ctx, zexp, d), hexp)
      | RPlus(hexp: Hexp.t, zexp: Zexp.t) =>
        RPlus(hexp, move_child(ctx, zexp, d))
      | LAsc(zexp: Zexp.t, htyp: Htyp.t) =>
        LAsc(move_child(ctx, zexp, d), htyp)
      //| RAsc(hexp: Hexp.t, ztyp: Ztyp.t) => raise(Unimplemented)//this is possible to do, see first test of type_action
      | NEHole(zexp: Zexp.t) => NEHole(move_child(ctx, zexp, d))
      | _ => raise(Unimplemented)
    }
    | _ => raise(Unimplemented) //this shouldn't ever be reached
  };
}
/*
and cursor_htyp_from_zexp = (ctx: typctx, e: Zexp.t): option(Htyp.t) => {
  switch(e){
    | Cursor(hexp: Hexp.t) => syn(ctx, hexp)
    | Lam(_, zexp: Zexp.t) => cursor_htyp_from_zexp(ctx, zexp)
      | LAp(zexp: Zexp.t, _) => cursor_htyp_from_zexp(ctx, zexp)
      | RAp(_, zexp: Zexp.t) => cursor_htyp_from_zexp(ctx, zexp)
      | LPlus(zexp: Zexp.t, _) => cursor_htyp_from_zexp(ctx, zexp)
      | RPlus(_, zexp: Zexp.t) => cursor_htyp_from_zexp(ctx, zexp)
      | LAsc(zexp: Zexp.t, _) => cursor_htyp_from_zexp(ctx, zexp)
      | RAsc(_, ztyp: Ztyp.t) => cursor_htyp_from_ztyp(ctx, ztyp)
      | NEHole(zexp: Zexp.t) => cursor_htyp_from_zexp(ctx, zexp)
  };
}

and cursor_htyp_from_ztyp = (ctx: typctx, t: Ztyp.t): option(Htyp.t) => {
  switch(t){
    | Cursor(htyp: Htyp.t) => Some(htyp)
    | LArrow(t: Ztyp.t, _) => cursor_htyp_from_ztyp(ctx, t)
    | RArrow(_, t: Ztyp.t) => cursor_htyp_from_ztyp(ctx, t)
  };
}
*/
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
