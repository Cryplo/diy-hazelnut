open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
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
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
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
      | Some(Arrow(t2: Htyp.t, t3: Htyp.t)) =>
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
    ana(ctx, hexp, htyp) ? Some(htyp) : None //Implement rule 1e+
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

and match_arrow = (t: Htyp.t): option(Htyp.t) => {
  switch (t) {
  | Arrow(t1: Htyp.t, t2: Htyp.t) => Some(Arrow(t1, t2))
  | Hole => Some(Arrow(Hole, Hole))
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  //Implement 2a
  | Lam(str: string, hexp: Hexp.t) =>
    switch (match_arrow(t)) {
    | Some(Arrow(t1: Htyp.t, t2: Htyp.t)) =>
      let newctx = TypCtx.add(str, t1, ctx);
      ana(newctx, hexp, t2);
    | _ => false
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
  switch (a) {
  | Move(d: Dir.t) =>
    switch (d) {
      //rule 7a
    | Child(_) =>
      let new_zexp = move_child(ctx, e, d);
      let syn_typ = syn(ctx, erase_exp(new_zexp));
      switch (syn_typ) {
      | Some(contents) => Some((new_zexp, contents))
      | None => None
      };
    | Parent =>
      let new_zexp = move_parent(ctx, e);
      let syn_typ = syn(ctx, erase_exp(new_zexp));
      switch (syn_typ) {
      | Some(contents) => Some((new_zexp, contents))
      | None => None
      };
    }
  | Del =>
    let new_zexp = delete(ctx, e);
    let syn_typ = syn(ctx, erase_exp(new_zexp));
    switch (syn_typ) {
    | Some(contents) => Some((new_zexp, contents))
    | None => None
    };
  | Finish =>
    let new_zexp = finish(ctx, e);
    let syn_typ = syn(ctx, erase_exp(new_zexp));
    switch (syn_typ) {
    | Some(contents) => Some((new_zexp, contents))
    | None => None
    };
  | Construct(shape: Shape.t) =>
    let new_zexp = construct(ctx, (e, t), shape);
    let syn_typ = syn(ctx, erase_exp(new_zexp));
    switch (syn_typ) {
    | Some(contents) => Some((new_zexp, contents))
    | None => None
    };
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (a) {
  // rule 7b
  | Move(d: Dir.t) =>
    switch (d) {
    | Child(_) =>
      let new_zexp = move_child(ctx, e, d);
      Some(new_zexp);
      //subsumption(ctx, e, a, t) ? Some(new_zexp) : None;
    | Parent =>
      let new_zexp = move_parent(ctx, e);
      Some(new_zexp);
      //subsumption(ctx, e, a, t) ? Some(new_zexp) : None;
    }
  | Del =>
    let new_zexp = delete(ctx, e);
    Some(new_zexp);
    //subsumption(ctx, e, a, t) ? Some(new_zexp) : None;
  | Finish =>
    let new_zexp = finish(ctx, e);
    switch(syn(ctx, erase_exp(new_zexp))){
      | Some(_) => ana(ctx, erase_exp(new_zexp), t) ? Some(new_zexp) : None
      | _ => None
    }
    //subsumption(ctx, e, a, t) ? Some(new_zexp) : None;
  | Construct(shape: Shape.t) =>
    let new_zexp = construct_ana(ctx, e, t, shape);
    Some(new_zexp);
  };
}

//rule 5
/*
and subsumption = (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): bool => {
  switch(syn(ctx, erase_exp(e))){
    | Some(_) => switch(syn_action(ctx, (e, t), a)){
      | Some((_, htyp: Htyp.t)) => consistent(t, htyp)
      | None => false
    };
    | None => false
  }
}*/

// Need to keep the action argument to keep track of first or second child
and move_child = (ctx: typctx, e: Zexp.t, d: Dir.t): Zexp.t => {
  switch (d) {
  | Child(c: Child.t) =>
    switch (e) {
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
    | Lam(str: string, zexp: Zexp.t) => Lam(str, move_child(ctx, zexp, d))
    | LAp(zexp: Zexp.t, hexp: Hexp.t) => LAp(move_child(ctx, zexp, d), hexp)
    | RAp(hexp: Hexp.t, zexp: Zexp.t) => RAp(hexp, move_child(ctx, zexp, d))
    | LPlus(zexp: Zexp.t, hexp: Hexp.t) =>
      LPlus(move_child(ctx, zexp, d), hexp)
    | RPlus(hexp: Hexp.t, zexp: Zexp.t) =>
      RPlus(hexp, move_child(ctx, zexp, d))
    | LAsc(zexp: Zexp.t, htyp: Htyp.t) =>
      LAsc(move_child(ctx, zexp, d), htyp)
    | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) =>
      RAsc(hexp, move_child_ztyp(ctx, ztyp, d))
    | NEHole(zexp: Zexp.t) => NEHole(move_child(ctx, zexp, d))
    }
  | _ => raise(Unimplemented) //this shouldn't ever be reached
  };
}

and move_child_ztyp = (ctx: typctx, t: Ztyp.t, d: Dir.t): Ztyp.t => {
  switch (t) {
  | Cursor(htyp: Htyp.t) =>
    switch (htyp) {
    | Arrow(htyp1: Htyp.t, htyp2: Htyp.t) =>
      switch (d) {
      | Child(c: Child.t) =>
        switch (c) {
        | One => LArrow(Cursor(htyp1), htyp2)
        | Two => RArrow(htyp1, Cursor(htyp2))
        }
      | Parent => Cursor(htyp)
      }
    | _ => Cursor(htyp)
    }
  | LArrow(ztyp: Ztyp.t, htyp: Htyp.t) =>
    LArrow(move_child_ztyp(ctx, ztyp, d), htyp)
  | RArrow(htyp: Htyp.t, ztyp: Ztyp.t) =>
    RArrow(htyp, move_child_ztyp(ctx, ztyp, d))
  };
}
and move_parent = (ctx: typctx, e: Zexp.t): Zexp.t => {
  switch (e) {
  | Cursor(hexp: Hexp.t) => Cursor(hexp)
  | Lam(str: string, zexp: Zexp.t) =>
    switch (zexp) {
    | Cursor(hexp: Hexp.t) => Cursor(Lam(str, hexp)) //move cursor up onto Lam
    | _ => Lam(str, move_parent(ctx, zexp))
    }
  | LAp(zexp: Zexp.t, hexp: Hexp.t) =>
    switch (zexp) {
    | Cursor(hexp2: Hexp.t) => Cursor(Ap(hexp2, hexp))
    | _ => LAp(move_parent(ctx, zexp), hexp)
    }
  | RAp(hexp: Hexp.t, zexp: Zexp.t) =>
    switch (zexp) {
    | Cursor(hexp2: Hexp.t) => Cursor(Ap(hexp, hexp2))
    | _ => RAp(hexp, move_parent(ctx, zexp))
    }
  | LPlus(zexp: Zexp.t, hexp: Hexp.t) =>
    switch (zexp) {
    | Cursor(hexp2: Hexp.t) => Cursor(Plus(hexp2, hexp))
    | _ => LPlus(move_parent(ctx, zexp), hexp)
    }
  | RPlus(hexp: Hexp.t, zexp: Zexp.t) =>
    switch (zexp) {
    | Cursor(hexp2: Hexp.t) => Cursor(Plus(hexp, hexp2))
    | _ => RPlus(hexp, move_parent(ctx, zexp))
    }
  | LAsc(zexp: Zexp.t, htyp: Htyp.t) =>
    switch (zexp) {
    | Cursor(hexp: Hexp.t) => Cursor(Asc(hexp, htyp))
    | _ => LAsc(move_parent(ctx, zexp), htyp)
    }
  | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) =>
    switch (ztyp) {
    | Cursor(htyp: Htyp.t) => Cursor(Asc(hexp, htyp))
    | _ => RAsc(hexp, move_parent_ztyp(ctx, ztyp))
    }
  | NEHole(zexp: Zexp.t) =>
    switch (zexp) {
    | Cursor(hexp: Hexp.t) =>
      switch (hexp) {
      | EHole => Cursor(EHole)
      | _ => Cursor(NEHole(hexp))
      }
    | _ => NEHole(move_parent(ctx, zexp))
    }
  };
}

and move_parent_ztyp = (ctx: typctx, t: Ztyp.t): Ztyp.t => {
  switch (t) {
  | Cursor(htyp: Htyp.t) => Cursor(htyp)
  | LArrow(ztyp: Ztyp.t, htyp: Htyp.t) =>
    switch (ztyp) {
    | Cursor(htyp2: Htyp.t) => Cursor(Arrow(htyp2, htyp))
    | _ => LArrow(move_parent_ztyp(ctx, t), htyp)
    }
  | RArrow(htyp: Htyp.t, ztyp: Ztyp.t) =>
    switch (ztyp) {
    | Cursor(htyp2: Htyp.t) => Cursor(Arrow(htyp, htyp2))
    | _ => RArrow(htyp, move_parent_ztyp(ctx, t))
    }
  };
}

and delete = (ctx: typctx, e: Zexp.t): Zexp.t => {
  switch (e) {
  | Cursor(_) => Cursor(EHole)
  | Lam(str: string, zexp: Zexp.t) => Lam(str, delete(ctx, zexp))
  | LAp(zexp: Zexp.t, hexp: Hexp.t) => LAp(delete(ctx, zexp), hexp)
  | RAp(hexp: Hexp.t, zexp: Zexp.t) => RAp(hexp, delete(ctx, zexp))
  | LPlus(zexp: Zexp.t, hexp: Hexp.t) => LPlus(delete(ctx, zexp), hexp)
  | RPlus(hexp: Hexp.t, zexp: Zexp.t) => RPlus(hexp, delete(ctx, zexp))
  | LAsc(zexp: Zexp.t, htyp: Htyp.t) => LAsc(delete(ctx, zexp), htyp)
  | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) => RAsc(hexp, delete_typ(ctx, ztyp))
  | NEHole(zexp: Zexp.t) => NEHole(delete(ctx, zexp))
  };
}

and delete_typ = (ctx: typctx, t: Ztyp.t): Ztyp.t => {
  switch (t) {
  | Cursor(_) => Cursor(Hole)
  | LArrow(ztyp: Ztyp.t, htyp: Htyp.t) =>
    LArrow(delete_typ(ctx, ztyp), htyp)
  | RArrow(htyp: Htyp.t, ztyp: Ztyp.t) =>
    RArrow(htyp, delete_typ(ctx, ztyp))
  };
}

and finish = (ctx: typctx, e: Zexp.t): Zexp.t => {
  switch (e) {
  | Cursor(hexp: Hexp.t) =>
    switch (hexp) {
    | NEHole(hexp2: Hexp.t) => finish(ctx, Cursor(hexp2))
    | _ => Cursor(hexp)
    }
  | Lam(str: string, zexp: Zexp.t) => Lam(str, finish(ctx, zexp))
  | LAp(zexp: Zexp.t, hexp: Hexp.t) => LAp(finish(ctx, zexp), hexp)
  | RAp(hexp: Hexp.t, zexp: Zexp.t) => RAp(hexp, finish(ctx, zexp))
  | LPlus(zexp: Zexp.t, hexp: Hexp.t) => LPlus(finish(ctx, zexp), hexp)
  | RPlus(hexp: Hexp.t, zexp: Zexp.t) => RPlus(hexp, finish(ctx, zexp))
  | LAsc(zexp: Zexp.t, htyp: Htyp.t) => LAsc(finish(ctx, zexp), htyp)
  | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) => RAsc(hexp, delete_typ(ctx, ztyp))
  | NEHole(zexp: Zexp.t) => NEHole(finish(ctx, zexp))
  };
}

and construct = (ctx: typctx, (e: Zexp.t, t: Htyp.t), shape: Shape.t): Zexp.t => {
  switch (e) {
  | Cursor(contents: Hexp.t) =>
    switch (shape) {
    | Arrow => raise(Unimplemented) // this should be for tpyes not expressions
    | Num => raise(Unimplemented) // same as above
    | Asc =>
      switch (syn(ctx, contents)) {
      | Some(htyp: Htyp.t) => RAsc(contents, Cursor(htyp))
      | None => RAsc(contents, Cursor(Hole))
      }
    | Var(str: string) => consistent(TypCtx.find(str, ctx), t) ? Cursor(Var(str)) : NEHole(Cursor(Var(str)))
    | Lam(str: string) =>
      RAsc(Lam(str, EHole), LArrow(Cursor(Hole), Hole))
    // synthesize the type for matching
    | Ap =>
      switch (syn(ctx, contents)) {
      // actually match the type to arrow type
      | Some(htyp: Htyp.t) =>
        switch (match_arrow(htyp)) {
        | Some(_) => RAp(contents, Cursor(EHole))
        | None => RAp(NEHole(contents), Cursor(EHole))
        }
      | None => RAp(NEHole(contents), Cursor(EHole))
      } // synthesize a type then check if it is of arrow type to see if i need to put it in a hole or not
    | Lit(num: int) => Cursor(Lit(num))
    | Plus =>
      switch (syn(ctx, contents)) {
      | Some(Num) => RPlus(contents, Cursor(EHole))
      | _ => RPlus(NEHole(contents), Cursor(EHole))
      }
    | NEHole => NEHole(Cursor(contents))
    }
  | Lam(str: string, zexp: Zexp.t) => 
    switch(t){
      | Arrow(_, htyp2: Htyp.t) => Lam(str, construct(ctx, (zexp, htyp2), shape))
      | _ => raise(Unimplemented)
    }
  | LAp(zexp: Zexp.t, hexp: Hexp.t) =>
    LAp(construct(ctx, (zexp, t), shape), hexp)
  | RAp(hexp: Hexp.t, zexp: Zexp.t) =>
    RAp(hexp, construct(ctx, (zexp, t), shape))
  | LPlus(zexp: Zexp.t, hexp: Hexp.t) =>
    LPlus(construct(ctx, (zexp, t), shape), hexp)
  | RPlus(hexp: Hexp.t, zexp: Zexp.t) =>
    RPlus(hexp, construct(ctx, (zexp, t), shape))
  | LAsc(zexp: Zexp.t, htyp: Htyp.t) =>
    LAsc(construct(ctx, (zexp, htyp), shape), htyp)
  | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) =>
    RAsc(hexp, construct_typ(ctx, ztyp, shape))
  | NEHole(zexp: Zexp.t) => NEHole(construct(ctx, (zexp, t), shape))
  //| _ => raise(Unimplemented)
  };
}


and construct_ana = (ctx: typctx, e: Zexp.t, t: Htyp.t, shape: Shape.t): Zexp.t => {
  switch(e){
    | Cursor(contents: Hexp.t) => switch(shape){
      | Asc => RAsc(contents, Cursor(t))
      | Var(str: string) => consistent(TypCtx.find(str, ctx), t) ? Cursor(Var(str)) : NEHole(Cursor(Var(str)))
      | Lam(str: string) => switch(match_arrow(t)){
        | Some(Arrow(_, _)) => Lam(str, Cursor(EHole))
        | _ => NEHole(RAsc(Lam(str, EHole), LArrow(Cursor(Hole), Hole)))
      }
      | Lit(num: int) =>
        switch (t) {
          | Num => Cursor(Lit(num))
          | _ => NEHole(Cursor((Lit(num))))
        }
      | _ => construct(ctx, (Cursor(contents), t), shape)
    }
    // recurse into zipper structure
    | Lam(str: string, zexp: Zexp.t) => Lam(str, construct_ana(ctx, zexp, t, shape))
    | LAp(zexp: Zexp.t, hexp: Hexp.t) =>
      LAp(construct_ana(ctx, zexp, t, shape), hexp)
    | RAp(hexp: Hexp.t, zexp: Zexp.t) =>
      RAp(hexp, construct_ana(ctx, zexp, t, shape))
    | LPlus(zexp: Zexp.t, hexp: Hexp.t) =>
      LPlus(construct_ana(ctx, zexp, t, shape), hexp)
    | RPlus(hexp: Hexp.t, zexp: Zexp.t) =>
      RPlus(hexp, construct_ana(ctx, zexp, t, shape))
    | LAsc(zexp: Zexp.t, htyp: Htyp.t) =>
      switch(t){
        | Arrow(htyp1, _) => LAsc(construct_ana(ctx, zexp, htyp1, shape), htyp)
        | _ => LAsc(construct_ana(ctx, zexp, t, shape), htyp)
      }
    | RAsc(hexp: Hexp.t, ztyp: Ztyp.t) =>
      RAsc(hexp, construct_typ(ctx, ztyp, shape))
    | NEHole(zexp: Zexp.t) => NEHole(construct_ana(ctx, zexp, t, shape))
  }
}

and construct_typ = (ctx: typctx, t: Ztyp.t, shape: Shape.t): Ztyp.t => {
  switch (t) {
  | Cursor(contents: Htyp.t) =>
    switch (shape) {
    | Arrow => RArrow(contents, Cursor(Hole))
    | Num => Cursor(Num)
    | _ => raise(Unimplemented)
    }
  | LArrow(ztyp: Ztyp.t, htyp: Htyp.t) => LArrow(construct_typ(ctx, ztyp, shape), htyp)
  | RArrow(htyp: Htyp.t, ztyp: Ztyp.t) => RArrow(htyp, construct_typ(ctx, ztyp, shape))
  };
} /*add a recurse to cursor helper function that I can just plug in a function in for late*/;
