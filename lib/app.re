open Core;
open Incr_dom;
module Hazelnut = Hazelnut_lib.Hazelnut;

let string_of_cursor = (e: string): string => "👉" ++ e ++ "👈";
let string_of_arrow = (t1: string, t2: string): string =>
  "(" ++ t1 ++ ") -> (" ++ t2 ++ ")";
let string_of_lam = (x: string, e: string): string =>
  "fun " ++ x ++ " -> { " ++ e ++ " }";
let string_of_ap = (e1: string, e2: string): string =>
  "(" ++ e1 ++ ") (" ++ e2 ++ ")";
let string_of_plus = (e1: string, e2: string): string =>
  "(" ++ e1 ++ ") + (" ++ e2 ++ ")";
let string_of_asc = (e: string, t: string): string =>
  "(" ++ e ++ "): (" ++ t ++ ")";
let string_of_ehole: string = "[ ]";
let string_of_nehole = (e: string): string => "[ " ++ e ++ " ]";

let rec string_of_htyp: Hazelnut.htyp => string =
  fun
  | Arrow(t1, t2) =>
    string_of_arrow(string_of_htyp(t1), string_of_htyp(t2))
  | Num => "Num"
  | Hole => string_of_ehole;

let rec string_of_hexp: Hazelnut.hexp => string =
  fun
  | Var(x) => x
  | Lam(x, e) => string_of_lam(x, string_of_hexp(e))
  | Ap(e1, e2) => string_of_ap(string_of_hexp(e1), string_of_hexp(e2))
  | Num(n) => string_of_int(n)
  | Plus(e1, e2) => string_of_plus(string_of_hexp(e1), string_of_hexp(e2))
  | Asc(e, t) => string_of_asc(string_of_hexp(e), string_of_htyp(t))
  | EHole => string_of_ehole
  | NEHole(e) => string_of_nehole(string_of_hexp(e));

let rec string_of_ztyp: Hazelnut.ztyp => string =
  fun
  | Cursor(t) => string_of_cursor(string_of_htyp(t))
  | LArrow(t1, t2) =>
    string_of_arrow(string_of_ztyp(t1), string_of_htyp(t2))
  | RArrow(t1, t2) =>
    string_of_arrow(string_of_htyp(t1), string_of_ztyp(t2));

let rec string_of_zexp: Hazelnut.zexp => string =
  fun
  | Cursor(e) => string_of_cursor(string_of_hexp(e))
  | Lam(x, e) => string_of_lam(x, string_of_zexp(e))
  | LAp(e1, e2) => string_of_ap(string_of_zexp(e1), string_of_hexp(e2))
  | RAp(e1, e2) => string_of_ap(string_of_hexp(e1), string_of_zexp(e2))
  | LPlus(e1, e2) => string_of_plus(string_of_zexp(e1), string_of_hexp(e2))
  | RPlus(e1, e2) => string_of_plus(string_of_hexp(e1), string_of_zexp(e2))
  | LAsc(e, t) => string_of_asc(string_of_zexp(e), string_of_htyp(t))
  | RAsc(e, t) => string_of_asc(string_of_hexp(e), string_of_ztyp(t))
  | NEHole(e) => string_of_nehole(string_of_zexp(e));

[@deriving (sexp, fields, compare)]
type state = {
  e: Hazelnut.zexp,
  t: Hazelnut.htyp,
  warning: option(string),
};

module Model = {
  [@deriving (sexp, fields, compare)]
  type t = {state};

  let set = (s: state): t => {state: s};

  let init = (): t =>
    set({
      e: Cursor(Plus(Plus(Num(1), EHole), Num(3))),
      t: Num,
      warning: None,
    });

  let clear = set({e: Cursor(EHole), t: Hole, warning: None});

  let cutoff = (t1: t, t2: t): bool => compare(t1, t2) == 0;
};

module Action = {
  [@deriving sexp]
  type t =
    | Clear
    | HazelnutAction(Hazelnut.action);
};

module State = {
  type t = unit;
};

let apply_action = (model: Model.t, action, _, ~schedule_action as _) => {
  let state = model.state;

  let warn = (warning: string): Model.t =>
    Model.set({...state, warning: Some(warning)});

  switch ((action: Action.t)) {
  | Clear => Model.clear
  | HazelnutAction(action) =>
    try({
      let result =
        Hazelnut.syn_action(
          Hazelnut.TypCtx.empty,
          (state.e, state.t),
          action,
        );

      switch (result) {
      | Some((e, t)) => Model.set({e, t, warning: None})
      | None => warn("Invalid action")
      };
    }) {
    | Hazelnut.Unimplemented => warn("Unimplemented")
    }
  };
};

let on_startup = (~schedule_action as _, _) => Async_kernel.return();

let view =
    (m: Incr.t(Model.t), ~inject: Action.t => Ui_effect.t(Base.unit))
    : Ui_incr.t(Vdom.Node.t) => {
  open Incr.Let_syntax;
  open Vdom;

  let%map body = {
    let%map state = m >>| Model.state;

    let expression =
      Node.div([
        Node.p([Node.textf("%s", string_of_zexp(state.e))]),
        Node.p([Node.textf("%s", string_of_htyp(state.t))]),
      ]);

    let buttons = {
      let button = (label, action) =>
        Node.div([
          Node.button(
            ~attr=
              Attr.many_without_merge([
                Attr.id(String.lowercase(label)),
                Attr.on_click(_ev => inject(action)),
              ]),
            [Node.text(label)],
          ),
        ]);

      let move_buttons =
        Node.div([
          button("Move to Parent", Action.HazelnutAction(Move(Parent))),
          button(
            "Move to Child 1",
            Action.HazelnutAction(Move(Child(One))),
          ),
          button(
            "Move to Child 2",
            Action.HazelnutAction(Move(Child(Two))),
          ),
        ]);

      let construct_buttons =
        Node.div([
          button(
            "Construct Arrow",
            Action.HazelnutAction(Construct(Arrow)),
          ),
          button("Construct Num", Action.HazelnutAction(Construct(Num))),
          button("Construct Asc", Action.HazelnutAction(Construct(Asc))),
          button(
            "Construct Var",
            Action.HazelnutAction(Construct(Var("TODO"))) // TODO: Don't hardcode value
          ),
          button(
            "Construct Lam",
            Action.HazelnutAction(Construct(Lam("TODO"))) // TODO: Don't hardcode value
          ),
          button("Construct Ap", Action.HazelnutAction(Construct(Ap))),
          button(
            "Construct Lit",
            Action.HazelnutAction(Construct(Lit(0))) // TODO: Don't hardcode value
          ),
          button("Construct Plus", Action.HazelnutAction(Construct(Plus))),
          button(
            "Construct NEHole",
            Action.HazelnutAction(Construct(NEHole)),
          ),
        ]);

      let delete_button =
        Node.div([button("Delete", Action.HazelnutAction(Del))]);

      let finish_button =
        Node.div([button("Finish", Action.HazelnutAction(Finish))]);

      let clear_button = Node.div([button("Clear", Action.Clear)]);

      Node.div([
        move_buttons,
        construct_buttons,
        delete_button,
        finish_button,
        clear_button,
      ]);
    };

    let warning =
      Node.p(
        switch (state.warning) {
        | Some(warning) => [Node.text(warning)]
        | None => []
        },
      );

    Node.div([expression, buttons, warning]);
  };

  Node.body([body]);
};

let create = (model, ~old_model as _, ~inject) => {
  open Incr.Let_syntax;
  let%map apply_action = {
    let%map model = model;
    apply_action(model);
  }
  and view = view(model, ~inject)
  and model = model;
  Component.create(~apply_action, model, view);
};

let initial_model = Model.init();
