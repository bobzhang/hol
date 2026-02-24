// Step 2: Types
//
// HOL types form the type language of a simply-typed lambda calculus:
//
//   Type ::= Var(name)              -- type variable (enables polymorphism)
//          | App(name, [args...])   -- type constructor application
//
// `Var("'a")` is a type variable; polymorphic constants like equality are
// parameterized over type variables.  `App("bool", [])` is the Boolean type,
// `App("fun", [A, B])` is the function type A -> B, etc.
//
// The set of valid type constructors and their arities is tracked in a
// mutable registry (`type_table`).  This mirrors the SML tutorial's design
// decision: type operators live in a global ref while `Type` values
// themselves remain immutable.  A purely functional alternative would
// thread a `KernelState` monad (see step6's `kernel_monad.mbt`).

///|
/// HOL types: a simply-typed lambda calculus type language with type variables (`Var`) and type constructor applications (`App`).
pub enum Type {
  // Type variable -- enables polymorphism (e.g., `'a` in `= : 'a -> 'a -> bool`)
  TyVar(String)
  // Type constructor applied to arguments (e.g., `App("fun", [bool, bool])`)
  TyApp(String, Array[Type])
} derive(Eq, Compare, Show, Debug)

///|
/// A substitution mapping type variables to types.
pub type TypeSubst = @foundation.Subst[Type, Type]

///|
/// Register a new type constructor with the given name and arity in the global type table.
pub fn Type::new_type(name : String, arity : Int) -> Unit {
  type_table.val = type_table.val.add(name, arity)
}

///|
/// Reset the type table to its last checkpointed state.
pub fn Type::reset_table() -> Unit {
  type_table.val = checkpoint_type_table.val
}

///|
/// Save the current type table as a checkpoint for later restoration via `reset_table`.
pub fn Type::checkpoint_defs() -> Unit {
  checkpoint_type_table.val = type_table.val
}

///|
/// Construct a type constructor application, checking that the argument count matches the registered arity.
pub fn Type::mk_type(name : String, args : Array[Type]) -> Type {
  match type_table.val.get(name) {
    Some(arity) =>
      if arity == args.length() {
        TyApp(name, args)
      } else {
        abort("mk_type: \{name} has arity \{arity}, got \{args.length()}")
      }
    None => abort("mk_type: unregistered type \{name}")
  }
}

///|
/// Construct a type variable from a name (e.g., `Var("'a")`).
pub fn mk_var(name : String) -> Type {
  TyVar(name)
}

///|
/// Decompose a type constructor application into its name and arguments; aborts on a type variable.
pub fn Type::dest_type(self : Type) -> (String, Array[Type]) {
  match self {
    TyApp(name, args) => (name, args)
    _ => abort("dest_type: expected App")
  }
}

///|
/// Extract the name from a type variable; aborts on a type constructor application.
pub fn Type::dest_var(self : Type) -> String {
  match self {
    TyVar(x) => x
    _ => abort("dest_var: expected Var")
  }
}

///|
/// Return true if this type is a constructor application (`App`).
pub fn Type::is_type(self : Type) -> Bool {
  self is TyApp(_, _)
}

///|
/// Return true if this type is a type variable (`Var`).
pub fn Type::is_var(self : Type) -> Bool {
  self is TyVar(_)
}

///|
/// Return the built-in Boolean type (`TyApp("bool", [])`).
// FIXME(upstream): it would be nice to have an easy way to 
// migrate method to `free_fn`, maybe
// `#as_free_fn(depercate_method=true)`
// migrate `free_fn` to `method` is easy
// `#as_free_fn(deprecated = true)`
pub fn bool_ty() -> Type {
  TyApp("bool", [])
}

///|
/// Return the built-in individual type (`App("ind", [])`), used for the axiom of infinity.
pub fn ind_ty() -> Type {
  TyApp("ind", [])
}

///|
/// Serialize the type into a human-readable string representation that mirrors the AST structure.
pub fn Type::serialize(self : Type) -> String {
  match self {
    TyVar(x) => "Var(\{x})"
    TyApp(name, args) => {
      let parts = args.map(t => t.serialize())
      let joined = parts.join(", ")
      "App(\{name}, [\{joined}])"
    }
  }
}

///|
/// Apply a type substitution, replacing type variables according to the given mapping.
pub fn Type::subst(self : Type, s : TypeSubst) -> Type {
  match self {
    TyVar(_) as v =>
      match s.lookup(v) {
        Some(rep) => rep
        None => v
      }
    TyApp(name, args) => TyApp(name, args.map(arg => arg.subst(s)))
  }
}

///|
/// Construct the function type `t1 -> t2` (i.e., `App("fun", [t1, t2])`).
pub fn mk_fun(t1 : Type, t2 : Type) -> Type {
  TyApp("fun", [t1, t2])
}

///|
/// Return true if this type is a function type (`App("fun", [_, _])`).
pub fn Type::is_fun(self : Type) -> Bool {
  match self {
    TyApp("fun", [_, _]) => true
    _ => false
  }
}

///|
/// Extract the range (return type) of a function type; aborts on non-function types.
pub fn Type::range(self : Type) -> Type {
  match self {
    TyApp("fun", [_, t]) => t
    _ => abort("range: expected function type")
  }
}

///|
/// Extract the domain (argument type) of a function type; aborts on non-function types.
pub fn Type::domain(self : Type) -> Type {
  match self {
    TyApp("fun", [t, _]) => t
    _ => abort("domain: expected function type")
  }
}

///|
/// Decompose a function type into its domain and range; aborts on non-function types.
pub fn Type::dest_fun(self : Type) -> (Type, Type) {
  match self {
    TyApp("fun", [t1, t2]) => (t1, t2)
    _ => abort("dest_fun: expected function type")
  }
}

///|
/// Pretty-print the type using conventional mathematical notation (e.g., `'a --> bool`).
pub fn Type::pprint(self : Type) -> String {
  match self {
    TyVar(x) => x
    TyApp("fun", [t1, t2]) => "\{t1.pprint()} --> \{t2.pprint()}"
    TyApp(name, []) => name
    TyApp(name, [t]) => "\{t.pprint()} \{name}"
    TyApp(name, args) => {
      let parts = args.map(t => t.pprint())
      let joined = parts.join(", ")
      "(\{joined}) \{name}"
    }
  }
}

///|
/// Collect all type variables occurring in this type, sorted and deduplicated.
pub fn Type::vars_in(self : Type) -> Array[Type] {
  match self {
    TyVar(_) as t => [t]
    TyApp(_, args) => {
      let vars : Array[Type] = []
      for arg in args {
        vars.append(arg.vars_in())
      }
      @foundation.dedup_sort(vars)
    }
  }
}
