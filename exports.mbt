// Re-export sub-package types and functions so that downstream
// packages can import only "bobzhang/hol".

///|
pub using @foundation {type Subst}

///|
pub using @types {type Type, type TypeSubst, type TypeMatchState, mk_fun, bool_ty, ind_ty}

///|
pub using @terms {type Term, type TermSubst, type TermMatchResult, mk_var, mk_app, const_}

///|
pub using @logic {type Thm, type Kernel, type BoolSyntax, type Equal}
