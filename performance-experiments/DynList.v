Declare Scope dyn_scope.
Delimit Scope dyn_scope with dyn.
Module DynList.
  Inductive t := nil | cons {T} (v : T) (rest : t).
  Module Export Notations.
    Bind Scope dyn_scope with t.
    Arguments cons {T}%type v%dyn rest%dyn.
    Infix "::" := cons (at level 60, right associativity) : dyn_scope.
    Notation "[ ]" := nil (format "[ ]") : dyn_scope.
    Notation "[ x ]" := (cons x nil) : dyn_scope.
    Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : dyn_scope.
  End Notations.
End DynList.
Export DynList.Notations.
