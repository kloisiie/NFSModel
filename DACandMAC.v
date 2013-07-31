Require Export SFSstate. 
 
Set Implicit Arguments.
Unset Strict Implicit. 
 
(*********************************************************************) 
(*                Preconditions for DAC and MAC                      *) 
(*********************************************************************) 
 
Section Preconditions. 
 
Variable s : SFSstate. 
 
(*This predicate asserts that for a entity to read an entity, the   *) 
(*former must belong to the set of readers of the last. Also, this   *) 
(*condition holds if the entity belongs to a group wich in turn     *) 
(*belongs to the entity's readers.                                   *) 
 
Definition PreDACRead (eSub : ENTITY) (eObj : ENTITY) : Prop :=
  match fcap (cap s) eSub with
  | Some x => set_In eObj (CanReadEntities x)
  | None => False
  end. 
 
 
(*This predicate asserts that for a entity to write to an entity,   *) 
(*the former must belong to the set of writers of the last. Also,    *) 
(*this condition holds if the entity belongs to a group wich in turn*) 
(*belongs to the entity's writers.                                   *) 
 
Definition PreDACWrite (eSub : ENTITY) (eObj : ENTITY) : Prop :=
  match fcap (cap s) eSub with
  | Some x => set_In eObj (CanWriteEntities x)
  | None => False
  end. 
 
 
(*This predicate asserts that for a entity to read or write an      *) 
(*entity, the entity's security class must be dominated by the       *) 
(*entity's security class.                                          *) 
 
Definition PreMAC (eSub : ENTITY) (eObj : ENTITY) : Prop :=
  match fESC (entitySC s) eObj, fESC (entitySC s) eSub with
  | None, _ => False
  | _, None => False
  | Some a, Some b => le_sc a b
  end. 
 
 
(*This predicate asserts that if a user is an active writer of any   *) 
(*entity b, then the security class of b must dominates the security *) 
(*class of o. This predicate is used to preserve the *-property*) 
 
Definition PreStarPropRead (eSub : ENTITY) (eObj : ENTITY) : Prop :=
  forall b : ENTITY,
  match fsecmat (secmat s) eSub, fESC (entitySC s) eObj, fESC (entitySC s) b with
  | None, _, _ => False
  | _, None, _ => False
  | _, _, None => False
  | Some x, Some y, Some z => (set_In eObj (EntReadingList x) /\ set_In b (EntWritingList x)) -> le_sc y z
  end. 
 

(*This predicate asserts that if a user is an active reader of any   *)
(*entity b, then the security class of b must be dominated by the    *)
(*security class of o. This predicate is used to preserve the        *)
(**-property.                                                        *)

Definition PreStarPropWrite (eSub : ENTITY) (eObj : ENTITY) : Prop :=
  forall b : ENTITY,
  match fsecmat (secmat s) eSub, fESC (entitySC s) eObj, fESC (entitySC s) b with
  | None, _, _ => False
  | _, None, _ => False
  | _, _, None => False
  | Some x, Some y, Some z => (set_In eObj (EntWritingList x) /\ set_In b (EntReadingList x)) -> le_sc z y
  end. 
 
Definition InSystem (e : ENTITY) : Prop :=
  set_In e (DOM ENTeq_dec (entitycontent s)). 
 
End Preconditions. 
 
Hint Unfold PreDACRead PreDACWrite PreMAC PreStarPropRead PreStarPropWrite InSystem. 
 