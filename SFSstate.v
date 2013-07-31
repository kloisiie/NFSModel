Require Export ListFunctions. 
 
Set Implicit Arguments.
Unset Strict Implicit. 


Definition SECLEV := nat. 
Parameter CATEGORY : Set. 

Record SecClass : Set := sclass {level : SECLEV; categs : set CATEGORY}. 
 
Definition eq_sc (a b : SecClass) : Prop :=
  level a = level b /\ categs a = categs b. 
 
Definition le_sc (a b : SecClass) : Prop :=
  level a <= level b /\ Included (categs a) (categs b). 
 
Hint Unfold eq_sc le_sc. 
 
 
(*********************************************************************) 
(*                  Security Policy Entities                         *) 
(*********************************************************************) 
 
Parameter ENTITY : Set. 

Axiom ENTeq_dec : forall x y : ENTITY, {x = y} + {x <> y}. 

Hint Resolve ENTeq_dec. 

Parameter BYTE : Set.

Definition ENTCONT := list BYTE.

Axiom BYTEeq_dec : forall x y : BYTE, {x = y} + {x <> y}.

Lemma ENTCONTeq_dec : forall x y : ENTCONT, {x = y} + {x <> y}. 
unfold ENTCONT in |- *; intros; apply Listeq_dec.
apply BYTEeq_dec.  
Qed. 
 
Hint Resolve ENTCONTeq_dec.

 
(*********************************************************************) 
(*                  Security Policy ENTITYs                          *) 
(*********************************************************************) 
 
 
Record RIGHTS : Set := allowedTo {read_right : bool; write_right : bool}. 

Record CapabilityData : Set := capdata
  {CanReadEntities : set ENTITY;
   CanWriteEntities : set ENTITY}. 
 
Record ReadingWriting : Set := mkRW
  {EntReadingList : set ENTITY; EntWritingList : set ENTITY}. 
 
Axiom RWeq_dec : forall x1 x2 : ReadingWriting, {x1 = x2} + {x1 <> x2}. 
 
(*********************************************************************) 
(*                     Secured System                            *) 
(*********************************************************************) 


Record SFSstate : Set := mkSFS
  {
   entitySC : set (ENTITY * SecClass);
   cap : set (ENTITY * CapabilityData);
   secmat : set (ENTITY * ReadingWriting);
   entitycontent : set (ENTITY * ENTCONT)}. 


Axiom ESCeq_dec : forall x1 x2 : ENTITY * SecClass, {x1 = x2} + {x1 <> x2}. 
Axiom
  CAPeq_dec :
    forall x1 x2 : ENTITY * CapabilityData, {x1 = x2} + {x1 <> x2}. 
Axiom
  SECMATeq_dec :
    forall x1 x2 : ENTITY * ReadingWriting, {x1 = x2} + {x1 <> x2}. 

 
Hint Resolve ESCeq_dec CAPeq_dec SECMATeq_dec RWeq_dec. 
 
 

(*In this section we implement finite partial functions (FPF) with type set defined at module ListSet.v.*)
 
Section PartialFunctions.

Variable X Y : Set. 
 
Hypothesis Xeq_dec : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}. 
Hypothesis Yeq_dec : forall x1 x2 : Y, {x1 = x2} + {x1 <> x2}. 
Hypothesis XYeq_dec : forall x1 x2 : X * Y, {x1 = x2} + {x1 <> x2}. 

(*Domain of a FPF*)
Fixpoint DOM (f : set (X * Y)) : set X :=
  match f with
  | nil => nil (A:=X)
  | (x, y) :: g => set_add Xeq_dec x (DOM g)
  end. 

(*Range of a FPF*)
Fixpoint RAN (f : set (X * Y)) : set Y :=
  match f with
  | nil => nil (A:=Y)
  | (x, y) :: g => set_add Yeq_dec y (RAN g)
  end. 

(*Application of a FPF*)
Fixpoint PARTFUNC (f : set (X * Y)) : X -> Exc Y :=
  fun x : X =>
  match f with
  | nil => None (A:=Y)
  | (x1, y) :: g =>
      match Xeq_dec x x1 with
      | left _ => Some y
      | right _ => PARTFUNC g x
      end
  end. 
 
(*Test to decide whether a set of pairs is a FPF or not*)
Fixpoint IsPARTFUNC (f : set (X * Y)) : Prop :=
  match f with
  | nil => True
  | a :: l =>
      match set_In_dec Xeq_dec (fst a) (DOM l) with
      | left _ => False
      | right _ => IsPARTFUNC l
      end
  end. 
 
(*Some usefull lemmas about our implementation of FPF*)

Lemma AddEq :
 forall (a b : X) (y : Y) (f : set (X * Y)),
 a <> b -> PARTFUNC f a = PARTFUNC (set_add XYeq_dec (b, y) f) a. 
intros. 
induction  f as [| a0 f Hrecf]. 
simpl in |- *. 
elim (Xeq_dec a b). 
intros. 
cut False. 
intro. 
elim H0. 
 
unfold not in H; apply H. 
auto. 
 
auto. 
 
simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F. 
elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
intros. 
auto. 
 
Qed. 
 
 
Lemma AddEq1 :
 forall (x : X) (y : Y) (f : set (X * Y)),
 ~ set_In x (DOM f) -> value y = PARTFUNC (set_add XYeq_dec (x, y) f) x. 
simple induction f. 
simpl in |- *. 
elim (Xeq_dec x x); auto. 
intro; absurd (x = x); auto. 
 
simpl in |- *. 
intros until l. 
elim a. 
intros until b. 
elim (XYeq_dec (x, y) (a0, b)). 
simpl in |- *. 
elim (Xeq_dec x a0). 
intros. 
injection a2; intros. 
rewrite H1; auto. 
 
intros. 
injection a1; intros; absurd (x = a0); auto. 
 
simpl in |- *. 
elim (Xeq_dec x a0). 
intros. 
rewrite a1 in H0. 
cut False. 
tauto. 
 
apply H0. 
apply set_add_intro2; auto. 
 
intros. 
apply H. 
intro; apply H0; apply set_add_intro1; auto. 
 
Qed. 
 
 
Lemma RemEq :
 forall (a b : X) (y : Y) (f : set (X * Y)),
 a <> b -> PARTFUNC f a = PARTFUNC (set_remove XYeq_dec (b, y) f) a. 
intros. 
induction  f as [| a0 f Hrecf].
auto.

simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F. 
elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F. 
elim F. 
 
auto. 
 
intros. 
auto. 
 
Qed. 
 
 
Lemma AddRemEq :
 forall (a b : X) (y z : Y) (f : set (X * Y)),
 a <> b ->
 PARTFUNC f a =
 PARTFUNC (set_add XYeq_dec (b, z) (set_remove XYeq_dec (b, y) f)) a. 
intros. 
induction  f as [| a0 f Hrecf]. 
simpl in |- *. 
elim (Xeq_dec a b). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
auto. 
 
simpl in |- *. 
elim a0. 
intros. 
elim (Xeq_dec a a1). 
elim (XYeq_dec (b, y) (a1, b0)). 
intros. 
cut False. 
intro F; elim F. 
 
unfold not in H; apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (XYeq_dec (b, z) (a1, b0)). 
intros. 
cut False. 
intro F; elim F. 
 
unfold not in H. 
apply H. 
rewrite a3. 
injection a2. 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
auto. 
 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
elim (XYeq_dec (b, y) (a1, b0)). 
auto. 
 
intros. 
simpl in |- *. 
elim (XYeq_dec (b, z) (a1, b0)). 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
intros. 
apply RemEq. 
auto. 
 
auto. 
 
simpl in |- *. 
elim (Xeq_dec a a1). 
intros. 
cut False. 
intro F; elim F. 
 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma NotInDOMIsUndef :
 forall (o : X) (f : set (X * Y)), ~ set_In o (DOM f) -> PARTFUNC f o = None. 
intros. 
induction  f as [| a f Hrecf]. 
simpl in |- *. 
auto. 
 
generalize H. 
simpl in |- *. 
elim a. 
intro; intro. 
elim (Xeq_dec o a0). 
intro. 
rewrite a1. 
intro. 
cut False. 
intro F; elim F. 
 
unfold not in H0. 
apply H0. 
apply set_add_intro2. 
auto. 
 
intros. 
apply Hrecf. 
unfold not in H0; unfold not in |- *. 
intro; apply H0. 
apply set_add_intro1. 
auto. 
 
Qed. 
 
Hint Resolve NotInDOMIsUndef.    
 
Lemma InDOMIsNotUndef :
 forall (o : X) (f : set (X * Y)), set_In o (DOM f) -> PARTFUNC f o <> None. 
simple induction f. 
auto. 
 
simpl in |- *. 
intro. 
elim a. 
intro. 
elim (Xeq_dec o a0). 
intros; intro H3; discriminate H3. 
 
intros; apply H. 
 
eauto. 
 
Qed. 
 
 
Lemma InDOMWhenAdd :
 forall (x : X) (y : Y) (f : set (X * Y)),
 set_In x (DOM (set_add XYeq_dec (x, y) f)). 
intros; induction  f as [| a f Hrecf]. 
simpl in |- *. 
left; auto. 
 
simpl in |- *. 
elim (XYeq_dec (x, y) a). 
simpl in |- *. 
elim a. 
intros. 
injection a1; intros. 
apply set_add_intro2; auto. 
 
simpl in |- *. 
elim a. 
intros. 
apply set_add_intro1; auto. 
 
Qed. 
 
 
Lemma DOMFuncRel :
 forall (a : X * Y) (f : set (X * Y)),
 ~ set_In (fst a) (DOM f) -> f = set_remove XYeq_dec a f. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intro; elim a0. 
intros until b; elim (XYeq_dec a (a1, b)). 
elim a. 
intros. 
injection a3; intros. 
simpl in H0; rewrite H2 in H0. 
cut False. 
tauto. 
 
apply H0; apply set_add_intro2; auto. 
 
elim a. 
simpl in |- *. 
intros. 
cut (l = set_remove XYeq_dec (a2, b0) l). 
intro. 
rewrite <- H1; auto. 
 
apply H. 
intro; apply H0; apply set_add_intro; auto. 
 
Qed. 
 
Hint Resolve DOMFuncRel. 
 
 
Lemma DOMFuncRel2 :
 forall (z : X * Y) (f : set (X * Y)), set_In z f -> set_In (fst z) (DOM f). 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intro; elim a. 
elim z. 
simpl in |- *. 
intros. 
elim H0; intro. 
injection H1; intros. 
apply set_add_intro; auto. 
 
cut (set_In a0 (DOM l)). 
intro; apply set_add_intro1; auto. 
 
auto. 
 
Qed. 
 
Hint Resolve DOMFuncRel2. 
 
 
Lemma DOMFuncRel3 :
 forall (x : X) (y : Y) (f : set (X * Y)),
 IsPARTFUNC f ->
 set_In (x, y) f -> ~ set_In x (DOM (set_remove XYeq_dec (x, y) f)). 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l; elim (set_In_dec Xeq_dec (fst a) (DOM l));
 elim (XYeq_dec (x, y) a). 
tauto. 
 
tauto. 
 
intros; cut (l = set_remove XYeq_dec (x, y) l). 
intro H2; rewrite <- H2; replace x with (fst a); auto. 
rewrite <- a0; auto. 
 
rewrite a0; auto. 
 
simpl in |- *. 
elim a. 
simpl in |- *. 
intros. 
elim H1; intro. 
absurd ((a0, b) = (x, y)); auto. 
 
elim (Xeq_dec x a0); intro. 
rewrite <- a1 in b1. 
intro; apply b1; replace x with (fst (x, y)); auto. 
 
cut (~ set_In x (DOM (set_remove XYeq_dec (x, y) l))). 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma DOMFuncRel4 :
 forall (x : X) (f : set (X * Y)),
 match PARTFUNC f x with
 | Some a => set_In (x, a) f
 | None => ~ set_In x (DOM f)
 end. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l; elim a. 
intros until b; elim (Xeq_dec x a0). 
elim (PARTFUNC l x). 
intros y2 H; left; rewrite H; auto. 
 
intros H H1; left; rewrite H; auto. 
 
elim (PARTFUNC l x). 
auto. 
 
auto. 
 
Qed. 
 
 
Lemma UndefWhenRem :
 forall (x : X) (y : Y) (f : set (X * Y)),
 IsPARTFUNC f ->
 set_In (x, y) f -> PARTFUNC (set_remove XYeq_dec (x, y) f) x = None. 
simple induction f. 
simpl in |- *; auto. 
 
simpl in |- *. 
intros until l. 
elim (set_In_dec Xeq_dec (fst a) (DOM l)); elim (XYeq_dec (x, y) a). 
tauto. 
 
tauto. 
 
intros. 
replace (set_remove XYeq_dec (x, y) l) with l. 
rewrite <- a0 in b. 
simpl in b. 
auto. 
 
rewrite <- a0 in b. 
auto. 
 
simpl in |- *. 
elim a. 
intros. 
elim H1; intro. 
cut False. 
tauto. 
 
apply b0; symmetry  in |- *; auto. 
 
elim (Xeq_dec x a0). 
intro. 
simpl in b1. 
rewrite <- a1 in b1. 
absurd (set_In x (DOM l)). 
auto. 
 
replace x with (fst (x, y)); auto. 
 
auto. 
 
Qed. 
 
End PartialFunctions. 
 
Hint Resolve AddEq RemEq AddRemEq NotInDOMIsUndef InDOMIsNotUndef
  InDOMWhenAdd UndefWhenRem AddEq1 DOMFuncRel3. 
 
 
 
(*Shorthands for domains and partial functions defined for each of the state's*) 
(*components.   *)
Definition dome (f : set (ENTITY * ENTCONT)) := DOM ENTeq_dec f. 
 
Definition fentities (f : set (ENTITY * ENTCONT)) : ENTITY -> Exc ENTCONT :=
  PARTFUNC ENTeq_dec f. 
                                                      
Definition domcap (f : set (ENTITY * CapabilityData)) := DOM ENTeq_dec f. 
 
Definition fcap (f : set (ENTITY * CapabilityData)) :
  ENTITY -> Exc CapabilityData := PARTFUNC ENTeq_dec f. 
 
Definition domsecmat (f : set (ENTITY * ReadingWriting)) := DOM ENTeq_dec f. 
 
Definition ransecmat (f : set (ENTITY * ReadingWriting)) := RAN RWeq_dec f. 
 
Definition fsecmat (f : set (ENTITY * ReadingWriting)) :
  ENTITY -> Exc ReadingWriting := PARTFUNC ENTeq_dec f. 
 
Definition domESC (f : set (ENTITY * SecClass)) := DOM ENTeq_dec f. 
 
Definition fESC (f : set (ENTITY * SecClass)) : ENTITY -> Exc SecClass :=
  PARTFUNC ENTeq_dec f. 
                 
 
(*Filesystem update functions.                                       *) 
Parameter write_entities : ENTITY -> nat -> ENTCONT -> set (ENTITY * ENTCONT). 
 
 
(*
READ: pure read access
WRITE: pure write access
*)
 
Inductive MODE : Set :=
  | READ : MODE
  | WRITE : MODE. 
 
 
(*The names of the system operations.                                *) 
 
Inductive Operation : Set :=
  | Read : Operation
  | Write : Operation.