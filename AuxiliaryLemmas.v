Require Import ModelProperties.

 (*ENTITY, Property and TransFunc*)
Ltac OpDontChangeStPSS :=
  intros s t Sub SS TF; inversion TF;
   match goal with
   | id:(s = t) |- _ => rewrite <- id; auto
   end.
 
Ltac OpDontChangeStPSP :=
  intros s t Sub SP TF;  (* ENTITY, Property and TransFunc *)
   inversion TF; match goal with
                 | id:(s = t) |- _ => rewrite <- id; auto
                 end. 

Ltac StartPSS := intros s t Sub SS TF; inversion TF. 

Ltac BreakSS :=
  match goal with
  | SS:(SecureState _) |- _ =>
      unfold SecureState in SS; elim SS; intros DAC MAC
  end. 

Ltac StartPSP := intros s t Sub SP TF; inversion TF. 
  
 
Lemma ReadWriteImpRead :
 forall s : SFSstate,
 DACSecureState s ->
 forall (eSub : ENTITY) (eObj : ENTITY),
 match fsecmat (secmat s) eSub with
 | Some y => set_In eObj (EntReadingList y) -> PreDACRead s eSub eObj
 | None => True
 end. 
unfold DACSecureState in |- *. 
intros. 
cut
 match fsecmat (secmat s) eSub with
 | Some y =>
     (set_In eObj (EntReadingList y) -> PreDACRead s eSub eObj) /\
     (set_In eObj (EntWritingList y) -> PreDACWrite s eSub eObj)
 | None => True
 end. 
elim (fsecmat (secmat s) eSub). 
intros. 
elim H0; intros. 
auto. 
 
auto. 
 
apply H. 
 
Qed. 
 
 
Lemma ReadWriteImpWrite :
 forall s : SFSstate,
 DACSecureState s ->
 forall (eSub : ENTITY) (eObj : ENTITY),
 match fsecmat (secmat s) eSub with
 | Some y => set_In eObj (EntWritingList y) -> PreDACWrite s eSub eObj
 | None => True
 end. 
unfold DACSecureState in |- *. 
intros. 
cut
 match fsecmat (secmat s) eSub with
 | Some y =>
     (set_In eObj (EntReadingList y) -> PreDACRead s eSub eObj) /\
     (set_In eObj (EntWritingList y) -> PreDACWrite s eSub eObj)
 | None => True
 end. 
elim (fsecmat (secmat s) eSub). 
intros. 
elim H0; intros. 
auto. 
 
auto. 
 
apply H. 
 
Qed. 
 
 
Lemma TwoImpLeft :
 forall (s : SFSstate) (eObj : ENTITY),
 (forall rw : ReadingWriting,
  set_In rw (ransecmat (secmat s)) ->
  ~ set_In eObj (EntReadingList rw) /\ ~ set_In eObj (EntWritingList rw)) ->
 forall rw : ReadingWriting,
 set_In rw (ransecmat (secmat s)) -> ~ set_In eObj (EntReadingList rw). 
intros. 
cut (~ set_In eObj (EntReadingList rw) /\ ~ set_In eObj (EntWritingList rw)). 
tauto. 
 
auto. 
 
Qed. 
 
 
Lemma TwoImpRight :
 forall (s : SFSstate) (eObj : ENTITY),
 (forall rw : ReadingWriting,
  set_In rw (ransecmat (secmat s)) ->
  ~ set_In eObj (EntReadingList rw) /\ ~ set_In eObj (EntWritingList rw)) ->
 forall rw : ReadingWriting,
 set_In rw (ransecmat (secmat s)) -> ~ set_In eObj (EntWritingList rw). 
intros. 
cut (~ set_In eObj (EntReadingList rw) /\ ~ set_In eObj (EntWritingList rw)). 
tauto. 
 
auto. 
 
Qed. 
 

 
Lemma eq_scIMPLYle_sc : forall a b : SecClass, eq_sc a b -> le_sc a b. 
unfold eq_sc, le_sc in |- *; intros. 
elim H; intros. 
rewrite H0; rewrite H1. 
auto. 
Qed. 
 
 
Lemma NotInDOMIsUndef2 :
 forall (s : SFSstate) (eSub eObj : ENTITY),
 ~ set_In eSub (domsecmat (secmat s)) ->
 eSub = eObj -> None = fsecmat (secmat s) eObj. 
intros. 
symmetry  in |- *. 
rewrite H0 in H. 
unfold fsecmat in |- *; apply NotInDOMIsUndef; auto. 
 
Qed. 
 

Lemma NoDACChange :
 forall (s : SFSstate) (e : ENTITY) (ESC : set (ENTITY * SecClass))
   (ENTITYCONTENT : set (ENTITY * ENTCONT)) (SM : set (ENTITY * ReadingWriting)),
 ~
 DACCtrlAttrHaveChanged s
   (mkSFS ESC (cap s) SM ENTITYCONTENT) e. 
intros. 
intro. 
inversion H; simpl in H1; cut (y = z). 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
Qed. 
 
 
Lemma NoDACChange2 :
 forall (s : SFSstate) (e : ENTITY), ~ DACCtrlAttrHaveChanged s s e. 
intros; intro;
 eapply
  (NoDACChange s e (entitySC s) (entitycontent s) (secmat s)). 
generalize H; elim s; simpl in |- *; auto. 
 
Qed. 
 
 
Lemma NoMACEntChange :
 forall (s : SFSstate) (eObj : ENTITY) (ENTITYCONTENT : set (ENTITY * ENTCONT))
   (CAP : set (ENTITY * CapabilityData)) (ESC : set (ENTITY * SecClass))
   (SM : set (ENTITY * ReadingWriting)),
 ~
 MACEntCtrlAttrHaveChanged s
   (mkSFS (entitySC s) CAP SM ENTITYCONTENT) eObj. 
intros; intro. 
inversion H; simpl in H1. 
cut (x = y). 
intro EQ; rewrite EQ in H2; inversion H2; auto. 
 
rewrite H0 in H1; injection H1; auto. 
 
Qed. 
 
 
Lemma NoMACEntChange2 :
 forall (s : SFSstate) (eObj : ENTITY), ~ MACEntCtrlAttrHaveChanged s s eObj. 
intros; intro;
 eapply
  (NoMACEntChange s eObj (entitycontent s) (cap s) 
     (entitySC s) (secmat s)). 
generalize H; elim s; simpl in |- *; auto. 
 
Qed. 
 
 
 
Lemma eq_scSym : forall a b : SecClass, eq_sc a b -> eq_sc b a. 
unfold eq_sc in |- *; intros. 
elim H; intros. 
rewrite H0; rewrite H1. 
auto. 
Qed. 
 

Lemma Aux1 :
 forall y : SecClass, ~ (Some y = None <-> None = None :>option SecClass). 
intro; unfold iff in |- *; intro H; elim H; intros. 
absurd (Some y = None); auto. 
intro D; discriminate D. 
 
Qed. 
 

 
Hint Resolve eq_scIMPLYle_sc eq_scSym TwoImpLeft
  TwoImpRight NoMACEntChange NoDACChange NoMACEntChange Aux1
  NotInDOMIsUndef2 NoMACEntChange2 NoDACChange2 NoMACEntChange2. 
