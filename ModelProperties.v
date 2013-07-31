Require Export TransFunc. 
 
Section ModelProperties. 
 
(*This is the defintion of a secure state from the DAC security      *) 
(*policy point of view.                                              *) 
 
Definition DACSecureState (s : SFSstate) : Prop :=
  forall (eSub : ENTITY) (eObj : ENTITY),
  match fsecmat (secmat s) eSub with
  | None => True
  | Some y =>
      (set_In eObj (EntReadingList y) -> PreDACRead s eSub eObj) /\
      (set_In eObj (EntWritingList y) -> PreDACWrite s eSub eObj)
  end. 
 

(*This is the defintion of a secure state from the MAC security      *) 
(*policy point of view. It says that an state is MAC secure if for   *) 
(*each ENTITY accesing an ENTITY, the security class of the former  *) 
(*is dominates the security class of the ENTITY.                     *) 
 
Definition MACSecureState (s : SFSstate) : Prop :=
  forall (eSub : ENTITY) (eObj : ENTITY),
  match fsecmat (secmat s) eSub, fESC (entitySC s) eObj, fESC (entitySC s) eSub with
  | None, _, _ => True
  | _, None, _ => True
  | _, _, None => True
  | Some x, Some y, Some z =>
      set_In eObj (EntReadingList x) \/ set_In eObj (EntWritingList x) -> le_sc y z
  end. 
       
 
(*An state is secure if it's both DAC and MAC secure.                *) 
 
Definition SecureState (s : SFSstate) : Prop :=
  DACSecureState s /\ MACSecureState s. 
 
 
(*This is the definition of the *-property adapted from the          *) 
(*Bell-LaPadula's model. It says that whenever a ENTITY is accesing *) 
(*an ENTITY for reading and, possibly, another ENTITY for writing,   *) 
(*then the security class of any ENTITY that is being open for       *) 
(*reading must be dominated by the security class of any             *) 
(*of those ENTITYs that are already open for writing.                *) 
 
Definition StarProperty (s : SFSstate) : Prop :=
  forall (eSub : ENTITY) (eObj1 eObj2 : ENTITY),
  match
    fsecmat (secmat s) eSub, fESC (entitySC s) eObj2, fESC (entitySC s) eObj1
  with
  | None, _, _ => True
  | _, None, _ => True
  | _, _, None => True
  | Some x, Some y, Some z =>
      set_In eObj1 (EntWritingList x) -> set_In eObj2 (EntReadingList x) -> le_sc y z
  end. 
 
 
(*We also want operations that deal securely with control            *) 
(*attributes, i.e. the owners of an ACL, the security class          *) 
(*associated with ENTITYs and ENTITYs, etc.                         *) 
(*Informally, the policy says that the owner of an ENTITY or a       *) 
(*member of RootGrp are the only allowed to change the DAC           *) 
(*control attributes associated with the ENTITY; that the members    *) 
(*of SecAdmGrp are the ones that can change the MAC control          *) 
(*attributes associated with ENTITYs and ENTITYs; and that RootGrp  *) 
(*must always be owner of all ENTITYs.                               *) 
 
Inductive CapabilityChanged : CapabilityData -> CapabilityData -> Prop :=
  | ER :
      forall (a : CapabilityData) (b c : set ENTITY),
      b <> c ->
      CapabilityChanged
        (capdata b (CanWriteEntities a))
        (capdata c (CanWriteEntities a))
  | EW :
      forall (a : CapabilityData) (b c : set ENTITY),
      b <> c ->
      CapabilityChanged
        (capdata (CanReadEntities a) b)
        (capdata (CanReadEntities a) c).
 
 
Inductive DACCtrlAttrHaveChanged (s t : SFSstate) (e : ENTITY) : Prop :=
  | Capabilities :
      forall y z : CapabilityData,
      fcap (cap s) e = Some y ->
      fcap (cap t) e = Some z ->
      CapabilityChanged y z -> DACCtrlAttrHaveChanged s t e. 
 
 
Inductive SecClassChanged : SecClass -> SecClass -> Prop :=
  | Level :
      forall (a : SecClass) (b c : set CATEGORY),
      b <> c -> SecClassChanged (sclass (level a) b) (sclass (level a) c)
  | Categ :
      forall (a : SecClass) (b c : SECLEV),
      b <> c -> SecClassChanged (sclass b (categs a)) (sclass c (categs a)). 

Inductive MACEntCtrlAttrHaveChanged (s t : SFSstate) (e : ENTITY) : Prop :=
    SCe :
      forall x y : SecClass,
      fESC (entitySC s) e = Some x ->
      fESC (entitySC t) e = Some y ->
      SecClassChanged x y -> MACEntCtrlAttrHaveChanged s t e. 
 
(*对应原来的WFSI3*)
Axiom
  WFSI1 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    DOM ENTeq_dec (cap s) =
    DOM ENTeq_dec (entitycontent s) ->
    TransFunc e s op t ->
    DOM ENTeq_dec (cap t) =
    DOM ENTeq_dec (entitycontent t).
    
Definition FuncPre1 (s : SFSstate) : Prop :=
  DOM ENTeq_dec (cap s) =
  DOM ENTeq_dec (entitycontent s). 

(*对应原来的WFSI4*)
Axiom
  WFSI2 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    DOM ENTeq_dec (cap s) = DOM ENTeq_dec (entitySC s) ->
    TransFunc e s op t -> DOM ENTeq_dec (cap t) = DOM ENTeq_dec (entitySC t). 
 
 
Definition FuncPre2 (s : SFSstate) : Prop :=
  DOM ENTeq_dec (cap s) = DOM ENTeq_dec (entitySC s). 
 
 
(*对应原来的WFSI5*)
Axiom
  WFSI3 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    Included (DOM ENTeq_dec (secmat s)) (DOM ENTeq_dec (cap s)) ->
    TransFunc e s op t ->
    Included (DOM ENTeq_dec (secmat t)) (DOM ENTeq_dec (cap t)).
 
Definition FuncPre3 (s : SFSstate) : Prop :=
  Included (DOM ENTeq_dec (secmat s)) (DOM ENTeq_dec (cap s)). 
 
(*对应原来的WFSI6*)
Axiom
  WFSI4 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    IsPARTFUNC ENTeq_dec (cap s) ->
    TransFunc e s op t -> IsPARTFUNC ENTeq_dec (cap t). 
 
 
Definition FuncPre4 (s : SFSstate) : Prop := IsPARTFUNC ENTeq_dec (cap s). 
 
(*对应原来的WFSI7*) 
Axiom
  WFSI5 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    IsPARTFUNC ENTeq_dec (secmat s) ->
    TransFunc e s op t -> IsPARTFUNC ENTeq_dec (secmat t). 
 
 
Definition FuncPre5 (s : SFSstate) : Prop := IsPARTFUNC ENTeq_dec (secmat s). 
 
(*对应原来的WFSI8*)
Axiom
  WFSI6 :
    forall (s : SFSstate) (op : Operation) (t : SFSstate) (e : ENTITY),
    IsPARTFUNC ENTeq_dec (entitySC s) ->
    TransFunc e s op t -> IsPARTFUNC ENTeq_dec (entitySC t). 
 
 
Definition FuncPre6 (s : SFSstate) : Prop :=
  IsPARTFUNC ENTeq_dec (entitySC s). 
 

End ModelProperties. 
 
Hint Unfold SecureState DACSecureState MACSecureState.

Hint Resolve ER EW Level Categ. 
Hint Resolve WFSI1 WFSI2 WFSI3 WFSI4 WFSI5 WFSI6.