Require Export read. 
Require Export write. 
 
Section TransitionFunction. 
 
(*********************************************************************) 
(*                   The Transition Relation                         *) 
(*********************************************************************) 
 
Inductive TransFunc : ENTITY -> SFSstate -> Operation -> SFSstate -> Prop :=
  | DoRead :
      forall (eSub : ENTITY) (eObj : ENTITY) (n : nat) (out : Exc ENTCONT)
        (s : SFSstate), read s eSub eObj n s out -> TransFunc eSub s Read s
  | DoWrite :
      forall (eSub : ENTITY) (eObj : ENTITY) (n : nat) (buf : ENTCONT)
        (s t : SFSstate), write s eSub eObj n buf t -> TransFunc eSub s Write t. 
 
End TransitionFunction. 