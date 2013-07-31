Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section writeIsSecure. 
 
Lemma WritePSS :
 forall (s t : SFSstate) (eSub : ENTITY),
 SecureState s -> TransFunc eSub s Write t -> SecureState t. 
StartPSS. 
inversion H. 
auto. 
 
Qed. 
 
 
Lemma WritePSP :
 forall (s t : SFSstate) (eSub : ENTITY),
 StarProperty s -> TransFunc eSub s Write t -> StarProperty t. 
StartPSP. 
inversion H. 
auto. 
 
Qed. 
 

 
 
End writeIsSecure. 
 
Hint Resolve WritePSS WritePSP. 