Require Import ModelProperties. 
Require Import AuxiliaryLemmas. 
 
Section readIsSecure. 
 
Lemma ReadPSS :
 forall (s t : SFSstate) (e : ENTITY),
 SecureState s -> TransFunc e s Read t -> SecureState t. 
OpDontChangeStPSS. 
Qed. 
 
 
Lemma ReadPSP :
 forall (s t : SFSstate) (e : ENTITY),
 StarProperty s -> TransFunc e s Read t -> StarProperty t. 
OpDontChangeStPSP. 
Qed. 
 
End readIsSecure. 
 
Hint Resolve ReadPSS ReadPSP. 
 