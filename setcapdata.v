Require Export SFSstate. 
 
Section setCapabilitydata. 
 
Variable s : SFSstate. 
 
(*This operator adds or removes a reader from a set of subjects      *)
(*on the rights the user has.                                        *)
 
Definition ChangeEntR (eSub : ENTITY) (x : set ENTITY) 
  (oct : RIGHTS) : set ENTITY :=
  match oct with
  | allowedTo false false => set_remove ENTeq_dec eSub x
  | allowedTo false true => set_remove ENTeq_dec eSub x
  | allowedTo true false => set_add ENTeq_dec eSub x
  | allowedTo true true => set_add ENTeq_dec eSub x
  end. 

(*This operator adds or removes a writer from a set of subjects      *)
(*on the rights the user has.                                        *)  

Definition ChangeEntW (eSub : ENTITY) (x : set ENTITY) 
  (oct : RIGHTS) : set ENTITY :=
  match oct with
  | allowedTo false false => set_remove ENTeq_dec eSub x
  | allowedTo false true => set_add ENTeq_dec eSub x
  | allowedTo true false => set_remove ENTeq_dec eSub x
  | allowedTo true true => set_add ENTeq_dec eSub x
  end. 
 
End setCapabilitydata.