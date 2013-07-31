Require Export DACandMAC. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section Read. 
 
Variable s : SFSstate. 
 
(*********************************************************************) 
(*                             read                                  *) 
(*********************************************************************) 
 
(*This operation outputs the first n BYTEs stored in a given file.   *)  
 
Inductive read (eSub : ENTITY) (eObj : ENTITY) (n : nat) :
SFSstate -> Exc ENTCONT -> Prop :=
    ReadOK :
    match fsecmat (secmat s) eSub with
      | None => False
      | Some y => set_In eObj (EntReadingList y)
      end ->
      read eSub eObj n s
        match fsecmat (secmat s) eSub, fentities (entitycontent s) eObj with
        | None, _ => None (A:=ENTCONT)
        | _, None => None (A:=ENTCONT)
        | Some y, Some z => Some (take n z)
        end. 
 
End Read.