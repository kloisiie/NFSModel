Require Export DACandMAC. 
 
Set Strict Implicit.
Unset Implicit Arguments. 
 
Section Write. 
 
Variable s : SFSstate. 
 
 
(*********************************************************************) 
(*                   Some Useful Synonymous                          *) 
(*********************************************************************) 
 
Let t (e : ENTITY) (n : nat) (buf : ENTCONT) : SFSstate :=
  mkSFS (entitySC s) (cap s) (secmat s) (write_entities e n buf). 
 
(*********************************************************************) 
(*                            write                                  *) 
(*********************************************************************) 
 
(*This operation writes the first n BYTEs of buf to the entity       *) 
(*represented by entity e.                                           *) 
 
Inductive write (eSub : ENTITY) (eObj : ENTITY) (n : nat) 
(buf : ENTCONT) : SFSstate -> Prop :=
    WriteOK :
      match fsecmat (secmat s) eSub with
      | None => False
      | Some y => set_In eObj (EntWritingList y)
      end -> write eSub eObj n buf (t eObj n buf). 
 
End Write. 