Require Export SFSstate. 
Set Implicit Arguments.
Unset Strict Implicit. 
 
Section InitialState. 
 
(*********************************************************************) 
(*                  Initial State of the System                      *) 
(*********************************************************************) 
 
Parameter SysEntitySC : set (ENTITY * SecClass). 
 
Axiom SysEntitySCIsPARTFUNC : IsPARTFUNC ENTeq_dec SysEntitySC.   
 
 
(*In the initial state the parameters previously defined are some of *) 
(*its fields, the others being empty sets (of apropriate types) which*) 
(*in turn are (trivially) partial functions.                         *) 
 
Definition InitState : SFSstate :=
  mkSFS SysEntitySC (empty_set (ENTITY * CapabilityData))
    (empty_set (ENTITY * ReadingWriting))
    (empty_set (ENTITY * ENTCONT)). 
  
End InitialState. 
 
Hint Resolve SysEntitySCIsPARTFUNC.