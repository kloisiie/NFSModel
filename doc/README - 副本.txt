This file briefly describes the pourpose of this model and the contents of each module.

We specify and formally verifiy security properties of an extension of a
UNIX filesystem. The extensions include MLS controls, separated MAC and DAC
administration, efective administrative groups, ACLs, and generalized owners
for files and directories. The security properties we verify are: a complete
formalization of the Bell-LaPadula security model, the standard DAC
properties based on ACLs, and those for security attributes.

The model takes the form of a state machine. The state has been defined in module SFSstate.v and the operations in several modules each with the name of a UNIX file system call (e.g. open, chmod, etc.). Some new system calls have been specified due to the introduction of new security attributes.

The reader should start reading the model by the module named SFSstate.v, which contains an informal interpretation of the basic (formal) terms, which, in turn, allows he or she to underestand the remaining formalization.

After reading the aformetioned module we recomend you to read module DACandMAC.v which states some commonly used preconditions. Then, the reader could follow with modules named whith file system operation names (i.e. those not ending with "IsSecure").   

Before reading files with names of the form *IsSecure, we suggets to read module ModelProperties.v, which contains the formalization of the properties we proved. Files *IsSecure contain proof scripts of the corresponding operation. For example, file openIsSecure stores the proof scripts about properies verified by operation open.

Finally, module ModelLemmas.v states the main lemma of the verification, i.e. basic security theorem.

Readers interested in this work could download from lifia.info.unlp.edu.ar the MSc author's thesis "Formal Verification of an Extension of a Secure, Compatible UNIX File System". Also in that URL, you will find documentation about LiSex (Lifia Secure Linux) which is an implementation of this model. New versions of LiSex will implement improvments of the present module.


Maximiliano Cristi?Universidad Nacional de Rosario y Lifia (UNLP)
Argentina


MODULE CONTENTS 
basis:
DACandMAC: contains preconditions used un many operations' specification
SFSstate: system state definition and other basic definitions.

Definations:
TransFunc: definition of the transition relation
InitialState: defines a possible initial state of the system
ListFunctions: some definitions and lemmas about lists and sets
ModelProperties: formalization of the properties the system (should) verify

spec:
chmod: specification of chmod
chobjsc: specification of chobjsc
chown: specification of chown
chsubsc: specification of chsubsc
close: specification of close
create: specification of create
aclstat: specification of aclstat
addUsrGrpToAcl: specification of addUsrGrpToAcl
delUsrGrpFromAcl: specification of delUsrGrpFromAcl
mkdir: specification of mkdir
open: specification of open
oscstat: specification of oscstat
owner_close: specification of owner_close
readdir: specification of readdir
read: specification of read
rmdir: specification of rmdir
sscstat: specification of sscstat
stat: specification of stat
unlink: specification of unlink
write: specification of write


others:
setACLdata: some auxiliary definitions used in chmod, chown, and others
ListSet: identical to ListSet.v of the standard library, except for the definition of set_remove.

