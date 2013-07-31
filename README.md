NFSModel
========

This file briefly describes the pourpose of this model and the contents of each module.

The extensions include MLS controls, separated MAC and DAC administration, efective administrative groups, ACLs, and generalized owners for files and directories. The security properties we verify are: a complete formalization of the Bell-LaPadula security model, the standard DAC properties based on ACLs, and those for security attributes.

The reader should start reading the model by the module named SFSstate.v, which contains an informal interpretation of the basic (formal) terms, which, in turn, allows he or she to underestand the remaining formalization.

After reading the aformetioned module we recomend you to read module DACandMAC.v which states some commonly used preconditions. Then, the reader could follow with modules named whith file system operation names (i.e. those not ending with "IsSecure").   

Before reading files with names of the form *IsSecure, we suggets to read module ModelProperties.v, which contains the formalization of the properties we proved. Files *IsSecure contain proof scripts of the corresponding operation. For example, file openIsSecure stores the proof scripts about properies verified by operation open.

Finally, module ModelLemmas.v states the main lemma of the verification, i.e. basic security theorem.


MODULE CONTENTS

Basic definations:
ListSet: identical to ListSet.v of the standard library, except for the definition of set_remove.
ListFunctions: some definitions and lemmas about lists and sets
SFSstate: system state definition and other basic definitions.
DACandMAC: contains preconditions used un many operations' specification
setCapabilitydata: some auxiliary definitions used in operations

operations:
create: specification of create
open: specification of open
read: specification of read
write: specification of write

Basis of proof:
TransFunc: definition of the transition relation
ModelProperties: formalization of the properties the system (should) verify
AuxiliaryLemmas: auxiliary lemmas for many proof scripts

Proof of operations:
readIsSecure: proof scripts of read
writeIsSecure: proof scripts of write

Proof of secure states:
InitialState: defines a possible initial state of the system
ModelLemmas: contains two lemmas about the system as a whole
