# gc

meeting notes 25/3: <br/>
design decisions:

- regions identified with regionId, or implicitly with bridge object id?
  - a separate regionId allows for arbitrary switching of the bridge object without massive changes to the model every time it happens
  - however, this doesnt reflect the reggion code as well as it doesnt reflect that when a reference is to a region, it is to a bridge object and if the bridge object changes then so should the reference (but maybe it doesn't matter since the only way to access the object is to enter it anyway, so we always arrive at the bridge object one way or another)
- heap is a set of regions with objects, or a set of objects with region info?
  - a set of regions better reflects the actual runtime of reggio, and it's easier to see
- does a stack frame include temporary objects?
  - yes, it allows for easier bookkeeping, as we don't need to create new objects in a region everytime we are in an execution frame only to remove them after because they are temporary
- separate open/closed/frozen heaps?
  - no, labelling them is fine, and it allows for easier bookkeeping in proofs

assuming that we have 1 combined heap: <br/>
```
Store := (Map VarName ObjectId)

v1:
    Heap := Map RegionId (Region x Status)
    Region := (BridgeObjectId x Map ObjectId (Map VarName ObjectId))
    Status := Open | Closed | Frozen
    // changing the bridge object involves changing the region
// SD
// Can we write this using the infix notattion
//  Heap :=  RegionId --> (Region x Status)
//  Region := (BridgeObjectId x   ObjectId --> (FldName --> ObjectId))


v2:
    Heap := Map ObjectId (BridgeObjectId x (Map VarName ObjectId))
    // the objects implicitly hold info about the regions
    // SD
    // Doing gc in a region will feel like a "global" operation on the whole heap, rather than like
    // replacing a region bu a gc-ed version of same region

v3: Heap := (Map ObjectId (RegionId x (Map VarName ObjectId))) x (Map RegionId (BridgeObjectId x Status))
    Status := Open | Closed | Frozen

v4: Region := (BridgeObjectId x (Map VarName ObjectId) x Powerset(Region))
    Heap := Map RegionId Region

v4.1: Region := (BridgeObjectId x (Map VarName ObjectId) x List RegionId)
      Heap := Map RegionId Region
```
thoughts: <br/>
v1 is closer to the paper in terms of definitions
v2 is a very different view, regions are more implicity so there may be more work when it comes to proofs
v3 is similar to v2, but simplifies the case where we change the bridge object
v4 shows clearly the tree structure of the regions, traversing the regions may be more/less work, creating regions aren't a concern because creating a region is inherently putting it under another region as we are always "in" a region at execution

ive made the decision to separate regionIds from bridgeObjectIds allowing for more flexibility every time the bridge object is changed (i hope)

is the stack always nonempty?
there is always a base, "global" region that we are in, so yes? in that case we wouldn't have to pass around `stack_nonempty` all the time, and have it as an invariant?
for exit we would then need that stack.length > 1 so that we stay inside the invariant

regionIds are allocated based on the first bridge object's id:
making a region involves creating an object, assigning it to a region, then making said object the bridge object of the region, so the regionId can be the same as the that object's id. once we change the bridge object, we can keep the region id, and since object ids are globally unique, by proxy regionIds are too.

correction:
// SD creation, rather than correction?
get a fresh object id first
create the region with regionId = fresh_objectId
create a new object within the region
assign the var to the region

// SD I think we need to have a list of the operations we want to model.
// For example
// region creation
// region open / close
// .... Hiang, complete this!
// gc - high level view thereof (calc reachable, free list, collect...)
// concurrent mutation -- does async/sync matter?
// can gc be concurrent with mutation?
// can it be acyc/sunc?

model
---
make region
make objects local/region
change bridge object

traversing through the regions/references
read/write
access - legality check on the reference (the way we specify the path will determine how we check it)
read - return the reference
write - changes the reference

gc?


---
function call/return

if conc execution
then mulitple stacks

parametric based on async/sync

sync - lock and wait

async in verona
- natural - message sending is in memory
- locks are artificial
- locks are expensive - lock memory for atomicity

data-race freedom
mutation conc w/ gc
multiple active regions in 1 thread
model gc in a diff region to an active region

guarantee that no 2 threads are in the same region
spawn

purpose of file
what does each function do
separate proofs from construction

meeting notes 27/3:

file structure:
Config.lean
Mutation.lean
GC.lean
Theorems.lean


thoughts on read/write/access:
read:
we model x.f.y.z... as a list of var names
return none for not found
return some objectid for found

treat the list of varnames as a stack
at each stage, have a current object and varname
lookup the varname and pop varname off the list
if varname not found in object, return none
if varname found and list is empty, return objectid
if varname found and list not empty, find the object with the objectid and recurse

how about references to frozen heaps?
how about references down the stack?

what reads are legal? what reads are illegal?
legal:
inside the current active region(s)
inside suspended regions
reads down the stack
through frozen regions

how do we model a read down the stack?
current impl:
the first call to read' contains the references of all frames in the stack, so the first call to read' will allow us to read from a stack variable which is not in the current frame
what if that then refers to another variable in down the stack?

e.g. we have the stack of frames 1,2,3, current stack is 1, x in 1 refers to an object in 2, the object in 2 then refers to an object in 3?

current impl won't work then, since only the first call to read' is considered

what if we maintain another stack in read, which reflects what frame we are at when tracking a reference? there is no way an object can refer to other objects up the stack right? given the example, is there a mutation possible that mutates an object in frame 2 to refer to an object in frame 1? no, because the objects in frame 2 and 3 are currently suspended, so no mutation is possible

meeting notes 1/4:
assignments to an object's field are valid if they are in the same region,
or the object is from a temporary

getBridgeObject (region)

exec : valid cfg -> valid cfg

source language

x := y.f
x.f := y

x := y === z.f := y, x := z.f
x.a := y.b === z := y.b, x.a := z

swap (x, y.f)
swap (x, y) === swap (x, z.f), swap (y, z.f), swap (x, z.f)
swap (x.a, y.b) === swap (z, x.a), swap (z, y.b), swap (z, x.a)

enter x
exit
makeLocalObj
makeObjRegion
makeRegion

method call/functions?

enter a b c, then enter a.d?

lean quicker pls !!!

diagrams for each invariant
explain what they mean in maths and words

gc invariant for validconfig

---

should a frame have its index stay the same when frames are added? or should the latest frame always have index 0?

i think the latest frame should have the highest index (e.g. we append to the list)

we have the following
all RegionIds in the stack are in the heap and have status Open
all RegionIds in the stack are unique
all ObjectIds in the stack and heap are unique
external references to a RegionId is at most 1
no external references to objects
no references from the heap to the stack
objects belong in a single region
  since all objectIds are unique, no objectId can ever appear in 2 different regions/stack, so this is free
  but maybe we want to state it explicitly?
no path from an earlier frame to a later frame
no path from an earlier frame to a region in a later frame
operations:

varAsgn
fieldAsgn
swap
enterVar
exit
makeLocalObj
makeRegionObj
makeRegion

varAsgn (var : VarName) (path : Path) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
if path doesnt resolve return none

fieldAsgn (path : Path) (var : Name) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if path doesnt resolve return none
if stack empty return none
if var not in stack return none
location of ref in var must be same as region of path

swap (var : VarName) (path : Path) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
if var not in stack return none
if path doesnt resolve return none
legality of swap?

enterVar (var : varName) (bridgeVar : varName) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
if var is not a RegionId return none
if regionId from var not found in heap return none
create new frame with bridgeVar, empty ObjMap and VarMap
change regionId status to be open

exit (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
if stack.regionId not found in heap return none (should never happen bc of inv)
remove frame
change regionId status to be closed

makeLocalObj (var : VarName) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
create obj, put reference to obj in var in stack frame

makeRegionObj (var : VarName) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
create obj in the region put reference to obj in var in stack frame

makeRegion (var : VarName) (cfg : RuntimeConfiguration) : Option RuntimeConfiguration
if stack empty return none
create region with status closed, put reference to region in var in stack frame
regionid is objectid of bridge object in region

thoughts on:
- no path from earlier frame to later frame
since there are no refs from the heap to the stack, the only way a frame can ref a later frame is through referencing the stack vars. then, no ref from earlier frame to later frame is enough to hold this.
- no path from earlier frame to region of later frame
assume no ref from earlier frame to region of later frame
from above, earlier frame can only go into region
can the region of the earlier frame go to the region of the later frame?
no because objects have no external references

what do we do about hiding?
we don't hide, the mutation algorithms prevent duplicate entering

20/4 meeting:
pattern matching on ++ e.g. s1 ++ [f1] ++ s2

frames within the region? (check the paper)

todo:
reachability/gc diagrams
underlying language work
brainstorm

i added annotations to semantics
i chose to change Path from List VarName to VarName x ListVarName to respect the fact that a path is always nonempty

1/5/26

todo:
split heap and stack invariants
come up with gc invariants

ValidConfig cfg ->
exit cfg = some cfg' ->
gc invariant

gc invariant has the shape of gc(c, c'), as it describes an invariant between configs, not within a config

consider gc invariants for different gc schemes

richard jones

report:

informal discussion of the requirements of the heap and the stack
explain my model
why it is good with respect to the original reggio
how it differs from the model proposed

define equivalent configurations
bisimilar configurations

bijection between addresses
this will be useful for defining garbage collection schemes:
cfg1 -> cfg2 ^ cfg1 ~ cfg1' ^ cfg1' -> cfg2' -> cfg2 ~ cfg2'
cfg1' represents a garbage collected config, cfg1 is ungarbage collected

we don't have to physically garbage collect, it is enough to mark objects/regions as alive or dead

gc can just mark dead objects, doesnt have to remove -> would help with making new object case

plan + report in next 2 weeks
report by weds

for next meeting
refer to the files in the model
report with all changes
diagrams included for all invariant
discussion of alternatives considered

start on the gc model (?)

gc scheme based on invariant
gc scheme not based on invariant

show they give equivalent output

but our current definition of equivalence is a bijection between addresses, which doesnt exactly work if gc is involved or? actually it might be too weak?


