open Name
open Objects
open Path

-- This signature will represent the dynamic behaviour of git repository
-- The contents of the repository will be changed along the workflow
sig State {}

-- The representation of git objects, conceptually the belong
-- to a set of states
abstract sig Object {
	objects: set State
}

-- The representation of a file content (called blob on git) 
sig Blob extends Object {}

-- Equivalent to a folder on the filesystem. It's sons
-- can be blobs or other trees, each son is uniquely 
-- identified by a name
sig Tree extends Object {
		contains : Name  -> lone (Tree+Blob)
}

-- Just to aid in specification
fun contents: Tree -> Object -> Name{
	{t:Tree, o:Object, n:Name | t -> n-> o in contains}
}

-- The sharing nature of git, says that trees with the same 
-- content are represented as the same tree. There are no cycles
-- among them. And because git if file oriented, there cannot be
-- trees (folders) with no sons.
-- Note : Probably the two last restrictions can be passed to 
-- the Properties.als, in order to check consistency of git
fact {
		all t,t' : Tree | t.contains = t'.contains implies t=t'
		no ^(contents.Name) & iden 
}

-- The representation of the commit object.
-- Each commit points to a root tree, that represents
-- the root folder of the repository.
-- Each commit has a set of parent commits.
-- The abs (abstraction) relation is used to 
-- identify wich files and folders are represented on commit.
-- The merge relation points to wich commits will be parent of
-- the next merge commit
sig Commit extends Object {
	points : Tree,
	parent : set Commit,
	abs: Path -> Object,
	merge : set State
}

sig RootCommit extends Commit {}

-- The representation of the branch. Each branch
-- points to a specific commit on a given state.
-- A branch exists on a given state, and can be
-- the current branch (head) on a given state.
sig Branch{
	marks: Commit lone -> State,
	branches: set State,
	head: set State
}

lone sig Master extends Branch{}

fact {
	
	-- There can be no cycles on a parent relation of commmits.
	-- This can probably pass to Properties.als file, in order to check for consistency
	no ^parent & iden
	all s:State | lone head.s
	-- Only Commits (not RootCommits) can and must have parents.
	-- All objects represented on a commit can be associated to a path, and the
	-- parent relation among them must be preserved
	-- At least the first property can be passed to Properties.als, in order to
	-- check for consistency
	all c: Commit{
		c not in RootCommit <=> some c.parent
		let objs = c.points.*(contents.Name){
			c.abs in Path some -> lone objs
			(c.abs).(c.points) in Root
			--all p,q: (c.abs).univ | p -> q in pathparent implies q.(c.abs) -> p.(c.abs) -> p.name in contents
			all p : (c.abs).univ | some p.pathparent implies some q : (c.abs).univ | p -> q in pathparent and q.(c.abs) -> p.(c.abs) -> p.name in contents
			all t,o : objs, n : Name | t -> o -> n in contents implies all y : c.abs.t | some x : c.abs.o | x -> y in pathparent and x.name = n
		}
	}
}
