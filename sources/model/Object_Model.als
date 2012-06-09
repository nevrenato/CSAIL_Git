open Objects
open Path

-- The representation of the commit object.
-- Each commit points to a root tree, that represents
-- the root folder of the repository.
-- Each commit has a set of parent commits.
-- The abs (abstraction) relation is used to 
-- identify wich files and folders are represented on commit.
sig Commit extends Object {
	points : Tree,
	parent : set Commit,
	abs: Path -> Object
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
			all p,q : (c.abs).univ | p -> q in pathparent implies q.(c.abs) -> p.(c.abs) -> p.name in contents
			all t,o : objs, n : Name | t -> o -> n in contents implies all y : c.abs.t | some x : c.abs.o | x -> y in pathparent and x.name = n
		}
	}
}
