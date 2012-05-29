open Objects
open Path

sig Commit extends Object {
	points : Tree,
	parent : set Commit,
	abs: Path -> Object
}

sig RootCommit extends Commit {}

sig Branch{
	marks: Commit -> State,
	branches: set State,
	head: set State
}

lone sig Master extends Branch{}

fact {
	//no cycles
	no ^parent & iden

	all s:State{
		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s

		//all object from one state descend from one of its commit
		(objects.s - Commit) in (objects.s).points.*(contents.Name)
		
		//referential integrity for the content of a tree
		all t : objects.s & Tree | t.contents.Name in objects.s
		//referential integrity for commits
		all c:objects.s & Commit | c.points in objects.s and c.parent in objects.s
		//referential integrity for marks
		marks.s in branches.s -> one objects.s
	}

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

run{
	some objects.State & Commit
//	some s:State, p:Path | p not in (head.s).(marks.s).abs.Object
} for 3 but 1 State
