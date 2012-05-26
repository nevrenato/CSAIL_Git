open Objects
open Path

sig Commit extends Object {
	points : one Tree,
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
	no ^parent & iden //check3

	all s:State{
		all c:objects.s & Commit | c.points in objects.s and c.parent in objects.s//check4 and check5

		// RootCommits doesn't have a parent
		no RootCommit.parent
		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s

		marks.s in branches.s -> one objects.s
		//if a path is not a parent then it is a file
		Path in File.path + Path.pathparent
	}

	all c: Commit{
		c not in RootCommit <=> some c.parent
		let objs = c.points.*(contents.Name){
			c.abs in Path some -> lone objs
			(c.abs).(c.points) in Root
/*			all p,q: ((c.abs).Object).pathparent| p -> q in pathparent implies 
				some p.(c.abs) && some q.(c.abs) & Tree && q.(c.abs)  -> p.name -> p.(c.abs) in contains
			all t,o : objs, n : Name | t -> o -> n in contents
				=> some x : c.abs.o, y : c.abs.t | x -> y in pathparent and x.name = n
			all p:c.abs.univ | some pathparent.p iff p.(c.abs) in Tree
			all p:c.abs.univ | no pathparent.p iff p.(c.abs) in Blob*/
			all p,q : (c.abs).univ | p -> q in pathparent implies q.(c.abs) -> p.(c.abs) -> p.name in contents
			all t,o : objs, n : Name | t -> o -> n in contents implies some x : c.abs.o, y : c.abs.t | x -> y in pathparent and x.name = n
			
		}
	}
	all o:Name.(Tree.contains) & Blob, p:(Commit.abs).o | o in (path.p).blob
}

run{
	some objects.State & Commit
//	some s:State, p:Path | p not in (head.s).(marks.s).abs.Object
} for 3 but 1 State
