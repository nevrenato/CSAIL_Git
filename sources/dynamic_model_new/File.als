open Objects
open Name
open State

sig Path {

	parent : lone Path,
	name : Name

}
sig File {

	blob : State -> one Blob,
	pathname : State -> one Path 

}

fact {
	
		// no cycles
		no ^parent & iden

		let r = {f : File, p : Path | some s : State | f->s->p in pathname } {
				// pathname is injective
				r.~r in iden

				// The name of a file has to be always in a leaf
				no (Path.parent) & (File.r)
		}

		// two paths with the same parent can't have the same name
		all disj p,p' : Path | p.parent = p'.parent implies p.name != p'.name
}



run {
#File = 1
#State = 2
#Tree = 0
#parent = 2
	
} for 4
