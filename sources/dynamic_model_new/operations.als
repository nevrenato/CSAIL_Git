open Path
open Object_Model

pred add[s,s' : State,  p: Path ] {
		s != s'
	//pre-condition
		//path has to be a leaf
		no pathparent.p
	
	//post-condition
		//a path is added to the set of objects
		objects.s' = objects.s + p.blob
		//a path is added to index
		index.s' = index.s + p

		//all others relations are kept

		parent.s' = parent.s
		marks.s' = marks.s
		branches.s' = branches.s
		head.s' = head.s
}

pred rm[s,s' : State, p:Path] {
	
	s != s'
	//pre-condition
	p in index.s

	let r = { t : Tree, o : (Tree+Blob) | some n : Name | t->n->o in contains},
			root = (Head.(on.s)).(marks.s).points,
			pathdown = root.*r {

				some t : pathdown {
					
						// there is one tree in the commit that has the relation name->blob
						p.name -> p.blob in t.contains 

						let pathup = t.^(~r) {
					
								// the depth of the path tree must be equal to the path leading to the
								// tree t
								#p.^pathparent = #(pathup & pathdown) 

								//for all parent trees there must be some correspondance to a parent
								// path
								all t' : (pathup & pathdown) {
								
									// t'' is son of t' ; p' is some parent in the path
									some t'' : (t.*(~r) & pathdown), p' : p.^pathparent { 
											p'.name -> t'' in t'.contains 
											#(t.*(~r) & t'.*r) = #p'.*(~pathparent)
									}
							 }	
						}
				 }
		 }


	//post-condition
	// the path is removed from the index
	index.s' = index.s - p

	//all others relations are kept
	parent.s' = parent.s
	marks.s' = marks.s
	branches.s' = branches.s
	head.s' = head.s
}


run { 
	some s,s':State, p:Path | rm[s,s',p] 

} for 5 but exactly 2 State
