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
			root = (((head.s).marks).s).points,
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
	objects.s' = objects.s
}

pred commit[s,s' : State] {

	s != s' 

	some new : Commit & objects.s' {
	//pre-conditions

		let lastC = (((head.s).marks).s),
				r = { t : Tree, o : (Tree+Blob) | some n : Name | t->n->o in contains},
				root = new.points,
				pathdown = root.*r,
				r' = {t : Tree, n : Name, t' : Tree+Blob | t->n->t' in contains and t in pathdown
																																		 and n->t' in t.contains} {

				//new commit cannot have same relative to last commit
				new.points != lastC.points
		
				// the number of relations to the model that new points must be equal to the index
				#r' = #(Path & index.s').*pathparent

	// post-conditions
				//the new commit must  be son of the previous head commit, or none if none existed before
				lastC = (new.parent).s'


				//the branch points to the new commit and head must point to the same branch
				new = ((head.s').marks).s' and  head.s' = head.s			
			
				// all files and just the files in the index must be present in the new commit
				// (Hard)
				all p : (index.s & blob.Blob) {
		
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
													
													(p'.name -> t'' in t'.contains)  
													(#(t.*(~r) & t'.*r) = #p'.*(~pathparent))				
											}
										}
				 				}
		 				}
				}
			}


				// all objects that  belong to the previous state must belong to new state plus the
				// new ones
				let r = { t : Tree, o : (Tree+Blob) | some n : Name | t->n->o in contains} |
						let newObjs = (new.points).*r | objects.s' = objects.s + newObjs 
		}
	// all the rest must remain the same
	index.s' = index.s
}


run { 
	
	some s,s':State | commit[s,s'] and #(index.s) = 2 and #(index.s).pathparent = 2

} for 10 but exactly 2 State
