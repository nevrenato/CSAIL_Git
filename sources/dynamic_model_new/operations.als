open Index
open File
open Object_model

pred add[s,s' : State, f : File ] {
			s != s'
			s'.(Index.staged ) = s.(Index.staged) + f
}

pred rm[s,s' : State, f : File ] {
			s != s' 
			s'.(Index.staged)  = s.(Index.staged) - f
}

pred commit[s,s' : State] {
			s != s'

			some c : Commit  {
					
					// the parent of the new commit is the last commit
					s'.(c.parent) = s.(Head.pointsToLast)
					// the new commit cannot be in the last state
					no s.(c.parent) 
				 	// Head points to the new commit
					s'.(Head.pointsToLast) = c
			
					
					// The Hard part
					all f : s.(Index.staged) {

						let root = c.points, 
								fname = (s.(f.pathname)).name,
								fparents = (s.(f.pathname)).^parent,
								sons = 
								{t : Tree, t' : (Tree+Blob) | some n : Name | t->s'->n->t' in contains}  {
				
								
							// The object model of the new commit (s') can only have the blobs
							// that are staged in s
							(root.^sons) & Blob in s.((s.(Index.staged)).blob)
					

								one t : root.*sons {
														
											// relation name->blob in some tree									
											fname->s.(f.blob) in s'.(t.contains)
														
											// and for all parents of that file there must be a correspondent
											// tree										
											all fp : fparents |
												one t'',t' : root.*sons |
														some fp.parent implies s'->(fp.name->t'') in t'.contains   		
							  }
					   }
					}
			}
}

run { 

			some s,s' : State | commit[s,s'] and #s.(Index.staged) > 0
			#State = 2
			all f : File, s : State | some (s.(f.pathname)).parent
} for 8
