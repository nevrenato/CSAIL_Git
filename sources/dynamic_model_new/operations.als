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
			}
}
run { 

			some s,s' : State | commit[s,s']
			#State = 2

} for 5
