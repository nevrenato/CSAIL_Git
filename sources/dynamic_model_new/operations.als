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
			
}
run { 

			some s,s' : State | commit[s,s']


} for 3
