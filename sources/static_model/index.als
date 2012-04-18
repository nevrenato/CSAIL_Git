open util/ordering[Index]
open working_directory
open object_model


sig Index{

	containFiles: set File,
	containShas: set Sha, 
	stage: containShas one -> containFiles

}
{
   containFiles in Sha.stage
	 containShas in stage.File
}

fact{
	//all Sha in stage name a Blob
	Index.containShas in Blob.namedBy.StateOM
}

pred init[i:Index]{
	no stage
	
}

pred add[i,i':Index, s:Sha, f:File]{
	f in wdparent.last.(Root & wdobjects.last)
	i'.stage = i.stage - (Sha -> f) + (s -> f)
}

run{
	//some i,i':Index, s:Sha, f:File | i.stage != i'.stage && add[i,i',s,f]
	//some f:File | f not in Index.containFiles
} for 3 but 1 Index, 1 StateWD, 1 StateOM
