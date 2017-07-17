add_llvm_loadable_module( LLVMFScanner
  FScanner.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
