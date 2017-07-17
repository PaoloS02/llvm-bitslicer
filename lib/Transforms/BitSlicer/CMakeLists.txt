add_llvm_loadable_module( LLVMBitSlicer
  BitSlicer.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
