--------------------- MODULE AllocatorRefinement ----------------------

EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator
SimpleAllocator == Simple!SimpleAllocator

THEOREM
Allocator => SimpleAllocator
=======================================================================
