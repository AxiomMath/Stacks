module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Kernels and cokernels of quasi-coherent modules on an arbitrary scheme

On a scheme `X` the kernel and the cokernel of a morphism of quasi-coherent `𝒪_X`-modules are
quasi-coherent. These are the instances
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` and
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`, registered here for
the Stacks Project tags 01LB and, for the kernel, 01IC.

## References

* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

add_to_stacks 01LB "kernel" Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
add_to_stacks 01LB "cokernel"
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
add_to_stacks 01IC "kernel" Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
