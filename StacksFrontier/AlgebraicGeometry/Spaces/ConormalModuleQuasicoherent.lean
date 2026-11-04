module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent

/-!
# Quasi-coherence of the degree-one piece of the conormal algebra

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  The degree-one piece of the conormal algebra of Stacks 09RN of `i` is `i^*𝓘`, the
inverse image along `i` of the kernel ideal sheaf `𝓘 ⊆ 𝒪_X`.  This file proves that it is
**quasi-coherent** as soon as `i` is quasi-compact, with no immersion hypothesis.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalAlgebra_piece_one`: the degree-one piece
  of the conormal algebra of Stacks 09RN of a *quasi-compact* morphism is quasi-coherent, with no
  immersion hypothesis.

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {Z X : AlgebraicSpaces B S hS}

/-- **The degree-one piece of the conormal algebra of a quasi-compact morphism is
quasi-coherent.**  For `i : Z ⟶ X` quasi-compact, the degree-one piece `i^*𝓘` of the conormal
algebra of Stacks 09RN is a quasi-coherent `𝒪_Z`-module. -/
theorem isQuasicoherentOnSite_conormalAlgebra_piece_one (i : Z ⟶ X)
    (hi : IsQuasiCompact B S hS i.hom) :
    ((conormalAlgebra B S hS i).piece 1).IsQuasicoherentOnSite := by
  rw [conormalAlgebra_piece_one]
  exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS i _
    (isQuasicoherentOnSite_kernelIdealSheaf B S hS i hi)

end AlgebraicGeometry.Space

end
