module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of `f_* 𝒪_Y` and of its integral closure, for `f` quasi-compact quasi-separated

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S`.  The
direct image `f_* 𝒪_Y` is a quasi-coherent `𝒪_X`-algebra, and so is the integral closure `𝒪'` of
`𝒪_X` in it.  These are the two quasi-coherence inputs of the normalization of `X` in `Y`
(Definition 0822), and both are theorems at quasi-compactness and quasi-separatedness of `f`
alone.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs`: `f_* 𝒪_Y` is
  quasi-coherent.  It is `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra` with its
  hypothesis `h03M9` discharged by Stacks 03M9,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`.
* `AlgebraicGeometry.Space.isQuasicoherent_integralClosureSheaf_pushforwardAlgebra`: the integral
  closure of `𝒪_X` in `f_* 𝒪_Y` is quasi-coherent, by Stacks 0820,
  `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_integralClosureSheaf`.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The direct image of the structure sheaf along a quasi-compact, quasi-separated morphism of
algebraic spaces is a quasi-coherent algebra**, with no further hypothesis: the input `h03M9` of
`AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra` is Stacks 03M9, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`. -/
@[ega "IV 21.12.1" "more general"]
theorem isQuasicoherent_pushforwardAlgebra_of_qcqs (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent :=
  isQuasicoherent_pushforwardAlgebra B S hS f hfqc hfqs
    fun hqc hqs ↦ isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hqc hqs

/-- **The integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` is quasi-coherent** for a quasi-compact,
quasi-separated morphism `f : Y ⟶ X` of algebraic spaces: Stacks 0820 applied to the
quasi-coherent algebra of `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs`. -/
theorem isQuasicoherent_integralClosureSheaf_pushforwardAlgebra (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent :=
  AlgebraSheaf.isQuasicoherent_integralClosureSheaf _
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs)

end AlgebraicGeometry.Space

end
