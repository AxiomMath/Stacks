module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosureEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The colimit clauses of Stacks 03M1 at the universe of the schemes

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  This file
proves, at the universe `u` of the schemes and with no hypothesis, that quasi-coherence of
`𝒪_F`-modules is closed under direct sums and under colimits of an arbitrary shape — the
colimit clauses of Stacks 03M1 — and that `QCoh(𝒪_F)` is degenerate only if the structure sheaf
is a zero module.  These are the inputs on colimits of Stacks 077V, which is assembled in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentSeparator.lean` together with the separator
of `QCoh(𝒪_F)`.

## Main results

* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves` and
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse`:
  **the direct-sum and the arbitrary-colimit clauses of Stacks 03M1 at the universe of the
  schemes, with no hypothesis.**
* `AlgebraicGeometry.Space.exists_not_isZero_quasicoherentSheaves`: `QCoh(𝒪_F)` is degenerate
  only if the structure sheaf is a zero module.

## Implementation notes

The module universe is `u`, the universe of the schemes, where the source puts the
`𝒪_F`-modules.  It is not free: the direct-sum clause rests on Descent, Proposition 03DX(2),
which this tree has at `u` only.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The colimit clauses of Stacks 03M1 at the universe of the schemes -/

/-- **The direct-sum clause of Stacks 03M1 at the universe of the schemes, with no hypothesis.**
Quasi-coherence of `𝒪_F`-modules is closed under the colimits of a discrete shape.

This is `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX`
with its `h03DX` supplied by Descent, Proposition 03DX(2),
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`.  The index type
lives in an arbitrary universe. -/
theorem isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves (ι : Type w)
    [HasColimitsOfShape (Discrete ι) (Modules.{u, u} B S hS F hF)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape (Discrete ι) :=
  isClosedUnderColimitsOfShape_discrete_quasicoherent_of_h03DX B S hS F hF
    (fun G hG => (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF G).1 hG) ι

/-- **The colimit clause of Stacks 03M1 at the universe of the schemes, with no hypothesis.**
Quasi-coherence of `𝒪_F`-modules is closed under the colimits of an arbitrary shape.

This is `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves` with both of
its hypotheses discharged: the direct-sum clause by
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves` and the
cokernel clause by `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`.  It
subsumes the cokernel clause, and it is the hypothesis `hfc` of
`AlgebraicGeometry.Space.quasicoherentSheaves_isGrothendieckAbelian_of_closure` for an arbitrary
shape rather than only a filtered one. -/
theorem isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse (K : Type w)
    [Category.{w'} K] [HasCoproducts.{max w w'} (Modules.{u, u} B S hS F hF)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_quasicoherentSheaves B S hS F hF K
    (fun I => isClosedUnderColimitsOfShape_discrete_quasicoherentSheaves B S hS F hF I)
    (isClosedUnderCokernels_quasicoherentSheaves B S hS F hF)

/-! ### Non-degeneracy of `QCoh(𝒪_F)` -/

/-- **`QCoh(𝒪_F)` is degenerate only if the structure sheaf is a zero module.**  If `𝒪_F` is not
a zero `𝒪_F`-module then not every quasi-coherent `𝒪_F`-module is zero.

The structure sheaf is quasi-coherent on any ringed site, by Stacks 03DL(6) for the structure
sheaf, `SheafOfModules.isQuasicoherentOnSite_unit`, so it is itself an object of `QCoh(𝒪_F)`.

This pins down exactly when the two parts of Stacks 077V are statements about a degenerate
category: precisely when `𝒪_F` is zero, which for the small étale ringed site means that every
étale chart of `F` has the zero ring of functions. -/
theorem exists_not_isZero_quasicoherentSheaves
    (h : ¬ IsZero (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)) : Modules.{u, u} B S hS F hF)) :
    ∃ M : QuasicoherentSheaves.{u, u} B S hS F hF,
      ¬ IsZero ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι.obj M) :=
  ⟨⟨_, SheafOfModules.isQuasicoherentOnSite_unit _⟩, h⟩

end AlgebraicGeometry.Space

end
