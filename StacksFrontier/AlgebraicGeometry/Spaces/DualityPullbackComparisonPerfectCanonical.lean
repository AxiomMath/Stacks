module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDual

/-!
# The map of Stacks 0E5P at a dualizable object

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated algebraic spaces and `a` the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. If derived pullback is a monoidal functor
`D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` whose structure maps are those of Stacks 07A4, and `K` has a dual
`K'` in `D_QCoh(𝒪_Y)`, then the two-variable map `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` of Stacks 0E5P
is an isomorphism for every `L`.

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing`:
  the map of Stacks 0E5P is invertible at a dualizable object, for a monoidal structure on derived
  pullback whose tensor structure maps are those of Stacks 07A4.
* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing'`:
  the same for the monoidal structure on derived pullback with the structure maps of Stacks 07A4.

## References

* [Stacks Project, Tag 0E5Q](https://stacks.math.columbia.edu/tag/0E5Q)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **The map of Stacks 0E5P is invertible at a dualizable object**, for a monoidal structure on
derived pullback whose tensor structure maps are those of Stacks 07A4. -/
theorem isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing
    (hF : @Functor.Monoidal _ _ (quasicoherentDerivedMonoidal Y) _ _
      (quasicoherentDerivedMonoidal X) (quasicoherentDerivedModulePullback f))
    (hδ : ∀ K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2,
      @Functor.OplaxMonoidal.δ _ _ (quasicoherentDerivedMonoidal Y) _ _
        (quasicoherentDerivedMonoidal X) _ hF.toOplaxMonoidal K L =
          (quasicoherentDerivedPullbackTensorComparison f).app (L, K))
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (p : @ExactPairing _ _ (quasicoherentDerivedMonoidal Y) K K')
    (L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (quasicoherentDerivedCompareWithPullbackTensor hZ f hXqc hXqs hYqs K L) := by
  let := quasicoherentDerivedMonoidal X
  let := quasicoherentDerivedMonoidal Y
  let := hF
  let := p
  let := ExactPairing.map (quasicoherentDerivedModulePullback f) K K'
  let D := quasicoherentDualityData hZ f hXqc hXqs hYqs
  have hπ : ∀ K₀, D.projectionFormulaTwoSquare K₀ =
      ProjectionFormula.projection (quasicoherentDerivedModulePullback f) D.adj K₀ := fun K₀ =>
    NatTrans.ext (funext fun E =>
      ProjectionFormula.adjunctionTensorMap_eq_projection_app _ D.adj
        D.tensorPullbackComparison (fun X K => (hδ K X).symm) E K₀)
  refine D.isIso_compareWithPullbackTensor_of_mateEquiv
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs)
    (tensorLeftAdjunction ((quasicoherentDerivedModulePullback f).obj K)
      ((quasicoherentDerivedModulePullback f).obj K'))
    (tensorLeftAdjunction K K') ?_ L
  change _ = inv (D.projectionFormulaTwoSquare K)
  apply IsIso.eq_inv_of_inv_hom_id
  rw [hπ K, hπ K']
  exact ProjectionFormula.mateEquiv_projection_comp_projection _ D.adj K K'

/-- **The map of Stacks 0E5P is invertible at a dualizable object**: if `K` has a dual `K'` in
`D_QCoh(𝒪_Y)`, then `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` is an isomorphism for every `L`, derived
pullback being monoidal on `D_QCoh` with the structure maps of Stacks 07A4. -/
theorem isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing'
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (p : @ExactPairing _ _ (quasicoherentDerivedMonoidal Y) K K')
    (L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (quasicoherentDerivedCompareWithPullbackTensor hZ f hXqc hXqs hYqs K L) :=
  isIso_quasicoherentDerivedCompareWithPullbackTensor_of_exactPairing hZ f hXqc hXqs hYqs
    (quasicoherentDerivedPullbackMonoidal f (smallEtaleDerivedPullbackTensorIso_associativity f))
    (quasicoherentDerivedPullbackMonoidal_δ f (smallEtaleDerivedPullbackTensorIso_associativity f))
    K K' p L

end AlgebraicGeometry.Space

end
