module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# Morphism descent systems from étale charts of a descent situation

For a descent situation with bounded charts, an étale chart of the chosen stage together with a
morphism over the stage to a base change along `Spec R' ⟶ Spec R`, for `R ⟶ R'` of finite
presentation, is a morphism descent system in the sense of Stacks 084W. The case of the structure
homomorphism of a presentation `A[x₁, …, xₙ]/(g₁, …, gₙ)` is the situation of display 70.5.10.1
in the proof of Stacks 07SQ.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfSpecMapOfChartsBounded`: the
  morphism descent system attached to a chart and a morphism to a base change along `Spec.map φ`.
* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfPresentationOfChartsBounded`:
  its specialisation to the structure homomorphism of a presentation.
-/

universe u

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The morphism descent system of Stacks 07SQ -/

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The morphism descent system of the proof of Stacks 07SQ.** Let `D` be a descent situation,
let `φ : R ⟶ R'` present `R'` as a finitely presented `R`-algebra, let
`p : X₀ ⟶ Spec R` be a morphism from the chosen stage of `D` to the functor of points of
`Spec R`, let `U` be an object of the site with quasi-compact quasi-separated total scheme and
`a : U ⟶ X₀` an étale chart of the stage, and let `f₀` be a morphism over the stage from that
chart to the base change `X₀ ×_{Spec R} Spec R'`. Then `f₀` is a morphism descent system in the
sense of Stacks 084W, so the descent results of
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded` — Stacks 084S among them — apply
to it.

With `R` a `u`-model of the ring of global functions of the stage, `R'` the presentation
`AlgebraicGeometry.Space.presentationAlgebra` and `p` the canonical morphism of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom`, this is the situation of display
70.5.10.1 in the proof of Stacks 07SQ, read at the chosen stage. -/
noncomputable def morphismDescentSystemOfSpecMapOfChartsBounded (hI : ChartsBounded B S hS D.system)
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec R))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ)))) :
    MorphismDescentSystemOfChartsBounded B S hS hZ I :=
  D.morphismDescentSystemOfChartsBounded hI (Over.mk a)
    (Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ))))
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS φ
      (RingHom.FiniteType.of_finitePresentation hφ) (D.algebraicSpace D.base) p)
    (isFinitePresentation_etaleChart B S hS hZ (D.algebraicSpace D.base)
      (D.quasiSeparated D.base) hUqc hUqs ha)
    (isFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ
      (D.algebraicSpace D.base) p)
    f₀

/-- **The morphism descent system of display 70.5.10.1 of the proof of Stacks 07SQ.** This is
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfSpecMapOfChartsBounded` at the
spectrum of the structure homomorphism of a presentation `A[x₁, …, xₙ]/(g₁, …, gₙ)`, which is of
finite presentation by `AlgebraicGeometry.Space.finitePresentation_presentationStructureHom`.

With `A` a `u`-model of the ring of global functions of the stage and `p` the canonical morphism
of `AlgebraicGeometry.Space.exists_specMap_of_globalHom`, the two verticals of the base change
are the left vertical and the bottom edge of the square of Stacks 084U. -/
noncomputable def morphismDescentSystemOfPresentationOfChartsBounded
    (hI : ChartsBounded B S hS D.system)
    {A : Type u} [CommRing A] {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec (CommRingCat.of A)))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g)))))) :
    MorphismDescentSystemOfChartsBounded B S hS hZ I :=
  D.morphismDescentSystemOfSpecMapOfChartsBounded hI
    (CommRingCat.ofHom (presentationStructureHom g))
    (finitePresentation_presentationStructureHom g) p hUqc hUqs ha f₀

end DescentSituation

end AlgebraicGeometry.Space

end
