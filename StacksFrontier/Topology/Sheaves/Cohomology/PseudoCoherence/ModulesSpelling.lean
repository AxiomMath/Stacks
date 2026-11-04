module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# Pseudo-coherence read on the tensor-product spelling of the module category

The pseudo-coherence predicates of Stacks 08CB are stated on `D(𝒪_X)` with the category of
modules spelled `StrictlyPerfect.OXMod X`; the derived pullback, the derived tensor product and
the derived internal Hom are stated on `D(𝒪_X)` with the category spelled
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`. The two categories are the same.
This file states three facts about pseudo-coherence on the second spelling: an object isomorphic to
the class of a strictly perfect complex is pseudo-coherent, pseudo-coherence passes to the third
vertex of a distinguished triangle, and a bounded below object is locally bounded below.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_of_iso_Q_obj_modules`
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_obj₃_of_distinguished_modules`
* `AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_of_isGE_modules`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {Y : RingedSpace.{u, u}}

/-- An object of `D(𝒪_Y)` isomorphic to the class of a strictly perfect complex is
pseudo-coherent. -/
theorem isPseudoCoherent_of_iso_Q_obj_modules
    (P : CochainComplex (KFlatDerivedPullback.Modules Y) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect (X := Y) P)
    (E : DerivedCategory (KFlatDerivedPullback.Modules Y)) (e : DerivedCategory.Q.obj P ≅ E) :
    IsPseudoCoherent (X := Y) E :=
  ⟨P, isPseudoCoherentComplex_of_isStrictlyPerfect hP, ⟨e⟩⟩

/-- If the first two vertices of a distinguished triangle of `D(𝒪_Y)` are pseudo-coherent, so is
the third (Stacks 08CD). -/
theorem isPseudoCoherent_obj₃_of_distinguished_modules
    (T : Triangle (DerivedCategory (KFlatDerivedPullback.Modules Y))) (hT : T ∈ distTriang _)
    (h₁ : IsPseudoCoherent (X := Y) T.obj₁) (h₂ : IsPseudoCoherent (X := Y) T.obj₂) :
    IsPseudoCoherent (X := Y) T.obj₃ :=
  (isPseudoCoherent_iff_forall (X := Y) T.obj₃).2 fun k =>
    isPseudoCoherentFrom_obj₃_of_distinguished k T hT
      ((isPseudoCoherent_iff_forall (X := Y) T.obj₁).1 h₁ (k + 1))
      ((isPseudoCoherent_iff_forall (X := Y) T.obj₂).1 h₂ k)

/-- An object of `D(𝒪_Y)` with no cohomology below `b` is locally bounded below. -/
theorem isLocallyBoundedBelow_of_isGE_modules
    (E : DerivedCategory (KFlatDerivedPullback.Modules Y)) (b : ℤ) (h : E.IsGE b) :
    IsLocallyBoundedBelow Y E :=
  fun _ => ⟨⊤, trivial, b, fun i hi =>
    (PseudoCoherence.restrictModules Y ⊤).map_isZero ((DerivedCategory.isGE_iff E b).1 h i hi)⟩

end AlgebraicGeometry.RingedSpace

end
