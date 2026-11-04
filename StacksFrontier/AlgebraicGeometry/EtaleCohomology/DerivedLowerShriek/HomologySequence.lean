module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechClasses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale

/-!
# The higher direct images `R^q f_!` of sheaves and their long exact sequence

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄` over `Y`, and `Λ` a
ring. For a sheaf `G` of `Λ`-modules on `X_étale` placed in degree `0`, the cohomology sheaves of
`Rf_! G = R f̄_*(j_! G)` (`Stacks.EtaleCohomology.derivedLowerShriek`) are the sheaves
`R^q f_! G` on `Y_étale` (`Stacks.EtaleCohomology.lowerShriekHomology`). A short exact sequence
`0 → G₁ → G₂ → G₃ → 0` gives a distinguished triangle in `D⁺(X_étale, Λ)`, which the triangulated
functor `Rf_!` carries to a distinguished triangle, whence the long exact sequence

`… → R^q f_! G₁ → R^q f_! G₂ → R^q f_! G₃ --δ--> R^{q+1} f_! G₁ → …`,

natural in the short exact sequence. The construction is made for any triangulated functor
`Φ : D⁺(𝒜) ⥤ D⁺(ℬ)` (`Stacks.EtaleCohomology.singleHomology`) and specialised to `Rf_!`.

## Main definitions

* `Stacks.EtaleCohomology.singleHomology`: `G ↦ Hᵠ(Φ(G[0]))`.
* `Stacks.EtaleCohomology.singleHomologyδ`: the connecting map of a short exact sequence.
* `Stacks.EtaleCohomology.lowerShriekHomology`: `G ↦ R^q f_! G`.

## Main results

* `Stacks.EtaleCohomology.singleHomology_exact₂`, `_exact₃`, `_exact₁`: exactness of the long
  exact sequence.
* `Stacks.EtaleCohomology.singleHomologyδ_naturality`: naturality of the connecting map.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` is defined in the standard model
`HasDerivedCategory.standard` of the derived category, so its specialisation is stated in that
model; the generic part is stated for any model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Pretriangulated AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### The long exact sequence of a triangulated functor on objects placed in degree zero -/

section Generic

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [Category* B] [Abelian B]
  [HasDerivedCategory B]

/-- The functor placing an object of `𝒜` in degree `0` of a bounded-below complex is additive. -/
instance singlePlus_additive : (singlePlus A).Additive := by
  have : (singlePlus A ⋙ CochainComplex.Plus.ι A).Additive :=
    inferInstanceAs (HomologicalComplex.single A (ComplexShape.up ℤ) 0).Additive
  exact Functor.additive_of_comp_faithful _ (CochainComplex.Plus.ι A)

variable (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- `G ↦ Hᵠ(Φ(G[0]))` for a triangulated functor `Φ : D⁺(𝒜) ⥤ D⁺(ℬ)`. -/
def singleHomology (q : ℤ) : A ⥤ B :=
  singlePlus A ⋙ DerivedCategory.Plus.Q ⋙ Φ ⋙ DerivedCategory.Plus.homologyFunctor B q

/-- The functor `G ↦ Hᵠ(Φ(G[0]))` is additive. -/
instance (q : ℤ) : (singleHomology Φ q).Additive := by
  dsimp only [singleHomology]
  infer_instance

variable {S : ShortComplex A}

omit [HasDerivedCategory A] in
/-- A short exact sequence in `𝒜`, placed in degree `0`, is a short exact sequence of complexes. -/
theorem shortExact_toSC_map_singlePlus (hS : S.ShortExact) :
    (Stacks.Cohomology.RightDerivedBoundary.toSC (S.map (singlePlus A))).ShortExact :=
  hS.map_of_exact (HomologicalComplex.single A (ComplexShape.up ℤ) 0)

/-- The triangle `Φ(G₁) → Φ(G₂) → Φ(G₃) → Φ(G₁)[1]` of a short exact sequence, read in `D(ℬ)`. -/
def singleTriangle (hS : S.ShortExact) : Triangle (DerivedCategory B) :=
  DerivedCategory.Plus.ι.mapTriangle.obj (Φ.mapTriangle.obj
    (Stacks.Cech.Hypercohomology.plusTriangle (S.map (singlePlus A))
      (shortExact_toSC_map_singlePlus hS)))

/-- The triangle `singleTriangle Φ hS` of a short exact sequence is distinguished. -/
theorem singleTriangle_distinguished (hS : S.ShortExact) : singleTriangle Φ hS ∈ distTriang _ :=
  DerivedCategory.Plus.ι.map_distinguished _
    (Functor.map_distinguished _ _ (Stacks.Cech.Hypercohomology.plusTriangle_distinguished _ _))

/-- **The connecting map `Hᵠ(Φ(G₃)) ⟶ Hᵠ⁺¹(Φ(G₁))`** of a short exact sequence. -/
def singleHomologyδ (hS : S.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    (singleHomology Φ q).obj S.X₃ ⟶ (singleHomology Φ q').obj S.X₁ :=
  DerivedCategory.HomologySequence.δ (singleTriangle Φ hS) q q' hq

/-- Exactness of `Hᵠ(Φ(G₁)) → Hᵠ(Φ(G₂)) → Hᵠ(Φ(G₃))`. -/
theorem singleHomology_exact₂ (hS : S.ShortExact) (q : ℤ) : (S.map (singleHomology Φ q)).Exact :=
  DerivedCategory.HomologySequence.exact₂ _ (singleTriangle_distinguished Φ hS) q

/-- The composite `Hᵠ(Φ(G₂)) → Hᵠ(Φ(G₃)) → Hᵠ⁺¹(Φ(G₁))` is zero. -/
theorem singleHomology_map_comp_δ (hS : S.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    (singleHomology Φ q).map S.g ≫ singleHomologyδ Φ hS q q' hq = 0 :=
  DerivedCategory.HomologySequence.comp_δ _ (singleTriangle_distinguished Φ hS) q q' hq

/-- The composite `Hᵠ(Φ(G₃)) → Hᵠ⁺¹(Φ(G₁)) → Hᵠ⁺¹(Φ(G₂))` is zero. -/
theorem singleHomologyδ_comp_map (hS : S.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    singleHomologyδ Φ hS q q' hq ≫ (singleHomology Φ q').map S.f = 0 :=
  DerivedCategory.HomologySequence.δ_comp _ (singleTriangle_distinguished Φ hS) q q' hq

/-- Exactness of `Hᵠ(Φ(G₂)) → Hᵠ(Φ(G₃)) → Hᵠ⁺¹(Φ(G₁))`. -/
theorem singleHomology_exact₃ (hS : S.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    (ShortComplex.mk _ _ (singleHomology_map_comp_δ Φ hS q q' hq)).Exact :=
  DerivedCategory.HomologySequence.exact₃ _ (singleTriangle_distinguished Φ hS) q q' hq

/-- Exactness of `Hᵠ(Φ(G₃)) → Hᵠ⁺¹(Φ(G₁)) → Hᵠ⁺¹(Φ(G₂))`. -/
theorem singleHomology_exact₁ (hS : S.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    (ShortComplex.mk _ _ (singleHomologyδ_comp_map Φ hS q q' hq)).Exact :=
  DerivedCategory.HomologySequence.exact₁ _ (singleTriangle_distinguished Φ hS) q q' hq

/-- The morphism of triangles induced by a morphism of short exact sequences. -/
def singleTriangleMap {S S' : ShortComplex A} (φ : S ⟶ S') (hS : S.ShortExact)
    (hS' : S'.ShortExact) : singleTriangle Φ hS ⟶ singleTriangle Φ hS' :=
  DerivedCategory.Plus.ι.mapTriangle.map (Φ.mapTriangle.map
    (Triangle.homMk (Stacks.Cech.Hypercohomology.plusTriangle (S.map (singlePlus A))
        (shortExact_toSC_map_singlePlus hS))
      (Stacks.Cech.Hypercohomology.plusTriangle (S'.map (singlePlus A))
        (shortExact_toSC_map_singlePlus hS'))
      (DerivedCategory.Plus.Q.map ((singlePlus A).map φ.τ₁))
      (DerivedCategory.Plus.Q.map ((singlePlus A).map φ.τ₂))
      (DerivedCategory.Plus.Q.map ((singlePlus A).map φ.τ₃))
      (by
        dsimp [Stacks.Cech.Hypercohomology.plusTriangle]
        simp only [← Functor.map_comp, φ.comm₁₂])
      (by
        dsimp [Stacks.Cech.Hypercohomology.plusTriangle]
        simp only [← Functor.map_comp, φ.comm₂₃])
      (Stacks.Cech.Hypercohomology.plusδ_naturality (shortExact_toSC_map_singlePlus hS)
        (shortExact_toSC_map_singlePlus hS') ((singlePlus A).mapShortComplex.map φ))))

omit [Φ.IsTriangulated] in
/-- **Naturality of the connecting map.** -/
theorem singleHomologyδ_naturality {S S' : ShortComplex A} (φ : S ⟶ S') (hS : S.ShortExact)
    (hS' : S'.ShortExact) (q q' : ℤ) (hq : q + 1 = q') :
    (singleHomology Φ q).map φ.τ₃ ≫ singleHomologyδ Φ hS' q q' hq =
      singleHomologyδ Φ hS q q' hq ≫ (singleHomology Φ q').map φ.τ₁ :=
  Functor.homologySequenceδ_naturality (DerivedCategory.homologyFunctor B 0)
    (singleTriangleMap Φ φ hS hS') q q' hq

end Generic

/-! ### `R^q f_!` -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **`R^q f_! G`** for a sheaf `G` of `Λ`-modules on `X_étale`, placed in degree `0`: the
`q`-th cohomology sheaf of `Rf_! G = R f̄_*(j_! G)`, computed through the compactification `j`. -/
abbrev lowerShriekHomology (q : ℤ) : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ Y :=
  singleHomology (derivedLowerShriek.{u, 0} f j Λ) q

end LowerShriek

end Stacks.EtaleCohomology
