module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# A right derived functor of an exact functor

Let `B : 𝒜 ⥤ ℬ` be an exact additive functor between abelian categories and `RB` a right derived
functor of `B` whose unit `u_K : B(K) ⟶ RB(K)` is invertible on every cochain complex `K` (as it is
as soon as every complex has a K-injective resolution, by
`StacksDraft.DerivedUnitSquare.isIso_unitQ_of_preservesFiniteColimits`). Then `RB` is the functor
`B.mapDerivedCategory` that `B` induces on derived categories, and in particular it commutes with
the cohomology objects: `Hⁿ(RB(K)) ≅ B(Hⁿ(K))`.

## Main definitions

* `StacksDraft.DerivedUnitSquare.isoMapDerivedCategory`: the identification
  `RB ≅ B.mapDerivedCategory`.

## Main results

* `StacksDraft.DerivedUnitSquare.isIso_homologyFunctor_map_map`: `RB` carries a morphism which is
  invertible on `Hⁿ` to one which is invertible on `Hⁿ`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace StacksDraft.DerivedUnitSquare

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (B : C ⥤ D) [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  {RB : DerivedCategory C ⥤ DerivedCategory D}
  (u : B.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RB)
  (hu : ∀ K : CochainComplex C ℤ, IsIso (unitQ B u K))

/-- The inverse of the unit, as an isomorphism `Q ⋙ RB ≅ B ⋙ Q` of functors on cochain
complexes. -/
def unitQIso : DerivedCategory.Q ⋙ RB ≅ B.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q :=
  NatIso.ofComponents (fun K => (@asIso _ _ _ _ (unitQ B u K) (hu K)).symm) (fun {K L} φ => by
    have := unitQ_naturality B u φ
    dsimp
    rw [← cancel_mono (unitQ B u L), Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.assoc, this, IsIso.inv_hom_id_assoc])

include hu in
/-- **A right derived functor of an exact functor whose unit is invertible is the functor induced
on derived categories.** -/
def isoMapDerivedCategory : RB ≅ B.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (B.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) RB :=
    ⟨unitQIso B u hu⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (B.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (B.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) RB B.mapDerivedCategory
    (Iso.refl _)

include hu in
/-- **The derived functor of an exact functor preserves isomorphisms on cohomology objects**:
if `Hⁿ(α)` is invertible, so is `Hⁿ(RB(α))`. -/
lemma isIso_homologyFunctor_map_map {M N : DerivedCategory C} (α : M ⟶ N) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor C n).map α)) :
    IsIso ((DerivedCategory.homologyFunctor D n).map (RB.map α)) :=
  (NatIso.isIso_map_iff (Functor.isoWhiskerRight (isoMapDerivedCategory B u hu)
    (DerivedCategory.homologyFunctor D n)) α).2
    ((B.isIso_homologyFunctor_map_mapDerivedCategory_map_iff α n).2 inferInstance)

end StacksDraft.DerivedUnitSquare

end
