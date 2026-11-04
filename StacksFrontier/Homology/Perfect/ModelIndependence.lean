module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

@[expose] public noncomputable section

/-!
# Perfectness does not depend on the chosen derived category

An instance of `CategoryTheory.HasDerivedCategory.{w} C` carries a localization of
`CochainComplex C ℤ` at the quasi-isomorphisms as data, so two instances give two categories
`DerivedCategory C`. Both perfectness predicates, over a ring and on a ringed space, consist of a
condition on a cochain complex together with an isomorphism between the class of that complex and
the object in question. This file shows that such isomorphisms, and hence perfectness, can be
carried between any two chosen models.

## Main definitions

* `StacksDraft.DerivedModel.qObjIsoOfModel`: an isomorphism between the classes of two cochain
  complexes at one chosen model gives one at any other chosen model.

## Main results

* `StacksDraft.Perfect.isPerfect_iff_of_model`: two objects of two chosen derived categories of
  `R`-modules represented by the same cochain complex are perfect together.
* `Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model`: the same on a ringed space.
-/

open CategoryTheory

universe u v w z d₁ d₂

namespace StacksDraft.DerivedModel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An isomorphism `Q₁(E) ≅ Q₁(F)` between the classes of two cochain complexes in one chosen
derived category gives an isomorphism `Q₂(E) ≅ Q₂(F)` in another, by conjugating with the
identification `StacksDraft.DerivedModel.modelCompQIso` of the two localization functors. -/
def qObjIsoOfModel (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)
    {E F : CochainComplex C ℤ}
    (e : (@DerivedCategory.Q C _ _ h₁).obj E ≅ (@DerivedCategory.Q C _ _ h₁).obj F) :
    (@DerivedCategory.Q C _ _ h₂).obj E ≅ (@DerivedCategory.Q C _ _ h₂).obj F :=
  ((modelCompQIso h₁ h₂).app E).symm ≪≫ (modelEquiv h₁ h₂).functor.mapIso e ≪≫
    (modelCompQIso h₁ h₂).app F

/-- Being isomorphic to the class of a fixed cochain complex `F` does not depend on the chosen
derived category, for objects `K`, `L` represented by the same complex `E`. -/
private theorem nonempty_iso_iff_of_model (h₁ : HasDerivedCategory.{w} C)
    (h₂ : HasDerivedCategory.{z} C) {E F : CochainComplex C ℤ}
    {K : @DerivedCategory C _ _ h₁} {L : @DerivedCategory C _ _ h₂}
    (e₁ : (@DerivedCategory.Q C _ _ h₁).obj E ≅ K) (e₂ : (@DerivedCategory.Q C _ _ h₂).obj E ≅ L) :
    Nonempty (K ≅ (@DerivedCategory.Q C _ _ h₁).obj F) ↔
      Nonempty (L ≅ (@DerivedCategory.Q C _ _ h₂).obj F) :=
  ⟨fun ⟨e⟩ => ⟨e₂.symm ≪≫ qObjIsoOfModel h₁ h₂ (e₁ ≪≫ e)⟩,
    fun ⟨e⟩ => ⟨e₁.symm ≪≫ qObjIsoOfModel h₂ h₁ (e₂ ≪≫ e)⟩⟩

end StacksDraft.DerivedModel

namespace StacksDraft.Perfect

/-- **Perfectness over a ring does not depend on the chosen derived category.** If an object `K`
of one chosen derived category of `R`-modules and an object `L` of another are both represented by
the same cochain complex `E`, then `K` is perfect if and only if `L` is. -/
theorem isPerfect_iff_of_model {R : Type u} [Ring R]
    (h₁ : HasDerivedCategory.{w} (ModuleCat.{v} R))
    (h₂ : HasDerivedCategory.{z} (ModuleCat.{v} R)) {E : CochainComplex (ModuleCat.{v} R) ℤ}
    {K : @DerivedCategory (ModuleCat.{v} R) _ _ h₁} {L : @DerivedCategory (ModuleCat.{v} R) _ _ h₂}
    (e₁ : (@DerivedCategory.Q (ModuleCat.{v} R) _ _ h₁).obj E ≅ K)
    (e₂ : (@DerivedCategory.Q (ModuleCat.{v} R) _ _ h₂).obj E ≅ L) :
    @IsPerfect R _ h₁ K ↔ @IsPerfect R _ h₂ L := by
  simp only [IsPerfect, DerivedModel.nonempty_iso_iff_of_model h₁ h₂ e₁ e₂]

end StacksDraft.Perfect

namespace Stacks.Cohomology.PerfectComplexes

/-- **Perfectness on a ringed space does not depend on the chosen derived category.** If an object
`K` of one chosen derived category of `𝒪_X`-modules and an object `L` of another are both
represented by the same cochain complex `E`, then `K` is perfect if and only if `L` is. -/
theorem isPerfect_iff_of_model {X : AlgebraicGeometry.RingedSpace.{u, v}}
    (h₁ : HasDerivedCategory.{d₁} (StrictlyPerfect.OXMod.{u, v} X))
    (h₂ : HasDerivedCategory.{d₂} (StrictlyPerfect.OXMod.{u, v} X))
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, v} X) ℤ}
    {K : @DerivedCategory (StrictlyPerfect.OXMod.{u, v} X) _ _ h₁}
    {L : @DerivedCategory (StrictlyPerfect.OXMod.{u, v} X) _ _ h₂}
    (e₁ : (@DerivedCategory.Q (StrictlyPerfect.OXMod.{u, v} X) _ _ h₁).obj E ≅ K)
    (e₂ : (@DerivedCategory.Q (StrictlyPerfect.OXMod.{u, v} X) _ _ h₂).obj E ≅ L) :
    @IsPerfect X h₁ K ↔ @IsPerfect X h₂ L := by
  simp only [IsPerfect, Iso.nonempty_iso_symm _ K, Iso.nonempty_iso_symm _ L,
    StacksDraft.DerivedModel.nonempty_iso_iff_of_model h₁ h₂ e₁ e₂]

end Stacks.Cohomology.PerfectComplexes

end
