module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Transporting the vanishing of étale cohomology along restriction maps

For an abelian sheaf `G` on the small étale site of `X` and a morphism `c : Z ⟶ X`, write
`P(Z, c)` for the vanishing of `H^q(Z, c⁻¹G)`. If `c₁ = h ≫ c₂` and restriction along `h` is
bijective in degree `q` at `c₂⁻¹G`, then `P(Z₁, c₁) ↔ P(Z₂, c₂)`: the inverse image along `c₁` is
the inverse image along `h` of the inverse image along `c₂`. Restriction along an isomorphism of
schemes is always bijective, inverse image being then an equivalence.

This is the bookkeeping by which the proof of [Stacks, Tag 095T] moves the vanishing of
cohomology of an injective sheaf from one fibre of `ℙ¹` to another.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_isIso` — restriction along
  an isomorphism of schemes is bijective.
* `Stacks.EtaleCohomology.subsingleton_H_inverseImage_iff_of_bijective` — the transport.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Inverse image of abelian sheaves along an isomorphism of schemes is an equivalence.** -/
theorem isEquivalence_etaleAbelianInverseImage_of_isIso {T Z : Scheme.{u}} (c : T ⟶ Z)
    [IsIso c] : (etaleAbelianInverseImage.{u, 0} c).IsEquivalence := by
  have := isEquivalence_smallEtalePullbackAb_of_isIso c
  exact Functor.isEquivalence_of_iso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange c)
      AddCommGrpCat.{u + 1} _ _)

/-- **Restriction of étale cohomology along an isomorphism of schemes is bijective.** -/
theorem bijective_etaleCohomologyRestrictionMap_of_isIso {T Z : Scheme.{u}} (c : T ⟶ Z)
    [IsIso c] [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} c F q) := by
  have := isEquivalence_etaleAbelianInverseImage_of_isIso c
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives Z
  have h := (etaleAbelianInverseImage.{u, 0} c).mapExt_bijective_of_preservesInjectiveObjects
    ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) F q
  let e := (etaleAbelianInverseImageConstantIso.{u, 0} c).app (AddCommGrpCat.of (ULift ℤ))
  have hp : Function.Bijective (fun x : Ext.{u + 1} ((etaleAbelianInverseImage.{u, 0} c).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))) ((etaleAbelianInverseImage.{u, 0} c).obj F) q ↦
      (Ext.mk₀ e.inv).comp x (zero_add q)) := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(Ext.mk₀ e.hom).comp y (zero_add q), ?_⟩⟩
    · have := congrArg (fun z ↦ (Ext.mk₀ e.hom).comp z (zero_add q)) hxy
      simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp] using this
    · simp only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  exact hp.comp h

variable {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

/-- **Transport of the vanishing of cohomology along a bijective restriction map.** If
`c₁ = h ≫ c₂` and restriction along `h` is bijective in degree `q` at `c₂⁻¹G`, then
`H^q(Z₁, c₁⁻¹G)` vanishes exactly when `H^q(Z₂, c₂⁻¹G)` does. -/
theorem subsingleton_H_inverseImage_iff_of_bijective {Z₁ Z₂ : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Z₁.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z₂.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (c₁ : Z₁ ⟶ X) (c₂ : Z₂ ⟶ X) (h : Z₁ ⟶ Z₂) (hc : c₁ = h ≫ c₂)
    (hb : Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} h
      ((etaleAbelianInverseImage.{u, 0} c₂).obj G) q)) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} c₁).obj G) q) ↔
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} c₂).obj G) q) := by
  rw [subsingleton_H_iff_of_iso ((etaleAbelianInverseImageCompIso'.{u, 0} h c₂ c₁ hc).app G)]
  exact (Equiv.ofBijective _ hb).subsingleton_congr.symm

/-- `Stacks.EtaleCohomology.subsingleton_H_inverseImage_iff_of_bijective` along an isomorphism of
schemes. -/
theorem subsingleton_H_inverseImage_iff_of_isIso {Z₁ Z₂ : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Z₁.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z₂.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (c₁ : Z₁ ⟶ X) (c₂ : Z₂ ⟶ X) (h : Z₁ ⟶ Z₂) [IsIso h] (hc : c₁ = h ≫ c₂) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} c₁).obj G) q) ↔
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} c₂).obj G) q) :=
  subsingleton_H_inverseImage_iff_of_bijective G q c₁ c₂ h hc
    (bijective_etaleCohomologyRestrictionMap_of_isIso h _ q)

end Stacks.EtaleCohomology

end
