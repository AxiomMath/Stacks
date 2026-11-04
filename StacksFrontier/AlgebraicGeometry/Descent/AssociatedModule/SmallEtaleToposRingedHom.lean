module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# `ε` as an abstract morphism of ringed topoi

`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom` records
`ε = id_{small, étale, Zar} : S_étale → S_Zar` as an `AlgebraicGeometry.RingedToposSiteHom`,
i.e. with its geometric datum presented by the continuous inclusion of the small Zariski site of
`S` into the small étale site.  This module records it as an
`AlgebraicGeometry.RingedToposHom` instead: the two-field structure of Stacks 01D3 (2), whose
geometric datum is an arbitrary morphism of topoi.  That is the form in which the exactness of
the pullback of sheaves of modules along a flat morphism — Stacks 04JC, second assertion, as
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` — is available at
*different object universes* for the two sites, which is the situation `ε` is in.

The morphism of topoi is `AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi`.  Its direct
image on sheaves of sets is restriction along the inclusion, so the direct image of sheaves of
commutative rings that the two-field structure asks for is restriction too, by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; the structure map is therefore
`AlgebraicGeometry.SmallEtale.commRingStructureMap` read through that identification, which is
the identity on sections.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom`: `ε` as an
  `AlgebraicGeometry.RingedToposHom`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The direct image of sheaves of commutative rings along the morphism of topoi of `ε` is
restriction along the inclusion of the small Zariski site of `S`.**  The comparison is the
identity on sections. -/
public noncomputable def pushCommRingIso :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS) ≅
      (opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  NatIso.ofComponents
    (fun O ↦ restrictionCommRingIso (Opens.grothendieckTopology ↥S) (topology B S hS)
      (opensToSmallEtale B S hS) O)
    (fun a ↦ restrictionCommRingIso_naturality (Opens.grothendieckTopology ↥S)
      (topology B S hS) (opensToSmallEtale B S hS) a)

/-- The identification of the direct image of the structure sheaf of the small étale site along
the morphism of topoi of `ε` with its restriction along the inclusion of the small Zariski site
of `S`.  It is the identity on sections. -/
public noncomputable abbrev pushforwardStructureIso :
    (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS)).obj
        (ringedTopos B S hS).O ≅
      ((opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (ringedTopos B S hS).O :=
  (pushCommRingIso B S hS).app (ringedTopos B S hS).O

/-- **`ε = id_{small, étale, Zar} : S_étale → S_Zar` as an abstract morphism of ringed topoi.**
The underlying morphism of topoi is `AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi` and
the structure map is `AlgebraicGeometry.SmallEtale.commRingStructureMap`, read through the
identification of the abstract direct image of sheaves of commutative rings with restriction
along the inclusion of the small Zariski site of `S`. -/
public noncomputable def toZariskiAbstractRingedToposHom :
    AlgebraicGeometry.RingedToposHom (ringedTopos B S hS) S.zariskiRingedTopos where
  toToposHom := toZariskiMorphismOfTopoi B S hS
  fSharp := commRingStructureMap B S hS ≫ (pushforwardStructureIso B S hS).inv

/-- The underlying morphism of topoi of `toZariskiAbstractRingedToposHom` is
`AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi`. -/
@[simp]
public theorem toZariskiAbstractRingedToposHom_toToposHom :
    (toZariskiAbstractRingedToposHom B S hS).toToposHom = toZariskiMorphismOfTopoi B S hS := rfl

/-- The structure map of `toZariskiAbstractRingedToposHom` is
`AlgebraicGeometry.SmallEtale.commRingStructureMap` followed by the inverse of
`pushforwardStructureIso`. -/
@[simp]
public theorem toZariskiAbstractRingedToposHom_fSharp :
    (toZariskiAbstractRingedToposHom B S hS).fSharp =
      commRingStructureMap B S hS ≫ (pushforwardStructureIso B S hS).inv := rfl

/-! ### The two inverse images of sheaves of commutative rings -/

/-- **The two constructions of `ε⁻¹` on sheaves of commutative rings agree.**  On the left is
the one transported from the inverse image of sheaves of sets along the morphism of topoi, on
the right Mathlib's pullback of `CommRingCat`-valued sheaves along the continuous inclusion.
Both are left adjoint to the same direct image, by `pushCommRingIso`, and a left adjoint is
unique up to canonical isomorphism. -/
public noncomputable def invCommRingIso :
    inverseImageCommRingFunctor.{u, u, u, u + 1, u, u} (toposHom B S hS) ≅
      inverseImageCommRing B S hS :=
  Adjunction.leftAdjointUniq
    ((commRingImageAdjunction.{u, u, u, u + 1, u, u} (toposHom B S hS)).ofNatIsoRight
      (pushCommRingIso B S hS))
    (inverseImageCommRingAdjunction B S hS)

section

universe v₀ u₀ v₁ u₁

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {𝒟 : Type u₁} [Category.{v₁} 𝒟]

/-- Transposing along one of two adjunctions with the same right adjoint differs from
transposing along the other by the canonical comparison of the two left adjoints. -/
public theorem homEquiv_symm_comp_leftAdjointUniq {L₁ L₂ : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) (Y : 𝒞) (X : 𝒟) (φ : Y ⟶ R.obj X) :
    (adj₁.homEquiv Y X).symm φ =
      (Adjunction.leftAdjointUniq adj₁ adj₂).hom.app Y ≫ (adj₂.homEquiv Y X).symm φ := by
  refine (adj₁.homEquiv Y X).injective ?_
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Equiv.apply_symm_apply]

/-- Transposing along an adjunction whose right adjoint has been replaced by an isomorphic one
is transposing along the original adjunction after correcting by the isomorphism. -/
public theorem homEquiv_symm_ofNatIsoRight {L : 𝒞 ⥤ 𝒟} {R R' : 𝒟 ⥤ 𝒞} (adj : L ⊣ R)
    (iso : R ≅ R') (Y : 𝒞) (X : 𝒟) (φ : Y ⟶ R'.obj X) :
    ((adj.ofNatIsoRight iso).homEquiv Y X).symm φ =
      (adj.homEquiv Y X).symm (φ ≫ iso.inv.app X) := by
  simp [Adjunction.ofNatIsoRight, Adjunction.homEquiv_counit]

end

/-- **The inverse-image form of the structure map of `ε`, as the abstract morphism of ringed
topoi computes it, is `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`**, read through
the comparison of the two inverse images of sheaves of commutative rings.

Both are the transpose of `AlgebraicGeometry.SmallEtale.commRingStructureMap`: one along the
adjunction of the morphism of topoi, the other along Mathlib's sheaf-pullback adjunction, and
`invCommRingIso` is exactly the comparison of the two left adjoints. -/
public theorem toZariskiAbstractRingedToposHom_fSharpInverseImage :
    (toZariskiAbstractRingedToposHom B S hS).fSharpInverseImage =
      (invCommRingIso B S hS).hom.app S.zariskiCommRingSheaf ≫
        inverseImageStructureMap B S hS := by
  have h := homEquiv_symm_comp_leftAdjointUniq
    ((commRingImageAdjunction.{u, u, u, u + 1, u, u} (toposHom B S hS)).ofNatIsoRight
      (pushCommRingIso B S hS))
    (inverseImageCommRingAdjunction B S hS) S.zariskiCommRingSheaf
    (commRingStructureSheaf B S hS) (commRingStructureMap B S hS)
  have h2 := homEquiv_symm_ofNatIsoRight
    (commRingImageAdjunction.{u, u, u, u + 1, u, u} (toposHom B S hS))
    (pushCommRingIso B S hS) S.zariskiCommRingSheaf (commRingStructureSheaf B S hS)
    (commRingStructureMap B S hS)
  exact h2.symm.trans h

end AlgebraicGeometry.SmallEtale

end
