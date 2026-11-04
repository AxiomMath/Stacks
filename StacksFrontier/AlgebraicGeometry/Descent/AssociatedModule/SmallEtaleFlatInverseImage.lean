module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineImageCover
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of `ε = id_{small, étale, Zar} : S_étale → S_Zar`

Let `ε` be the morphism of ringed sites of Stacks 070R.  Its structure map in inverse-image
form is `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`, the morphism of sheaves of
commutative rings `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}`, and this module proves that it is flat, which
is Stacks 0GNA.

The argument is the one of the source.  Étale morphisms are open, so `ε⁻¹𝒪_{S_Zar}` is the
étale sheafification of `(f : V → S) ↦ 𝒪_S(f(V))`, over which the global functions
`V ↦ Γ(V, 𝒪_V)` form a presheaf of modules whose associated sheaf is `𝒪_{S_étale}`.  Every
object of the small étale site is covered by affine opens whose image in `S` is an affine open,
and over such an open the ring map `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is an étale ring map, hence flat.
Stacks 0GN1 — a presheaf of modules which is objectwise flat on a covering of every object has
a flat associated sheaf — concludes.

Flatness of a morphism of sheaves of commutative rings is asserted after lifting the sections
into the universe containing the small étale site, since that is where the tensor product of
sheaves of modules lives, so the whole argument is carried out for the lifted sections.

## Main definitions

* `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageRingULift`: the comparison map
  `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}` with its sections lifted.
* `AlgebraicGeometry.SmallEtale.sectionsAsImageSectionsModuleULift`: the global functions
  `V ↦ Γ(V, 𝒪_V)` with their sections lifted, as a presheaf of modules over the lifted
  `(f : V → S) ↦ 𝒪_S(f(V))`.

## Main results

* `AlgebraicGeometry.SheafOfModules.moduleFlat_compHom_commRingCatULift`: a flat ring map stays
  flat when the universe of its sections is raised.
* `AlgebraicGeometry.SmallEtale.imageSectionsRestriction_app_eq_appLE`: the restriction
  `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is the sections map of the structure morphism of `V` over its image
  open.
* `AlgebraicGeometry.SmallEtale.sheafificationIsoInverseImageStructure`: the sheafification of
  `V ↦ Γ(V, 𝒪_V)` over `(f : V → S) ↦ 𝒪_S(f(V))` is `𝒪_{S_étale}` as an `ε⁻¹𝒪_{S_Zar}`-module.
* `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`: **Stacks 0GNA**, the
  morphism of ringed sites `ε` is flat.

## References

* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Presheaf

universe w z v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {P Q : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : P ⟶ Q)

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings does
not change its equalizer sieves. -/
public theorem equalizerSieve_whiskerRight_commRingCatULift {X : Cᵒᵖ}
    (x y : ToType (((P ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z}) ⋙
      forget₂ CommRingCat.{max w z} RingCat.{max w z}).obj X)) :
    equalizerSieve (F := (P ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z}) ⋙
        forget₂ CommRingCat.{max w z} RingCat.{max w z}) x y
      = equalizerSieve (F := P) x.down y.down := by
  ext V i
  simp only [equalizerSieve_apply]
  exact ⟨fun h => congrArg ULift.down h, fun h => congrArg ULift.up h⟩

/-- Raising the universe of the sections of a morphism of presheaves of commutative rings does
not change its image sieves. -/
public theorem imageSieve_whiskerRight_commRingCatULift {X : Cᵒᵖ}
    (s : ToType (((Q ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z}) ⋙
      forget₂ CommRingCat.{max w z} RingCat.{max w z}).obj X)) :
    imageSieve (whiskerRight (whiskerRight φ
        AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z})
      (forget₂ CommRingCat.{max w z} RingCat.{max w z})) s = imageSieve φ s.down := by
  ext V i
  simp only [imageSieve_apply]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.down, congrArg ULift.down ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- Raising the universe of the sections preserves local injectivity. -/
public instance isLocallyInjective_whiskerRight_commRingCatULift [IsLocallyInjective J φ] :
    IsLocallyInjective J (whiskerRight (whiskerRight φ
        AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z})
      (forget₂ CommRingCat.{max w z} RingCat.{max w z})) where
  equalizerSieve_mem x y h := by
    rw [equalizerSieve_whiskerRight_commRingCatULift]
    exact equalizerSieve_mem J φ x.down y.down (congrArg ULift.down h)

/-- Raising the universe of the sections preserves local surjectivity. -/
public instance isLocallySurjective_whiskerRight_commRingCatULift [IsLocallySurjective J φ] :
    IsLocallySurjective J (whiskerRight (whiskerRight φ
        AlgebraicGeometry.SheafOfModules.commRingCatULift.{w, z})
      (forget₂ CommRingCat.{max w z} RingCat.{max w z})) where
  imageSieve_mem s := by
    rw [imageSieve_whiskerRight_commRingCatULift]
    exact imageSieve_mem J φ s.down

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.SheafOfModules

universe w z

/-- **A flat ring map stays flat when the universe of its sections is raised.**  The lift
changes neither the rings nor the map, only the universe their carriers live in. -/
public theorem moduleFlat_compHom_commRingCatULift {A B : CommRingCat.{w}} (φ : A ⟶ B)
    (h : φ.hom.Flat) :
    @Module.Flat ↥(commRingCatULift.{w, z}.obj A) ↥(commRingCatULift.{w, z}.obj B) _ _
      (Module.compHom ↥(commRingCatULift.{w, z}.obj B)
        (commRingCatULift.{w, z}.map φ).hom) := by
  let : Algebra A B := φ.hom.toAlgebra
  have hAB : Module.Flat A B := h
  have h2 : @Module.Flat (ULift.{z} A) (ULift.{z} B) _ _ ULift.module := by
    rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
    exact hAB
  have hinst : (ULift.module : Module (ULift.{z} A) (ULift.{z} B))
      = Module.compHom ↥(commRingCatULift.{w, z}.obj B)
        (commRingCatULift.{w, z}.map φ).hom :=
    Module.ext' _ _ fun _ _ => rfl
  exact hinst ▸ h2

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The restriction over the image open as a sections map -/

/-- **The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is the sections map of the structure morphism of
`V` over its image open.**  The structure morphism factors through its image open, and the
restriction is the identification of the sections of `𝒪_S` over that open with the functions on
it, followed by the pullback of functions along the factorization. -/
public theorem imageSectionsRestriction_app_eq_appLE (V : SmallEtale B S hS)
    (e : (⊤ : ((toScheme B S hS).obj V).Opens) ≤ V.obj.hom.hom ⁻¹ᵁ imageOpen B S hS V) :
    (imageSectionsRestriction B S hS).app (op V)
      = V.obj.hom.hom.appLE (imageOpen B S hS V) ⊤ e := by
  have h0 : (imageSectionsRestriction B S hS).app (op V)
      = (Scheme.Opens.topIso (imageOpen B S hS V)).inv ≫
        (commRingStructureSheaf B S hS).obj.map (toImageOpen B S hS V).op := rfl
  have h1 : (Scheme.Opens.topIso (imageOpen B S hS V)).inv
      = (imageOpen B S hS V).ι.appLE (imageOpen B S hS V) ⊤
        (imageOpen B S hS V).ι_preimage_self.ge := by
    rw [Scheme.Opens.ι_appLE]
    exact congrArg S.presheaf.map (Subsingleton.elim _ _)
  have h2 : (commRingStructureSheaf B S hS).obj.map (toImageOpen B S hS V).op
      = ((toImageOpen B S hS V).hom.left.hom).appTop := rfl
  have h3 : ((toImageOpen B S hS V).hom.left.hom).appTop
      = ((toImageOpen B S hS V).hom.left.hom).appLE ⊤ ⊤ (fun _ _ => trivial) :=
    (Scheme.Hom.appLE_eq_app _).symm
  revert e
  rw [BigEtaleOver.hom_hom_eq B S hS (toImageOpen B S hS V).hom]
  intro e
  rw [h0, h1, h2, h3]
  exact Scheme.Hom.appLE_comp_appLE ..

/-! ### The comparison map and the module of global functions, with lifted sections -/

/-- `ε⁻¹𝒪_{S_Zar}` with its sections lifted into the universe of the objects of the small étale
site, where the tensor product of sheaves of modules is available. -/
public noncomputable abbrev inverseImageULift :
    Sheaf (topology B S hS) CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (topology B S hS)).obj
    ((inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf)

/-- `𝒪_{S_étale}` with its sections lifted into the universe of the objects of the small étale
site. -/
public noncomputable abbrev commRingStructureSheafULift :
    Sheaf (topology B S hS) CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u} (topology B S hS)).obj (commRingStructureSheaf B S hS)

/-- The presheaf of commutative rings `(f : V → S) ↦ 𝒪_S(f(V))` with its sections lifted into
the universe of the objects of the small étale site. -/
public noncomputable abbrev imageSectionsPresheafULift :
    (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  imageSectionsPresheaf B S hS ⋙ SheafOfModules.commRingCatULift.{u, u + 1}

/-- **The comparison map `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}` with lifted sections**,
read on presheaves of not necessarily commutative rings.  This is the locally bijective map
Stacks 0GN1 takes as its first input. -/
public noncomputable abbrev imageSectionsToInverseImageRingULift :
    imageSectionsPresheafULift B S hS ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
        (inverseImageULift B S hS)).obj :=
  whiskerRight (whiskerRight (imageSectionsToInverseImage B S hS)
    SheafOfModules.commRingCatULift.{u, u + 1}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- `ε⁻¹𝒪_{S_Zar}` with lifted sections is a sheafification of the lifted
`(f : V → S) ↦ 𝒪_S(f(V))`, injective half. -/
public instance isLocallyInjective_imageSectionsToInverseImageRingULift :
    Presheaf.IsLocallyInjective (topology B S hS)
      (imageSectionsToInverseImageRingULift B S hS) :=
  Presheaf.isLocallyInjective_whiskerRight_commRingCatULift.{u, u + 1} (topology B S hS)
    (imageSectionsToInverseImage B S hS)

/-- `ε⁻¹𝒪_{S_Zar}` with lifted sections is a sheafification of the lifted
`(f : V → S) ↦ 𝒪_S(f(V))`, surjective half. -/
public instance isLocallySurjective_imageSectionsToInverseImageRingULift :
    Presheaf.IsLocallySurjective (topology B S hS)
      (imageSectionsToInverseImageRingULift B S hS) :=
  Presheaf.isLocallySurjective_whiskerRight_commRingCatULift.{u, u + 1} (topology B S hS)
    (imageSectionsToInverseImage B S hS)

/-- The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` with lifted sections, read on presheaves of not
necessarily commutative rings. -/
public noncomputable abbrev imageSectionsRestrictionRingULift :
    imageSectionsPresheafULift B S hS ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
        (commRingStructureSheafULift B S hS)).obj :=
  whiskerRight (whiskerRight (imageSectionsRestriction B S hS)
    SheafOfModules.commRingCatULift.{u, u + 1}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- **The global functions `V ↦ Γ(V, 𝒪_V)` with lifted sections, as a presheaf of modules over
the lifted `(f : V → S) ↦ 𝒪_S(f(V))`**, the module structure being restriction of scalars along
the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.  Its sheafification is the object whose flatness
Stacks 0GNA asserts. -/
public noncomputable def sectionsAsImageSectionsModuleULift :
    PresheafOfModules.{u + 1}
      (imageSectionsPresheafULift B S hS ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (PresheafOfModules.restrictScalars (imageSectionsRestrictionRingULift B S hS)).obj
    (PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
      (commRingStructureSheafULift B S hS)).obj)

/-- The comparison map followed by the lifted structure map of `ε` is the lifted restriction
`𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`: this is
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage_comp_inverseImageStructureMap` with
the universe of the sections raised. -/
public theorem imageSectionsToInverseImageRingULift_comp :
    imageSectionsToInverseImageRingULift B S hS ≫
        ((sheafCompose (topology B S hS)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((SheafOfModules.sheafULift.{u, u + 1, u} (topology B S hS)).map
            (inverseImageStructureMap B S hS))).hom
      = imageSectionsRestrictionRingULift B S hS := by
  have h2 : whiskerRight (whiskerRight (imageSectionsToInverseImage B S hS ≫
        (inverseImageStructureMap B S hS).hom) SheafOfModules.commRingCatULift.{u, u + 1})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      = imageSectionsRestrictionRingULift B S hS := by
    rw [imageSectionsToInverseImage_comp_inverseImageStructureMap]
  rw [← h2, whiskerRight_comp, whiskerRight_comp]
  rfl

/-- The global functions as a module over the lifted `(f : V → S) ↦ 𝒪_S(f(V))` are the lifted
`𝒪_{S_étale}` restricted along the comparison map: restriction of scalars along a composite is
restriction along the factors, and the composite is the restriction
`𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`. -/
public theorem forget_restrictScalars_uliftRestrictedUnit :
    (_root_.SheafOfModules.forget _ ⋙
          PresheafOfModules.restrictScalars (imageSectionsToInverseImageRingULift B S hS)).obj
        (SheafOfModules.uliftRestrictedUnit.{u, u + 1, u} (inverseImageStructureMap B S hS))
      = sectionsAsImageSectionsModuleULift B S hS := by
  have h0 : (_root_.SheafOfModules.forget _ ⋙
        PresheafOfModules.restrictScalars (imageSectionsToInverseImageRingULift B S hS)).obj
        (SheafOfModules.uliftRestrictedUnit.{u, u + 1, u} (inverseImageStructureMap B S hS))
      = (PresheafOfModules.restrictScalars (imageSectionsToInverseImageRingULift B S hS ≫
          ((sheafCompose (topology B S hS) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((SheafOfModules.sheafULift.{u, u + 1, u} (topology B S hS)).map
              (inverseImageStructureMap B S hS))).hom)).obj
        (PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1}
          (commRingStructureSheafULift B S hS)).obj) := rfl
  rw [h0, imageSectionsToInverseImageRingULift_comp]
  rfl

/-- **The sheafification of `V ↦ Γ(V, 𝒪_V)` over `(f : V → S) ↦ 𝒪_S(f(V))` is `𝒪_{S_étale}` as
an `ε⁻¹𝒪_{S_Zar}`-module.**  The presheaf of global functions is already a sheaf, so the counit
of the sheafification adjunction of presheaves of modules is an isomorphism at it. -/
public noncomputable def sheafificationIsoInverseImageStructure :
    (PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
          (imageSectionsToInverseImageRingULift B S hS)).obj
        (sectionsAsImageSectionsModuleULift B S hS)
      ≅ SheafOfModules.uliftRestrictedUnit.{u, u + 1, u} (inverseImageStructureMap B S hS) :=
  have : IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (imageSectionsToInverseImageRingULift B S hS)).counit.app
      (SheafOfModules.uliftRestrictedUnit.{u, u + 1, u} (inverseImageStructureMap B S hS))) :=
    NatIso.isIso_app_of_isIso _ _
  ((PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
        (imageSectionsToInverseImageRingULift B S hS)).mapIso
      (eqToIso (forget_restrictScalars_uliftRestrictedUnit B S hS))).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (imageSectionsToInverseImageRingULift B S hS)).counit.app _)

/-! ### Objectwise flatness on the affine-image covering -/

/-- **Étale ring maps are flat, on a member of the affine-image covering, with lifted
sections.** -/
public theorem moduleFlat_sectionsAsImageSectionsModuleULift (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T) :
    Module.Flat ((imageSectionsPresheafULift B S hS).obj
        (op ((affineImageCover B S hS T).X i)))
      ((sectionsAsImageSectionsModuleULift B S hS).obj
        (op ((affineImageCover B S hS T).X i))) := by
  have himg : imageOpen B S hS ((affineImageCover B S hS T).X i) = (i.down.2.1 : S.Opens) :=
    TopologicalSpace.Opens.ext
      ((imageOpen_coe B S hS _).trans (range_affineImageCover_X B S hS T i))
  have e : (⊤ : ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)).Opens) ≤
      ((affineImageCover B S hS T).X i).obj.hom.hom ⁻¹ᵁ
        imageOpen B S hS ((affineImageCover B S hS T).X i) :=
    fun x _ => ⟨x, rfl⟩
  have hr : ((imageSectionsRestriction B S hS).app
      (op ((affineImageCover B S hS T).X i))).hom.Flat := by
    rw [imageSectionsRestriction_app_eq_appLE B S hS _ e]
    exact ((((affineImageCover B S hS T).X i).obj.hom.hom).appLE_congr e himg rfl
      (fun φ => φ.hom.Flat)).mpr (flat_appLE_affineImageCover B S hS T i _)
  exact SheafOfModules.moduleFlat_compHom_commRingCatULift.{u, u + 1}
    ((imageSectionsRestriction B S hS).app (op ((affineImageCover B S hS T).X i))) hr

/-- **Every object of the small étale site is covered by objects over which the global functions
are flat over the sections of `𝒪_S` on the image.**  This is the hypothesis of Stacks 0GN1. -/
public theorem exists_cover_moduleFlat_sectionsAsImageSectionsModuleULift
    (T : SmallEtale B S hS) :
    ∃ (I : Type (u + 1)) (X : I → SmallEtale B S hS) (g : ∀ i, X i ⟶ T),
      Sieve.ofArrows X g ∈ topology B S hS T ∧
        ∀ i, Module.Flat ((imageSectionsPresheafULift B S hS).obj (op (X i)))
          ((sectionsAsImageSectionsModuleULift B S hS).obj (op (X i))) :=
  ⟨AffineImageIndex B S hS T, (affineImageCover B S hS T).X,
    (affineImageCover B S hS T).f, mem_topology_sieve₀_affineImageCover B S hS T,
    moduleFlat_sectionsAsImageSectionsModuleULift B S hS T⟩

/-! ### Stacks 0GNA -/

/-- **Stacks 0GNA.**  The morphism of ringed sites `ε = id_{small, étale, Zar} : S_étale → S_Zar`
is flat: `𝒪_{S_étale}` is a flat module over `ε⁻¹𝒪_{S_Zar}`, the flatness being asserted for
the structure map `AlgebraicGeometry.SmallEtale.inverseImageStructureMap` of `ε` in
inverse-image form.

This is also the first assertion of **Stacks 08H8**, which states exactly that the `ε` of
Equation 75.4.0.1 — `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`, carrying Stacks
08H7 — is a flat morphism of ringed sites, and cites Descent, Lemma 35.10.1, which is 0GNA,
for it.  The second assertion of 08H8, exactness of `ε^*`, is carried by
`AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariski`.  The third, the
implication `ε^*𝓕 = 0 ⟹ 𝓕 = 0`, is *not* carried by this statement and is not available in
the library; the attribute clause records that scope. -/
@[stacks 0GNA, stacks 08H8 "the flatness assertion: `ε` is a flat morphism of ringed sites.
  The exactness of `ε^* : Mod(𝒪_X) → Mod(𝒪_étale)` is carried by
  `AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariski`; the faithfulness
  assertion `ε^*𝓕 = 0 ⟹ 𝓕 = 0` is not carried here and is not in the library"]
public theorem isFlatMapULift_inverseImageStructureMap :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u}
      (inverseImageStructureMap B S hS) := by
  refine SheafOfModules.isFlatMapULift_of_isFlatULift_of_iso
    (inverseImageStructureMap B S hS) ?_ (sheafificationIsoInverseImageStructure B S hS)
  exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat
    (topology B S hS) (imageSectionsToInverseImageRingULift B S hS)
    (sectionsAsImageSectionsModuleULift B S hS)
    (exists_cover_moduleFlat_sectionsAsImageSectionsModuleULift B S hS)

end AlgebraicGeometry.SmallEtale

end
