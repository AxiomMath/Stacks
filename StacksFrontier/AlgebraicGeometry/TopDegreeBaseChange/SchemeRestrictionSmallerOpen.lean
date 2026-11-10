module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestrictionCocycle

/-!
# The middle comparison of the nested-opens cocycle, for schemes, natural in the smaller open

Let `f : X ⟶ Y` be a morphism of schemes and `W ≤ V` a nested pair of opens of `Y`. Restricting
a module on `f⁻¹(V)` along `f⁻¹(W) ≤ f⁻¹(V)` and taking the `p`-th higher direct image along
`f ∣_ W` agrees with taking the `p`-th higher direct image along `f ∣_ V` and restricting along
`W ≤ V`, naturally in the module over `f⁻¹(V)`. The middle comparison
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE` of the
nested-opens cocycle of [Stacks, Tag 01E5] in the scheme vocabulary is this comparison,
whiskered by restriction to `f⁻¹(V)` and followed by the transitivity isomorphism of restrictions
on the `X` side. Both statements hold for the `ℕ`-indexed and for the `ℤ`-indexed right derived
functors.

## Main definitions

* `Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen.restrictionOfLEIso`: **the middle
  comparison across `W ≤ V` in the scheme vocabulary, as a comparison of functors out of the
  modules over `f⁻¹(V)`**.
* `Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen.rightDerivedPlusRestrictionOfLEIso`: the
  same for the `ℤ`-indexed derived functors, and
  `...rightDerivedPlusRestrictionOfLEObjIso`: its component at a module over `f⁻¹(V)`.

## Main results

* `...rightDerivedPlusRestrictionOfLEObjIso_hom_naturality` and `..._inv_naturality`: **the
  `ℤ`-indexed middle comparison is natural in the module over `f⁻¹(V)`**, in the objectwise
  spelling.
* `Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen.higherDirectImageRestrictIsoOfLE_hom_eq`
  and `...higherDirectImageRestrictIsoOfLE_hom_app_eq`: **the scheme-level middle comparison of
  the cocycle is `restrictionOfLEIso`**, whiskered by restriction to `f⁻¹(V)` and followed by the
  scheme-level transitivity isomorphism `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` on
  the `X` side, as an equality of natural transformations and at a module on `X`.
* `...rightDerivedPlusRestrictObjIso_ofLE_eq` and `...rightDerivedPlusRestrictIsoOfLE_hom_eq`:
  **the same identification for the `ℤ`-indexed comparison**
  `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.rightDerivedPlusRestrictIsoOfLE`.
* `...whiskerLeft_transportIso_inv` and `...eq_comp_of_transport`: the left-whiskered inverse of
  a transported isomorphism, and a transported morphism compared with a composite of two
  transported ones.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen

open SchemeRestrictionCocycle (transportIso obj_eq_of_functor_eq)
open SchemeHigherDirectImage (higherDirectImageRestrictIso_source
  restrictFunctor_eq_moduleRestriction toShHom_morphismRestrict)

attribute [local instance] HasDerivedCategory.standard

/-! ### Two further readings of a transported isomorphism -/

/-- **The left-whiskered inverse of a transported isomorphism of functors**, read through an
equality of the functor it is whiskered by. -/
theorem whiskerLeft_transportIso_inv {C D E : Type*} [Category C] [Category D] [Category E]
    {K K' : C ⥤ D} (hK : K = K') {P P' Q Q' : D ⥤ E} (hP : P = P') (hQ : Q' = Q) (β : P' ≅ Q')
    (hA : K ⋙ Q = K' ⋙ Q') (hB : K' ⋙ P' = K ⋙ P) :
    Functor.whiskerLeft K (transportIso hP hQ β).inv =
      eqToHom hA ≫ Functor.whiskerLeft K' β.inv ≫ eqToHom hB := by
  subst hK hP hQ
  simp [transportIso]

/-- **One transported morphism read as a composite of two transported ones.**  Given a morphism
`w`, a composable pair `u₁`, `u₂`, and transports of all three along equalities of their sources
and targets, the identity `w = u₁ ≫ u₂` follows from the identity between the transported
morphisms. -/
theorem eq_comp_of_transport {C : Type*} [Category C] {A B D A₀ B₀ D₀ : C}
    (hA : A = A₀) (hB : B = B₀) (hD : D = D₀)
    {u₁ : A ⟶ B} {u₂ : B ⟶ D} {w : A ⟶ D} {v₁ : A₀ ⟶ B₀} {v₂ : B₀ ⟶ D₀} {z : A₀ ⟶ D₀}
    (h1 : u₁ = eqToHom hA ≫ v₁ ≫ eqToHom hB.symm)
    (h2 : u₂ = eqToHom hB ≫ v₂ ≫ eqToHom hD.symm)
    (h3 : w = eqToHom hA ≫ z ≫ eqToHom hD.symm)
    (hz : z = v₁ ≫ v₂) :
    w = u₁ ≫ u₂ := by
  subst hA hB hD
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h1 h2 h3
  rw [h1, h2, h3, hz]

/-! ### The two vocabularies, atomically -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The right derived functors of the scheme-level and of the ringed-space-level restricted
pushforward agree.** -/
theorem rightDerived_pushforward_morphismRestrict_eq (V : Y.Opens) (p : ℕ) :
    (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p =
      (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p := by
  change (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p = _
  rw [toShHom_morphismRestrict f V]
  rfl

/-- **Restriction to the preimage of an open of the target means the same thing over a scheme and
over its ringed space**, with the preimage spelled as
`Stacks.Cohomology.HigherDirectImage.preimageOpen`. -/
theorem restrictFunctor_preimage_eq_moduleRestriction (V : Y.Opens) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) :=
  restrictFunctor_eq_moduleRestriction X (f ⁻¹ᵁ V)

/-- Preimages of opens along a morphism of schemes are monotone, so a nested pair of opens of the
target has nested preimages. -/
theorem preimage_mono {W V : Y.Opens} (h : W ≤ V) : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V :=
  preimageOpen_mono f.toLRSHom.toShHom h

variable {W V : Y.Opens} (h : W ≤ V) (p : ℕ)

/-- **Restriction along the inclusion of the preimages means the same thing over a scheme and over
its ringed space**, with the inclusion spelled as
`Stacks.Cohomology.HigherDirectImage.preimageOpen_mono`. -/
theorem restrictFunctor_homOfLE_preimage_eq :
    Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) =
      moduleRestrictionOfLE X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h) :=
  SchemeRestrictionCocycle.restrictFunctor_homOfLE_eq X (preimage_mono f h)

/-! ### The middle comparison natural in the smaller open's modules -/

/-- The source of the middle comparison natural in the modules over `f⁻¹(V)`, in the ringed-space
vocabulary: restrict along `f⁻¹(W) ≤ f⁻¹(V)` and take the `p`-th higher direct image along
`f ∣_ W`. -/
theorem restrictionOfLEIso_source :
    Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p =
      moduleRestrictionOfLE X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom W)).rightDerived p := by
  rw [restrictFunctor_homOfLE_preimage_eq f h, rightDerived_pushforward_morphismRestrict_eq f W p]
  rfl

/-- The target of the middle comparison natural in the modules over `f⁻¹(V)`, in the ringed-space
vocabulary: take the `p`-th higher direct image along `f ∣_ V` and restrict along `W ≤ V`. -/
theorem restrictionOfLEIso_target :
    (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) =
      (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p ⋙
        moduleRestrictionOfLE Y.toRingedSpace h := by
  rw [SchemeRestrictionCocycle.restrictFunctor_homOfLE_eq Y h,
    rightDerived_pushforward_morphismRestrict_eq f V p]
  rfl

/-- **The middle comparison across a nested pair of opens, for schemes, natural in the modules
over `f⁻¹(V)`.**  Restricting a module on `f⁻¹(V)` along `f⁻¹(W) ≤ f⁻¹(V)` and taking the `p`-th
higher direct image along `f ∣_ W` agrees with taking the `p`-th higher direct image along
`f ∣_ V` and restricting along `W ≤ V`. -/
noncomputable def restrictionOfLEIso :
    Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p ≅
      (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) :=
  transportIso (restrictionOfLEIso_source f h p) (restrictionOfLEIso_target f h p).symm
    (higherDirectImageRestrictionOfLEIso f.toLRSHom.toShHom h p)

/-- `restrictionOfLEIso` is the `Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.transportIso`
of the ringed-space middle comparison
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictionOfLEIso`. -/
theorem restrictionOfLEIso_eq_transport :
    restrictionOfLEIso f h p =
      transportIso (restrictionOfLEIso_source f h p) (restrictionOfLEIso_target f h p).symm
        (higherDirectImageRestrictionOfLEIso f.toLRSHom.toShHom h p) :=
  rfl

/-! ### The factorisation of the cocycle's middle comparison -/

/-- The intermediate functor of the factorisation of the cocycle's middle comparison, in the
ringed-space vocabulary: restrict to `f⁻¹(V)`, restrict along `f⁻¹(W) ≤ f⁻¹(V)`, and take the
`p`-th higher direct image along `f ∣_ W`. -/
theorem restrictIsoOfLE_middle_eq :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) ⋙
          (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        moduleRestrictionOfLE X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h) ⋙
          (modulePushforward (restrictedMorphism f.toLRSHom.toShHom W)).rightDerived p := by
  rw [restrictFunctor_preimage_eq_moduleRestriction f V, restrictFunctor_homOfLE_preimage_eq f h,
    rightDerived_pushforward_morphismRestrict_eq f W p]
  rfl

/-- The source of the scheme-level transitivity isomorphism for the preimages, in the ringed-space
vocabulary. -/
theorem restrictLE_preimage_source_eq :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        moduleRestrictionOfLE X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h) := by
  rw [restrictFunctor_preimage_eq_moduleRestriction f V, restrictFunctor_homOfLE_preimage_eq f h]
  rfl

/-- The scheme-level transitivity isomorphism of restrictions for the preimages of a nested pair
of opens of the target is the transport of the ringed-space one, with the ringed-space inclusion
spelled by `Stacks.Cohomology.HigherDirectImage.preimageOpen_mono`. -/
theorem restrictLEIso_preimage_eq_transport :
    Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso (preimage_mono f h) =
      transportIso (restrictLE_preimage_source_eq f h)
        (restrictFunctor_preimage_eq_moduleRestriction f W).symm
        (moduleRestrictionOfLEIso X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h)) :=
  SchemeRestrictionCocycle.eq_transportIso_of_heq _ _
    (SchemeRestrictionCocycle.heq_restrictLEIso X (preimage_mono f h))

/-- The source of the cocycle's middle comparison, in the ringed-space vocabulary and with the
composite on the scheme side bracketed as a left whiskering produces it. -/
theorem restrictIsoOfLE_source_assoc :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ⋙
          Scheme.Modules.restrictFunctor (Y.homOfLE h) =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p ⋙
          moduleRestrictionOfLE Y.toRingedSpace h := by
  rw [restrictFunctor_preimage_eq_moduleRestriction f V,
    SchemeRestrictionCocycle.restrictFunctor_homOfLE_eq Y h,
    rightDerived_pushforward_morphismRestrict_eq f V p]
  rfl

/-- The intermediate functor of the factorisation of the cocycle's middle comparison, bracketed
as a right whiskering produces it. -/
theorem restrictIsoOfLE_middle_eq_assoc :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
          Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))) ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerived p =
      (moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
          moduleRestrictionOfLE X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h)) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom W)).rightDerived p :=
  restrictIsoOfLE_middle_eq f h p

/-- **The middle comparison of the scheme-level nested-opens cocycle is the comparison natural in
the modules over `f⁻¹(V)`**, whiskered by restriction to `f⁻¹(V)` and followed by the scheme-level
transitivity isomorphism `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` on the `X` side.
-/
theorem higherDirectImageRestrictIsoOfLE_hom_eq :
    (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE f h p).hom =
      Functor.whiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
          (restrictionOfLEIso f h p).inv ≫
        Functor.whiskerRight
          (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso (preimage_mono f h)).hom
          ((Scheme.Modules.pushforward (f ∣_ W)).rightDerived p) := by
  rw [restrictionOfLEIso_eq_transport f h p, restrictLEIso_preimage_eq_transport f h,
    SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_eq_transport f h p]
  exact eq_comp_of_transport
    (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source f h p)
    (restrictIsoOfLE_middle_eq f h p) (higherDirectImageRestrictIso_source f W p)
    (whiskerLeft_transportIso_inv (restrictFunctor_preimage_eq_moduleRestriction f V)
      (restrictionOfLEIso_source f h p) (restrictionOfLEIso_target f h p).symm
      (higherDirectImageRestrictionOfLEIso f.toLRSHom.toShHom h p)
      (restrictIsoOfLE_source_assoc f h p) (restrictIsoOfLE_middle_eq f h p).symm)
    (SchemeRestrictionCocycle.whiskerRight_transportIso_hom
      (restrictLE_preimage_source_eq f h)
      (restrictFunctor_preimage_eq_moduleRestriction f W).symm
      (moduleRestrictionOfLEIso X.toRingedSpace (preimageOpen_mono f.toLRSHom.toShHom h))
      (rightDerived_pushforward_morphismRestrict_eq f W p)
      (restrictIsoOfLE_middle_eq_assoc f h p)
      (higherDirectImageRestrictIso_source f W p).symm)
    (SchemeRestrictionCocycle.transportIso_hom
      (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE_source f h p)
      (higherDirectImageRestrictIso_source f W p).symm
      (higherDirectImageRestrictIsoSuccOfLE f.toLRSHom.toShHom h p))
    (higherDirectImageRestrictIsoSuccOfLE_hom_eq f.toLRSHom.toShHom h p)

/-- **The middle comparison of the scheme-level nested-opens cocycle is the comparison natural in
the modules over `f⁻¹(V)`, at a module on `X`.** -/
theorem higherDirectImageRestrictIsoOfLE_hom_app_eq (F : X.Modules) :
    (SchemeRestrictionCocycle.higherDirectImageRestrictIsoOfLE f h p).hom.app F =
      (restrictionOfLEIso f h p).inv.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≫
        ((Scheme.Modules.pushforward (f ∣_ W)).rightDerived p).map
          ((Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso
            (preimage_mono f h)).hom.app F) := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using NatTrans.congr_app (higherDirectImageRestrictIsoOfLE_hom_eq f h p) F

/-! ### The `ℤ`-indexed comparison -/

/-- **The middle comparison across a nested pair of opens, for schemes, in the `ℤ`-indexed derived
functors, natural in the modules over `f⁻¹(V)`**: `restrictionOfLEIso` conjugated by
`Stacks.DerivedIndexing.rightDerivedIso` on either side. -/
noncomputable def rightDerivedPlusRestrictionOfLEIso :
    Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)) ⋙
        (Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ) ≅
      (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ) ⋙
        Scheme.Modules.restrictFunctor (Y.homOfLE h) :=
  Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h)))
      (Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (f ∣_ W)) p).symm ≪≫
    restrictionOfLEIso f h p ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p)
      (Scheme.Modules.restrictFunctor (Y.homOfLE h))

/-- **The `ℤ`-indexed middle comparison at a module over `f⁻¹(V)`**: the component of
`rightDerivedPlusRestrictionOfLEIso`. -/
noncomputable def rightDerivedPlusRestrictionOfLEObjIso (M : (f ⁻¹ᵁ V).toScheme.Modules) :
    ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))).obj M) ≅
      (Scheme.Modules.restrictFunctor (Y.homOfLE h)).obj
        (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj M) :=
  (rightDerivedPlusRestrictionOfLEIso f h p).app M

/-- The backward map of the objectwise `ℤ`-indexed middle comparison is the component of the
backward map of `rightDerivedPlusRestrictionOfLEIso`. -/
theorem rightDerivedPlusRestrictionOfLEObjIso_inv (M : (f ⁻¹ᵁ V).toScheme.Modules) :
    (rightDerivedPlusRestrictionOfLEObjIso f h p M).inv =
      (rightDerivedPlusRestrictionOfLEIso f h p).inv.app M :=
  rfl

/-- **The `ℤ`-indexed middle comparison is natural in the module over `f⁻¹(V)`.**  For a morphism
`φ : M ⟶ N` of modules over `f⁻¹(V)` — which need not be the restriction of a morphism of modules
on `X` — restricting along `f⁻¹(W) ≤ f⁻¹(V)` and taking the `p`-th higher direct image along
`f ∣_ W` agrees with taking the `p`-th higher direct image along `f ∣_ V` and restricting along
`W ≤ V`, compatibly with `φ`. -/
theorem rightDerivedPlusRestrictionOfLEObjIso_hom_naturality
    {M N : (f ⁻¹ᵁ V).toScheme.Modules} (φ : M ⟶ N) :
    ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ)).map
          ((Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))).map φ) ≫
        (rightDerivedPlusRestrictionOfLEObjIso f h p N).hom =
      (rightDerivedPlusRestrictionOfLEObjIso f h p M).hom ≫
        (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).map φ) :=
  (rightDerivedPlusRestrictionOfLEIso f h p).hom.naturality φ

/-- **The `ℤ`-indexed middle comparison is natural in the module over `f⁻¹(V)`, read on the
inverse.** -/
theorem rightDerivedPlusRestrictionOfLEObjIso_inv_naturality
    {M N : (f ⁻¹ᵁ V).toScheme.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).map
          (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).map φ) ≫
        (rightDerivedPlusRestrictionOfLEObjIso f h p N).inv =
      (rightDerivedPlusRestrictionOfLEObjIso f h p M).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ)).map
          ((Scheme.Modules.restrictFunctor (X.homOfLE (preimage_mono f h))).map φ) :=
  (rightDerivedPlusRestrictionOfLEIso f h p).inv.naturality φ

/-- **The middle comparison of the `ℤ`-indexed nested-opens cocycle is
`rightDerivedPlusRestrictionOfLEIso`, at a module on `X`**: its component at `F`, followed by
the `p`-th higher direct image of the transitivity isomorphism on the `X` side. -/
theorem rightDerivedPlusRestrictObjIso_ofLE_eq (F : X.Modules) :
    (SchemeRestrictionCocycle.rightDerivedPlusRestrictIsoOfLE f h p).hom.app F =
      (rightDerivedPlusRestrictionOfLEObjIso f h p
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ)).map
          ((Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso
            (preimage_mono f h)).hom.app F) := by
  have key := higherDirectImageRestrictIsoOfLE_hom_app_eq f h p F
  have hnat := (Stacks.DerivedIndexing.rightDerivedIso
      (Scheme.Modules.pushforward (f ∣_ W)) p).hom.naturality
    ((Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso (preimage_mono f h)).hom.app F)
  rw [rightDerivedPlusRestrictionOfLEObjIso_inv]
  dsimp only [SchemeRestrictionCocycle.rightDerivedPlusRestrictIsoOfLE,
    rightDerivedPlusRestrictionOfLEIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj] at hnat ⊢
  rw [key]
  simp only [Category.assoc, hnat]

/-- **The middle comparison of the `ℤ`-indexed nested-opens cocycle is
`rightDerivedPlusRestrictionOfLEIso`**, whiskered by restriction to `f⁻¹(V)` and followed by the
transitivity isomorphism on the `X` side. -/
theorem rightDerivedPlusRestrictIsoOfLE_hom_eq :
    (SchemeRestrictionCocycle.rightDerivedPlusRestrictIsoOfLE f h p).hom =
      Functor.whiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
          (rightDerivedPlusRestrictionOfLEIso f h p).inv ≫
        Functor.whiskerRight
          (Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso (preimage_mono f h)).hom
          ((Scheme.Modules.pushforward (f ∣_ W)).rightDerivedPlus (p : ℤ)) :=
  NatTrans.ext (funext fun F => by
    rw [rightDerivedPlusRestrictObjIso_ofLE_eq f h p F,
      rightDerivedPlusRestrictionOfLEObjIso_inv]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app])

end Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen

end
