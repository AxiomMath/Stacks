module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms

/-!
# Higher direct images of modules on schemes commute with restriction to an open

[Stacks, Tag 01E5] says that higher direct images commute with restriction to an open subspace.
It is proved in this repository over a `AlgebraicGeometry.RingedSpace`, as
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`, and the statements that
consume it live over a `AlgebraicGeometry.Scheme` and use `AlgebraicGeometry.Scheme.Modules`,
`AlgebraicGeometry.Scheme.Modules.pushforward` and Mathlib's `f ∣_ V`. The two are the same
data, but not to instance search, and nothing connected them.

This file connects them: the scheme-level restriction functor *is* the ringed-space one, the
scheme-level restricted morphism *is* the ringed-space one, and therefore Tag 01E5 holds in the
scheme vocabulary — for the `ℕ`-indexed right derived functors as a natural isomorphism, and
objectwise for the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` through
`Stacks.DerivedIndexing.rightDerivedIso`. The consequence that motivates it is that vanishing of
a higher direct image after restriction to an open `V` forces the stalk to vanish at every point
of `V`, which is how part (1) of [Stacks, Tag 0E7D] follows from part (2).

## Main results

* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.structureSheafRing_eq_ringCatSheaf`,
  `...structureSheafRing_restrictToOpen_eq_ringCatSheaf`,
  `...category_modules_eq_category_sheafOfModules`: the two vocabularies' sheaves of rings, and
  the `Category` instances they generate on sheaves of modules, are equal by `rfl`.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`: the
  scheme-level and ringed-space-level restriction functors are equal.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.toShHom_morphismRestrict`: Mathlib's
  `f ∣_ V` and the ringed-space restricted morphism are equal on sheaved spaces.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso`: **[Stacks,
  Tag 01E5]** in the scheme vocabulary, for `Functor.rightDerived`, together with the two
  functor equalities `..._source` and `..._target` it is transported along.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictIso`: the same for
  `Functor.rightDerivedPlus`, as a natural isomorphism, and
  `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`: its
  component at a module, which is the spelling the consumers use.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso_hom_naturality`
  and `..._inv_naturality`: **the restriction comparison is natural in the module**, in the
  objectwise spelling.
* `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict`: a module
  whose restriction to an open vanishes has vanishing stalks on that open.
* `isZero_stalk_of_isZero_rightDerivedPlus_restrict` in the same namespace: the restriction
  comparison applied to vanishing, at a point.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_stalk_rightDerivedPlus_of_affine_base`:
  **part (1) of [Stacks, Tag 0E7D]**, granted the same vanishing over an affine base that
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isAffineOpen_vanishing_of_affine_base`
  assumes for part (2).

## Implementation notes

The two equalities are proved as equalities of a functor and of a morphism, so no choice is
involved and no `eqToHom` survives into the statement of `higherDirectImageRestrictIso`. They
are packaged as the two functor equalities `higherDirectImageRestrictIso_source` and
`higherDirectImageRestrictIso_target`, and the isomorphism is the explicit
`CategoryTheory.eqToIso` transport of the ringed-space one along them. It used to be obtained by
`rw`ing the goal instead; that is the same isomorphism, but the resulting `Eq.mpr` made every
*statement* about it unreachable — reading the ringed-space comparison back out of it needs the
`Eq.mpr` unfolded, and the kernel times out on these terms. With the transport explicit,
`Iso.trans_hom` and `CategoryTheory.eqToHom_app` compute the components, which is what the
nested-opens cocycle of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestrictionCocycle.lean` needs.

`Mathlib.Topology.Sheaves.Abelian` is imported for `TopCat.instAbelianPresheaf`, without which
`(TopCat.Presheaf.stalkFunctor Ab y).PreservesZeroMorphisms` does not synthesize and the stalk
argument cannot be stated; the stalk comparison itself is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`.

`Stacks.DerivedIndexing.rightDerivedIso` is the comparison of the `ℕ`- and `ℤ`-indexed right
derived functors. In a fixed degree it is itself a natural isomorphism, so whiskering it in on
either side gives the `ℤ`-indexed comparison as an isomorphism of functors
(`rightDerivedPlusRestrictIso`) and not merely objectwise; the objectwise comparison is defined
as its component so that the two cannot drift apart. Naturality in the module is then read off
the natural isomorphism. Its behaviour under shrinking `V` is not proved here: the identification
of restriction along `W ≤ V` with the ringed-space one, the comparison of the two transitivity
isomorphisms, the reading of this file's comparison as a transport of the ringed-space one, and
the resulting nested-opens cocycle for the `ℕ`-indexed comparison
(`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.higherDirectImageRestrictIso_ofLE`) are all
in `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestrictionCocycle.lean`.

Both theorems about `rightDerivedPlus` take the degree as an integer and convert with
`Int.toNat_of_nonneg`, so that they apply at the degree in which the tag states them.

## References

* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.AlgebraicGeometry.SchemeHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of the structure sheaf of rings

The scheme-level development states its sheaves of modules over
`AlgebraicGeometry.Scheme.ringCatSheaf` and the ringed-space development over
`Stacks.Cohomology.HigherDirectImage.structureSheafRing`.  The four lemmas here record that the
two spellings — and, for an open subscheme, the third one that the restriction functors of
`Stacks.SheafOfModules.restrictSheafOfRings` produce (see
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.restrictSheafOfRings_eq_ringCatSheaf`) — are
the *same* sheaf of rings, by `rfl`, and that the `Category` instances the two generate on
sheaves of modules are therefore equal by `rfl` as well.  Nothing has to be identified; the two
spellings already are. -/

/-- The structure sheaf of a scheme read as a sheaf of `RingCat`-valued rings is Mathlib's
`AlgebraicGeometry.Scheme.ringCatSheaf`.  Both are `X.presheaf ⋙ forget₂ CommRingCat RingCat`
packaged as a sheaf, so this is `rfl`. -/
theorem structureSheafRing_eq_ringCatSheaf (X : Scheme.{u}) :
    structureSheafRing X.toRingedSpace = X.ringCatSheaf :=
  rfl

/-- The same for an open subscheme: the structure sheaf of the open subspace of the underlying
ringed space is the structure sheaf of the open subscheme. -/
theorem structureSheafRing_restrictToOpen_eq_ringCatSheaf (X : Scheme.{u}) (V : X.Opens) :
    structureSheafRing (restrictToOpen X.toRingedSpace V) = V.toScheme.ringCatSheaf :=
  rfl

/-- **The two spellings generate the same category, with the same instance.**  The `Category`
instance Mathlib puts on `AlgebraicGeometry.Scheme.Modules` — which is a structure copy of the
one on `SheafOfModules`, not that instance itself — is equal to it by `rfl`.  So a morphism
formed in either spelling may be used in the other; what must be avoided is a *composite* whose
factors were elaborated in different spellings, for which see the implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestrictionCocycle.lean`. -/
theorem category_modules_eq_category_sheafOfModules (X : Scheme.{u}) :
    (inferInstance : Category X.Modules) =
      (inferInstance : Category (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  rfl

/-- Restricting a sheaf of modules on a scheme to an open subscheme is the restriction of
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` on the underlying ringed space. The
structure sheaf of the open subscheme is the restriction of the structure sheaf definitionally,
so no change of rings intervenes on either side. -/
theorem restrictFunctor_eq_moduleRestriction (X : Scheme.{u}) (V : X.Opens) :
    Scheme.Modules.restrictFunctor V.ι = moduleRestriction X.toRingedSpace V := by
  change Scheme.Modules.restrictFunctor V.ι = restMod (asRingSheafedSpace X.toRingedSpace) V
  unfold Scheme.Modules.restrictFunctor restMod
  congr 1
  ext U
  simp [phiSh, Scheme.Opens.ι_appIso]
  rfl

/-- Mathlib's restriction `f ∣_ V` of a morphism of schemes over an open of the target induces
the ringed-space restricted morphism `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`.
Both compose with the inclusion of `V` to the same morphism, and that inclusion is a
monomorphism of sheaved spaces because it is one of presheafed spaces. -/
theorem toShHom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    (f ∣_ V).toLRSHom.toShHom = restrictedMorphism f.toLRSHom.toShHom V := by
  have hmono : Mono (openSubspaceInclusion Y.toRingedSpace V) := by
    apply (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).mono_of_mono_map
    change Mono ((Y.toRingedSpace.toPresheafedSpace).ofRestrict V.isOpenEmbedding)
    infer_instance
  apply (cancel_mono (openSubspaceInclusion Y.toRingedSpace V)).mp
  change ((f ∣_ V) ≫ V.ι).toLRSHom.toShHom =
    restrictedMorphism f.toLRSHom.toShHom V ≫ openSubspaceInclusion Y.toRingedSpace V
  rw [morphismRestrict_ι]
  change openSubspaceInclusion X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ≫
      f.toLRSHom.toShHom =
    restrictedMorphism f.toLRSHom.toShHom V ≫ openSubspaceInclusion Y.toRingedSpace V
  exact restrictedMorphism_comp_openSubspaceInclusion f.toLRSHom.toShHom V

/-- The source of the scheme-level comparison of [Stacks, Tag 01E5], in the ringed-space
vocabulary: restricting to `f⁻¹(V)` and taking the `p`-th right derived functor of the
pushforward along `f ∣_ V` is the ringed-space composite for the restricted morphism. This is
the two equalities above, read in the one place where `higherDirectImageRestrictIso` needs
them. -/
theorem higherDirectImageRestrictIso_source {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p =
      moduleRestriction X.toRingedSpace (preimageOpen f.toLRSHom.toShHom V) ⋙
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).rightDerived p := by
  rw [restrictFunctor_eq_moduleRestriction X (f ⁻¹ᵁ V)]
  change moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p = _
  rw [toShHom_morphismRestrict f V]
  rfl

/-- The target of the scheme-level comparison of [Stacks, Tag 01E5], in the ringed-space
vocabulary: taking the `p`-th higher direct image along `f` and restricting to `V` is the
ringed-space composite. -/
theorem higherDirectImageRestrictIso_target {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (p : ℕ) :
    (Scheme.Modules.pushforward f).rightDerived p ⋙ Scheme.Modules.restrictFunctor V.ι =
      (modulePushforward f.toLRSHom.toShHom).rightDerived p ⋙
        moduleRestriction Y.toRingedSpace V := by
  rw [restrictFunctor_eq_moduleRestriction Y V]
  rfl

/-- **[Stacks, Tag 01E5] for schemes.** Restricting a sheaf of modules on `X` to `f⁻¹(V)` and
taking the `p`-th higher direct image along `f ∣_ V` agrees with taking the `p`-th higher direct
image along `f` and restricting to `V`, naturally in the module.

This is the ringed-space statement
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso` read through the two
equalities above. -/
noncomputable def higherDirectImageRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerived p ≅
      (Scheme.Modules.pushforward f).rightDerived p ⋙ Scheme.Modules.restrictFunctor V.ι := by
  rw [restrictFunctor_eq_moduleRestriction X (f ⁻¹ᵁ V), restrictFunctor_eq_moduleRestriction Y V]
  change moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
      (modulePushforward (f ∣_ V).toLRSHom.toShHom).rightDerived p ≅
    (modulePushforward f.toLRSHom.toShHom).rightDerived p ⋙ moduleRestriction Y.toRingedSpace V
  rw [toShHom_morphismRestrict f V]
  exact Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
    f.toLRSHom.toShHom V p

/-- **An isomorphism transported along three rewrites and a `change` is the conjugate by
`eqToIso`.**  The left-hand side is the shape of the term the tactic block defining
`higherDirectImageRestrictIso` elaborates to: two outer casts from its first `rw`, the `id` of
its `change`, and one cast from its second `rw`.  At variables the casts are removed by `subst`. -/
theorem mpr_mpr_id_mpr_iso {D : Type*} [Category D] {A B A₁ B₁ A₂ B₂ A₃ B₃ : D}
    (hA : A = A₃) (hB : B = B₃) (h₁ : (A ≅ B) = (A₁ ≅ B₁)) (h₂ : (A₁ ≅ B₁) = (A₂ ≅ B₂))
    (k : (A₂ ≅ B₂) = (A₃ ≅ B₃)) (x : A₃ ≅ B₃) :
    h₁.mpr (h₂.mpr (id (k.mpr x))) = eqToIso hA ≪≫ x ≪≫ eqToIso hB.symm := by
  subst hA; subst hB
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  simp only [eq_mpr_eq_cast, id_eq, cast_cast, cast_eq]

/-- **The scheme-level comparison of [Stacks, Tag 01E5] is the ringed-space one conjugated by
the two functor equalities** `higherDirectImageRestrictIso_source` and
`higherDirectImageRestrictIso_target`.

`higherDirectImageRestrictIso` is defined by rewriting along those equalities; this records the
result as an equation, proved once by matching the shape of that definition against
`mpr_mpr_id_mpr_iso`, so that a consumer computes with `eqToIso` and never unfolds the
definition. -/
theorem higherDirectImageRestrictIso_eq_eqToIso_trans {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (p : ℕ) :
    higherDirectImageRestrictIso f V p =
      eqToIso (higherDirectImageRestrictIso_source f V p) ≪≫
        Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso
          f.toLRSHom.toShHom V p ≪≫
        eqToIso (higherDirectImageRestrictIso_target f V p).symm := by
  unfold higherDirectImageRestrictIso
  exact mpr_mpr_id_mpr_iso (higherDirectImageRestrictIso_source f V p)
    (higherDirectImageRestrictIso_target f V p) _ _ _ _

/-- **[Stacks, Tag 01E5] for schemes, in the `ℤ`-indexed derived functors, as a natural
isomorphism.** The comparison `higherDirectImageRestrictIso` is between `ℕ`-indexed derived
functors, and `Stacks.DerivedIndexing.rightDerivedIso` changes the index type; in each fixed
degree that change is itself a natural isomorphism, so whiskering it in on either side carries
the comparison over to `CategoryTheory.Functor.rightDerivedPlus` as a comparison of functors
and not only objectwise.

That is what makes the comparison usable in a construction which has to vary the module: see
`rightDerivedPlusRestrictObjIso_hom_naturality`. -/
noncomputable def rightDerivedPlusRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) :
    Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        (Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ) ≅
      (Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ) ⋙
        Scheme.Modules.restrictFunctor V.ι :=
  Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι)
      (Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (f ∣_ V)) p).symm ≪≫
    higherDirectImageRestrictIso f V p ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p)
      (Scheme.Modules.restrictFunctor V.ι)

/-- **[Stacks, Tag 01E5] for schemes, in the `ℤ`-indexed derived functors.** The restriction
comparison of `higherDirectImageRestrictIso` for `CategoryTheory.Functor.rightDerivedPlus` at a
natural-number degree, objectwise. -/
noncomputable def rightDerivedPlusRestrictObjIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) (F : X.Modules) :
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) :=
  ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (f ∣_ V)) p).app
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).symm ≪≫
    (higherDirectImageRestrictIso f V p).app F ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) p).app F)

/-- **The component of a conjugate of a natural isomorphism by two whiskered ones**, at
variables. -/
theorem whiskerConj_app {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ B) {P P' : B ⥤ D} {Q Q' : A ⥤ C} (R : C ⥤ D) (ρ : P' ≅ P) (σ : Q' ≅ Q)
    (α : L ⋙ P' ≅ Q' ⋙ R) (F : A) :
    (Functor.isoWhiskerLeft L ρ.symm ≪≫ α ≪≫ Functor.isoWhiskerRight σ R).app F =
      (ρ.app (L.obj F)).symm ≪≫ α.app F ≪≫ R.mapIso (σ.app F) :=
  Iso.ext rfl

/-- **The objectwise comparison is the component of the natural one.**  Both are the same
three-factor composite, objectwise and as natural isomorphisms, so a statement proved about
either holds of the other. -/
theorem rightDerivedPlusRestrictObjIso_eq_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) (F : X.Modules) :
    rightDerivedPlusRestrictObjIso f V p F = (rightDerivedPlusRestrictIso f V p).app F := by
  unfold rightDerivedPlusRestrictObjIso rightDerivedPlusRestrictIso
  exact (whiskerConj_app _ _ _ _ _ F).symm

/-- **The restriction comparison is natural in the module.** For `φ : F ⟶ F'`, restricting to
`f⁻¹(V)` and taking the `p`-th higher direct image along `f ∣_ V` agrees with taking the `p`-th
higher direct image along `f` and restricting to `V`, compatibly with `φ`.

This is `rightDerivedPlusRestrictIso` read at `φ`; it is recorded separately because consumers
meet the comparison in its objectwise spelling. -/
theorem rightDerivedPlusRestrictObjIso_hom_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) {F F' : X.Modules} (φ : F ⟶ F') :
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).map
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map φ) ≫
        (rightDerivedPlusRestrictObjIso f V p F').hom =
      (rightDerivedPlusRestrictObjIso f V p F).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).map φ) := by
  rw [rightDerivedPlusRestrictObjIso_eq_app, rightDerivedPlusRestrictObjIso_eq_app]
  exact (rightDerivedPlusRestrictIso f V p).hom.naturality φ

/-- **The restriction comparison is natural in the module, read on the inverse.** -/
theorem rightDerivedPlusRestrictObjIso_inv_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ) {F F' : X.Modules} (φ : F ⟶ F') :
    (Scheme.Modules.restrictFunctor V.ι).map
          (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).map φ) ≫
        (rightDerivedPlusRestrictObjIso f V p F').inv =
      (rightDerivedPlusRestrictObjIso f V p F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).map
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).map φ) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    rightDerivedPlusRestrictObjIso_hom_naturality]

/-- A sheaf of modules on a scheme whose restriction to an open `V` is zero has vanishing stalk
at every point of `V`: the stalk of the restriction at a point is the stalk of the module
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), and a zero object is carried to a zero
object by the additive functors to presheaves of abelian groups and to the stalk. -/
theorem isZero_stalk_of_isZero_restrict {Y : Scheme.{u}} (V : Y.Opens) (G : Y.Modules)
    (y : Y) (hy : y ∈ V) (h : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj G)) :
    IsZero (G.presheaf.stalk y) := by
  set y' : V.toScheme := ⟨y, hy⟩ with hy'
  exact (Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} y')
    (Functor.map_isZero (Scheme.Modules.toPresheaf V.toScheme) h)).of_iso
    ((Scheme.Modules.restrictStalkNatIso V.ι y').app G).symm

/-- Vanishing of the `p`-th higher direct image along `f ∣_ V` of the restriction of `F` forces
the stalk of the `p`-th higher direct image along `f` of `F` to vanish at every point of `V`. -/
theorem isZero_stalk_of_isZero_rightDerivedPlus_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (F : X.Modules) {p : ℤ} (hp : 0 ≤ p)
    (hzero : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp).symm⟩
  exact isZero_stalk_of_isZero_restrict V _ y hy
    (IsZero.of_iso hzero (rightDerivedPlusRestrictObjIso f V n F).symm)

end Stacks.AlgebraicGeometry.SchemeHigherDirectImage

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **[Stacks, Tag 0E7D] part (1), reduced to an affine base.** Granted the same vanishing
hypothesis `hvan` over an affine base that
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isAffineOpen_vanishing_of_affine_base`
assumes for part (2) — a proper morphism onto an affine scheme all of whose fibres have
dimension at most `d` has vanishing higher direct images of quasi-coherent modules above `d` —
the stalk at `y` of the `i`-th higher direct image of a quasi-coherent module vanishes for
`i > d`, whenever the fibre `X_y` has dimension at most `d`.

Part (2) produces an affine open `V ∋ y` over which the higher direct images of `f ∣_ V` vanish
above `d`; the restriction of `F` to `f⁻¹(V)` is again quasi-coherent, so this applies to it, and
`SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict` transports the
vanishing to the stalk at `y`. This is the source's remark that part (2)
"will immediately imply (1)", and with it both parts of the tag rest on `hvan` alone. -/
theorem isZero_stalk_rightDerivedPlus_of_affine_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (hvan : ∀ {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀), IsProper g → IsAffine Y₀ →
      (∀ s : Y₀, topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) := by
  obtain ⟨V, hyV, -, -, -, -, -, hV⟩ :=
    exists_isAffineOpen_vanishing_of_affine_base f y d hdim hvan
  exact SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict f V y hyV F
    ((Int.natCast_nonneg d).trans hi.le) (hV i hi _ inferInstance)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
