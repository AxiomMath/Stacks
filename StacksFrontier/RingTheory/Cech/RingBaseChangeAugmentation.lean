module

public import StacksFrontier.RingTheory.Cech.RingBaseChangeDerived
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Augmentation

/-!
# Augmentations of the extended alternating Čech complex under change of rings

Let `φ : A → B` be a homomorphism of commutative rings and `f₁, …, f_r ∈ A`, and write
`g_i = φ(f_i)`. The change-of-rings map of complexes of `A`-modules
$$ C^\bullet(f_1, \ldots, f_r; A) \longrightarrow C^\bullet(g_1, \ldots, g_r; B) $$
commutes with the augmentations of the two complexes onto the two rings, on the nose.

## Main results

* `Stacks.LocalCohomology.comp_restrictScalars_map_eq_comp_singleRingHom`: a map of complexes
  commutes with two augmentations onto the rings as soon as it does so in degree zero.
* `Stacks.CechRingBaseChange.extendedComplexMap_augmentation`: the change-of-rings map of the
  extended alternating Čech complexes commutes with the augmentations onto the two rings.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LocalCohomology

/-! ### The augmentation in degree zero -/

section Augmentation

variable {R : Type u} [CommRing R] {r : ℕ}

/-- In degree zero the augmentation is the identification of the degree-zero term with the
module, read with target the module itself rather than the degree-zero term of the complex
concentrated in degree zero. -/
theorem extendedCechAugmentation_f_zero_comp_singleObjXSelf (f : Fin r → R)
    (M : ModuleCat.{u} R) :
    (extendedCechAugmentation f M).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom =
      (extendedCechXZeroIso f M).hom := by
  rw [extendedCechAugmentation_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- `Stacks.LocalCohomology.cechTermZeroEquiv_lof` with the module universe pinned to the
ring's. -/
theorem cechTermZeroEquiv_lof' (f : Fin r → R) (M : ModuleCat.{u} R)
    (x : Cech.cechMod f M (default : ExtendedAlternatingCech.Idx r 0).1) :
    cechTermZeroEquiv f M (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod f M s.1) default x) =
      Stacks.CechBaseChange.cechModEmptyEquiv f M x :=
  cechTermZeroEquiv_lof f x

end Augmentation

/-! ### Augmentation squares are degree-zero statements -/

section Square

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- In degree zero, `φ` placed in degree zero is `φ`, through the identifications of the
degree-zero terms of the two complexes concentrated in degree zero with the two rings. -/
theorem singleRingHom_f_zero :
    (singleRingHom φ).f 0 =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫
          restrictedRingHom φ) ≫ (ModuleCat.restrictScalars.{u} φ).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B B)).inv := by
  have hsplit : (singleRingHom φ).f 0 =
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map (restrictedRingHom φ)).f 0 ≫
        ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{u} φ)
          (ComplexShape.up ℤ) 0).inv.app (ModuleCat.of B B)).f 0 := rfl
  rw [hsplit, singleFunctor_map_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Let `K` be a complex of `A`-modules with an augmentation `a` onto `A`, let `L` be a complex
of `B`-modules with an augmentation `b` onto `B`, and let `u : K → L` be a map of complexes of
`A`-modules. The square formed by `u`, `a`, `b` and `φ` commutes as soon as its degree-zero
component does. -/
theorem comp_restrictScalars_map_eq_comp_singleRingHom
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L)
    (a : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    (b : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
    (h : u.f 0 ≫ (ModuleCat.restrictScalars φ).map (b.f 0 ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of B B)).hom) =
          a.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A A)).hom ≫ restrictedRingHom φ) :
    u ≫ (CochainComplex.restrictScalars φ).map b = a ≫ singleRingHom φ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have hleft : (u ≫ (CochainComplex.restrictScalars φ).map b).f 0 =
        u.f 0 ≫ (ModuleCat.restrictScalars.{u} φ).map (b.f 0) := rfl
    have hright : (a ≫ singleRingHom φ).f 0 = a.f 0 ≫ (singleRingHom φ).f 0 := rfl
    rw [hleft, hright, singleRingHom_f_zero]
    refine ((Iso.eq_comp_inv ((ModuleCat.restrictScalars.{u} φ).mapIso _)).2 ?_).trans
      (Category.assoc _ _ _)
    exact (Category.assoc _ _ _).trans
      ((congrArg (u.f 0 ≫ ·) (Functor.map_comp _ _ _).symm).trans h)
  · exact (Functor.map_isZero (ModuleCat.restrictScalars φ)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of B B) n hn)).eq_of_tgt _ _

end Square

end Stacks.LocalCohomology

namespace Stacks.CechRingBaseChange

open Stacks.LocalCohomology

variable {A B : Type u} [CommRing A] [CommRing B] {r : ℕ}

/-! ### Degree zero -/

/-- The change-of-rings map is `φ` on the degree-zero Čech term, through the identifications of
that term with the two rings. -/
theorem cechTermZeroEquiv_termMap (φ : A →+* B) (f : Fin r → A) (x : Cech.cechTerm f A 0) :
    cechTermZeroEquiv (mapFamily φ f) (ModuleCat.of B B) (termMap φ f 0 x) =
      φ (cechTermZeroEquiv f (ModuleCat.of A A) x) := by
  have key : (restrictHom φ (ModuleCat.ofHom
        (cechTermZeroEquiv (mapFamily φ f) (ModuleCat.of B B)).toLinearMap)).comp
        (termMap φ f 0) =
      (ofRingHom φ).comp (cechTermZeroEquiv f (ModuleCat.of A A)).toLinearMap := by
    refine DirectSum.linearMap_ext A fun s => LinearMap.ext fun y => ?_
    obtain rfl : s = default := Subsingleton.elim _ _
    change cechTermZeroEquiv (mapFamily φ f) (ModuleCat.of B B)
        (termMap φ f 0 (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
          (fun t ↦ Cech.cechMod f (ModuleCat.of A A) t.1) default y)) =
      φ (cechTermZeroEquiv f (ModuleCat.of A A)
        (DirectSum.lof A (ExtendedAlternatingCech.Idx r 0)
          (fun t ↦ Cech.cechMod f (ModuleCat.of A A) t.1) default y))
    refine Eq.trans (congrArg (cechTermZeroEquiv (mapFamily φ f) (ModuleCat.of B B))
      (termMap_lof φ f 0 default y)) ?_
    refine Eq.trans (cechTermZeroEquiv_lof' (mapFamily φ f) (ModuleCat.of B B) _) ?_
    refine Eq.trans (cechModEmptyEquiv_modMap φ f y) ?_
    exact congrArg φ (cechTermZeroEquiv_lof' f (ModuleCat.of A A) y).symm
  exact LinearMap.congr_fun key x

/-- The change-of-rings map is `φ` in degree zero, through the identifications of the
degree-zero terms of the two `ℕ`-indexed Čech complexes with the two rings. -/
theorem complexMap_f_zero_comp_cechZeroIso (φ : A →+* B) (f : Fin r → A) :
    (complexMap φ f).f 0 ≫ (ModuleCat.restrictScalars φ).map
        (cechZeroIso (mapFamily φ f) (ModuleCat.of B B)).hom =
      (cechZeroIso f (ModuleCat.of A A)).hom ≫ restrictedRingHom φ :=
  ModuleCat.hom_ext (LinearMap.ext fun x => cechTermZeroEquiv_termMap φ f x)

/-- The change-of-rings map is `φ` in degree zero, through the identifications of the
degree-zero terms of the two integer-indexed Čech complexes with the two rings. -/
theorem extendedComplexMap_f_zero_comp_extendedCechXZeroIso (φ : A →+* B) (f : Fin r → A) :
    (extendedComplexMap φ f).f 0 ≫ (ModuleCat.restrictScalars φ).map
        (extendedCechXZeroIso (mapFamily φ f) (ModuleCat.of B B)).hom =
      (extendedCechXZeroIso f (ModuleCat.of A A)).hom ≫ restrictedRingHom φ := by
  have hzero : (extendedComplexMap φ f).f 0 =
      (extendXZeroIso f (ModuleCat.of A A)).hom ≫ (complexMap φ f).f 0 ≫
        (ModuleCat.restrictScalars φ).map (extendXZeroIso (mapFamily φ f)
          (ModuleCat.of B B)).inv :=
    HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ (complexMap φ f)
      ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero
  rw [hzero, extendedCechXZeroIso_hom, extendedCechXZeroIso_hom, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc]
  rw [complexMap_f_zero_comp_cechZeroIso]

/-! ### Condition (a) -/

/-- For a ring map `φ : A → B` and a finite family `f₁, …, f_r ∈ A` with images
`g_i = φ(f_i)`, the change-of-rings map of complexes of `A`-modules
`C^•(f₁, …, f_r; A) → C^•(g₁, …, g_r; B)` commutes with the augmentations of the two Čech
complexes onto the two rings, on the nose. -/
theorem extendedComplexMap_augmentation (φ : A →+* B) (f : Fin r → A) :
    extendedComplexMap φ f ≫ (CochainComplex.restrictScalars φ).map
        (extendedCechAugmentation (mapFamily φ f) (ModuleCat.of B B)) =
      extendedCechAugmentation f (ModuleCat.of A A) ≫ singleRingHom φ := by
  refine comp_restrictScalars_map_eq_comp_singleRingHom φ _ _ _ ?_
  rw [extendedCechAugmentation_f_zero_comp_singleObjXSelf, ← Category.assoc,
    extendedCechAugmentation_f_zero_comp_singleObjXSelf]
  exact extendedComplexMap_f_zero_comp_extendedCechXZeroIso φ f

end Stacks.CechRingBaseChange

end
