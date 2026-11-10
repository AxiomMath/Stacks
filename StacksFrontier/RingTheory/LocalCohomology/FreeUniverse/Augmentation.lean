module

public import StacksFrontier.RingTheory.Cech.ShrinkFunctor
public import StacksFrontier.RingTheory.Dualizing.ExtShrink
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Augmentation
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The Čech augmentation and its universal property, in a free module universe

Let `R` be a commutative ring in `Type u`, let `f : Fin r → R` generate the finitely generated
ideal `I`, and let `M` be an `R`-module in `Type v` with `v` *independent* of `u`. This file
carries out, for the small model `Cech.extendedCechComplexShrink` of
`StacksFrontier/RingTheory/Cech/Shrink.lean`, everything that
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean` and
`StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Augmentation.lean` do for
`Stacks.LocalCohomology.extendedCechComplex`: the augmentation onto `M` in degree zero, its
naturality in `M`, the fact that the Čech object has `I`-power-torsion cohomology, and the
universal property that makes the augmentation a coreflection.

Each of the three inputs is already available at a free module universe, which is what makes
this file short. The complex and its cohomology are
`Cech.cechComplexShrink` and `Cech.cechComplexShrink_homology_torsion_support_vanishes`; its
functoriality is `Cech.cechFunctorShrink`; the orthogonality of the terms away from degree zero
to a torsion object is
`Stacks.LocalCohomology.subsingleton_hom_singleFunctorShrink_extendedCechComplexShrink_X`; and
the stupid-filtration argument `Stacks.LocalCohomology.bijective_comp_toSingle` is stated for an
arbitrary abelian category and so needs no change at all.

## Main definitions

* `Stacks.LocalCohomology.cechTermZeroEquivFree`, `Stacks.LocalCohomology.cechTermShrinkZeroEquiv`
  — the degree-zero term of the Čech complex, and of its small model, is `M`.
* `Stacks.LocalCohomology.extendedCechAugmentationShrink`,
  `Stacks.LocalCohomology.cechAugmentationShrink` — **the augmentation of the small model onto
  `M` in degree zero**, and the natural transformation it assembles into.
* `Stacks.LocalCohomology.extendedCechObjectShrink`,
  `Stacks.LocalCohomology.extendedCechObjectFunctorShrink` — the small Čech object of the derived
  category, and its functor.
* `Stacks.LocalCohomology.cechAugmentationHomShrink` — the augmentation in the derived category,
  as a natural transformation.

## Main results

* `Stacks.LocalCohomology.extendedCechAugmentationShrink_naturality` — the augmentation of the
  small model is natural in the module.
* `Stacks.LocalCohomology.derivedPowerTorsionProperty_extendedCechObjectShrink` — **Tag 0G6K for
  the small model in the derived category**: it is an object of `D_{I^∞-torsion}(R)`.
* `Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHomShrink` — **the universal
  property of the augmentation of the small model**, at a module universe independent of the ring
  universe.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v w w' u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-! ### The degree-zero term, in free universes -/

section Zero

variable (M : Type w) (N : Type w') [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The degree-zero term of the Čech complex is `M` itself: the only index set of cardinality
zero is the empty one, and localizing at the empty product inverts nothing. This is
`Stacks.LocalCohomology.cechTermZeroEquiv` with the module universe free. -/
def cechTermZeroEquivFree : Cech.cechTerm f M 0 ≃ₗ[R] M :=
  (DirectSum.linearEquivFunOnFintype R _ _).trans
    ((LinearEquiv.piUnique (R := R)
      (fun s : ExtendedAlternatingCech.Idx r 0 => Cech.cechMod f M s.1)).trans
      (Stacks.CechBaseChange.cechModEmptyEquiv f M))

/-- On the summand indexed by the empty set the degree-zero identification is the identification
of the localization at the empty subset. -/
theorem cechTermZeroEquivFree_lof
    (x : Cech.cechMod f M (default : ExtendedAlternatingCech.Idx r 0).1) :
    cechTermZeroEquivFree f M (DirectSum.lof R (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod f M s.1) default x) =
      Stacks.CechBaseChange.cechModEmptyEquiv f M x := by
  simp [cechTermZeroEquivFree]

variable {M N}

/-- The identification of the localization at the empty subset with the module is natural, with
the two module universes independent. -/
theorem cechModEmptyEquivFree_naturality (g : M →ₗ[R] N)
    (x : Cech.cechMod f M (∅ : Finset (Fin r))) :
    Stacks.CechBaseChange.cechModEmptyEquiv f N (Cech.cechModMap f g ∅ x) =
      g (Stacks.CechBaseChange.cechModEmptyEquiv f M x) := by
  obtain ⟨m, rfl⟩ : ∃ m, x = LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M m :=
    ⟨Stacks.CechBaseChange.cechModEmptyEquiv f M x, by
      rw [← Stacks.CechBaseChange.cechModEmptyEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩
  rw [Cech.cechModMap_mkLinearMap, Stacks.CechBaseChange.cechModEmptyEquiv_mk,
    Stacks.CechBaseChange.cechModEmptyEquiv_mk]

/-- The identification of the degree-zero Čech term with the module is natural, with the two
module universes independent. -/
theorem cechTermZeroEquivFree_naturality (g : M →ₗ[R] N) (x : Cech.cechTerm f M 0) :
    cechTermZeroEquivFree f N (Cech.cechTermMap f g 0 x) =
      g (cechTermZeroEquivFree f M x) := by
  have h : (cechTermZeroEquivFree f N).toLinearMap.comp (Cech.cechTermMap f g 0) =
      g.comp (cechTermZeroEquivFree f M).toLinearMap := by
    refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun y => ?_
    obtain rfl : s = default := Subsingleton.elim _ _
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, Cech.cechTermMap_lof,
      cechTermZeroEquivFree_lof, cechTermZeroEquivFree_lof]
    exact cechModEmptyEquivFree_naturality f g y
  exact LinearMap.congr_fun h x

end Zero

section ZeroShrink

variable (M : Type w) (N : Type w') [AddCommGroup M] [Module R M] [Small.{v} M]
  [AddCommGroup N] [Module R N] [Small.{v} N]

/-- The degree-zero term of the small model of the Čech complex is `M` itself. -/
def cechTermShrinkZeroEquiv : Cech.cechTermShrink.{v} f M 0 ≃ₗ[R] M :=
  (Cech.cechTermShrinkEquiv.{v} f M 0).trans (cechTermZeroEquivFree f M)

variable {M N}

/-- The degree-zero identification of the small model is natural in the module. -/
theorem cechTermShrinkZeroEquiv_naturality (g : M →ₗ[R] N)
    (x : Cech.cechTermShrink.{v} f M 0) :
    cechTermShrinkZeroEquiv.{v} f N (Cech.cechTermShrinkMap.{v} f g 0 x) =
      g (cechTermShrinkZeroEquiv.{v} f M x) := by
  change cechTermZeroEquivFree f N (Cech.cechTermShrinkEquiv.{v} f N 0
    (Cech.cechTermShrinkMap.{v} f g 0 x)) = _
  rw [Cech.cechTermShrinkEquiv_cechTermShrinkMap, cechTermZeroEquivFree_naturality]
  rfl

end ZeroShrink

/-! ### The augmentation of the small model -/

section Augmentation

variable {M N : ModuleCat.{v} R}

/-- The degree-zero component of a map of complexes concentrated in degree zero. This is
`Stacks.LocalCohomology.singleFunctor_map_f_zero` with the module universe free. -/
theorem singleFunctor_map_f_zero_free {X Y : ModuleCat.{v} R} (φ : X ⟶ Y) :
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map φ).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ φ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv :=
  HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 φ

/-- The reindexing isomorphism of the small model in degree zero. -/
def extendXZeroIsoShrink (M : ModuleCat.{v} R) :
    (Cech.extendedCechComplexShrink.{v} f (M : Type v)).X 0 ≅
      (Cech.cechComplexShrink.{v} f (M : Type v)).X 0 :=
  HomologicalComplex.extendXIso (Cech.cechComplexShrink.{v} f (M : Type v))
    ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero

/-- The degree-zero term of the `ℕ`-indexed small model is the module. -/
def cechZeroIsoShrink (M : ModuleCat.{v} R) :
    (Cech.cechComplexShrink.{v} f (M : Type v)).X 0 ≅ ModuleCat.of R (M : Type v) :=
  (cechTermShrinkZeroEquiv.{v} f (M : Type v)).toModuleIso

/-- The degree-zero term of the integer-indexed small model is the module. -/
def extendedCechXZeroIsoShrink (M : ModuleCat.{v} R) :
    (Cech.extendedCechComplexShrink.{v} f (M : Type v)).X 0 ≅ ModuleCat.of R (M : Type v) :=
  extendXZeroIsoShrink.{v} f M ≪≫ cechZeroIsoShrink.{v} f M

/-- The degree-zero identification of the small model is natural in the module. -/
theorem extendedCechXZeroIsoShrink_naturality (g : M ⟶ N) :
    (Cech.extendedCechComplexShrinkMap.{v} f g).f 0 ≫
        (extendedCechXZeroIsoShrink.{v} f N).hom =
      (extendedCechXZeroIsoShrink.{v} f M).hom ≫ g := by
  have hmap : (Cech.extendedCechComplexShrinkMap.{v} f g).f 0 =
      (extendXZeroIsoShrink.{v} f M).hom ≫ (Cech.cechComplexShrinkMap.{v} f g).f 0 ≫
        (extendXZeroIsoShrink.{v} f N).inv :=
    HomologicalComplex.extendMap_f _ _ ComplexShape.embeddingUpNat_f_zero
  have hzero : (Cech.cechComplexShrinkMap.{v} f g).f 0 ≫ (cechZeroIsoShrink.{v} f N).hom =
      (cechZeroIsoShrink.{v} f M).hom ≫ g :=
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      cechTermShrinkZeroEquiv_naturality.{v} f g.hom x)
  rw [extendedCechXZeroIsoShrink, extendedCechXZeroIsoShrink, Iso.trans_hom, Iso.trans_hom, hmap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hzero]

/-- **The augmentation of the small model of the Čech complex.** It is the identification of the
degree-zero term with `M` in degree zero and zero elsewhere. -/
def extendedCechAugmentationShrink (M : ModuleCat.{v} R) :
    Cech.extendedCechComplexShrink.{v} f (M : Type v) ⟶
      (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M :=
  bottomProjection (Cech.extendedCechComplexShrink.{v} f (M : Type v)) 0
      (fun _ hi => Cech.isZero_extendedCechComplexShrink_X_of_neg.{v} f (M : Type v) hi) ≫
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map
      (extendedCechXZeroIsoShrink.{v} f M).hom

/-- The augmentation of the small model is invertible in degree zero. -/
theorem isIso_extendedCechAugmentationShrink_f_zero (M : ModuleCat.{v} R) :
    IsIso ((extendedCechAugmentationShrink.{v} f M).f 0) := by
  rw [extendedCechAugmentationShrink, HomologicalComplex.comp_f]
  have := isIso_bottomProjection_f (Cech.extendedCechComplexShrink.{v} f (M : Type v)) 0
    (fun _ hi => Cech.isZero_extendedCechComplexShrink_X_of_neg.{v} f (M : Type v) hi)
  infer_instance

/-- In degree zero the augmentation of the small model is the degree-zero identification. -/
theorem extendedCechAugmentationShrink_f_zero (M : ModuleCat.{v} R) :
    (extendedCechAugmentationShrink.{v} f M).f 0 =
      (extendedCechXZeroIsoShrink.{v} f M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  rw [extendedCechAugmentationShrink, HomologicalComplex.comp_f, bottomProjection,
    HomologicalComplex.mkHomToSingle_f,
    singleFunctor_map_f_zero_free.{v} (extendedCechXZeroIsoShrink.{v} f M).hom]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]

/-- **The augmentation of the small model is natural in the module.** -/
theorem extendedCechAugmentationShrink_naturality (g : M ⟶ N) :
    Cech.extendedCechComplexShrinkMap.{v} f g ≫ extendedCechAugmentationShrink.{v} f N =
      extendedCechAugmentationShrink.{v} f M ≫
        (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    extendedCechAugmentationShrink_f_zero, extendedCechAugmentationShrink_f_zero,
    singleFunctor_map_f_zero_free.{v} g]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, extendedCechXZeroIsoShrink_naturality, Category.assoc]

/-- The augmentation of the small model, as a natural transformation to the functor placing a
module in degree zero. -/
def cechAugmentationShrink :
    Cech.extendedCechFunctorShrink.{v} f ⟶ CochainComplex.singleFunctor (ModuleCat.{v} R) 0 where
  app M := extendedCechAugmentationShrink.{v} f M
  naturality _ _ g := extendedCechAugmentationShrink_naturality.{v} f g

end Augmentation

/-! ### The small Čech object of the derived category -/

section Derived

variable {M N : ModuleCat.{v} R}

/-- The small model of the extended alternating Čech complex, as an object of the derived
category of `R`, in a module universe independent of the ring universe. -/
abbrev extendedCechObjectShrink (M : ModuleCat.{v} R) : DerivedCategory (ModuleCat.{v} R) :=
  DerivedCategory.Q.obj (Cech.extendedCechComplexShrink.{v} f (M : Type v))

/-- The small Čech object of the derived category, functorially in the module. -/
def extendedCechObjectFunctorShrink :
    ModuleCat.{v} R ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Cech.extendedCechFunctorShrink.{v} f ⋙ DerivedCategory.Q

/-- The small Čech object functor at a module is the small Čech object of that module. -/
@[simp] theorem extendedCechObjectFunctorShrink_obj :
    (extendedCechObjectFunctorShrink.{v} f).obj M = extendedCechObjectShrink.{v} f M := rfl

/-- The augmentation of the small model, as a morphism of the derived category onto `M` placed in
degree zero. -/
def extendedCechAugmentationHomShrink (M : ModuleCat.{v} R) :
    extendedCechObjectShrink.{v} f M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M :=
  DerivedCategory.Q.map (extendedCechAugmentationShrink.{v} f M) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app M).inv

/-- The augmentation of the small model in the derived category, as a natural
transformation. -/
def cechAugmentationHomShrink :
    extendedCechObjectFunctorShrink.{v} f ⟶
      DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 :=
  Functor.whiskerRight (cechAugmentationShrink.{v} f) DerivedCategory.Q ≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).inv

/-- At each module the derived-category augmentation is the map of the small Čech model. -/
@[simp] theorem cechAugmentationHomShrink_app (M : ModuleCat.{v} R) :
    (cechAugmentationHomShrink.{v} f).app M = extendedCechAugmentationHomShrink.{v} f M := rfl

end Derived

/-! ### The torsion property and the universal property -/

section Universal

variable (I : Ideal R) (hI : I.FG)

/-- The integer-indexed small model vanishes outside the degrees `0, …, r`. -/
theorem isZero_extendedCechComplexShrink_X (M : ModuleCat.{v} R) (i : ℤ)
    (hi : i < 0 ∨ (r : ℤ) + 1 ≤ i) :
    IsZero ((Cech.extendedCechComplexShrink.{v} f (M : Type v)).X i) :=
  hi.elim (fun h => Cech.isZero_extendedCechComplexShrink_X_of_neg.{v} f (M : Type v) h)
    (fun h => isZero_extendedCechComplexShrink_X_of_gt.{v} f (M : Type v) (by omega))

/-- **Tag 0G6K in the derived category, at a free module universe.** The small Čech object has
`I`-power-torsion cohomology, so it is an object of `D_{I^∞-torsion}(R)`. -/
theorem derivedPowerTorsionProperty_extendedCechObjectShrink (M : ModuleCat.{v} R)
    (hIf : Ideal.span (Set.range f) = I) :
    Dualizing.derivedPowerTorsionProperty R I hI (extendedCechObjectShrink.{v} f M) := by
  classical
  have hgen : Ideal.span ((Finset.image f Finset.univ : Finset R) : Set R) = I := by
    rw [← hIf, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [SupportSurjectivity.derivedPowerTorsion_iff_localizations I hI _ hgen]
  intro g hg
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
  rw [SupportSurjectivity.derivedLocalization_isZero_iff]
  intro q
  rw [SupportSurjectivity.smallLocalization_isZero_iff]
  intro m
  have e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) q).app
    (Cech.extendedCechComplexShrink.{v} f (M : Type v))
  obtain ⟨n, -, hn⟩ :=
    (Cech.cechComplexShrink_homology_torsion_support_vanishes.{v} f (M : Type v) q).2.1 i
      (e.toLinearEquiv m)
  refine ⟨⟨f i ^ n, n, rfl⟩, e.toLinearEquiv.injective ?_⟩
  rw [map_zero]
  change e.toLinearEquiv ((f i ^ n) • m) = 0
  rw [map_smul]
  exact hn

/-- **The universal property of the augmentation of the small model.** For every object `W` of
`D(R)` with `I`-power-torsion cohomology, composing with the augmentation identifies the
morphisms from `W` to the small Čech object with the morphisms from `W` to `M`. This is
`Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom` with the constraint
`ModuleCat.{max u v}` removed. -/
theorem bijective_comp_extendedCechAugmentationHomShrink (M : ModuleCat.{v} R)
    (hIf : Ideal.span (Set.range f) = I) (W : DerivedCategory (ModuleCat.{v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun g : W ⟶ extendedCechObjectShrink.{v} f M =>
      g ≫ extendedCechAugmentationHomShrink.{v} f M) := by
  have hbase := bijective_comp_toSingle W
    (Cech.extendedCechComplexShrink.{v} f (M : Type v)) M 0 0 (r + 1)
    (extendedCechAugmentationShrink.{v} f M)
    (isIso_extendedCechAugmentationShrink_f_zero.{v} f M)
    (fun i hi => isZero_extendedCechComplexShrink_X.{v} f M i
      (by push_cast at hi ⊢; omega))
    (fun i hi q => subsingleton_hom_singleFunctorShrink_extendedCechComplexShrink_X.{v}
      f (M : Type v) I hI hIf W hW i hi q)
  set e := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app M with he
  have hpost : Function.Bijective
      (fun h : W ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{v} R) 0).obj M) => h ≫ e.inv) :=
    ⟨fun _ _ hh => (cancel_mono e.inv).1 hh, fun h => ⟨h ≫ e.hom, by simp⟩⟩
  have hcomp := hpost.comp hbase
  simpa only [Function.comp_def, extendedCechAugmentationHomShrink, Category.assoc] using hcomp

/-- **The universal property of local cohomology (Stacks 0A6Q) at a free module universe.** For
an object `W` of `D(R)` with `I`-power-torsion cohomology, composing with the counit identifies
the morphisms from `W` to `RΓ_{V(I)}(X)` with the morphisms from `W` to `X`. This is
`Stacks.LocalCohomology.bijective_comp_localCohomologyCounit` with the constraint
`ModuleCat.{max u v}` removed; the adjunction itself is already stated at a free module
universe. -/
theorem bijective_comp_localCohomologyCounitShrink
    (X W : DerivedCategory (ModuleCat.{v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W) :
    Function.Bijective (fun h : W ⟶ (Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj X) =>
      h ≫ (Dualizing.localCohomologyAdjunction R I hI).counit.app X) := by
  set P := Dualizing.derivedPowerTorsionProperty R I hI with hP
  set adj := Dualizing.localCohomologyAdjunction R I hI with hadj
  set Z := (Dualizing.localCohomologyFunctor R I hI).obj X with hZ
  have hfull : Function.Bijective
      (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g) :=
    P.fullyFaithfulι.homEquiv.bijective
  have hcomp : Function.Bijective
      (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g ≫ adj.counit.app X) := by
    have heq : (fun g : (⟨W, hW⟩ : P.FullSubcategory) ⟶ Z => P.ι.map g ≫ adj.counit.app X) =
        (adj.homEquiv ⟨W, hW⟩ X).symm := by
      funext g
      exact (adj.homEquiv_counit _ _ g).symm
    rw [heq]
    exact (adj.homEquiv ⟨W, hW⟩ X).symm.bijective
  exact (hfull.of_comp_iff _).mp hcomp

/-- **The Čech model of local cohomology at a free module universe, at a module.** The value of
`RΓ_{V(I)}` at `M` placed in degree zero is isomorphic, in `D(R)`, to the small model of the
extended alternating Čech complex, with the module universe independent of the ring universe.
This carries no `@[stacks 0A6R]` attribute, for the reason given at
`Stacks.LocalCohomology.nonempty_localCohomology_iso_extendedCechObject`. -/
theorem nonempty_localCohomology_iso_extendedCechObjectShrink (M : ModuleCat.{v} R)
    (hIf : Ideal.span (Set.range f) = I) :
    Nonempty ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)) ≅
      extendedCechObjectShrink.{v} f M) := by
  refine nonempty_iso_of_coreflection (Dualizing.derivedPowerTorsionProperty R I hI)
    (derivedPowerTorsionProperty_extendedCechObjectShrink.{v} f I hI M hIf)
    ((Dualizing.localCohomologyFunctor R I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).property
    (extendedCechAugmentationHomShrink.{v} f M)
    ((Dualizing.localCohomologyAdjunction R I hI).counit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M))
    (fun W hW => bijective_comp_extendedCechAugmentationHomShrink.{v} f I hI M hIf W hW)
    (fun W hW => ?_)
  exact bijective_comp_localCohomologyCounitShrink.{v} I hI _ W hW

end Universal

end Stacks.LocalCohomology

end
