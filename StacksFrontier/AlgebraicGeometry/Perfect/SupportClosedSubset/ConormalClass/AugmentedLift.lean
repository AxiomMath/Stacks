module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.Splice
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality

/-!
# Supported augmented complexes and their classes in local cohomology

Let `X` be a scheme, `T ⊆ X` a closed subset and `ℱ` an `𝒪_X`-module.  An `ℕ`-indexed complex
`L^•` of `𝒪_X`-modules together with a map `a : L⁰ ⟶ ℱ` is a map of complexes `L^• ⟶ ℱ[0]`.  If
the cohomology sheaves of `L^•` are supported on `T`, the counit `i_* R𝓗_T(L^•) ⟶ L^•` of
Stacks 0G72 is invertible, and inverting it gives the canonical map

`L^• ⟶ i_* R𝓗_T(ℱ)`

of Stacks 0G7L.  In degree `p` it carries the class of a `p`-cocycle `u : M ⟶ Lᵖ` to a map
`M ⟶ i_*ℋᵖ_T(ℱ)`.  This file records the two facts used to compare such classes: they are
unchanged along a map of augmented complexes, and they are natural in the coefficient module.

## Main definitions

* `Stacks.Perfect.ConormalClass.augLift`: the canonical map `L^• ⟶ i_* R𝓗_T(ℱ)`.
* `Stacks.Perfect.ConormalClass.augClass`: the class in `i_*ℋᵖ_T(ℱ)` of a `p`-cocycle.

## Main results

* `Stacks.Perfect.ConormalClass.Q_map_comp_augLift` and `augClass_comp`: a map of augmented
  complexes is compatible with the canonical maps and with the classes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.SupportedFraction (supportPush supportPushCounit supportPushSingle
  supportCohomologySheaf cocycleClass cocycleClass_comp_homologyMap comp_cocycleClass
  supportCohomologySheafMap)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Augmented complexes -/

section Augmented

variable {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)

/-- The augmentation `L^• ⟶ ℱ[0]` of an `ℕ`-indexed complex determined by a map out of its
degree-`0` term. -/
def augComplex : L ⟶ (CochainComplex.single₀ X.Modules).obj F :=
  (L.toSingle₀Equiv F).symm a

/-- The augmentation `L^• ⟶ ℱ[0]` in the derived category. -/
def augQ : DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat) ⟶
    (DerivedCategory.singleFunctor X.Modules 0).obj F :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendMap (augComplex L a) ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom)

/-- A map of augmented complexes is compatible with the augmentations. -/
theorem augComplex_comp {L' : CochainComplex X.Modules ℕ} (a' : L'.X 0 ⟶ F) (g : L ⟶ L')
    (hg : g.f 0 ≫ a' = a) : g ≫ augComplex L' a' = augComplex L a := by
  apply (L.toSingle₀Equiv F).injective
  rw [augComplex, augComplex, Equiv.apply_symm_apply]
  refine (HomologicalComplex.comp_f g ((L'.toSingle₀Equiv F).symm a') 0).trans ?_
  rw [CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact hg

/-- A map of augmented complexes is compatible with the augmentations in the derived
category. -/
theorem Q_map_comp_augQ {L' : CochainComplex X.Modules ℕ} (a' : L'.X 0 ⟶ F) (g : L ⟶ L')
    (hg : g.f 0 ≫ a' = a) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
      augQ L' a' = augQ L a := by
  rw [augQ, augQ, ← Functor.map_comp, ← Category.assoc, ← HomologicalComplex.extendMap_comp,
    augComplex_comp L a a' g hg]

end Augmented

/-! ### Naturality in the coefficient module -/

section Natural

variable {F G : X.Modules} (φ : F ⟶ G) {L L' : CochainComplex X.Modules ℕ} (a : L.X 0 ⟶ F)
  (a' : L'.X 0 ⟶ G) (g : L ⟶ L') (hg : g.f 0 ≫ a' = a ≫ φ)

include hg in
/-- The augmentation `L^• ⟶ ℱ[0]` is natural in the coefficient module. -/
theorem augComplex_natural :
    g ≫ augComplex L' a' = augComplex L a ≫ (CochainComplex.single₀ X.Modules).map φ := by
  apply (L.toSingle₀Equiv G).injective
  refine (HomologicalComplex.comp_f g ((L'.toSingle₀Equiv G).symm a') 0).trans ?_
  refine Eq.trans ?_ (HomologicalComplex.comp_f ((L.toSingle₀Equiv F).symm a)
    ((CochainComplex.single₀ X.Modules).map φ) 0).symm
  rw [CochainComplex.toSingle₀Equiv_symm_apply_f_zero,
    CochainComplex.toSingle₀Equiv_symm_apply_f_zero]
  refine hg.trans ?_
  simp [CochainComplex.single₀, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso]
  rfl

/-- The extension of a single complex in degree `0` is natural. -/
theorem extendSingleIso_natural :
    HomologicalComplex.extendMap ((CochainComplex.single₀ X.Modules).map φ)
        ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).hom ≫
        (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ := by
  let e := ComplexShape.embeddingUpNat
  have hzero : e.f 0 = 0 := rfl
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst n
    rw [HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f (φ := (CochainComplex.single₀ X.Modules).map φ)
        (e := e) (h := hzero),
      HomologicalComplex.extendSingleIso_hom_f e G 0 0 hzero, HomologicalComplex.comp_f,
      HomologicalComplex.extendSingleIso_hom_f e F 0 0 hzero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simp [CochainComplex.single₀, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn).eq_of_tgt _ _

include hg in
/-- **The augmentation is natural in the coefficient module.** -/
theorem Q_map_comp_augQ_natural :
    DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
        augQ L' a' = augQ L a ≫ (DerivedCategory.singleFunctor X.Modules 0).map φ := by
  show DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ)
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ← Category.assoc,
    ← HomologicalComplex.extendMap_comp, augComplex_natural φ a a' g hg,
    HomologicalComplex.extendMap_comp, Category.assoc, extendSingleIso_natural φ, ← Category.assoc]

end Natural

/-! ### The canonical map into local cohomology -/

section Lift

variable {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
  {T : Set X} (hT : IsClosed T)
  (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))

include hL in
/-- The counit `i_* R𝓗_T(L^•) ⟶ L^•` is invertible on a complex supported on `T`. -/
theorem isIso_supportPushCounit_of_supported :
    IsIso ((supportPushCounit hT).app
      (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat))) :=
  Stacks.Perfect.SupportedQuasicoherent.isIso_derivedSupportedSectionsToId_app_of_supported
    X.toRingedSpace T hT _ hL

/-- **The canonical map `L^• ⟶ i_* R𝓗_T(ℱ)` of Stacks 0G7L** of an augmented complex supported
on `T`: the inverse of the counit followed by `i_* R𝓗_T` of the augmentation. -/
def augLift : DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat) ⟶
    supportPushSingle hT F :=
  (@asIso _ _ _ _ _ (isIso_supportPushCounit_of_supported L hT hL)).inv ≫
    (supportPush hT).map (augQ L a)

/-- The canonical map preceded by the counit is `i_* R𝓗_T` of the augmentation. -/
theorem supportPushCounit_comp_augLift :
    (supportPushCounit hT).app (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)) ≫
      augLift L a hT hL = (supportPush hT).map (augQ L a) :=
  (@asIso _ _ _ _ _ (isIso_supportPushCounit_of_supported L hT hL)).hom_inv_id_assoc _

/-- Compatibility of a map of augmented complexes with the canonical maps, from compatibility
of the augmentations. -/
private theorem Q_map_comp_augLift_of_comp_eq {F G : X.Modules} {L L' : CochainComplex X.Modules ℕ}
    (a : L.X 0 ⟶ F) (a' : L'.X 0 ⟶ G) (g : L ⟶ L') {T : Set X} (hT : IsClosed T)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
    (hL' : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L'.extend ComplexShape.embeddingUpNat)))
    (k : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj G)
    (h : DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
      augQ L' a' = augQ L a ≫ k) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
      augLift L' a' hT hL' = augLift L a hT hL ≫ (supportPush hT).map k := by
  refine ((@asIso _ _ _ _ _ (isIso_supportPushCounit_of_supported L hT hL)).cancel_iso_hom_left
    _ _).mp ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun ψ => ψ ≫ augLift L' a' hT hL')
    ((supportPushCounit hT).naturality (DerivedCategory.Q.map
      (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat))).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun ψ => (supportPush hT).map (DerivedCategory.Q.map
      (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) ≫ ψ)
    (supportPushCounit_comp_augLift L' a' hT hL')).trans ?_
  refine ((supportPush hT).map_comp _ _).symm.trans ?_
  refine (congrArg (supportPush hT).map h).trans ?_
  refine ((supportPush hT).map_comp _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact congrArg (fun ψ => ψ ≫ (supportPush hT).map k)
    (supportPushCounit_comp_augLift L a hT hL).symm

/-- **A map of augmented complexes is compatible with the canonical maps.** -/
theorem Q_map_comp_augLift {L' : CochainComplex X.Modules ℕ} (a' : L'.X 0 ⟶ F) (g : L ⟶ L')
    (hg : g.f 0 ≫ a' = a)
    (hL' : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L'.extend ComplexShape.embeddingUpNat))) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
      augLift L' a' hT hL' = augLift L a hT hL := by
  refine (Q_map_comp_augLift_of_comp_eq a a' g hT hL hL' (𝟙 _)
    (by rw [Q_map_comp_augQ L a a' g hg, Category.comp_id])).trans ?_
  exact (congrArg (augLift L a hT hL ≫ ·) ((supportPush hT).map_id _)).trans (Category.comp_id _)

end Lift

/-! ### Classes of cocycles -/

section Class

variable {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
  {T : Set X} (hT : IsClosed T)
  (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
  (p : ℕ) {M : X.Modules} (u : M ⟶ L.X p) (hu : u ≫ L.d p (p + 1) = 0)

/-- The homology of the complex mapped into `i_*ℋᵖ_T(ℱ)` by the canonical map. -/
def augHomology : L.homology p ⟶ supportCohomologySheaf hT F (p : ℤ) :=
  (derivedHomologyExtendIso L p).inv ≫
    (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map (augLift L a hT hL)

/-- **The class in `i_*ℋᵖ_T(ℱ)` of a `p`-cocycle** of a supported augmented complex. -/
def augClass : M ⟶ supportCohomologySheaf hT F (p : ℤ) :=
  cocycleClass (CochainComplex.next ℕ p) u hu ≫ augHomology L a hT hL p

/-- Precomposing a cocycle precomposes its class. -/
theorem comp_augClass {N : X.Modules} (v : N ⟶ M) :
    v ≫ augClass L a hT hL p u hu =
      augClass L a hT hL p (v ≫ u) (by rw [Category.assoc, hu, comp_zero]) := by
  rw [augClass, augClass, ← Category.assoc, comp_cocycleClass]

/-- The homology map of a map of complexes extended to `ℤ`, read on the original complexes. -/
theorem homologyMap_comp_derivedHomologyExtendIso_inv {L' : CochainComplex X.Modules ℕ}
    (g : L ⟶ L') :
    HomologicalComplex.homologyMap g p ≫ (derivedHomologyExtendIso L' p).inv =
      (derivedHomologyExtendIso L p).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  have h1 := DerivedCategory.homologyFunctorFactors_hom_naturality
    (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) (p : ℤ)
  have h2 := HomologicalComplex.extendHomologyIso_hom_naturality g ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f p = p)
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (fun ψ => ψ ≫
      (L'.extendHomologyIso ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f p = p)).hom) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun ψ =>
      ((DerivedCategory.homologyFunctorFactors X.Modules (p : ℤ)).app _).hom ≫ ψ) h2).trans
        (Category.assoc _ _ _).symm)))).symm

/-- The class of the image of a cocycle under a map of complexes, in terms of the canonical map
of the source. -/
private theorem augClass_comp_eq {L' : CochainComplex X.Modules ℕ} (a' : L'.X 0 ⟶ F)
    (g : L ⟶ L')
    (hL' : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L'.extend ComplexShape.embeddingUpNat))) :
    augClass L' a' hT hL' p (u ≫ g.f p)
        (by rw [Category.assoc, g.comm, ← Category.assoc, hu, zero_comp]) =
      cocycleClass (CochainComplex.next ℕ p) u hu ≫ (derivedHomologyExtendIso L p).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
            augLift L' a' hT hL') := by
  rw [augClass, ← cocycleClass_comp_homologyMap g, Category.assoc, augHomology,
    ← Category.assoc (HomologicalComplex.homologyMap g p),
    homologyMap_comp_derivedHomologyExtendIso_inv, Category.assoc, Functor.map_comp]

/-- **A map of augmented complexes carries the class of a cocycle to the class of its image.** -/
theorem augClass_comp {L' : CochainComplex X.Modules ℕ} (a' : L'.X 0 ⟶ F) (g : L ⟶ L')
    (hg : g.f 0 ≫ a' = a)
    (hL' : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
      (DerivedCategory.Q.obj (L'.extend ComplexShape.embeddingUpNat))) :
    augClass L' a' hT hL' p (u ≫ g.f p)
        (by rw [Category.assoc, g.comm, ← Category.assoc, hu, zero_comp]) =
      augClass L a hT hL p u hu := by
  rw [augClass_comp_eq L hT p u hu a' g hL', Q_map_comp_augLift L a hT hL a' g hg hL', augClass,
    augHomology]

end Class

/-! ### Naturality of the classes in the coefficient module -/

section ClassNatural

variable {F G : X.Modules} (φ : F ⟶ G) {L L' : CochainComplex X.Modules ℕ} (a : L.X 0 ⟶ F)
  (a' : L'.X 0 ⟶ G) (g : L ⟶ L') (hg : g.f 0 ≫ a' = a ≫ φ) {T : Set X} (hT : IsClosed T)
  (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
  (hL' : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L'.extend ComplexShape.embeddingUpNat)))

include hg in
/-- **The canonical map is natural in the coefficient module.** -/
theorem augLift_natural :
    DerivedCategory.Q.map (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat) ≫
        augLift L' a' hT hL' =
      augLift L a hT hL ≫
        (supportPush hT).map ((DerivedCategory.singleFunctor X.Modules 0).map φ) := by
  exact Q_map_comp_augLift_of_comp_eq a a' g hT hL hL' _ (Q_map_comp_augQ_natural φ a a' g hg)

include hg in
/-- **The class of a cocycle is natural in the coefficient module.** -/
theorem augClass_natural (p : ℕ) {M : X.Modules} (u : M ⟶ L.X p) (hu : u ≫ L.d p (p + 1) = 0) :
    augClass L' a' hT hL' p (u ≫ g.f p)
        (by rw [Category.assoc, g.comm, ← Category.assoc, hu, zero_comp]) =
      augClass L a hT hL p u hu ≫ supportCohomologySheafMap hT φ (p : ℤ) := by
  rw [augClass_comp_eq L hT p u hu a' g hL', augLift_natural φ a a' g hg hT hL hL', augClass,
    augHomology, Category.assoc, Category.assoc]
  exact congrArg (fun ψ => cocycleClass (CochainComplex.next ℕ p) u hu ≫
    (derivedHomologyExtendIso L p).inv ≫ ψ)
    ((DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map_comp _ _)

end ClassNatural

/-! ### Classes on sections -/

section Sections

variable {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
  {T : Set X} (hT : IsClosed T)
  (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))

/-- A monomorphism of sheaves of modules is injective on sections. -/
theorem injective_app_of_mono {A B : X.Modules} (m : A ⟶ B) [Mono m] (U : X.Opens) :
    Function.Injective (m.app U) := by
  have h1 : Mono ((Scheme.Modules.toPresheaf X).map m) := inferInstance
  have h2 : Mono (((Scheme.Modules.toPresheaf X).map m).app (op U)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).1 h2

/-- **The class of a cocycle on a section is determined by the value of the cocycle on it.** -/
theorem augClass_app_eq (p : ℕ) {M : X.Modules} (u u' : M ⟶ L.X p)
    (hu : u ≫ L.d p (p + 1) = 0) (hu' : u' ≫ L.d p (p + 1) = 0) (U : X.Opens) (s s' : Γ(M, U))
    (h : u'.app U s = u.app U s') :
    (augClass L a hT hL p u' hu').app U s = (augClass L a hT hL p u hu).app U s' := by
  have hc : (L.liftCycles u' (p + 1) (CochainComplex.next ℕ p) hu').app U s =
      (L.liftCycles u (p + 1) (CochainComplex.next ℕ p) hu).app U s' := by
    refine injective_app_of_mono (L.iCycles p) U ?_
    have e1 := congrArg (fun ψ => ψ.app U s)
      (L.liftCycles_i u' (p + 1) (CochainComplex.next ℕ p) hu')
    have e2 := congrArg (fun ψ => ψ.app U s')
      (L.liftCycles_i u (p + 1) (CochainComplex.next ℕ p) hu)
    exact e1.trans (h.trans e2.symm)
  show (augHomology L a hT hL p).app U ((L.homologyπ p).app U
      ((L.liftCycles u' (p + 1) (CochainComplex.next ℕ p) hu').app U s)) =
    (augHomology L a hT hL p).app U ((L.homologyπ p).app U
      ((L.liftCycles u (p + 1) (CochainComplex.next ℕ p) hu).app U s'))
  rw [hc]

end Sections

end Stacks.Perfect.ConormalClass
