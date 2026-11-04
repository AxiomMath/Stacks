module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedKoszulGenerator

/-!
# Perfect objects on an affine scheme stay perfect on its represented algebraic space

Let `A` be a ring and let `T` be the object `Spec A` of the big fppf site. For a perfect object
`E` of `D(𝒪_{Spec A})`, the object `ε^*E` of `D(𝒪_{h_T})`, the pullback to the small étale site
of the represented algebraic space `h_T`, is perfect. This is the direction "`E` perfect ⟹ `ε^*E`
perfect" of Stacks 08HG, read on the small étale site of the algebraic space `h_T` (rather than on
the small étale site of the scheme, where
`AlgebraicGeometry.SmallEtale.perfectToAssociatedModule_of_slice_exact` proves it), for an affine
scheme `T`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule_Q_tilde`: for a bounded
  complex `C` of finite projective `A`-modules, `ε^*(C̃)` is perfect.
* `AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule_of_isPerfect`: for a
  perfect object `E` of `D(𝒪_{Spec A})`, `ε^*E` is perfect.
* `AlgebraicGeometry.Space.representedTildeFullyFaithful`: the functor `M ↦ ε^*(M̃)` from
  `A`-modules to modules on the small étale site of `h_T` is fully faithful.
* `AlgebraicGeometry.Space.exists_isPerfect_tilde_iso_of_isStrictlyPerfect`: conversely, if
  `ε^*E` is represented by a (global) strictly perfect complex and `E` has quasi-coherent
  cohomology, then `E = M̃` for a perfect object `M` of `D(A)`.

## Implementation notes

The functor `M ↦ ε^*(M̃)` from `A`-modules to modules on the small étale site of `h_T` is additive,
right exact and carries `A` to the structure sheaf, so it carries a bounded complex of finite
projective modules to a strictly perfect complex. A perfect object of `D(𝒪_{Spec A})` has
quasi-coherent cohomology, so it is `M̃` for an object `M` of `D(A)` (Stacks 06Z0), which is
perfect by Stacks 08EB, that is, represented by a bounded complex of finite projective modules.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- **`ε^*` of a bounded complex of finite projective modules is perfect.** For a bounded
complex `C` of finite projective `A`-modules, the image under `ε^* : D(𝒪_{Spec A}) ⥤ D(𝒪_{h_T})`
of the complex of associated sheaves `C̃` is a perfect object: it is represented by the image of
`C` under the additive right exact functor `M ↦ ε^*(M̃)`, which carries `A` to the structure
sheaf, and that complex is strictly perfect. -/
theorem isPerfect_representedDerivedAssociatedModule_Q_tilde
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (hb : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i)) :
    (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj
        (DerivedCategory.Q.obj
          (((tilde.functor (CommRingCat.of A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            C))) := by
  let T := BigFppfOver.mk B S hS hA p
  let ε : (Spec (CommRingCat.of A)).Modules ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  let Φ : ModuleCat.{u} A ⥤
      Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    tilde.functor (CommRingCat.of A) ⋙ ε
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  have : (tilde.functor (CommRingCat.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : ε.Additive := additive_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits ε :=
    preservesFiniteColimits_representedAssociatedModule B S hS T _
  have : Φ.Additive := inferInstanceAs (tilde.functor (CommRingCat.of A) ⋙ ε).Additive
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  have : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS T _
  have : PreservesFiniteColimits Φ := comp_preservesFiniteColimits _ _
  let e : Φ.obj (ModuleCat.of A A) ≅ SheafOfModules.unit _ :=
    ε.mapIso tildeSelf ≪≫ (representedModulePushforward B S hS T).mapIso
      (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property))
  exact ⟨(Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C,
    RingedSite.isPerfectComplex_of_isStrictlyPerfect _ _
      (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
        Φ e hb hfin hproj),
    ⟨DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl Φ) (ComplexShape.up ℤ)).app C).symm ≪≫
      (ε.mapDerivedCategoryFactors.app _).symm⟩⟩

/-- **`ε^*` of a perfect object of `D(𝒪_{Spec A})` is perfect.** Let `E` be a perfect object of
`D(𝒪_{Spec A})`. Then `ε^*E` is a perfect object of `D(𝒪_{h_T})`: `E` has quasi-coherent
cohomology, hence is `M̃` for some `M` in `D(A)`, which is perfect by Stacks 08EB and so is
represented by a bounded complex of finite projective modules. -/
theorem isPerfect_representedDerivedAssociatedModule_of_isPerfect
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of A)).toRingedSpace) E) :
    (smallEtaleRingedSite B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
        (isAlgebraicSpace_yoneda B S hS _)).IsPerfect
      ((representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj E) := by
  obtain ⟨M, ⟨eM⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory
    (CommRingCat.of A) E
    (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ E hE)
  obtain ⟨C, a, b, ha, hb, hfin, hproj, ⟨eC⟩⟩ := (isPerfect_tilde_iff M).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec (CommRingCat.of A)).toRingedSpace) eM.symm hE)
  have hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite := by
    refine Set.Finite.subset (Set.finite_Icc a b) fun i hi => ?_
    simp only [Set.mem_setOf_eq] at hi
    refine Set.mem_Icc.2 ⟨?_, ?_⟩ <;> by_contra hcon
    · exact hi (C.isZero_of_isStrictlyGE a i (by lia))
    · exact hi (C.isZero_of_isStrictlyLE b i (by lia))
  obtain ⟨F, hF, ⟨eF⟩⟩ := isPerfect_representedDerivedAssociatedModule_Q_tilde B S hS hA p C hbd
    hfin hproj
  exact ⟨F, hF, ⟨eF ≪≫ (representedDerivedAssociatedModule B S hS
    (BigFppfOver.mk B S hS hA p)).mapIso
      ((((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors).app C).symm ≪≫
        (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eC.symm ≪≫ eM)⟩⟩

/-! ### The converse for a globally strictly perfect complex -/

/-- The functor `M ↦ ε^*(M̃)` from `A`-modules to modules on the small étale site of `h_T`, for
`T` the object `Spec A` of the big fppf site. -/
def representedTilde : ModuleCat.{u} A ⥤
    Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _) :=
  tilde.functor (CommRingCat.of A) ⋙
    representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)
      (isAlgebraicSpace_yoneda B S hS _)

/-- The functor `M ↦ ε^*(M̃)` from `A`-modules to modules on the small étale site of `h_T` is
additive. -/
instance representedTilde_additive : (representedTilde B S hS hA p).Additive := by
  have : (tilde.functor (CommRingCat.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let ε : (Spec (CommRingCat.of A)).Modules ⥤ Modules.{u, u} B S hS
      (yoneda.obj (BigFppfOver.mk B S hS hA p)) (isAlgebraicSpace_yoneda B S hS _) :=
    representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p) _
  have : ε.Additive := additive_representedAssociatedModule B S hS _ _
  exact inferInstanceAs (tilde.functor (CommRingCat.of A) ⋙ ε).Additive

/-- The functor `M ↦ ε^*(M̃)` preserves finite colimits, that is, it is right exact. -/
instance representedTilde_preservesFiniteColimits :
    PreservesFiniteColimits (representedTilde B S hS hA p) := by
  have : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  let ε : (Spec (CommRingCat.of A)).Modules ⥤ Modules.{u, u} B S hS
      (yoneda.obj (BigFppfOver.mk B S hS hA p)) (isAlgebraicSpace_yoneda B S hS _) :=
    representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p) _
  have : PreservesFiniteColimits ε := preservesFiniteColimits_representedAssociatedModule B S hS _ _
  exact comp_preservesFiniteColimits (tilde.functor (CommRingCat.of A)) ε

/-- The functor `M ↦ ε^*(M̃)` preserves finite limits, that is, it is left exact. -/
instance representedTilde_preservesFiniteLimits :
    PreservesFiniteLimits (representedTilde B S hS hA p) := by
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  let ε : (Spec (CommRingCat.of A)).Modules ⥤ Modules.{u, u} B S hS
      (yoneda.obj (BigFppfOver.mk B S hS hA p)) (isAlgebraicSpace_yoneda B S hS _) :=
    representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p) _
  have : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS _ _
  exact comp_preservesFiniteLimits (tilde.functor (CommRingCat.of A)) ε

/-- `ε^*(Ã) ≅ 𝒪`: the functor `M ↦ ε^*(M̃)` carries `A` to the structure sheaf. -/
def representedTildeUnitIso :
    (representedTilde B S hS hA p).obj (ModuleCat.of A A) ≅ SheafOfModules.unit _ :=
  (representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)
      (isAlgebraicSpace_yoneda B S hS _)).mapIso tildeSelf ≪≫
    (representedModulePushforward B S hS (BigFppfOver.mk B S hS hA p)).mapIso
      (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hA p))
        (BigFppfOver.mk B S hS hA p).left.property))

/-- `ε^*` on derived categories, composed with the derived functor of `~`, is the derived functor
of `M ↦ ε^*(M̃)`. -/
def representedTildeMapDerivedCategoryIso :
    (tilde.functor (CommRingCat.of A)).mapDerivedCategory ⋙
        representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p) ≅
      (representedTilde B S hS hA p).mapDerivedCategory := by
  haveI : (tilde.functor (CommRingCat.of A)).Additive := ⟨by intros; exact tilde.map_add _ _⟩
  haveI : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  haveI : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  let ε : (Spec (CommRingCat.of A)).Modules ⥤ Modules.{u, u} B S hS
      (yoneda.obj (BigFppfOver.mk B S hS hA p)) (isAlgebraicSpace_yoneda B S hS _) :=
    representedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p) _
  haveI : ε.Additive := additive_representedAssociatedModule B S hS _ _
  haveI : PreservesFiniteColimits ε :=
    preservesFiniteColimits_representedAssociatedModule B S hS _ _
  haveI : PreservesFiniteLimits ε := preservesFiniteLimits_representedAssociatedModule B S hS _ _
  exact Stacks.DerivedGlueing.mapDerivedCategoryCompIso (tilde.functor (CommRingCat.of A)) ε

/-- The derived functor of `~` lands in `D_QCoh(𝒪_{Spec A})`. -/
theorem representedSchemeDerivedQcoh_tilde (M : DerivedCategory (ModuleCat.{u} A)) :
    representedSchemeDerivedQcoh B S hS (BigFppfOver.mk B S hS hA p)
      ((tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj M) := fun n =>
  AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj
    (CommRingCat.of A) M n

/-- **`M ↦ ε^*(M̃)` is fully faithful.** Placing modules in degree `0`, it is the composite of the
fully faithful functors `D(A) ⥤ D_QCoh(𝒪_{Spec A})` (Stacks 06Z0) and
`ε^* : D_QCoh(𝒪_{Spec A}) ⥤ D(𝒪_{h_T})` (Stacks 071Q), and placing in degree `0` is fully
faithful on both sides. -/
def representedTildeFullyFaithful : (representedTilde B S hS hA p).FullyFaithful := by
  let T := BigFppfOver.mk B S hS hA p
  let s := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let Fd := (tilde.functor (CommRingCat.of A)).mapDerivedCategory
  let L : ModuleCat.{u} A ⥤ (representedSchemeDerivedQcoh B S hS T).FullSubcategory :=
    ObjectProperty.lift _ (s ⋙ Fd) fun M => representedSchemeDerivedQcoh_tilde B S hS hA p _
  have hsF : (s ⋙ Fd).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful s).comp
      (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful (CommRingCat.of A))
  have hL : L.FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := (representedSchemeDerivedQcoh B S hS T).ι)
      (hsF.ofIso (ObjectProperty.liftCompιIso _ _ _).symm)
  have h2 := hL.comp (representedDerivedAssociatedModuleFullyFaithful B S hS T)
  have e : L ⋙ (representedSchemeDerivedQcoh B S hS T).ι ⋙
        representedDerivedAssociatedModule B S hS T ≅
      representedTilde B S hS hA p ⋙ DerivedCategory.singleFunctor _ 0 :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft s (representedTildeMapDerivedCategoryIso B S hS hA p) ≪≫
      (representedTilde B S hS hA p).mapDerivedCategorySingleFunctor 0
  exact Functor.FullyFaithful.ofCompFaithful (G := DerivedCategory.singleFunctor _ 0)
    (h2.ofIso e)

/-- **A direct summand of a finite free module on `h_T` is `ε^*(M̃)` for a finite projective
`A`-module `M`.** Its idempotent on `ε^*` of a finite free module comes from an idempotent on the
finite free `A`-module by full faithfulness, and idempotents split in `A`-modules. -/
theorem exists_representedTilde_iso_of_isDirectSummandOfFiniteFree
    (X : Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _))
    (hX : IsDirectSummandOfFiniteFree _ X) :
    ∃ M : ModuleCat.{u} A, Module.Finite A M ∧ Module.Projective A M ∧
      Nonempty ((representedTilde B S hS hA p).obj M ≅ X) := by
  classical
  let Φ := representedTilde B S hS hA p
  let hΦ := representedTildeFullyFaithful B S hS hA p
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ X).1 hX
  let Fn := ModuleCat.of A (ULift.{u} (Fin n) → A)
  let φ := Stacks.SheafOfModules.freeIsoMapFinitePi Φ (representedTildeUnitIso B S hS hA p)
    (ULift.{u} (Fin n))
  obtain ⟨i', r', hir'⟩ : ∃ (i' : X ⟶ Φ.obj Fn) (r' : Φ.obj Fn ⟶ X), i' ≫ r' = 𝟙 X :=
    ⟨i ≫ φ.hom, φ.inv ≫ r, by simp [hir]⟩
  let q : Fn ⟶ Fn := hΦ.preimage (r' ≫ i')
  have hq : q ≫ q = q := hΦ.map_injective (by
    rw [Φ.map_comp, hΦ.map_preimage, Category.assoc, ← Category.assoc i', hir',
      Category.id_comp])
  obtain ⟨Y, a, b, hab, hba⟩ := IsIdempotentComplete.idempotents_split Fn q hq
  have hy : b.hom ∘ₗ a.hom = LinearMap.id := congrArg ModuleCat.Hom.hom hab
  refine ⟨Y, ?_, ?_, ⟨Iso.mk (Φ.map a ≫ r') (i' ≫ Φ.map b) ?_ ?_⟩⟩
  · exact Module.Finite.of_surjective b.hom
      (Function.RightInverse.surjective (LinearMap.congr_fun hy))
  · exact Module.Projective.of_split a.hom b.hom hy
  · have : Φ.map a ≫ (r' ≫ i') ≫ Φ.map b = 𝟙 _ := by
      rw [← hΦ.map_preimage (r' ≫ i')]
      show Φ.map a ≫ Φ.map q ≫ Φ.map b = 𝟙 _
      rw [← hba, ← Φ.map_comp, ← Φ.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hab, hab, Φ.map_id]
    simpa only [Category.assoc] using this
  · have : i' ≫ Φ.map (b ≫ a) ≫ r' = 𝟙 X := by
      rw [hba, hΦ.map_preimage, ← Category.assoc, ← Category.assoc, hir', Category.id_comp, hir']
    simpa only [Φ.map_comp, Category.assoc] using this

/-- **`ε^*E` given by a strictly perfect complex forces `E` perfect.** Let `E` be an object of
`D(𝒪_{Spec A})` with quasi-coherent cohomology and let `P` be a strictly perfect complex of
modules on the small étale site of `h_T` with `ε^*E ≅ P`. Then `E ≅ M̃` for a perfect object `M`
of `D(A)`: every term of `P` is `ε^*(M̃ⁱ)` for a finite projective `Mⁱ`, the differentials come
from maps `Mⁱ ⟶ Mⁱ⁺¹` by full faithfulness, and `ε^*` reflects isomorphisms on `D_QCoh`. -/
theorem exists_isPerfect_tilde_iso_of_isStrictlyPerfect
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsQuasicoherent)
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj (BigFppfOver.mk B S hS hA p))
      (isAlgebraicSpace_yoneda B S hS _)) ℤ)
    (hP : IsStrictlyPerfect _ P)
    (e : (representedDerivedAssociatedModule B S hS (BigFppfOver.mk B S hS hA p)).obj E ≅
      DerivedCategory.Q.obj P) :
    ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
      Nonempty ((tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj M ≅ E) := by
  classical
  let Φ := representedTilde B S hS hA p
  let hΦ := representedTildeFullyFaithful B S hS hA p
  choose M hfin hproj hM using fun i =>
    exists_representedTilde_iso_of_isDirectSummandOfFiniteFree B S hS hA p (P.X i)
      (hP.termDirectSummand i)
  let φ : ∀ i, Φ.obj (M i) ≅ P.X i := fun i => (hM i).some
  let d : ∀ i j, M i ⟶ M j := fun i j => hΦ.preimage ((φ i).hom ≫ P.d i j ≫ (φ j).inv)
  have hd : ∀ i j, (representedTilde B S hS hA p).map (d i j) =
      (φ i).hom ≫ P.d i j ≫ (φ j).inv := fun i j =>
    hΦ.map_preimage _
  let C : CochainComplex (ModuleCat.{u} A) ℤ :=
    { X := M
      d := d
      shape := fun i j hij => hΦ.map_injective (by rw [hd, P.shape i j hij]; simp)
      d_comp_d' := fun i j k _ _ => hΦ.map_injective (by simp [hd]) }
  let eC : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅ P :=
    HomologicalComplex.Hom.isoOfComponents φ (fun i j _ => by
      show (φ i).hom ≫ P.d i j = (representedTilde B S hS hA p).map (d i j) ≫ (φ j).hom
      rw [hd]
      simp)
  have hb : {i : ℤ | ¬ IsZero (C.X i)}.Finite :=
    hP.bounded.subset fun i hi hz => hi <|
      (IsZero.iff_id_eq_zero _).2 (hΦ.map_injective ((hz.of_iso (φ i)).eq_of_src _ _))
  obtain ⟨a, ha⟩ := hb.bddBelow
  obtain ⟨b, hb'⟩ := hb.bddAbove
  have hCGE : C.IsStrictlyGE a := (C.isStrictlyGE_iff a).2 fun i hi =>
    by_contra fun h => (ha h).not_gt hi
  have hCLE : C.IsStrictlyLE b := (C.isStrictlyLE_iff b).2 fun i hi =>
    by_contra fun h => (hb' h).not_gt hi
  obtain ⟨e'⟩ := nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS
    (BigFppfOver.mk B S hS hA p) E _ hE
    (representedSchemeDerivedQcoh_tilde B S hS hA p (DerivedCategory.Q.obj C))
    (e ≪≫ DerivedCategory.Q.mapIso eC.symm ≪≫
      (Φ.mapDerivedCategoryFactors.app C).symm ≪≫
      ((representedTildeMapDerivedCategoryIso B S hS hA p).app _).symm)
  exact ⟨DerivedCategory.Q.obj C, ⟨C, a, b, hCGE, hCLE, hfin, hproj, ⟨Iso.refl _⟩⟩, ⟨e'.symm⟩⟩

end AlgebraicGeometry.Space
