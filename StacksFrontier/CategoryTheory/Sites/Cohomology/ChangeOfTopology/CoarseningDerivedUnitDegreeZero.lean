module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningMorphismOfRingedSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologies
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# The derived unit in degree zero, and the unit of Stacks 07A8 for a coarsening

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi along which degreewise
pullback is exact, so that the derived adjunction `Lf^* ⊣ Rf_*` of Tag 07A6 is available. For a
sheaf `N` of `𝒪'`-modules the derived unit at `N` placed in degree zero,

`η : N[0] ⟶ Rf_*Lf^*(N[0])`,

has degree-zero cohomology the ordinary unit `N ⟶ f_*f^*N`. This file proves that and reads off
the consequence for the comparison morphism `ε` of a topology and a coarser one: the derived unit
is invertible at `N[0]` for every `N` of the class `A'` of Stacks 07A8, which is the third
hypothesis of Tag 0D7W for `ε`.

## Main results

In the namespace `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction`:

* `isIso_homology_derivedPushforwardUnit_app_single` and `derivedPushforwardZeroNatIso`:
  **`R⁰f_* = f_*`**, the comparison `f_*M ⟶ Rf_*(M[0])` being invertible on degree-zero
  cohomology.
* `isIso_homology_derivedUnit_app_singleFunctor_obj`: **`H⁰(η)` is the ordinary unit
  `N ⟶ f_*f^*N`**, hence invertible whenever that one is.
* `isIso_derivedUnit_app_singleFunctor_obj_of_isZero`: the derived unit is invertible at `N[0]`
  as soon as the ordinary unit is invertible at `N` and `Rᵖf_*Lf^*(N[0])` vanishes for `p > 0`.
* `Stacks.Cohomology.CompareTopologies.isIso_derivedUnit_app_singleFunctor_obj_imageOfLE`: **the
  unit hypothesis of Stacks 0D7W for the coarsening `ε`** — if `A` is closed under isomorphisms
  and the cohomology `H^p_τ(U, F)` vanishes for `p > 0`, `F` in `A` and `U` in a family which
  `τ'`-covers every object, then `N[0] ⟶ Rε_*Lε^*(N[0])` is invertible for every `N` of the
  image class `A'`.

## The argument

Degree zero rests on two facts. The first is that `R⁰f_*` is `f_*`: the direct image is a right
adjoint, hence left exact, and the degree-zero comparison of a right derived functor of a left
exact functor is invertible, which is
`Stacks.DerivedFunctor.isIso_singleUnitHomology_app`; its two inputs — that `Rf_*` carries
`D^{≥0}` into `D^{≥0}` and that the comparison is invertible on complexes of injectives — are
`Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj` and the existence of
K-injective resolutions over a Grothendieck abelian category. The second is the compatibility of
the derived unit with the ordinary one,
`derivedPullbackPushforwardAdjunction_unit_fac`: after composing with `Rf_*` of the comparison
map of `Lf^*` — invertible here, because degreewise pullback is exact — the derived unit at
`Qh(N[0])` is the degreewise unit followed by the comparison map of `Rf_*`. Applying `H⁰`, the
first factor is the ordinary unit (the degreewise unit of `N[0]` is an isomorphism of complexes
as soon as the ordinary unit at `N` is one, its other terms being maps of zero objects) and the
second is invertible by the first fact.

Away from degree zero both sides vanish: `N[0]` has no cohomology outside degree `0`, and
`Rf_*Lf^*(N[0])` has none below degree `0` because both derived functors preserve boundedness
below. Above degree `0` the vanishing is a hypothesis; for the coarsening it is Tag 072W, in the
form `Stacks.Cohomology.CompareTopologies.isZero_homology_derivedPushforwardCoarsening_obj`.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0D7W](https://stacks.math.columbia.edu/tag/0D7W)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

/-- A natural transformation invertible at an object is invertible at any isomorphic object. -/
private lemma isIso_app_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (η : F ⟶ G) {Z₁ Z₂ : C} (e : Z₁ ≅ Z₂) (h : IsIso (η.app Z₁)) :
    IsIso (η.app Z₂) := by
  have hη : η.app Z₂ = F.map e.inv ≫ η.app Z₁ ≫ G.map e.hom := by
    rw [← η.naturality e.hom, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id,
      Category.id_comp]
  rw [hη]
  have := h
  infer_instance

/-- The image under a functor of a natural transformation invertible at an object is invertible
at any isomorphic object. -/
private lemma isIso_map_app_of_iso {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (η : F ⟶ G) (T : D ⥤ E) {Z₁ Z₂ : C} (e : Z₁ ≅ Z₂)
    (h : IsIso (T.map (η.app Z₁))) : IsIso (T.map (η.app Z₂)) :=
  isIso_app_of_iso (Functor.whiskerRight η T) e h

/-- A morphism between two zero objects is invertible. -/
private lemma isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {Z W : C} (hZ : IsZero Z) (hW : IsZero W) (g : Z ⟶ W) : IsIso g :=
  ⟨0, hZ.eq_of_src _ _, hW.eq_of_tgt _ _⟩

/-- An object placed in degree `n` has no cohomology in any other degree. -/
private lemma isZero_homology_singleFunctor_obj_of_ne {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{u} C] (X : C) (n j : ℤ) (hj : j ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor C j).obj
      ((DerivedCategory.singleFunctor C n).obj X)) := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · exact DerivedCategory.isZero_of_isGE _ n j hlt
  · exact DerivedCategory.isZero_of_isLE _ n j hgt

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (f : RingedToposSiteHom X Y)
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **`R⁰f_* = f_*`.** The comparison `f_*M ⟶ Rf_*(M[0])` of the derived direct image is
invertible on degree-zero cohomology, because `f_*` is left exact — it is a right adjoint — and
the degree-zero comparison of a right derived functor of a left exact functor is invertible. -/
theorem isIso_homology_derivedPushforwardUnit_app_single
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
      ((derivedPushforwardUnit f).app
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj P))) := by
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hpf : PreservesFiniteLimits f.pushforwardTopos := by
    have : PreservesLimitsOfSize.{0, 0} f.pushforwardTopos :=
      f.pullbackPushforwardAdjunctionTopos.rightAdjoint_preservesLimits
    infer_instance
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardTopos
      (derivedPushforward f) (derivedPushforwardUnit f)
  have key := @Stacks.DerivedFunctor.isIso_singleUnitHomology_app
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _ _
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _ _ _
    f.pushforwardTopos _ (derivedPushforward f) (derivedPushforwardUnit f) _ _ _ hpf
    (fun _ ↦ Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj f _ 0
      inferInstance)
    (fun I hI ↦ Stacks.DerivedFunctor.isIso_unit_app_single_of_injective
      f.pushforwardTopos (derivedPushforward f) (derivedPushforwardUnit f)
      (exists_quasiIso_isKInjective X) I hI) P
  rw [Stacks.DerivedFunctor.singleUnitHomology_app] at key
  exact key

/-- **`R⁰f_* ≅ f_*`**, the previous statement as a natural isomorphism: the degree-zero
cohomology of the derived direct image of a sheaf of modules placed in degree zero is its direct
image. -/
def derivedPushforwardZeroNatIso :
    DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 ⋙ derivedPushforward f ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0 ≅
      f.pushforwardTopos :=
  have _ := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hpf : PreservesFiniteLimits f.pushforwardTopos :=
    have : PreservesLimitsOfSize.{0, 0} f.pushforwardTopos :=
      f.pullbackPushforwardAdjunctionTopos.rightAdjoint_preservesLimits
    inferInstance
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated f.pushforwardTopos
      (derivedPushforward f) (derivedPushforwardUnit f)
  @Stacks.DerivedFunctor.derivedZeroNatIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _ _
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _ _ _
    f.pushforwardTopos _ (derivedPushforward f) (derivedPushforwardUnit f) _ _ _ hpf
    (fun _ ↦ Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj f _ 0
      inferInstance)
    (fun I hI ↦ Stacks.DerivedFunctor.isIso_unit_app_single_of_injective
      f.pushforwardTopos (derivedPushforward f) (derivedPushforwardUnit f)
      (exists_quasiIso_isKInjective X) I hI)

/-- **The degree-zero cohomology of the derived unit is the ordinary unit `N ⟶ f_*f^*N`**, and is
therefore invertible whenever the ordinary unit is. The derived unit at `N[0]`, composed with
`Rf_*` of the comparison map of `Lf^*` — invertible because degreewise pullback is exact — is the
degreewise unit followed by the comparison map of `Rf_*`; in degree zero the first factor is the
ordinary unit and the second is invertible because `R⁰f_*` is `f_*`. -/
theorem isIso_homology_derivedUnit_app_singleFunctor_obj
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hN : IsIso (f.pullbackPushforwardAdjunctionTopos.unit.app N)) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N))) := by
  have hdeg : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
      f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)).f n) := by
    intro n
    change IsIso (f.pullbackPushforwardAdjunctionTopos.unit.app
      (((CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N).X n))
    by_cases hn : n = 0
    · subst hn
      exact isIso_app_of_iso _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).symm hN
    · have hz : IsZero
          (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N).X n) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N n hn
      exact isIso_of_isZero_of_isZero hz
        (f.pushforwardTopos.map_isZero (f.pullbackTopos.map_isZero hz)) _
  have hu : IsIso ((Adjunction.mapHomologicalComplexAdjunction
      f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hkappa : IsIso (DerivedCategory.Qh.map
      ((homotopyPullbackPushforwardAdjunction f).unit.app
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N))) := by
    have heq : DerivedCategory.Qh.map
        ((homotopyPullbackPushforwardAdjunction f).unit.app
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) =
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).map
          ((Adjunction.mapHomologicalComplexAdjunction
            f.pullbackPushforwardAdjunctionTopos (ComplexShape.up ℤ)).unit.app
              ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) := rfl
    rw [heq]
    have := hu
    exact Functor.map_isIso _ _
  have hpush : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
      ((derivedPushforwardUnit f).app
        ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)))) := by
    refine isIso_map_app_of_iso (derivedPushforwardUnit f) _
      (((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos
            (ComplexShape.up ℤ) 0).app N)).symm ≪≫
        ((f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
          ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)).symm) ?_
    exact isIso_homology_derivedPushforwardUnit_app_single f (f.pullbackTopos.obj N)
  have hcmp : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) := by
    have := Stacks.Cohomology.CohomologicalDescent.isIso_derivedPullbackComparison f
    infer_instance
  have hfac := derivedPullbackPushforwardAdjunction_unit_fac f ⊤ (hasResolutions_top Y)
    (pullbackInvertsQuasiIso_top f)
    ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)
  have hmid : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)))) := by
    have hprod : IsIso
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) ≫
            (derivedPushforward f).map ((derivedPullbackComparison f).app
              ((HomotopyCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)))) := by
      rw [show (derivedPullbackPushforwardAdjunctionOfExact f).unit.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) ≫
            (derivedPushforward f).map ((derivedPullbackComparison f).app
              ((HomotopyCategory.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) = _
          from hfac, Functor.map_comp]
      have := hkappa
      have := hpush
      infer_instance
    rw [Functor.map_comp] at hprod
    have hc : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
        ((derivedPushforward f).map ((derivedPullbackComparison f).app
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)))) := by
      have := hcmp
      infer_instance
    have := hprod
    have := hc
    exact IsIso.of_isIso_comp_right _
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).map
        ((derivedPushforward f).map ((derivedPullbackComparison f).app
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N))))
  exact isIso_map_app_of_iso (derivedPullbackPushforwardAdjunctionOfExact f).unit _
    ((DerivedCategory.singleFunctorIsoCompQh
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).app N).symm hmid

/-- **The derived unit is invertible at `N[0]`** as soon as the ordinary unit is invertible at `N`
and the higher direct images `Rᵖf_*Lf^*(N[0])` vanish for `p > 0`. Degree zero is the previous
statement; in the negative degrees both sides vanish, since `N[0]` has no cohomology there and
both derived functors preserve boundedness below; in the positive degrees `N[0]` again has no
cohomology and the other side vanishes by hypothesis. -/
theorem isIso_derivedUnit_app_singleFunctor_obj_of_isZero
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hN : IsIso (f.pullbackPushforwardAdjunctionTopos.unit.app N))
    (hvan : ∀ p : ℕ, 0 < p → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((derivedPushforward f).obj
        ((derivedPullback f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N))))) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) := by
  rw [DerivedCategory.isIso_iff]
  intro j
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hGE : ((derivedPullback f ⋙ derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)).IsGE 0 :=
      Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj f _ 0
        (Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj f _ 0 inferInstance)
    have := hGE
    exact isIso_of_isZero_of_isZero
      (isZero_homology_singleFunctor_obj_of_ne N 0 j (by omega))
      (DerivedCategory.isZero_of_isGE _ 0 j hj) _
  · subst hj
    exact isIso_homology_derivedUnit_app_singleFunctor_obj f N hN
  · obtain ⟨p, hp, hp0⟩ : ∃ p : ℕ, j = (p : ℤ) ∧ 0 < p := ⟨j.toNat, by omega, by omega⟩
    subst hp
    exact isIso_of_isZero_of_isZero
      (isZero_homology_singleFunctor_obj_of_ne N 0 (p : ℤ) (by omega)) (hvan p hp0) _

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CompareTopologies

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- **The unit hypothesis of Stacks 0D7W for the comparison morphism `ε` of a topology and a
coarser one.** Let `J' ≤ J` be two topologies on `C`, let `R` be a sheaf of rings for `J` and let
`A` be a class of sheaves of `R`-modules for `J`, closed under isomorphisms. Assume every object
of `C` has a `J'`-covering by members of a family `B` and that `H^p_J(U, F)` vanishes for `p > 0`,
`U` in `B` and `F` in `A`. Then for every `N` in the image class `A'` of Stacks 07A8 the unit

`N[0] ⟶ Rε_*Lε^*(N[0])`

of the derived adjunction is invertible.

In degree zero this is the ordinary unit `N ⟶ ε_*ε^*N`, invertible because `N` lies in the
essential image of the fully faithful `ε_*`; in the positive degrees it is the vanishing of the
higher direct images of `ε^*N`, which lies in `A`. -/
theorem isIso_derivedUnit_app_singleFunctor_obj_imageOfLE
    (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)
    [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
    [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
    (hA : A.IsClosedUnderIsomorphisms)
    (B : Set S.C)
    (hB : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : S.C, B U → ∀ p : ℕ, 0 < p →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O), A F →
      IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
        U p F))
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h))
    (hN : imageOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A N) :
    letI : (pullbackOnHomotopy (S.coarseningHom h).toRingedToposSiteHom).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).ringedTopos.O))
          (ComplexShape.up ℤ)) :=
      S.hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom h
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact
        (S.coarseningHom h).toRingedToposSiteHom).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h)) 0).obj N)) := by
  let : (pullbackOnHomotopy (S.coarseningHom h).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.ofLe h).ringedTopos.O))
        (ComplexShape.up ℤ)) :=
    S.hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom h
  have hAp : A ((S.coarseningHom h).toRingedToposSiteHom.pullbackTopos.obj N) :=
    hA.of_iso ((S.pullbackToposCoarseningHomIso h).app N).symm
      (prop_pullback_obj h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) A hA hN)
  let : (S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos.Full :=
    @Functor.Full.of_iso _ _ _ _ _ _
      (SheafOfModules.fullyFaithfulOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).full
      (S.pushforwardToposCoarseningHomIso h).symm
  let : (S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos.Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _
      (SheafOfModules.fullyFaithfulOfLE h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).faithful
      (S.pushforwardToposCoarseningHomIso h).symm
  obtain ⟨M₀, -, ⟨e₀⟩⟩ := id hN
  have hunit : IsIso
      ((S.coarseningHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app N) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage
      (S.coarseningHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).mpr
      ⟨M₀, ⟨(S.pushforwardToposCoarseningHomIso h).app M₀ ≪≫ e₀⟩⟩
  refine isIso_derivedUnit_app_singleFunctor_obj_of_isZero
    (S.coarseningHom h).toRingedToposSiteHom N hunit (fun p hp ↦ ?_)
  refine IsZero.of_iso (isZero_homology_derivedPushforwardCoarsening_obj S h p
    ((S.coarseningHom h).toRingedToposSiteHom.pullbackTopos.obj N) B hB
    (fun U hU ↦ hvan U hU p hp _ hAp)) ?_
  exact (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h))
    (p : ℤ)).mapIso ((derivedPushforward (S.coarseningHom h).toRingedToposSiteHom).mapIso
      (Stacks.Cohomology.CohomologicalDescent.derivedPullbackSingleFunctorObjIso
        (S.coarseningHom h).toRingedToposSiteHom N))

end Stacks.Cohomology.CompareTopologies

end
