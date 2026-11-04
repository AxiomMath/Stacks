module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationDerivedMap

/-!
# The extended alternating Čech complex represents cohomology with support (Stacks 0G7M)

Let `X` be a scheme, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` global functions, `Z` the complement of
`⋃ᵢ X.basicOpen fᵢ`, and `F` a quasi-coherent `𝒪_X`-module.  Stacks 0G7M asserts that the
extended alternating Čech complex `𝓕^•` of Stacks 0G7I represents `i_* R𝓗_Z(F)` in
`D_Z(𝒪_X)`, the comparison being the augmentation of Stacks 0G7L.

The source argues in three steps.  First, `𝓕^•` lies in `D_Z(𝒪_X)`, so applying `i_* R𝓗_Z`
to it changes nothing (Stacks 0AEF).  Second, every positive-degree term `𝓕^p` is a direct
image `(U_{i₀…i_p} → X)_* (F|_{U_{i₀…i_p}})` along an affine morphism, so it is its own derived
direct image (Stacks 01XC) and therefore killed by `R𝓗_Z` (Stacks 0G73).  Third, a complex
whose positive-degree terms are killed and whose degree-`0` term is `F` has the augmentation as
an isomorphism after applying the derived functor.

This file proves the third step, and proves it for an arbitrary additive, finite-limit-preserving
functor out of `X.Modules` in place of sections supported on `Z` — so the geometry enters only
through the hypothesis the other two steps discharge.  The reduction is unconditional: nothing
here is assumed beyond the Stacks 0G7I complex and the Stacks 0G7L augmentation.

## Main results

* `Stacks.Perfect.CechAugmentation.isIso_map_augmentation_of_isZero_obj_single_X_succ`: if the
  total right derived
  functor `RH` kills every positive-degree term of the complex, placed in degree `0`, then `RH`
  inverts the augmentation.
* `Stacks.Perfect.CechAugmentation.isIso_map_augmentation_of_isZero_obj_single_restrictedModule`:
  the same with the
  hypothesis in the form Stacks 01XC and Stacks 0G73 supply it, namely vanishing on each
  `(U_{i₀…i_p} → X)_* (F|_{U_{i₀…i_p}})`.
* `Stacks.Perfect.CechAugmentation.isIso_homEquiv_of_fullyFaithful_of_isIso_map`: the final
  transpose step, which
  turns the previous conclusion into an isomorphism in the supported derived category as soon as
  the adjunction of Stacks 0AEF is available (its left adjoint being fully faithful makes its
  unit invertible).

Supporting results about total right derived functors, none of them specific to schemes:

* `Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor`: a total right derived
  functor on the
  unbounded derived category of a Grothendieck abelian category is triangulated.
* `Stacks.Perfect.CechAugmentation.isZero_obj_of_plus_of_rightAcyclic`: it kills a bounded-below
  complex with right
  acyclic terms that it sends to zero.
* `Stacks.Perfect.CechAugmentation.rightAcyclic_and_isZero_of_isZero_obj_single`: conversely,
  killing an object in
  degree `0` makes that object right acyclic and sent to zero.
* `Stacks.Perfect.CechAugmentation.isIso_map_of_isZero_kernel`: a triangulated functor inverts an
  epimorphism whose
  kernel it kills.

## Implementation notes

The augmentation is a map of `ℤ`-indexed complexes `ψ : 𝓕^• ⟶ F[0]`, obtained by extending the
`ℕ`-indexed projection by zero.  It is an *epimorphism*, because it is an isomorphism in degree
`0` and its target vanishes elsewhere; so the kernel short exact sequence gives a distinguished
triangle, and `RH` inverts `ψ` exactly when it kills `kernel ψ`.  The kernel vanishes in degrees
`≤ 0` and is the complex's own term in each positive degree, which is why the hypothesis is
stated on those terms.

Killing `kernel ψ` is *not* immediate from killing its terms: the complex is unbounded above.
The route is `Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`, which needs each term to
be right acyclic — and that is extracted from the same vanishing hypothesis by
`rightAcyclic_and_isZero_of_isZero_obj_single`, running the comparison with the bounded-below
right derived functor in the opposite direction.  Both directions go through
`nonempty_obj_iso_rightDerivedFunctorPlus`, which compares `RH` with `F.rightDerivedFunctorPlus`
on a bounded-below object by resolving it injectively.

`isTriangulated_of_isRightDerivedFunctor` is what makes the triangle argument available at all,
and it is proved from the functorial K-injective resolution of Stacks 079P: K-injective complexes
are a class of objects on which the comparison is invertible and which is closed under the third
object of a triangle, which is exactly the input `Functor.isTriangulated_of_leftExtension` wants.

The section variables `H` and `α` are pulled in with `include`: the two main statements mention
only `RH`, so the instance `[RH.IsRightDerivedFunctor α _]` — whose type mentions `α`, which
mentions `H` — would otherwise be dropped, and the proofs would fail with `H` reported as an
unknown identifier rather than as a missing hypothesis.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0G73](https://stacks.math.columbia.edu/tag/0G73)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechAugmentation

/-! ### Generic facts about total right derived functors -/

section Generic

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The adjoint transpose of a morphism is an isomorphism as soon as the unit at its source and
the right adjoint's value on it are. -/
public theorem isIso_homEquiv_of_isIso_unit_of_isIso_map
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {x : C} {z : D} (g : L.obj x ⟶ z)
    (hunit : IsIso (adj.unit.app x)) (hmap : IsIso (R.map g)) :
    IsIso (adj.homEquiv x z g) := by
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- When the left adjoint is fully faithful, the adjoint transpose of a morphism is an
isomorphism as soon as the right adjoint's value on it is. -/
public theorem isIso_homEquiv_of_fullyFaithful_of_isIso_map
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Full] [L.Faithful] {x : C} {z : D} (g : L.obj x ⟶ z) (hmap : IsIso (R.map g)) :
    IsIso (adj.homEquiv x z g) :=
  isIso_homEquiv_of_isIso_unit_of_isIso_map adj g inferInstance hmap

/-- A triangulated functor out of the derived category inverts an epimorphism of complexes whose
kernel it sends to zero. -/
public theorem isIso_map_of_isZero_kernel
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
      [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
    (R : DerivedCategory C ⥤ D) [R.CommShift ℤ] [R.IsTriangulated]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) [Epi φ]
    (hker : IsZero (R.obj (DerivedCategory.Q.obj (kernel φ)))) :
    IsIso (R.map (DerivedCategory.Q.map φ)) := by
  have hS : (ShortComplex.kernelSequence φ).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact φ) inferInstance
      (inferInstanceAs (Epi φ))
  exact (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _
    (R.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS))).mp hker

/-- Every complex in a Grothendieck abelian category admits a K-injective resolution, supplied by
the functorial resolution of Stacks 079P. -/
public theorem exists_isKInjective_quasiIso {C : Type*} [Category* C] [Abelian C]
    [IsGrothendieckAbelian C] (K : CochainComplex C ℤ) :
    ∃ (J : CochainComplex C ℤ) (q : K ⟶ J), J.IsKInjective ∧ QuasiIso q :=
  ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion C).app K,
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective C K,
    Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso C K⟩

/-- A comparison transformation exhibiting a right derived functor is invertible at every
K-injective complex. -/
public theorem isIso_app_quotient_obj_of_isKInjective (F : A ⥤ B) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
      (DerivedCategory.Qh (C := A)) R β I hI

/-- A total right derived functor on the unbounded derived category of a Grothendieck abelian
category is triangulated: K-injective complexes provide the left extension's triangles. -/
public theorem isTriangulated_of_isRightDerivedFunctor
    [IsGrothendieckAbelian A] (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    letI := Functor.IsRightDerivedFunctor.commShift RF α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
    RF.IsTriangulated := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  apply Functor.isTriangulated_of_leftExtension RF α
  intro X Y f
  let e (W : DerivedCategory A) : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A
      (ComplexShape.up ℤ)).obj ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj
        (DerivedCategory.Q.objPreimage W))) ≅ W :=
    (DerivedCategory.quotientCompQhIso A).app _ ≪≫
      (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion A).app
        (DerivedCategory.Q.objPreimage W)))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso W
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj (DerivedCategory.Q.objPreimage X)
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj (DerivedCategory.Q.objPreimage Y)
  let eI := e X
  let eJ := e Y
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) J).surjective
    (eI.hom ≫ f ≫ eJ.inv)
  obtain ⟨Z, g₂, g₃, hT⟩ := Pretriangulated.distinguished_cocone_triangle g
  have hZ := ObjectProperty.ext_of_isTriangulatedClosed₃
    (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal _ hT
      (CochainComplex.IsKInjective.rightOrthogonal I)
      (CochainComplex.IsKInjective.rightOrthogonal J)
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have hL : CochainComplex.IsKInjective L :=
    (CochainComplex.isKInjective_iff_rightOrthogonal L).2 hZ
  have hc := isIso_app_quotient_obj_of_isKInjective F RF α exists_isKInjective_quasiIso
  exact ⟨Pretriangulated.Triangle.mk g g₂ g₃, hT,
    hc I (Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective A _),
    hc J (Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective A _), hc L hL,
    ⟨Arrow.isoMk eI eJ (by simp [hg])⟩⟩

/-- The value of a total right derived functor on a bounded-below object agrees with the value of
the bounded-below right derived functor, up to isomorphism. -/
public theorem nonempty_obj_iso_rightDerivedFunctorPlus
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (E : DerivedCategory.Plus A) (a : ℤ) (hE : E.obj.IsGE a) :
    Nonempty (R.obj E.obj ≅ (F.rightDerivedFunctorPlus.obj E).obj) := by
  obtain ⟨K, _, ⟨e⟩⟩ := E.obj.exists_iso_Q_obj_of_isGE a
  obtain ⟨I, f, hf, hI, hIa⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K a
  let J : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
      (HomotopyCategory.plus_quotient_obj_iff I).2 ((CochainComplex.plus_iff A I).2 ⟨a, hIa⟩)⟩
  have : ∀ n : ℤ, Injective (J.obj.as.X n) := hI
  have hc := hcomp I (CochainComplex.isKInjective_of_injective I a)
  let eI : DerivedCategory.Qh.obj J.obj ≅ E.obj :=
    (DerivedCategory.quotientCompQhIso A).app I ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫ e.symm
  let eP : DerivedCategory.Plus.Qh.obj J ≅ E := DerivedCategory.Plus.ι.preimageIso eI
  exact ⟨R.mapIso eI.symm ≪≫ (asIso (β.app J.obj)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso (F.rightDerivedFunctorPlusUnit.app J)) ≪≫
    DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso eP)⟩

/-- A total right derived functor kills a bounded-below complex all of whose terms are right
acyclic and sent to zero. -/
public theorem isZero_obj_of_plus_of_rightAcyclic
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (K : CochainComplex A ℤ) (hK : CochainComplex.plus A K)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) (hzero : ∀ n, IsZero (F.obj (K.X n))) :
    IsZero (R.obj (DerivedCategory.Q.obj K)) := by
  obtain ⟨a, ha⟩ := hK
  let J : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K,
      (HomotopyCategory.plus_quotient_obj_iff K).2 ((CochainComplex.plus_iff A K).2 ⟨a, ha⟩)⟩
  let E : DerivedCategory.Plus A := DerivedCategory.Plus.Qh.obj J
  let eK : E.obj ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.Plus.QhCompιIsoιCompQh A).app J ≪≫
      (DerivedCategory.quotientCompQhIso A).app K
  have hQ : (DerivedCategory.Q.obj K).IsGE a := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  obtain ⟨e⟩ := nonempty_obj_iso_rightDerivedFunctorPlus F R β hcomp E a
    (DerivedCategory.TStructure.t.isGE_of_iso eK.symm a)
  have hFK : IsZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    apply (IsZero.iff_id_eq_zero _).2
    ext n
    exact (hzero n).eq_of_src _ _
  let Kplus : CochainComplex.Plus A := ⟨K, (CochainComplex.plus_iff A K).2 ⟨a, ha⟩⟩
  have hFKplus : IsZero (F.mapCochainComplexPlus.obj Kplus) :=
    IsZero.of_full_of_faithful_of_isZero (CochainComplex.Plus.ι B) _
      (hFK.of_iso ((Functor.mapCochainComplexPlusCompι F).app Kplus))
  have hsource : IsZero ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj J) :=
    Functor.map_isZero DerivedCategory.Plus.Qh
      ((HomotopyCategory.Plus.quotient B).map_isZero hFKplus)
  have hunit : IsIso (F.rightDerivedFunctorPlusUnit.app J) :=
    Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F K ⟨a, ha⟩ hacyclic
  have hRFplus : IsZero (F.rightDerivedFunctorPlus.obj E) :=
    IsZero.of_iso hsource (asIso (F.rightDerivedFunctorPlusUnit.app J)).symm
  exact ((DerivedCategory.Plus.ι.map_isZero hRFplus).of_iso e).of_iso (R.mapIso eK).symm

/-- If a total right derived functor kills an object placed in degree zero, that object is right
acyclic and sent to zero. -/
public theorem rightAcyclic_and_isZero_of_isZero_obj_single
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (M : A) [PreservesFiniteLimits F]
    (hzero : IsZero (R.obj ((DerivedCategory.singleFunctor A 0).obj M))) :
    F.rightAcyclic M ∧ IsZero (F.obj M) := by
  let E := (DerivedCategory.Plus.singleFunctor A 0).obj M
  let eE : E.obj ≅ (DerivedCategory.singleFunctor A 0).obj M :=
    (DerivedCategory.Plus.singleFunctorιIso A 0).app M
  have hE : E.obj.IsGE 0 := (DerivedCategory.Plus.isGE_ι_obj_iff E 0).2 inferInstance
  obtain ⟨eR⟩ := nonempty_obj_iso_rightDerivedFunctorPlus F R β hcomp E 0 hE
  have hRFobj : IsZero ((F.rightDerivedFunctorPlus.obj E).obj) :=
    IsZero.of_iso (IsZero.of_iso hzero (R.mapIso eE)) eR.symm
  have hRF : IsZero (F.rightDerivedFunctorPlus.obj E) :=
    IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _ hRFobj
  have hacyclic : F.rightAcyclic M :=
    ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F M).2
      ‹PreservesFiniteLimits F›).2 fun i _ =>
        (DerivedCategory.Plus.homologyFunctor B i).map_isZero hRF
  let J := (HomotopyCategory.Plus.singleFunctor A 0).obj M
  have hunit : IsIso (F.rightDerivedFunctorPlusUnit.app J) := hacyclic
  have hRFJ : IsZero ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).obj J) :=
    IsZero.of_iso hRF (F.rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).app M)).symm
  have hsource : IsZero ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj J) :=
    IsZero.of_iso hRFJ (asIso (F.rightDerivedFunctorPlusUnit.app J))
  have hsingle : IsZero ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M)) :=
    IsZero.of_iso hsource ((Functor.mapSingleFunctorCompQhIso F).app M).symm
  refine ⟨hacyclic, ?_⟩
  let e : (DerivedCategory.Plus.homologyFunctor B 0).obj
      ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M)) ≅ F.obj M :=
    (Functor.associator (DerivedCategory.Plus.singleFunctor B 0)
      DerivedCategory.Plus.ι (DerivedCategory.homologyFunctor B 0)).symm.app (F.obj M) ≪≫
    (Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso B 0)
      (DerivedCategory.homologyFunctor B 0)).app (F.obj M) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app (F.obj M)
  exact IsZero.of_iso ((DerivedCategory.Plus.homologyFunctor B 0).map_isZero hsingle) e.symm

/-- An additive functor out of the derived category kills a finite product of objects placed in
degree zero as soon as it kills each factor. -/
public theorem isZero_obj_single_pi
    (R : DerivedCategory A ⥤ DerivedCategory B) [Functor.Additive R]
    {ι : Type*} [Finite ι] (M : ι → A)
    (hzero : ∀ i, IsZero (R.obj ((DerivedCategory.singleFunctor A 0).obj (M i)))) :
    IsZero (R.obj ((DerivedCategory.singleFunctor A 0).obj (∏ᶜ M))) := by
  let MD := Discrete.functor M
  have hSR : IsZero (MD ⋙ DerivedCategory.singleFunctor A 0 ⋙ R) :=
    Functor.isZero _ fun i => hzero i.as
  change IsZero (R.obj ((DerivedCategory.singleFunctor A 0).obj (limit MD)))
  exact (isLimitOfPreserves R
    (isLimitOfPreserves (DerivedCategory.singleFunctor A 0) (limit.isLimit MD))).isZero_pt hSR

end Generic

/-! ### The extended alternating Čech complex -/

section Cech

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- The augmentation of Stacks 0G7L as a morphism of `ℤ`-indexed complexes, before passing to
the derived category. -/
public abbrev augmentationExtended :
    (extendedAlternatingCech f F).complex.extend ComplexShape.embeddingUpNat ⟶
      ((CochainComplex.single₀ X.Modules).obj F).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex f F)
    ComplexShape.embeddingUpNat

/-- The extended augmentation is an isomorphism in degree `0`. -/
public instance isIso_augmentationExtended_f_zero :
    IsIso ((augmentationExtended f F).f 0) := by
  rw [HomologicalComplex.extendMap_f
    (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentationComplex f F)
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  infer_instance

/-- The target of the extended augmentation vanishes in every positive degree. -/
public theorem isZero_extendSingle_X_succ (p : ℕ) :
    IsZero ((((CochainComplex.single₀ X.Modules).obj F).extend
      ComplexShape.embeddingUpNat).X (Int.ofNat (p + 1))) :=
  IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 F (p + 1) (by omega))
    (((CochainComplex.single₀ X.Modules).obj F).extendXIso
      ComplexShape.embeddingUpNat (i := p + 1) (i' := Int.ofNat (p + 1)) rfl)

/-- The extended augmentation is an epimorphism: it is an isomorphism in degree `0` and its
target vanishes in all other degrees. -/
public instance epi_augmentationExtended : Epi (augmentationExtended f F) := by
  refine HomologicalComplex.epi_of_epi_f _ fun n => ?_
  match n with
  | Int.negSucc k =>
      exact (((CochainComplex.single₀ X.Modules).obj F).isZero_extend_X
        ComplexShape.embeddingUpNat (Int.negSucc k) (fun _ => by simp)).epi _
  | Int.ofNat 0 =>
      have : IsIso ((augmentationExtended f F).f (Int.ofNat 0)) :=
        isIso_augmentationExtended_f_zero f F
      infer_instance
  | Int.ofNat (p + 1) => exact (isZero_extendSingle_X_succ F p).epi _

/-- The kernel of the extended augmentation vanishes in every degree `≤ 0`. -/
public theorem isZero_kernel_augmentationExtended_X_of_nonpos (n : ℤ) (hn : n ≤ 0) :
    IsZero ((kernel (augmentationExtended f F)).X n) := by
  have e := PreservesKernel.iso (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n)
    (augmentationExtended f F)
  match n, hn with
  | Int.negSucc k, _ =>
      have hC : IsZero (((extendedAlternatingCech f F).complex.extend
          ComplexShape.embeddingUpNat).X (Int.negSucc k)) :=
        (extendedAlternatingCech f F).complex.isZero_extend_X
          ComplexShape.embeddingUpNat (Int.negSucc k) (fun _ => by simp)
      have : Mono ((augmentationExtended f F).f (Int.negSucc k)) := hC.mono _
      exact IsZero.of_iso (isZero_kernel_of_mono ((augmentationExtended f F).f (Int.negSucc k))) e
  | Int.ofNat 0, _ =>
      exact IsZero.of_iso (isZero_kernel_of_mono ((augmentationExtended f F).f 0)) e

/-- The kernel of the extended augmentation is bounded below. -/
public theorem plus_kernel_augmentationExtended :
    CochainComplex.plus X.Modules (kernel (augmentationExtended f F)) := by
  refine ⟨0, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun n hn => isZero_kernel_augmentationExtended_X_of_nonpos f F n hn.le

/-- In every positive degree the kernel of the extended augmentation is the corresponding term of
the extended alternating Čech complex. -/
public noncomputable def kernelAugmentationExtendedXIsoSucc (p : ℕ) :
    (kernel (augmentationExtended f F)).X (Int.ofNat (p + 1)) ≅
      (extendedAlternatingCech f F).complex.X (p + 1) :=
  have hφ : (augmentationExtended f F).f (Int.ofNat (p + 1)) = 0 :=
    (isZero_extendSingle_X_succ F p).eq_of_tgt _ _
  have hκ : IsIso (kernel.ι ((augmentationExtended f F).f (Int.ofNat (p + 1)))) := by
    rw [hφ]
    infer_instance
  PreservesKernel.iso (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ)
      (Int.ofNat (p + 1))) (augmentationExtended f F) ≪≫
    asIso (kernel.ι ((augmentationExtended f F).f (Int.ofNat (p + 1)))) ≪≫
    (extendedAlternatingCech f F).complex.extendXIso
      ComplexShape.embeddingUpNat (i := p + 1) (i' := Int.ofNat (p + 1)) rfl

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (H : X.Modules ⥤ D) [H.Additive] [PreservesFiniteLimits H]
  (RH : DerivedCategory X.Modules ⥤ DerivedCategory D)
  (α : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RH)
  [RH.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

include H α in
/-- **Stacks Project, Tag 0G7M**, reduced to the vanishing of the derived functor on the positive
degree terms.  If the total right derived functor `RH` of an additive, finite-limit-preserving
functor `H` out of the modules on `X` kills every positive-degree term of the extended
alternating Čech complex of `f` and `F`, placed in degree `0`, then `RH` inverts the
augmentation of Stacks 0G7L.

For `H` the sections supported on the common zero locus `Z` of `f` this is the statement that
the complex computes `R𝓗_Z(F)`: the hypothesis is exactly the vanishing supplied by
[Stacks, Tag 01XC] and [Stacks, Tag 0G73]. -/
public theorem isIso_map_augmentation_of_isZero_obj_single_X_succ
    (hvan : ∀ p : ℕ, IsZero (RH.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
      ((extendedAlternatingCech f F).complex.X (p + 1))))) :
    IsIso (RH.map (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F)) := by
  let ψ := augmentationExtended f F
  let _ : (H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso X.Modules) :=
    HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso _
  let _ : (H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso X.Modules) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  let _ : RH.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift RH α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have _ : RH.IsTriangulated := isTriangulated_of_isRightDerivedFunctor H RH α
  have hcomp (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
      IsIso (α.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_quotient_obj_of_isKInjective H RH α exists_isKInjective_quasiIso I hI
  have hkernelDerived (n : ℤ) :
      IsZero (RH.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((kernel ψ).X n))) := by
    by_cases hn : n ≤ 0
    · exact RH.map_isZero ((DerivedCategory.singleFunctor X.Modules 0).map_isZero
        (isZero_kernel_augmentationExtended_X_of_nonpos f F n hn))
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = Int.ofNat (p + 1) :=
        ⟨(n - 1).toNat, by simp only [Int.ofNat_eq_natCast]; omega⟩
      exact IsZero.of_iso (hvan p) (RH.mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso
          (kernelAugmentationExtendedXIsoSucc f F p)))
  have hpair (n : ℤ) :
      H.rightAcyclic ((kernel ψ).X n) ∧ IsZero (H.obj ((kernel ψ).X n)) :=
    rightAcyclic_and_isZero_of_isZero_obj_single H RH α hcomp _ (hkernelDerived n)
  have hψ : IsIso (RH.map (DerivedCategory.Q.map ψ)) :=
    isIso_map_of_isZero_kernel RH ψ (isZero_obj_of_plus_of_rightAcyclic H RH α hcomp (kernel ψ)
      (plus_kernel_augmentationExtended f F) (fun n => (hpair n).1) (fun n => (hpair n).2))
  rw [Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation]
  simp only [Functor.map_comp]
  infer_instance

include H α in
/-- **Stacks Project, Tag 0G7M**, reduced to the vanishing of the derived functor on the direct
images of the restrictions of `F` to the principal-open intersections.  This is the form in which
[Stacks, Tag 01XC] and [Stacks, Tag 0G73] discharge the hypothesis: those two results say exactly
that `R𝓗_Z` kills `(U_{i_0 … i_p} → X)_* (F|_{U_{i_0 … i_p}})`. -/
public theorem isIso_map_augmentation_of_isZero_obj_single_restrictedModule
    (hvan : ∀ (p : ℕ) (s : CechCochains.OrdIndex (I := Fin c) p),
      IsZero (RH.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
        (restrictedModule f F p s)))) :
    IsIso (RH.map (Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation f F)) := by
  let _ : RH.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift RH α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have _ : RH.IsTriangulated := isTriangulated_of_isRightDerivedFunctor H RH α
  exact isIso_map_augmentation_of_isZero_obj_single_X_succ f F H RH α fun p =>
    IsZero.of_iso (isZero_obj_single_pi RH _ (hvan p)) (RH.mapIso
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso
        ((extendedAlternatingCech f F).termIso p)))

end Cech

end Stacks.Perfect.CechAugmentation

end
