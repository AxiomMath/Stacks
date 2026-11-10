module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent

/-!
# `L : D⁺(A) ≌ D⁺_P(B)` for an exact left adjoint with invertible derived unit

Let `L : A ⥤ B` be an exact functor of abelian categories with a right adjoint `R`, let `B` have
enough injectives, and let `P` be a class of objects of `B` which contains every `L M` and every
object of which is isomorphic to some `L M`. On bounded below derived categories the adjunction
descends to `L : D⁺(A) ⥤ D⁺(B)`, `RR : D⁺(B) ⥤ D⁺(A)`
(`Stacks.ComparingTopologies.derivedPlusAdjunction`). This file proves that if the derived unit
`K ⟶ RR(LK)` is invertible for every `K` of `D⁺(A)`, then `L` is an equivalence

`D⁺(A) ≌ D⁺_P(B)`

onto the bounded below objects all of whose cohomology objects lie in `P`, with quasi-inverse
`RR`. This is the abelian form of the argument of Stacks 0D7U, and the formal content of
Stacks 0DAH once the unit is known to be invertible (Stacks 09XS) and the objects of `P` are known
to come from `A` (Stacks 0DAG).

## Main definitions

* `DerivedCategory.Plus.homologyIn`: for a class `P` of objects of `B`, the objects of `D⁺(B)` all
  of whose cohomology objects lie in `P`; this is `D⁺_P(B)`.
* `CategoryTheory.Adjunction.derivedPlusEquivalenceOfHomologyIn`: the equivalence
  `D⁺(A) ≌ D⁺_P(B)`.

## Main results

* `CategoryTheory.Adjunction.homologyIn_mapDerivedCategoryPlus_obj`: `L` carries `D⁺(A)` into
  `D⁺_P(B)`, its cohomology objects being `L` of those of its argument.
* `CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_counit_app_of_homologyIn`: the derived
  counit is invertible on `D⁺_P(B)`.
* `CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_of_rightAcyclic` and
  `..._of_isZero_rightDerived`: the derived unit is invertible on `D⁺(A)` as soon as the unit
  `M ⟶ R(LM)` is invertible and every `LM` is right acyclic for `R`.
* `derivedPlusEquivalenceOfHomologyIn_functor` and `..._inverse`: the two functors of the
  equivalence are the restrictions of `L` and of `RR`, by `rfl`.

## The argument

On an object `M` of `P` placed in degree zero write `M ≅ L N`; then `M[0] ≅ L(N[0])`, and the
counit at `L` of an object at which the unit is invertible is invertible by a triangle identity.
The dévissage `DerivedCategory.Plus.isIso_app_of_bounded_below` propagates this along the
truncation triangles to every object of `D⁺_P(B)`: both `RR ⋙ L` and the identity are exact,
commute with the shift and preserve `D^{≥m}`. Together with the invertible unit this makes the
restricted adjunction an equivalence.

The derived unit itself is invertible as soon as the unit `M ⟶ R(LM)` of `adj` is and every `LM`
is right acyclic for `R`: on the image of a bounded below complex `K` the derived unit is the
degreewise unit followed by the canonical map `R(LK) ⟶ RR(LK)`
(`CategoryTheory.Adjunction.derivedη_fac_app`), and the latter is invertible by Leray's acyclicity
lemma (Stacks 015E).

## Implementation notes

The dévissage needs the counit to be compatible with the shift. The shift on `RR` used for that
is the one transported from `L` along the adjunction
(`CategoryTheory.Adjunction.rightAdjointCommShift`), installed locally inside the proof; the
statements do not mention it.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0DAH](https://stacks.math.columbia.edu/tag/0DAH)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace DerivedCategory.Plus

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- `D⁺_P(B)`: the objects of the bounded below derived category of `B` all of whose cohomology
objects lie in the class `P`. -/
def homologyIn (P : ObjectProperty B) : ObjectProperty (DerivedCategory.Plus B) :=
  fun K ↦ ∀ q : ℤ, P ((homologyFunctor B q).obj K)

end DerivedCategory.Plus

namespace CategoryTheory.Adjunction

open DerivedCategory.Plus Stacks.ComparingTopologies

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
  (P : ObjectProperty B)

omit [EnoughInjectives B] in
/-- **`L` carries `D⁺(A)` into `D⁺_P(B)`** as soon as `P` contains the image of `L`: the
cohomology objects of `LK` are `L` of those of `K`. -/
theorem homologyIn_mapDerivedCategoryPlus_obj [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P (L.obj M)) (K : DerivedCategory.Plus A) :
    homologyIn P (L.mapDerivedCategoryPlus.obj K) := fun q ↦
  P.prop_of_iso ((L.mapDerivedCategoryHomologyIso q).app K.obj).symm (hP _)

/-- `L` of an object placed in degree zero is its image placed in degree zero, in `D⁺`. -/
def mapDerivedCategoryPlusSingleObjIso (N : A) :
    L.mapDerivedCategoryPlus.obj ((singleFunctor A 0).obj N) ≅
      (singleFunctor B 0).obj (L.obj N) :=
  DerivedCategory.Plus.ι.preimageIso ((L.mapDerivedCategorySingleFunctor 0).app N)

include adj in
/-- **The counit is invertible at an object of `P` placed in degree zero**, granted that the
derived unit is invertible and that every object of `P` is `L` of an object of `A`. -/
theorem isIso_derivedPlusAdjunction_counit_app_singleFunctor_obj
    (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) (M : B) (hM : P M) :
    IsIso ((derivedPlusAdjunction adj).counit.app ((singleFunctor B 0).obj M)) := by
  obtain ⟨N, ⟨e⟩⟩ := hsurj M hM
  exact (NatTrans.isIso_app_iff_of_iso (derivedPlusAdjunction adj).counit
    (mapDerivedCategoryPlusSingleObjIso N ≪≫ (singleFunctor B 0).mapIso e)).mp
      ((derivedPlusAdjunction adj).isIso_counit_app_obj_of_isIso_unit_app _ (hunit _))

include adj in
/-- **The derived counit is invertible on `D⁺_P(B)`**, granted that the derived unit is
invertible on `D⁺(A)` and that every object of `P` is `L` of an object of `A`: it is so on the
cohomology objects, placed in degree zero, and the dévissage along the truncation triangles
propagates that to every bounded below object. -/
theorem isIso_derivedPlusAdjunction_counit_app_of_homologyIn
    (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) (K : DerivedCategory.Plus B) (hK : homologyIn P K) :
    IsIso ((derivedPlusAdjunction adj).counit.app K) := by
  let adjP := derivedPlusAdjunction adj
  let : R.rightDerivedFunctorPlus.CommShift ℤ := adjP.rightAdjointCommShift ℤ
  let : adjP.CommShift ℤ := adjP.commShift_of_leftAdjoint ℤ
  have : adjP.IsTriangulated := Adjunction.IsTriangulated.mk' adjP
  have : R.rightDerivedFunctorPlus.IsTriangulated := adjP.isTriangulated_rightAdjoint
  obtain ⟨a, ha⟩ := K.property
  exact DerivedCategory.Plus.isIso_app_of_bounded_below adjP.counit
    (fun Y m h ↦ by
      have := h
      exact L.isGE_mapDerivedCategoryPlus_obj _ m
        (Functor.isGE_rightDerivedFunctorPlus_obj R Y m))
    (fun _ _ h ↦ h) K a ((DerivedCategory.Plus.isGE_ι_obj_iff K a).1 ha)
    (fun q ↦ isIso_derivedPlusAdjunction_counit_app_singleFunctor_obj adj P hunit hsurj _ (hK q))

/-! ### The derived unit from the underived one -/

include adj in
/-- **The derived unit `K ⟶ RR(LK)` is invertible on `D⁺(A)`** as soon as the unit `M ⟶ R(LM)`
of `adj` is invertible and every `LM` is right acyclic for `R`: represent `K` by a bounded below
complex; the derived unit is then the degreewise unit followed by the canonical map
`R(LK) ⟶ RR(LK)`, which is invertible by Leray's acyclicity lemma (Stacks 015E), all terms of
`LK` being right acyclic. -/
theorem isIso_derivedPlusAdjunction_unit_app_of_rightAcyclic
    (hunit : ∀ M, IsIso (adj.unit.app M)) (hac : ∀ M, R.rightAcyclic (L.obj M))
    (K : DerivedCategory.Plus A) :
    IsIso ((derivedPlusAdjunction adj).unit.app K) := by
  have : L.mapDerivedCategoryPlus.IsLeftDerivedFunctor
      L.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      L.mapDerivedCategoryPlusFactorsh
  have : (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)
  let K' := DerivedCategory.Plus.Qh.objPreimage K
  suffices IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Qh.obj K')) from
    (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Qh.objObjPreimageIso K)).1 this
  have hη := adj.mapHomotopyCategoryPlus.derivedη_fac_app
    (HomotopyCategory.Plus.quasiIso A) L.mapDerivedCategoryPlusFactorsh.hom
    R.rightDerivedFunctorPlusUnith K'
  change (derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Qh.obj K') ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K') = _ at hη
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have := Adjunction.isIso_mapHomotopyCategoryPlus_unit_app adj K'
  have : IsIso (R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K')) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic R _ fun n ↦ hac _
  have : IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Qh.obj K') ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K')) := by
    rw [hη]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K'))

include adj in
/-- **The derived unit `K ⟶ RR(LK)` is invertible on `D⁺(A)`** as soon as the unit `M ⟶ R(LM)`
of `adj` is invertible and the higher right derived functors of `R` vanish on every `LM`:
`R` is left exact, being a right adjoint, so this vanishing is right acyclicity (Stacks 015C). -/
theorem isIso_derivedPlusAdjunction_unit_app_of_isZero_rightDerived
    (hunit : ∀ M, IsIso (adj.unit.app M))
    (hvan : ∀ M (q : ℕ), 0 < q → IsZero ((R.rightDerived q).obj (L.obj M)))
    (K : DerivedCategory.Plus A) :
    IsIso ((derivedPlusAdjunction adj).unit.app K) := by
  have : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits R := inferInstance
  exact isIso_derivedPlusAdjunction_unit_app_of_rightAcyclic adj hunit
    (fun M ↦ (rightAcyclic_iff_isZero_rightDerived R (L.obj M)).2 (hvan M)) K

/-- **`L : D⁺(A) ⥤ D⁺_P(B)`**, the forward functor of the equivalence. -/
abbrev derivedPlusHomologyInFunctor [P.IsClosedUnderIsomorphisms] (hP : ∀ M, P (L.obj M)) :
    DerivedCategory.Plus A ⥤ (homologyIn P).FullSubcategory :=
  (homologyIn P).lift L.mapDerivedCategoryPlus (homologyIn_mapDerivedCategoryPlus_obj P hP)

/-- The derived adjunction `L ⊣ RR`, restricted to `D⁺(A)` and `D⁺_P(B)`. -/
def derivedPlusHomologyInAdjunction [P.IsClosedUnderIsomorphisms] (hP : ∀ M, P (L.obj M)) :
    derivedPlusHomologyInFunctor P hP ⊣ (homologyIn P).ι ⋙ R.rightDerivedFunctorPlus :=
  (derivedPlusAdjunction adj).restrictFullyFaithful (Functor.FullyFaithful.id _)
    (homologyIn P).fullyFaithfulι (Iso.refl _) (Iso.refl _)

include adj in
/-- The unit of `derivedPlusHomologyInAdjunction` is invertible at `K` of `D⁺(A)` whenever the
unit of `derivedPlusAdjunction` is invertible at every object of `D⁺(A)`. -/
theorem isIso_derivedPlusHomologyInAdjunction_unit_app [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P (L.obj M)) (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (K : DerivedCategory.Plus A) :
    IsIso ((derivedPlusHomologyInAdjunction adj P hP).unit.app K) := by
  change IsIso ((𝟭 _).map ((derivedPlusHomologyInAdjunction adj P hP).unit.app K))
  rw [derivedPlusHomologyInAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  have := hunit K
  dsimp
  infer_instance

include adj in
/-- The counit of `derivedPlusHomologyInAdjunction` is invertible at every object `E` of
`D⁺_P(B)`, provided the unit of `derivedPlusAdjunction` is invertible at every object of `D⁺(A)`
and every object satisfying `P` lies in the essential image of `L`. -/
theorem isIso_derivedPlusHomologyInAdjunction_counit_app [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P (L.obj M)) (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) (E : (homologyIn P).FullSubcategory) :
    IsIso ((derivedPlusHomologyInAdjunction adj P hP).counit.app E) := by
  suffices IsIso ((homologyIn P).ι.map
      ((derivedPlusHomologyInAdjunction adj P hP).counit.app E)) from
    isIso_of_reflects_iso _ (homologyIn P).ι
  rw [derivedPlusHomologyInAdjunction, Adjunction.map_restrictFullyFaithful_counit_app]
  have := isIso_derivedPlusAdjunction_counit_app_of_homologyIn adj P hunit hsurj E.obj E.property
  dsimp
  infer_instance

/-- **`L : D⁺(A) ≌ D⁺_P(B)` with quasi-inverse `RR`**, for an exact functor `L` with right
adjoint `R`, a class `P` of objects of `B` closed under isomorphisms, containing the image of `L`
and contained in its essential image, granted that the derived unit `K ⟶ RR(LK)` is invertible
for every `K` of `D⁺(A)`. -/
def derivedPlusEquivalenceOfHomologyIn [P.IsClosedUnderIsomorphisms] (hP : ∀ M, P (L.obj M))
    (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) :
    DerivedCategory.Plus A ≌ (homologyIn P).FullSubcategory :=
  haveI := isIso_derivedPlusHomologyInAdjunction_unit_app adj P hP hunit
  haveI := isIso_derivedPlusHomologyInAdjunction_counit_app adj P hP hunit hsurj
  (derivedPlusHomologyInAdjunction adj P hP).toEquivalence

/-- **The forward functor of the equivalence is `L`**, restricted to `D⁺(A) ⥤ D⁺_P(B)`. -/
theorem derivedPlusEquivalenceOfHomologyIn_functor [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P (L.obj M)) (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) :
    (derivedPlusEquivalenceOfHomologyIn adj P hP hunit hsurj).functor =
      (homologyIn P).lift L.mapDerivedCategoryPlus (homologyIn_mapDerivedCategoryPlus_obj P hP) :=
  rfl

/-- **The quasi-inverse of the equivalence is `RR`**, restricted to `D⁺_P(B) ⥤ D⁺(A)`. -/
theorem derivedPlusEquivalenceOfHomologyIn_inverse [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P (L.obj M)) (hunit : ∀ K, IsIso ((derivedPlusAdjunction adj).unit.app K))
    (hsurj : ∀ M, P M → L.essImage M) :
    (derivedPlusEquivalenceOfHomologyIn adj P hP hunit hsurj).inverse =
      (homologyIn P).ι ⋙ R.rightDerivedFunctorPlus :=
  rfl

end CategoryTheory.Adjunction

end
