module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms

/-!
# An exact left adjoint as an equivalence `D⁺_𝒬(𝒞) ≌ D⁺_𝒫(𝒟)`

Let `L ⊣ R` be an adjunction between abelian categories `𝒞` and `𝒟` with enough injectives, with
`L` exact, so that the right derived functors form an adjunction `RL ⊣ RR` on bounded below
derived categories, `RL` being `L` applied degreewise. Let `𝒬 ⊂ 𝒞` and `𝒫 ⊂ 𝒟` be classes of
objects, closed under isomorphisms, with `𝒬` containing the zero objects, and write `D⁺_𝒬(𝒞)`
and `D⁺_𝒫(𝒟)` for the bounded below objects all of whose cohomology objects lie in `𝒬`,
respectively `𝒫`. Suppose that

* `L` carries `𝒬` into `𝒫`, and an object `N` with `L(N) ∈ 𝒫` lies in `𝒬`;
* every object of `𝒫` is isomorphic to `L(N)` for some `N ∈ 𝒬`;
* the unit `K ⟶ RR(RL(K))` is an isomorphism for every `K` in `D⁺_𝒬(𝒞)`.

Then `RL : D⁺_𝒬(𝒞) ⟶ D⁺_𝒫(𝒟)` is an equivalence with quasi-inverse `RR`. This is the formal
argument of Stacks 0D7U, in the generality needed when cohomological descent only holds for a
class of coefficients, such as torsion sheaves for a proper hypercovering.

## The argument

The counit `RL(RR(M)) ⟶ M` is invertible at an object `M` of `𝒫` placed in degree zero: writing
`M = L(N)` with `N ∈ 𝒬`, the object `M[0]` is `RL(N[0])`, and the counit is invertible at `RL`
of an object at which the unit is invertible. The counit is a shift-compatible transformation
between exact functors which both preserve `D^{≥m}`, so the dévissage along the truncation
triangles makes it invertible at every object of `D⁺_𝒫(𝒟)`. For such an `M` the cohomology
objects of `RR(M)` lie in `𝒬`, because `L` of them are the cohomology objects of
`RL(RR(M)) ≅ M`. So both functors restrict, the restricted adjunction has invertible unit and
counit, and it is an equivalence.

## Main definitions

* `CategoryTheory.Adjunction.rightDerivedFunctorPlusEquivalenceOfProp`: **the equivalence**
  `D⁺_𝒬(𝒞) ≌ D⁺_𝒫(𝒟)`.

## Main results

* `CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlus_counit_app_of_prop`: the counit of
  `RL ⊣ RR` is invertible on `D⁺_𝒫(𝒟)`.
* `CategoryTheory.Adjunction.rightDerivedFunctorPlusEquivalenceOfProp_functor` and
  `rightDerivedFunctorPlusEquivalenceOfProp_inverse`: its two functors are the restrictions of
  `RL` and `RR`.

## Implementation notes

`D⁺_𝒬(𝒞)` is the preimage under the inclusion `D⁺(𝒞) ⟶ D(𝒞)` of
`DerivedCategoryB.derivedCategoryB 𝒬`. The statements hold for any model of the derived
categories. The compatibility of `RR` with the shift used in the dévissage is the one induced by
the adjunction from that of `RL`; it only enters the proof of the counit statement.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategoryB

open DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- **An object of a class containing the zero objects, placed in degree zero, has all its
cohomology objects in the class.** Its cohomology is the object itself in degree zero and
vanishes elsewhere. -/
theorem derivedCategoryB_singleFunctor_obj_zero (B : ObjectProperty A)
    [B.IsClosedUnderIsomorphisms] [B.ContainsZero] (M : A) (hM : B M) :
    derivedCategoryB B ((singleFunctor A 0).obj M) := fun n ↦ by
  by_cases hn : n = 0
  · subst hn
    exact B.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app M).symm hM
  · refine B.prop_of_isZero ?_
    rcases lt_or_gt_of_ne hn with h | h
    · exact isZero_of_isGE _ 0 n h
    · exact isZero_of_isLE _ 0 n h

end DerivedCategoryB

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ R) (Q : ObjectProperty C) (P : ObjectProperty D)

omit [EnoughInjectives D] in
/-- **`RL` carries `D⁺_𝒬(𝒞)` into `D⁺_𝒫(𝒟)`** as soon as `L` carries `𝒬` into `𝒫`: the right
derived functor of the exact functor `L` commutes with cohomology. -/
theorem derivedCategoryB_rightDerivedFunctorPlus_obj_of_prop [P.IsClosedUnderIsomorphisms]
    (hmap : ∀ N, Q N → P (L.obj N)) (K : DerivedCategory.Plus C)
    (hK : (DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι K) :
    (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι
      (L.rightDerivedFunctorPlus.obj K) := fun q ↦
  P.prop_of_iso ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso L q).app K).symm
    (hmap _ (hK q))

/-- **The counit of `RL ⊣ RR` is invertible on `D⁺_𝒫(𝒟)`**, granted that the unit is invertible
on `D⁺_𝒬(𝒞)` and that every object of `𝒫` is isomorphic to `L(N)` for some `N ∈ 𝒬`. -/
theorem isIso_rightDerivedFunctorPlus_counit_app_of_prop [Q.IsClosedUnderIsomorphisms]
    [Q.ContainsZero]
    (hunit : ∀ K, (DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι K →
      IsIso (adj.rightDerivedFunctorPlus.unit.app K))
    (hsurj : ∀ M, P M → ∃ N, Q N ∧ Nonempty (L.obj N ≅ M)) (M : DerivedCategory.Plus D)
    (hM : (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι M) :
    IsIso (adj.rightDerivedFunctorPlus.counit.app M) := by
  set adj' := adj.rightDerivedFunctorPlus
  let := L.commShiftRightDerivedFunctorPlus
  have := L.isTriangulated_rightDerivedFunctorPlus
  let := adj'.rightAdjointCommShift ℤ
  let := adj'.commShift_of_leftAdjoint ℤ
  have := Adjunction.IsTriangulated.mk' adj'
  have := adj'.isTriangulated_rightAdjoint
  obtain ⟨a, ha⟩ := M.property
  have hMa : M.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff M a).1 ha
  refine DerivedCategory.Plus.isIso_app_of_bounded_below adj'.counit
    (fun Y m hY ↦ by
      have : (R.rightDerivedFunctorPlus.obj Y).IsGE m :=
        Functor.isGE_rightDerivedFunctorPlus_obj R Y m
      exact Functor.isGE_rightDerivedFunctorPlus_obj L _ m)
    (fun _ _ h ↦ h) M a hMa (fun q ↦ ?_)
  obtain ⟨N, hN, ⟨e⟩⟩ := hsurj _ (hM q)
  have hu : IsIso (adj'.unit.app ((DerivedCategory.Plus.singleFunctor C 0).obj N)) :=
    hunit _ (DerivedCategoryB.derivedCategoryB_singleFunctor_obj_zero Q N hN)
  let e' : L.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj
        ((DerivedCategory.Plus.homologyFunctor D q).obj M) :=
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso L 0).app N).symm ≪≫
      (DerivedCategory.Plus.singleFunctor D 0).mapIso e
  exact (NatTrans.isIso_app_iff_of_iso adj'.counit e').mp
    (adj'.isIso_counit_app_obj_of_isIso_unit_app _ hu)

/-- **`RR` carries `D⁺_𝒫(𝒟)` into `D⁺_𝒬(𝒞)`**, under the hypotheses of
`isIso_rightDerivedFunctorPlus_counit_app_of_prop` and granted that an object `N` with
`L(N) ∈ 𝒫` lies in `𝒬`: `L` of a cohomology object of `RR(M)` is the corresponding cohomology
object of `RL(RR(M)) ≅ M`. -/
theorem derivedCategoryB_rightDerivedFunctorPlus_rightAdjoint_obj_of_prop
    [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hrefl : ∀ N, P (L.obj N) → Q N)
    (hunit : ∀ K, (DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι K →
      IsIso (adj.rightDerivedFunctorPlus.unit.app K))
    (hsurj : ∀ M, P M → ∃ N, Q N ∧ Nonempty (L.obj N ≅ M)) (M : DerivedCategory.Plus D)
    (hM : (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι M) :
    (DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι
      (R.rightDerivedFunctorPlus.obj M) := fun q ↦ by
  have := isIso_rightDerivedFunctorPlus_counit_app_of_prop adj Q P hunit hsurj M hM
  exact hrefl _ (P.prop_of_iso
    (((DerivedCategory.Plus.homologyFunctor D q).mapIso
        (asIso (adj.rightDerivedFunctorPlus.counit.app M))).symm ≪≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso L q).app _) (hM q))

variable [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero] [P.IsClosedUnderIsomorphisms]
  (hmap : ∀ N, Q N → P (L.obj N)) (hrefl : ∀ N, P (L.obj N) → Q N)
  (hunit : ∀ K, (DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι K →
    IsIso (adj.rightDerivedFunctorPlus.unit.app K))
  (hsurj : ∀ M, P M → ∃ N, Q N ∧ Nonempty (L.obj N ≅ M))

/-- `RL` restricted to `D⁺_𝒬(𝒞) ⥤ D⁺_𝒫(𝒟)`. -/
abbrev rightDerivedFunctorPlusOfProp :
    ((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).FullSubcategory ⥤
      ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).FullSubcategory :=
  ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).lift
    (((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).ι ⋙
      L.rightDerivedFunctorPlus)
    (fun K ↦ derivedCategoryB_rightDerivedFunctorPlus_obj_of_prop Q P hmap K.obj K.property)

/-- `RR` restricted to `D⁺_𝒫(𝒟) ⥤ D⁺_𝒬(𝒞)`. -/
abbrev rightDerivedFunctorPlusRightAdjointOfProp :
    ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).FullSubcategory ⥤
      ((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).FullSubcategory :=
  ((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).lift
    (((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).ι ⋙
      R.rightDerivedFunctorPlus)
    (fun M ↦ derivedCategoryB_rightDerivedFunctorPlus_rightAdjoint_obj_of_prop adj Q P hrefl
      hunit hsurj M.obj M.property)

/-- The restriction of `RL ⊣ RR` to `D⁺_𝒬(𝒞)` and `D⁺_𝒫(𝒟)`. -/
def rightDerivedFunctorPlusAdjunctionOfProp :
    rightDerivedFunctorPlusOfProp Q P hmap ⊣
      rightDerivedFunctorPlusRightAdjointOfProp adj Q P hrefl hunit hsurj :=
  adj.rightDerivedFunctorPlus.restrictFullyFaithful
    ((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).fullyFaithfulι
    ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- **An exact left adjoint as an equivalence `D⁺_𝒬(𝒞) ≌ D⁺_𝒫(𝒟)`.** Let `L ⊣ R` be an
adjunction of abelian categories with enough injectives, with `L` exact, and let `𝒬 ⊂ 𝒞` and
`𝒫 ⊂ 𝒟` be classes of objects closed under isomorphisms, `𝒬` containing the zero objects. If
`L` carries `𝒬` into `𝒫` and reflects it, every object of `𝒫` is `L(N)` for some `N ∈ 𝒬`, and
the unit `K ⟶ RR(RL(K))` is invertible on `D⁺_𝒬(𝒞)`, then `RL : D⁺_𝒬(𝒞) ⟶ D⁺_𝒫(𝒟)` is an
equivalence with quasi-inverse `RR`.

The restricted left adjoint is fully faithful because the unit is invertible on its source, the
restricted right adjoint because the counit is invertible on its source
(`isIso_rightDerivedFunctorPlus_counit_app_of_prop`). -/
def rightDerivedFunctorPlusEquivalenceOfProp :
    ((DerivedCategoryB.derivedCategoryB Q).inverseImage DerivedCategory.Plus.ι).FullSubcategory ≌
      ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).FullSubcategory :=
  letI hL := adj.rightDerivedFunctorPlus.fullyFaithfulιCompLeftAdjointOfLE hunit
  letI hR := adj.rightDerivedFunctorPlus.fullyFaithfulιCompRightAdjointOfLE
    (fun M hM ↦ isIso_rightDerivedFunctorPlus_counit_app_of_prop adj Q P hunit hsurj M hM)
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (rightDerivedFunctorPlusAdjunctionOfProp adj Q P hmap hrefl hunit hsurj).toEquivalence

/-- **The forward functor of the equivalence is `RL`.** -/
theorem rightDerivedFunctorPlusEquivalenceOfProp_functor :
    (rightDerivedFunctorPlusEquivalenceOfProp adj Q P hmap hrefl hunit hsurj).functor =
      rightDerivedFunctorPlusOfProp Q P hmap :=
  rfl

/-- **The quasi-inverse of the equivalence is `RR`.** -/
theorem rightDerivedFunctorPlusEquivalenceOfProp_inverse :
    (rightDerivedFunctorPlusEquivalenceOfProp adj Q P hmap hrefl hunit hsurj).inverse =
      rightDerivedFunctorPlusRightAdjointOfProp adj Q P hrefl hunit hsurj :=
  rfl

end CategoryTheory.Adjunction

end
