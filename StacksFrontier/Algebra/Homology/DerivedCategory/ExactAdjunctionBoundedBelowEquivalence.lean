module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowComparisonDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# An exact left adjoint as an equivalence of bounded below derived categories

Let `L ⊣ R` be an adjunction between abelian categories `𝒞` and `𝒟` with enough injectives, with
`L` exact, and let `𝒜 ⊂ 𝒟` be a class of objects containing `L(X)` for every `X`. The right
derived functors form an adjunction `RL ⊣ RR` on bounded below derived categories, and `RL` is
`L` applied degreewise, so it takes values in `D⁺_𝒜(𝒟)`, the bounded below objects all of whose
cohomology objects lie in `𝒜`. Suppose that

* the unit `K ⟶ RR(RL(K))` is an isomorphism for every `K` in `D⁺(𝒞)`, and
* every object of `𝒜` is isomorphic to `L(X)` for some `X`.

Then `RL : D⁺(𝒞) ⟶ D⁺_𝒜(𝒟)` is an equivalence of categories with quasi-inverse `RR`.

## Main definitions

* `CategoryTheory.Adjunction.rightDerivedFunctorPlusEquivalence`: **the equivalence**
  `D⁺(𝒞) ≌ D⁺_𝒜(𝒟)`.

## Main results

* `CategoryTheory.Adjunction.derivedCategoryB_rightDerivedFunctorPlus_obj`: `RL` takes values in
  `D⁺_𝒜(𝒟)`.
* `CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlus_counit_app`: the counit of `RL ⊣ RR`
  is invertible on `D⁺_𝒜(𝒟)`.
* `CategoryTheory.Adjunction.rightDerivedFunctorPlusEquivalence_functor` and
  `rightDerivedFunctorPlusEquivalence_inverse`: the two functors of the equivalence are `RL` and
  `RR`.

## Implementation notes

`D⁺_𝒜(𝒟)` is the preimage under the inclusion `D⁺(𝒟) ⟶ D(𝒟)` of
`DerivedCategoryB.derivedCategoryB 𝒜`, the objects all of whose cohomology objects lie in `𝒜`. No
closure property of `𝒜` beyond closure under isomorphisms is assumed.

The equivalence is the restricted adjunction, so its two functors are the restrictions of `RL`
and of `RR` on the nose.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0DH9](https://stacks.math.columbia.edu/tag/0DH9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Adjunction

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ R) (P : ObjectProperty D)

omit [EnoughInjectives D] in
/-- **`RL` takes values in `D⁺_𝒜(𝒟)`** as soon as `L` takes values in `𝒜`. -/
theorem derivedCategoryB_rightDerivedFunctorPlus_obj [P.IsClosedUnderIsomorphisms]
    (hLP : ∀ X, P (L.obj X)) (K : DerivedCategory.Plus C) :
    (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι
      (L.rightDerivedFunctorPlus.obj K) := fun q ↦
  P.prop_of_iso ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso L q).app K).symm
    (hLP _)

/-- **The counit of `RL ⊣ RR` is invertible on `D⁺_𝒜(𝒟)`**, granted that the unit is invertible
on `D⁺(𝒞)` and that every object of `𝒜` is isomorphic to `L(X)` for some `X`. -/
theorem isIso_rightDerivedFunctorPlus_counit_app
    (hunit : ∀ K, IsIso (adj.rightDerivedFunctorPlus.unit.app K))
    (hP : ∀ F, P F → L.essImage F) (M : DerivedCategory.Plus D)
    (hM : (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι M) :
    IsIso (adj.rightDerivedFunctorPlus.counit.app M) := by
  set adj' := adj.rightDerivedFunctorPlus
  have : IsIso adj'.unit := NatIso.isIso_of_isIso_app _
  have : L.rightDerivedFunctorPlus.Full := adj'.fullyFaithfulLOfIsIsoUnit.full
  have hQ : ∀ N, L.rightDerivedFunctorPlus.essImage N → IsIso (adj'.counit.app N) := by
    rintro N ⟨K, ⟨e⟩⟩
    exact (NatTrans.isIso_app_iff_of_iso adj'.counit e).mp
      (adj'.isIso_counit_app_obj_of_isIso_unit_app K (hunit K))
  have hsingle : ∀ F, L.essImage F →
      L.rightDerivedFunctorPlus.essImage ((DerivedCategory.Plus.singleFunctor D 0).obj F) := by
    rintro F ⟨X, ⟨e⟩⟩
    exact ⟨(DerivedCategory.Plus.singleFunctor C 0).obj X,
      ⟨((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso L 0).app X).symm ≪≫
        (DerivedCategory.Plus.singleFunctor D 0).mapIso e⟩⟩
  obtain ⟨a, ha⟩ := M.property
  have hMa : M.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff M a).1 ha
  refine (DerivedCategory.Plus.isIso_iff _).2 fun q ↦ ?_
  by_cases haq : a ≤ q
  · set T := (DerivedCategory.Plus.TStructure.t.truncLE q).obj M
    set j : T ⟶ M := (DerivedCategory.Plus.TStructure.t.truncLEι q).app M
    have hTa : T.IsGE a := inferInstance
    have hTq : T.IsLE q := inferInstance
    have hj : ∀ p ≤ q, IsIso ((DerivedCategory.Plus.homologyFunctor D p).map j) :=
      fun p hp ↦ DerivedCategory.Plus.isIso_homologyMap_truncLEι_app M p q hp
    have hn : ((q - a).toNat : ℤ) = q - a := Int.toNat_of_nonneg (by omega)
    have hT : L.rightDerivedFunctorPlus.essImage T := by
      refine DerivedCategory.Plus.prop_of_isGE_of_isLE _ a (q - a).toNat T hTa
        (by rw [hn]; simpa using hTq) fun p hp₁ hp₂ ↦ hsingle _ ?_
      rw [hn] at hp₂
      have := hj p (by omega)
      exact L.essImage.prop_of_iso
        (asIso ((DerivedCategory.Plus.homologyFunctor D p).map j)).symm (hP _ (hM p))
    have hεT := hQ T hT
    have := hj q le_rfl
    have hRj : IsIso ((DerivedCategory.Plus.homologyFunctor C q).map
        (R.rightDerivedFunctorPlus.map j)) := by
      have hGE : (R.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.TStructure.t.truncGT q).obj M)).IsGE (q + 1) :=
        Functor.isGE_rightDerivedFunctorPlus_obj R _ (q + 1)
      exact DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃
        (R.rightDerivedFunctorPlus.mapTriangle.obj
          ((DerivedCategory.Plus.TStructure.t.triangleLEGT q).obj M))
        (R.rightDerivedFunctorPlus.map_distinguished _
          (DerivedCategory.Plus.TStructure.t.triangleLEGT_distinguished q M)) q (q + 1) hGE
        (by omega)
    have hLRj : IsIso ((DerivedCategory.Plus.homologyFunctor D q).map
        (L.rightDerivedFunctorPlus.map (R.rightDerivedFunctorPlus.map j))) := by
      refine (NatIso.isIso_map_iff
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso L q) _).2 ?_
      dsimp
      infer_instance
    have hsq : L.rightDerivedFunctorPlus.map (R.rightDerivedFunctorPlus.map j) ≫
        adj'.counit.app M = adj'.counit.app T ≫ j := adj'.counit.naturality j
    have hcomp : IsIso ((DerivedCategory.Plus.homologyFunctor D q).map
        (L.rightDerivedFunctorPlus.map (R.rightDerivedFunctorPlus.map j)) ≫
        (DerivedCategory.Plus.homologyFunctor D q).map (adj'.counit.app M)) := by
      rw [← Functor.map_comp, hsq, Functor.map_comp]; infer_instance
    exact IsIso.of_isIso_comp_left ((DerivedCategory.Plus.homologyFunctor D q).map
      (L.rightDerivedFunctorPlus.map (R.rightDerivedFunctorPlus.map j))) _
  · have : (R.rightDerivedFunctorPlus.obj M).IsGE a :=
      Functor.isGE_rightDerivedFunctorPlus_obj R M a
    have : ((R.rightDerivedFunctorPlus ⋙ L.rightDerivedFunctorPlus).obj M).IsGE a :=
      Functor.isGE_rightDerivedFunctorPlus_obj L _ a
    exact IsZero.isIso (DerivedCategory.Plus.isZero_homology_of_isGE' _ a q (by omega))
      (DerivedCategory.Plus.isZero_homology_of_isGE' M a q (by omega)) _

variable [P.IsClosedUnderIsomorphisms] (hLP : ∀ X, P (L.obj X))
  (hunit : ∀ K, IsIso (adj.rightDerivedFunctorPlus.unit.app K))
  (hP : ∀ F, P F → L.essImage F)

/-- The restriction of `RL ⊣ RR` to `D⁺(𝒞)` and `D⁺_𝒜(𝒟)`. -/
def rightDerivedFunctorPlusRestrictedAdjunction :
    ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).lift
        L.rightDerivedFunctorPlus (derivedCategoryB_rightDerivedFunctorPlus_obj P hLP) ⊣
      ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).ι ⋙
        R.rightDerivedFunctorPlus :=
  adj.rightDerivedFunctorPlus.restrictFullyFaithful (Functor.FullyFaithful.id _)
    ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- **An exact left adjoint as an equivalence of bounded below derived categories.** Let
`L ⊣ R` be an adjunction of abelian categories with enough injectives, with `L` exact, and let
`𝒜 ⊂ 𝒟` be a class of objects closed under isomorphisms containing every `L(X)`. If the unit
`K ⟶ RR(RL(K))` is invertible for every `K` in `D⁺(𝒞)` and every object of `𝒜` is isomorphic to
some `L(X)`, then `RL : D⁺(𝒞) ⟶ D⁺_𝒜(𝒟)` is an equivalence with quasi-inverse `RR`. -/
def rightDerivedFunctorPlusEquivalence :
    DerivedCategory.Plus C ≌
      ((DerivedCategoryB.derivedCategoryB P).inverseImage
        DerivedCategory.Plus.ι).FullSubcategory :=
  letI : IsIso adj.rightDerivedFunctorPlus.unit := NatIso.isIso_of_isIso_app _
  letI hL : (((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).lift
      L.rightDerivedFunctorPlus
      (derivedCategoryB_rightDerivedFunctorPlus_obj P hLP)).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful
      (G := ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).ι)
      adj.rightDerivedFunctorPlus.fullyFaithfulLOfIsIsoUnit
  letI hR := adj.rightDerivedFunctorPlus.fullyFaithfulιCompRightAdjointOfLE
    (Q := (DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι)
    (fun M hM ↦ isIso_rightDerivedFunctorPlus_counit_app adj P hunit hP M hM)
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (rightDerivedFunctorPlusRestrictedAdjunction adj P hLP).toEquivalence

/-- **The forward functor of the equivalence is `RL`.** -/
theorem rightDerivedFunctorPlusEquivalence_functor :
    (rightDerivedFunctorPlusEquivalence adj P hLP hunit hP).functor =
      ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).lift
        L.rightDerivedFunctorPlus (derivedCategoryB_rightDerivedFunctorPlus_obj P hLP) :=
  rfl

/-- **The quasi-inverse of the equivalence is `RR`.** -/
theorem rightDerivedFunctorPlusEquivalence_inverse :
    (rightDerivedFunctorPlusEquivalence adj P hLP hunit hP).inverse =
      ((DerivedCategoryB.derivedCategoryB P).inverseImage DerivedCategory.Plus.ι).ι ⋙
        R.rightDerivedFunctorPlus :=
  rfl

end CategoryTheory.Adjunction
