module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms

/-!
# Derived pullback as an equivalence of bounded below derived categories

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a flat morphism of ringed topoi, let
`𝒜 ⊂ Mod(𝒪)` and `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories, assume that `f^*` induces an
equivalence `𝒜' ⟶ 𝒜`, and that `ℱ' ⟶ Rf_*f^*ℱ'` is an isomorphism for every `ℱ'` of `𝒜'`. Then

  `Lf^* : D⁺_{𝒜'}(𝒪') ⟶ D⁺_𝒜(𝒪)`

is an equivalence of categories, with quasi-inverse `Rf_* : D⁺_𝒜(𝒪) ⟶ D⁺_{𝒜'}(𝒪')`.

## The argument

The two derived functors restrict to the bounded below subcategories: `Lf^*` because it is
degreewise pullback, which is exact and carries `𝒜'` into `𝒜`; `Rf_*` because an object of `𝒜` is
`f^*` of an object of `𝒜'`, whose pushforward is that object again by the hypothesis on the unit,
and because a bounded below object is built from its cohomology objects along the truncation
triangles.

Once restricted, the adjunction restricts (`CategoryTheory.Adjunction.restrictFullyFaithful`), and
the hypothesis on the unit propagates from the heart to all of `D⁺_{𝒜'}(𝒪')` by Tag 0D7T, while
the hypothesis on the counit propagates by Tag 0D7S. So the restricted subcategories are contained
in the two subcategories of Tags 0D7Q and 0D7R where the unit resp. the counit is invertible, on
which the two adjoints are fully faithful — and an adjunction whose two adjoints are fully
faithful is an equivalence.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.derivedAdjunctionBoundedBelow`: the restriction of
  `Lf^* ⊣ Rf_*` to the bounded below subcategories.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalence`: **the equivalence.**

## Main results

* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryBPlus_derivedPullback_obj`: `Lf^*`
  carries `D⁺_{𝒜'}(𝒪')` into `D⁺_𝒜(𝒪)`.
* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryBPlus_derivedPushforward_obj`: `Rf_*`
  carries `D⁺_𝒜(𝒪)` into `D⁺_{𝒜'}(𝒪')`.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalence_functor` and
  `derivedPullbackEquivalence_inverse`: the two functors of the equivalence are the restrictions
  of `Lf^*` and of `Rf_*`.

## Implementation notes

**Flatness and the morphism-of-sites condition are the hypotheses of the source.** As in
`StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent`, the
statements open with `letI`, because the *type* of `Lf^*` mentions the instance saying that
degreewise pullback has a left derived functor, so nothing about `Lf^*` can be written down before
that instance is in scope. Producing it from flatness inside the statement is what keeps the
statement about a *flat* morphism rather than about a morphism along which pullback happens to be
exact.

**The equivalence is not assembled from the unit and the counit by hand.** It is the restricted
adjunction, whose two adjoints are fully faithful by Tags 0D7Q and 0D7R, read through
`CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful` and
`counit_isIso_of_R_fully_faithful`. In particular no formula for the unit of the restricted
adjunction is needed anywhere, and the two functors of the equivalence are the restricted adjoints
on the nose, which is what makes `derivedPullbackEquivalence_functor` and
`derivedPullbackEquivalence_inverse` hold by definition.

**Hypothesis (2) is used only through essential surjectivity.** The statements carry the full
equivalence of the source, which is the faithful hypothesis; what the proofs consume is that every
object of `𝒜` is `f^*` of an object of `𝒜'`.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
* [Stacks Project, Tag 07RB](https://stacks.math.columbia.edu/tag/07RB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposSiteHom X Y)
  (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]

section Exact

variable [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **`Lf^*` of a module placed in degree zero is `f^*` of it, placed in degree zero.** The
derived pullback is degreewise pullback, which is exact, and an exact functor commutes with
placing an object in a single degree. -/
noncomputable def derivedPullbackSingleFunctorObjIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (f.pullbackTopos.obj M) :=
  derivedPullbackObjIso f _ ≪≫ (f.pullbackTopos.mapDerivedCategorySingleFunctor 0).app M

/-- **`H^q(Lf^*K)` is `f^*H^q(K)`**, by the same two facts. -/
noncomputable def derivedPullbackHomologyObjIso
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (q : ℤ) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
        ((derivedPullback f).obj K) ≅
      f.pullbackTopos.obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj K) :=
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).mapIso
      (derivedPullbackObjIso f K) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      f.pullbackTopos q).app K

/-- Every `ℱ` in `𝒜` placed in degree zero is `Lf^*ℱ'` for some `ℱ'` in `𝒜'` placed in degree
zero, at which the unit is invertible. -/
private theorem exists_isIso_unit_app_and_nonempty_iso_of_mem
    (P : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (P' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hP : ∀ M, P' M → P (f.pullbackTopos.obj M))
    (hEquiv : (P.lift (P'.ι ⋙ f.pullbackTopos) (fun N ↦ hP N.obj N.property)).IsEquivalence)
    (hUnit : ∀ M, P' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : P M) :
    ∃ (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)), P' N ∧
      IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N)) ∧
      Nonempty ((derivedPullback f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) := by
  have := hEquiv
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (P.lift (P'.ι ⋙ f.pullbackTopos) (fun N ↦ hP N.obj N.property)) ⟨M, hM⟩
  exact ⟨N.obj, N.property, hUnit N.obj N.property, ⟨derivedPullbackSingleFunctorObjIso f N.obj ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
        (P.ι.mapIso e)⟩⟩

variable (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))

include hA in
omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] [A'.IsWeakSerreClass] in
/-- `Lf^*` carries `D⁺_{𝒜'}(𝒪')` into `D⁺_𝒜(𝒪)`: it preserves boundedness below, and its
cohomology objects are `f^*` of those of the source. -/
theorem derivedCategoryBPlus_derivedPullback_obj_of_exact
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryBPlus A' K) :
    DerivedCategoryB.derivedCategoryBPlus A ((derivedPullback f).obj K) := by
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1
  have hGE := isGE_derivedPullback_obj f K a ha
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨a, hGE⟩, fun q ↦ ?_⟩
  exact A.prop_of_iso (derivedPullbackHomologyObjIso f K q).symm (hA _ (hK.2 q))

variable (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))

include hEquiv hUnit

omit [A.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the pushforward `Rf_*ℱ` is the object of `𝒜'` whose pullback is `ℱ`.** Write
`ℱ = f^*ℱ'` using hypothesis (2); the unit `ℱ' ⟶ Rf_*Lf^*ℱ'` is invertible by hypothesis (3), and
`Lf^*ℱ'` is `ℱ` because derived pullback is degreewise pullback. -/
theorem derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : A M) :
    DerivedCategoryB.derivedCategoryBPlus A'
      ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)) := by
  obtain ⟨N, hN', hN, ⟨eL⟩⟩ :=
    exists_isIso_unit_app_and_nonempty_iso_of_mem f A A' hA hEquiv hUnit M hM
  have eR := (@asIso _ _ _ _ _ hN).trans ((derivedPushforward f).mapIso eL)
  exact (DerivedCategoryB.derivedCategoryBPlus_isClosedUnderIsomorphisms A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A')).of_iso eR
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') N hN')

omit [A.IsWeakSerreClass] [A'.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the counit `Lf^*Rf_*ℱ ⟶ ℱ` is invertible.** Write `ℱ = f^*ℱ'`, so that `ℱ`
placed in degree zero is `Lf^*` of `ℱ'` placed in degree zero; the counit at `Lf^*ℱ'` becomes
invertible because composing it with `Lf^*` of the unit at `ℱ'`, which is invertible by hypothesis
(3), gives the identity. -/
theorem isIso_derivedCounit_app_singleFunctor_obj_of_exact
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : A M) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)) := by
  obtain ⟨N, hN', hN, ⟨eL⟩⟩ :=
    exists_isIso_unit_app_and_nonempty_iso_of_mem f A A' hA hEquiv hUnit M hM
  have hcounit := Adjunction.isIso_counit_app_obj_of_isIso_unit_app
    (derivedPullbackPushforwardAdjunctionOfExact f) _ hN
  exact (NatTrans.isIso_app_iff_of_iso
    (derivedPullbackPushforwardAdjunctionOfExact f).counit eL).mp hcounit

omit [A.IsWeakSerreClass] in
/-- `Rf_*` carries `D⁺_𝒜(𝒪)` into `D⁺_{𝒜'}(𝒪')`: it is exact, it preserves boundedness below, and
it carries the cohomology objects of its argument, placed in degree zero, into `D⁺_{𝒜'}(𝒪')`. -/
theorem derivedCategoryBPlus_derivedPushforward_obj_of_exact
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryBPlus A K) :
    DerivedCategoryB.derivedCategoryBPlus A' ((derivedPushforward f).obj K) := by
  let : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact f)
  let : (derivedPushforward f).CommShift ℤ :=
    (derivedPullbackPushforwardAdjunctionOfExact f).rightAdjointCommShift ℤ
  let : (derivedPullbackPushforwardAdjunctionOfExact f).CommShift ℤ :=
    (derivedPullbackPushforwardAdjunctionOfExact f).commShift_of_leftAdjoint ℤ
  let : (derivedPullbackPushforwardAdjunctionOfExact f).IsTriangulated :=
    Adjunction.IsTriangulated.mk' (derivedPullbackPushforwardAdjunctionOfExact f)
  let : (derivedPushforward f).IsTriangulated :=
    (derivedPullbackPushforwardAdjunctionOfExact f).isTriangulated_rightAdjoint
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1
  refine DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE (derivedPushforward f) A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A')
    (fun L m h ↦ isGE_derivedPushforward_obj f L m h) K a ha fun q ↦ ?_
  exact derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit
    _ (hK.2 q)

/-- **The restriction of the derived adjunction `Lf^* ⊣ Rf_*` to the bounded below
subcategories.** -/
noncomputable def derivedAdjunctionBoundedBelow :
    (DerivedCategoryB.derivedCategoryBPlus A).lift
        ((DerivedCategoryB.derivedCategoryBPlus A').ι ⋙ derivedPullback f)
        (fun K ↦ derivedCategoryBPlus_derivedPullback_obj_of_exact f A A' hA K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryBPlus A').lift
        ((DerivedCategoryB.derivedCategoryBPlus A).ι ⋙ derivedPushforward f)
        (fun K ↦ derivedCategoryBPlus_derivedPushforward_obj_of_exact f A A' hA hEquiv hUnit
          K.obj K.property) :=
  (derivedPullbackPushforwardAdjunctionOfExact f).restrictFullyFaithful
    (DerivedCategoryB.derivedCategoryBPlus A').fullyFaithfulι
    (DerivedCategoryB.derivedCategoryBPlus A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

omit hUnit in
/-- **The equivalence, for a morphism along which degreewise pullback is exact.** The restricted
left adjoint is fully faithful because `D⁺_{𝒜'}(𝒪')` lies in the subcategory of Tag 0D7Q where the
unit is invertible, the restricted right adjoint because `D⁺_𝒜(𝒪)` lies in the subcategory of Tag
0D7R where the counit is invertible; an adjunction whose two adjoints are fully faithful is an
equivalence. -/
noncomputable def derivedPullbackEquivalenceOfExact
    (hUnitPlus : DerivedCategoryB.derivedCategoryBPlus A' ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).unitIsIso)
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso) :
    (DerivedCategoryB.derivedCategoryBPlus A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus A).FullSubcategory :=
  letI hL := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompLeftAdjointOfLE
    hUnitPlus
  letI hR := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompRightAdjointOfLE
    hCounitPlus
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (derivedAdjunctionBoundedBelow f A A' hA hEquiv
    (fun M hM ↦ hUnitPlus _ (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') M hM))).toEquivalence

end Exact

section Descent

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (hf : SheafOfModules.IsFlatMapULift.{w, w, w} (StacksPullbackFactorization.auxHomH f).fSharp)
  (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))

include hmos hf hA

omit [A'.IsWeakSerreClass] in
/-- **Stacks 0D7U**, the assertion that derived pullback restricts. Let `f` be a flat morphism of
ringed topoi and let `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories with
`f^*𝒜' ⊂ 𝒜`. Then `Lf^*` carries `D⁺_{𝒜'}(𝒪')` into `D⁺_𝒜(𝒪)`. -/
@[stacks 0D7U "derived pullback"]
theorem derivedCategoryBPlus_derivedPullback_obj :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      DerivedCategoryB.derivedCategoryBPlus A' K →
        DerivedCategoryB.derivedCategoryBPlus A ((derivedPullback f).obj K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  exact derivedCategoryBPlus_derivedPullback_obj_of_exact f A A' hA

variable (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)

include hEquiv

omit [A.IsWeakSerreClass] in
/-- **Stacks 0D7U**, the assertion that derived pushforward restricts. Under the hypotheses of the
source — `f` flat, `f^*` inducing an equivalence `𝒜' ⟶ 𝒜`, and the unit `ℱ' ⟶ Rf_*f^*ℱ'`
invertible on `𝒜'` — the pushforward `Rf_*` carries `D⁺_𝒜(𝒪)` into `D⁺_{𝒜'}(𝒪')`. -/
@[stacks 0D7U "derived pushforward"]
theorem derivedCategoryBPlus_derivedPushforward_obj :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) →
      ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
        DerivedCategoryB.derivedCategoryBPlus A K →
          DerivedCategoryB.derivedCategoryBPlus A' ((derivedPushforward f).obj K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  exact fun hUnit ↦ derivedCategoryBPlus_derivedPushforward_obj_of_exact f A A' hA hEquiv hUnit

/-- **Stacks 0D7U.** For a flat morphism of ringed topoi `f` and weak Serre subcategories
`𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` such that `f^*` induces an equivalence `𝒜' ⟶ 𝒜` and the unit
`ℱ' ⟶ Rf_*f^*ℱ'` is invertible for every `ℱ'` of `𝒜'`, the derived pullback is an **equivalence**
`D⁺_{𝒜'}(𝒪') ≌ D⁺_𝒜(𝒪)`.

The hypothesis on the unit propagates from `𝒜'` to all of `D⁺_{𝒜'}(𝒪')` by Tag 0D7T, and the
corresponding statement for the counit from `𝒜` to all of `D⁺_𝒜(𝒪)` by Tag 0D7S. -/
@[stacks 0D7U "equivalence"]
noncomputable def derivedPullbackEquivalence
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    (DerivedCategoryB.derivedCategoryBPlus A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus A).FullSubcategory :=
  letI := f.pullbackTopos_preservesFiniteLimits hmos hf
  letI := f.pullbackTopos_preservesFiniteColimits
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  derivedPullbackEquivalenceOfExact f A A' hA hEquiv
    (fun K hK ↦ isIso_derivedUnit_app_of_isIso_homology f hmos hf K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦ hUnit _ (hK.2 q))
    (fun K hK ↦ isIso_derivedCounit_app_of_isIso_homology f hmos hf K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦
        isIso_derivedCounit_app_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit _ (hK.2 q))

/-- **Stacks 0D7U**, the identification of the forward functor of the equivalence with the
restriction of the derived pullback. -/
@[stacks 0D7U "forward functor"]
theorem derivedPullbackEquivalence_functor
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (derivedPullbackEquivalence f A A' hmos hf hA hEquiv hUnit).functor =
      (DerivedCategoryB.derivedCategoryBPlus A).lift
        ((DerivedCategoryB.derivedCategoryBPlus A').ι ⋙ derivedPullback f)
        (fun K ↦ derivedCategoryBPlus_derivedPullback_obj f A A' hmos hf hA K.obj K.property) :=
  rfl

/-- **Stacks 0D7U**, the identification of the quasi-inverse of the equivalence with the
restriction of the derived pushforward. -/
@[stacks 0D7U "quasi-inverse"]
theorem derivedPullbackEquivalence_inverse
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (derivedPullbackEquivalence f A A' hmos hf hA hEquiv hUnit).inverse =
      (DerivedCategoryB.derivedCategoryBPlus A').lift
        ((DerivedCategoryB.derivedCategoryBPlus A).ι ⋙ derivedPushforward f)
        (fun K ↦ derivedCategoryBPlus_derivedPushforward_obj f A A' hmos hf hA hEquiv hUnit
          K.obj K.property) :=
  rfl

end Descent

end Stacks.Cohomology.CohomologicalDescent

end
