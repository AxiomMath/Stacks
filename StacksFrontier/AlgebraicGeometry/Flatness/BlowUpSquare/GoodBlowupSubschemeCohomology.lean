module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupCohomologyRank
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDivisorSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodChartSubschemeRank
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0F8X: the closed subscheme of `D'` on which `Li^*Q` has locally free cohomology

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks
tag 0GTY, `D' = b⁻¹D`, and `Q = Lη_{ℐ'}Lb^*M` the object of Stacks tag 0F8U.  Let `W ⊆ X` be the
maximal open over which the cohomology sheaves of `M` are locally free.  Tag 0F8X asserts a
closed immersion `i : T ⟶ D'` of finite presentation with (1) `D' ∩ b⁻¹(W) ⊆ T` scheme
theoretically, (2) `Li^*Q` has locally free cohomology sheaves, and (3) at `t ∈ T` over `x ∈ W`
the rank of `H^n(Li^*Q)_t` is the rank of `H^n(M)_x`.

The source proof applies Stacks tag 0GTZ to the pulled-back triple `(X', D', Lb^*M)`, which is
good, and uses that `b⁻¹(W)` lies in the locus where `Lb^*M` has locally free cohomology, `b`
being an isomorphism over `W` (tag 0F8W).  `T` is the closed subscheme of tag 0GTZ for the
pulled-back triple.

## Main results

* `isFiniteLocallyFree_etaDerivedPullbackRestrictHomology_of_isGoodOver` and
  `free_finrank_stalk_etaDerivedPullbackRestrictHomology_of_isGoodOver`: parts (2) and (3) for
  any `b` satisfying condition (1) of tag 0GTY and flat over `W`.
* `exists_closedSubscheme_goodBlowup`: **Stacks Tag 0F8X**.

## References

* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The closed subscheme of Stacks tag 0GTZ for the triple pulled back along a morphism good for
the triple. -/
abbrev pullbackSubscheme {X' : Scheme.{u}} (b : X' ⟶ S.X) (hb : S.IsGoodOver b) :
    (S.D.comap b).subscheme.IdealSheafData :=
  (S.pullback b hb.pullbackDefined).goodChartSubscheme hb.isGoodTriple

/-- **Stacks Tag 0F8X, part (2), for a morphism good for the triple.**  The cohomology sheaves
of `Li^*Q` are finite locally free. -/
theorem isFiniteLocallyFree_etaDerivedPullbackRestrictHomology_of_isGoodOver {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : S.IsGoodOver b) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.etaDerivedPullbackRestrictHomology b hb.pullbackDefined
        ((S.pullbackSubscheme b hb).subschemeι ≫ (S.D.comap b).subschemeι) n) :=
  isFiniteLocallyFree_homology_goodChartSubscheme (S.D.comap b) hb.pullbackDefined
    (S.derivedPullbackObject b) (S.isPerfect_derivedPullbackObject b) hb.isGoodTriple n

/-- **Stacks Tag 0F8X, part (3), for a morphism good for the triple and flat over `W`.**  At a
point `t ∈ T` over `x ∈ W` the stalk of `H^n(Li^*Q)` is free of the rank of `H^n(M)_x`. -/
theorem free_finrank_stalk_etaDerivedPullbackRestrictHomology_of_isGoodOver {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : S.IsGoodOver b)
    (hflat : AlgebraicGeometry.Flat ((b ⁻¹ᵁ S.locallyFreeLocus).ι ≫ b)) (n : ℤ)
    (t : (S.pullbackSubscheme b hb).subscheme)
    (hw : (((S.pullbackSubscheme b hb).subschemeι ≫ (S.D.comap b).subschemeι) ≫ b).base t ∈
      S.locallyFreeLocus) :
    letI F := S.etaDerivedPullbackRestrictHomology b hb.pullbackDefined
      ((S.pullbackSubscheme b hb).subschemeι ≫ (S.D.comap b).subschemeι) n
    letI x := (((S.pullbackSubscheme b hb).subschemeι ≫ (S.D.comap b).subschemeι) ≫ b).base t
    letI : Module (ToType (TopCat.Presheaf.stalk (S.pullbackSubscheme b hb).subscheme.presheaf t))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) :=
      RingedSpace.moduleStalk (X := (S.pullbackSubscheme b hb).subscheme.toRingedSpace) F t
    letI : Module (ToType (S.X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) :=
      RingedSpace.moduleStalk (X := S.X.toRingedSpace) (S.cohomologySheaf n) x
    Module.Free (ToType (TopCat.Presheaf.stalk (S.pullbackSubscheme b hb).subscheme.presheaf t))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) ∧
      Module.finrank
          (ToType (TopCat.Presheaf.stalk (S.pullbackSubscheme b hb).subscheme.presheaf t))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) =
        Module.finrank (ToType (S.X.presheaf.stalk x))
          (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) := by
  let y := ((S.pullbackSubscheme b hb).subschemeι ≫ (S.D.comap b).subschemeι).base t
  have hL2 := fun i =>
    S.freeAndFiniteStalk_and_finrank_homology_derivedPullbackObject b hflat y hw i
  have hy : y ∈ (S.pullback b hb.pullbackDefined).locallyFreeLocus := fun i => (hL2 i).1
  obtain ⟨h1, h2⟩ := free_finrank_stalk_homology_goodChartSubscheme (S.D.comap b)
    hb.pullbackDefined (S.derivedPullbackObject b) (S.isPerfect_derivedPullbackObject b)
    hb.isGoodTriple n t hy
  exact ⟨h1, h2.trans (hL2 n).2⟩

/-- **Stacks Tag 0F8X.**  In Situation 0F8S let `b : X' ⟶ X` be the morphism of tag 0GTY,
`D' = b⁻¹D`, `Q = Lη_{ℐ'}Lb^*M` as in tag 0F8U, and `W ⊆ X` the maximal open where the
cohomology sheaves of `M` are locally free.  There is a closed subscheme `T ⊆ D'`, with
inclusion `i : T ⟶ D'` locally of finite presentation, such that
1. `D' ∩ b⁻¹(W) ⊆ T` scheme theoretically,
2. the cohomology sheaves of `Li^*Q` are finite locally free, and
3. for `t ∈ T` mapping to `x ∈ W`, `H^n(Li^*Q)_t` is free over `𝒪_{T,t}` of the rank of
   `H^n(M)_x` over `𝒪_{X,x}`. -/
@[stacks 0F8X "the closed immersion `i : T → D'` of finite presentation (locally of finite \
presentation) with parts (1), (2) and (3), for the morphism `b` of tag 0GTY, \
AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase; `Li^*Q` is \
etaDerivedPullbackRestrict of `Q = Lη_{ℐ'}Lb^*M` along `T → D' → X'`, and the rank of a free \
stalk is Module.finrank"]
theorem exists_closedSubscheme_goodBlowup :
    ∃ T : (S.D.comap S.goodBlowupToBase).subscheme.IdealSheafData,
      LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((S.D.comap S.goodBlowupToBase).subschemeι ⁻¹ᵁ
          (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ ∧
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isGoodOver_goodBlowupToBase.pullbackDefined
          (T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n)) ∧
      ∀ (n : ℤ) (t : T.subscheme)
        (_ : ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
          S.goodBlowupToBase).base t ∈ S.locallyFreeLocus),
        letI F := S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isGoodOver_goodBlowupToBase.pullbackDefined
          (T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n
        letI x := ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
          S.goodBlowupToBase).base t
        letI : Module (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
            (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) :=
          RingedSpace.moduleStalk (X := T.subscheme.toRingedSpace) F t
        letI : Module (ToType (S.X.presheaf.stalk x))
            (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) :=
          RingedSpace.moduleStalk (X := S.X.toRingedSpace) (S.cohomologySheaf n) x
        Module.Free (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
            (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) ∧
          Module.finrank (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) =
            Module.finrank (ToType (S.X.presheaf.stalk x))
              (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) := by
  let hb := S.isGoodOver_goodBlowupToBase
  obtain ⟨h0, h1⟩ := S.locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase
    (S.pullbackSubscheme S.goodBlowupToBase hb)
    (fun C hI => (S.pullback S.goodBlowupToBase hb.pullbackDefined).ideal_goodChartSubscheme
      hb.isGoodTriple C hI)
  exact ⟨S.pullbackSubscheme S.goodBlowupToBase hb, h0, h1,
    S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology_of_isGoodOver _ hb,
    fun n t hw => S.free_finrank_stalk_etaDerivedPullbackRestrictHomology_of_isGoodOver _ hb
      S.flat_ι_comp_goodBlowupToBase_locallyFreeLocus n t hw⟩

end AlgebraicGeometry.ComplexAndDivisorSituation
