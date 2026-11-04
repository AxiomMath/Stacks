module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDecalagePerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDivisorSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties

/-!
# Stacks tag 0F9Y: the modification attached to a perfect complex and a divisor

Let `X` be a scheme, `D ⊂ X` an effective Cartier divisor and `M` a perfect object of
`D(𝒪_X)`, and let `W ⊂ X` be the maximal open over which the cohomology sheaves of `M` are
locally free.  Stacks tag 0F9Y collects the properties of the morphism `b : X' ⟶ X` of tag 0GTY
and of `Q = Lη_{ℐ'}Lb^*M`, where `ℐ'` is the ideal sheaf of `D' = b⁻¹D`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isProper_goodBlowupToBase`: `b` is proper.
* `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase_modification`:
  **Stacks tag 0F9Y**, every clause, for `b = goodBlowupToBase` and `Q` its décalage.

## Implementation notes

The closed subscheme `T ⊂ D'` of clause (6) is the one glued from the total obstruction ideals
of tag 0F81 on the good charts of `(X', D', Lb^*M)`,
`AlgebraicGeometry.ComplexAndDivisorSituation.goodChartSubscheme`; clause (8b) is its defining
property.  The ranks in clause (6c) are those of the stalks, which are free.

Clause (9) as printed asks for a *bounded* complex representing `Q`; that is false, and the
statement here has *locally bounded*, which is what tag 0GU0 (cited in the proof) gives.  For
`X = ⨆ₙ 𝔸¹`, `D` the origin of each copy and `M = 𝒪[n]` on the `n`-th copy, `W = X`, so `b` is
an isomorphism and `Q ≅ M` (here `η_t 𝒪[n] = t⁻ⁿ𝒪[n]`), whose cohomology is nonzero in infinitely
many degrees, so no bounded complex represents it.

## References

* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GU0](https://stacks.math.columbia.edu/tag/0GU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The morphism `b : X' ⟶ X` of Stacks tag 0GTY is proper: over each affine chart it is the
blowing up of the chart in an ideal of finite type, and the chart domains cover `X`. -/
instance isProper_goodBlowupToBase : IsProper S.goodBlowupToBase := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun C : AffineChart S => (C.U : S.X.Opens)) ?_ fun C => ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨C, hx, -⟩ := S.exists_chart_mem_le x ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hx⟩
  · obtain ⟨e, he, -⟩ := C.existsUnique_iso_preimage_blowUp
    have : IsProper (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf) :=
      isProper_blowUpToBase_of_fg _ C.fg_ideal_blowupCentreIdealSheaf
    rw [← he]
    infer_instance

attribute [local instance] isPullbackDefined_goodBlowupToBase in
/-- **Stacks tag 0F9Y.**  Let `(X, D, M)` be as in Situation 0F8S, `W ⊆ X` the maximal open over
which the cohomology sheaves of `M` are locally free, `b : X' ⟶ X` the morphism of tag 0GTY,
`D' = b⁻¹D` with ideal sheaf `ℐ'`, and `Q = Lη_{ℐ'}Lb^*M`.  Then `b` is proper and

1. `b` is an isomorphism over `X ∖ D`,
2. `b` is an isomorphism over `W`,
3. `D'` is an effective Cartier divisor,
4. `Q = Lη_{ℐ'}Lb^*M`,
5. `Q` is perfect,
6. there is a closed immersion `i : T ⟶ D'` of finite presentation with (a) `D' ∩ b⁻¹(W) ⊆ T`
   scheme theoretically, (b) `H^n(Li^*Q)` finite locally free, and (c) for `t ∈ T` over
   `x ∈ W`, `H^n(Li^*Q)_t` free of the rank of `H^n(M)_x`,
7. over an affine chart `(U, A, f, M^•)` of `(X, D, M)`, `b⁻¹U ⟶ U` is the blowing up of `U` in
   `∏ᵢ I_i(M^•, f)`,
8. over an affine chart `(V, B, g, N^•)` of `(X', D', Lb^*M)` with every `I_i(N^•, g)`
   principal, (a) `Q|_V` is the sheaf attached to `η_g N^•`, and (b) `T ∩ V ⊆ D' ∩ V` is cut
   out by `J(N^•, g)`,
9. if `M` is represented by a locally bounded complex of finite locally free modules, so is `Q`.

Clause (9) is printed with "bounded"; see the module docstring for why that is false and
"locally bounded" is the correct form. -/
@[stacks 0F9Y "the whole statement, for `b` the morphism of tag 0GTY \
(AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase) and the concrete \
`Q = Lη_{I'} Lb^* M` (etaDerivedPullbackObject, with Lη the derived décalage \
Stacks.Divisors.Eta.derivedEtaData): properness and clauses (1)--(9). `T` is the closed \
subscheme glued from the obstruction ideals J(N^•, g) of tag 0F81. Correction: clause (9) as \
printed asks for a BOUNDED complex representing Q, which is false (X = ⊔ₙ A¹, D the origins, \
M = O[n] on the n-th copy: then W = X, b is an isomorphism and Q ≅ M has unbounded cohomology); \
it is stated with LOCALLY BOUNDED, the form tag 0GU0 gives"]
theorem goodBlowupToBase_modification :
    IsProper S.goodBlowupToBase ∧
    IsIso (S.goodBlowupToBase ∣_ S.divisorComplement) ∧
    IsIso (S.goodBlowupToBase ∣_ S.locallyFreeLocus) ∧
    Stacks.Divisors.IsPullbackDefined S.goodBlowupToBase S.D ∧
    S.etaDerivedPullbackObject S.goodBlowupToBase S.isPullbackDefined_goodBlowupToBase =
      (Stacks.Divisors.Eta.derivedEtaData (S.D.comap S.goodBlowupToBase)).functor.obj
          (S.derivedPullbackObject S.goodBlowupToBase) ∧
    RingedSpace.IsPerfect (X := S.goodBlowup.toRingedSpace)
      (S.etaDerivedPullbackObject S.goodBlowupToBase S.isPullbackDefined_goodBlowupToBase) ∧
    (∃ T : (S.D.comap S.goodBlowupToBase).subscheme.IdealSheafData,
      IsClosedImmersion T.subschemeι ∧ LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((S.D.comap S.goodBlowupToBase).subschemeι ⁻¹ᵁ
          (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ ∧
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isPullbackDefined_goodBlowupToBase
          (T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n)) ∧
      (∀ (n : ℤ) (t : T.subscheme)
        (_ : ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
          S.goodBlowupToBase).base t ∈ S.locallyFreeLocus),
        letI F := S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isPullbackDefined_goodBlowupToBase
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
              (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x))) ∧
      (∀ C : AffineChart (S.pullback S.goodBlowupToBase S.isPullbackDefined_goodBlowupToBase),
        (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
          Nonempty ((RingedSpace.PseudoCoherence.restrictModules (S.pullback S.goodBlowupToBase
              S.isPullbackDefined_goodBlowupToBase).X.toRingedSpace C.U.1).mapDerivedCategory.obj
                (S.etaDerivedPullbackObject S.goodBlowupToBase
                  S.isPullbackDefined_goodBlowupToBase) ≅
            DerivedCategory.Q.obj C.specEtaComplex) ∧
          T.ideal C.divisorAffineOpen = C.obstructionIdeal)) ∧
    (∀ C : AffineChart S,
      ∃! e : (S.goodBlowupToBase ⁻¹ᵁ (C.U : S.X.Opens)).toScheme ≅
          AlgebraicGeometry.blowUp C.blowupCentreIdealSheaf,
        e.hom ≫ AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf =
          S.goodBlowupToBase ∣_ (C.U : S.X.Opens)) ∧
    ((∃ ℳ : CochainComplex (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace) ℤ,
        Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
          Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)) →
      ∃ 𝒬 : CochainComplex S.goodBlowup.Modules ℤ,
        Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
          Nonempty (DerivedCategory.Q.obj 𝒬 ≅
            S.etaDerivedPullbackObject S.goodBlowupToBase
              S.isPullbackDefined_goodBlowupToBase)) := by
  have hb := S.isGoodBlowup_goodBlowupToBase
  have hgo := S.isGoodOver_goodBlowupToBase
  have hT := fun C hI =>
    (S.pullback S.goodBlowupToBase hgo.pullbackDefined).ideal_goodChartSubscheme
      hgo.isGoodTriple C hI
  obtain ⟨h0, h1⟩ := S.locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase
    (S.pullbackSubscheme S.goodBlowupToBase hgo) hT
  refine ⟨inferInstance, ?_, S.isIso_morphismRestrict_goodBlowupToBase_locallyFreeLocus,
    S.isPullbackDefined_goodBlowupToBase, rfl, S.isPerfect_etaDerivedPullbackObject_goodBlowup,
    ⟨S.pullbackSubscheme S.goodBlowupToBase hgo, inferInstance, h0, h1,
      S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology_of_isGoodOver _ hgo,
      fun n t hw => S.free_finrank_stalk_etaDerivedPullbackRestrictHomology_of_isGoodOver _ hgo
        S.flat_ι_comp_goodBlowupToBase_locallyFreeLocus n t hw,
      fun C hI => ⟨⟨chartDerivedEtaIso (S.D.comap S.goodBlowupToBase)
        S.isPullbackDefined_goodBlowupToBase (S.derivedPullbackObject S.goodBlowupToBase)
        (S.isPerfect_derivedPullbackObject S.goodBlowupToBase) C⟩, hT C hI⟩⟩,
    fun C => C.existsUnique_iso_preimage_blowUp,
    fun hrep => Stacks.BlowUpComplexes.exists_isLocallyBoundedFiniteLocallyFree_etaDerivedPullback
      S _ _ hgo.isGoodTriple hrep⟩
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact hb.isIso_resLE_divisorComplement

end AlgebraicGeometry.ComplexAndDivisorSituation

end
