module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDecalagePerfect
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupAdmissible
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupModification
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowupGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties

/-!
# The modification of a perfect complex along an effective Cartier divisor, collected

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with ideal sheaf `ℐ`, `M` a perfect
object of `D(𝒪_X)`, and `W ⊆ X` the maximal open over which the cohomology sheaves `H^i(M)` are
locally free.  There is a proper morphism `b : X' ⟶ X` and an object `Q` of `D(𝒪_{X'})` such
that

1. `b` is an isomorphism over `X ∖ D`,
2. `b` is an isomorphism over `W`,
3. `D' = b⁻¹D` is an effective Cartier divisor,
4. `Q = Lη_{ℐ'}Lb^*M`, where `ℐ'` is the ideal sheaf of `D'`,
5. `Q` is perfect,
6. there is a closed immersion `i : T ⟶ D'` of finite presentation with `D' ∩ b⁻¹(W) ⊆ T`
   scheme-theoretically, such that `Li^*Q` has finite locally free cohomology sheaves whose
   ranks at a point `t` over `W` are the ranks of the `H^i(M)` at the image of `t`,
7. over every affine chart `(U, A, f, M^•)` of `(X, D, M)`, `b` is the blowing up of `U` in
   `∏ᵢ I_i(M^•, f)`,
8. on every affine chart `(V, B, g, N^•)` of `(X', D', Lb^*M)` whose determinantal ideals
   `I_i(N^•, g)` are principal, `Q|_V` is the complex associated with `η_g N^•` and `T ∩ V` is
   cut out in `D' ∩ V` by the total obstruction ideal `J(N^•, g)`, and
9. if `M` is represented by a locally bounded complex of finite locally free `𝒪_X`-modules, then
   so is `Q` by such a complex of `𝒪_{X'}`-modules.

The morphism is that of Stacks tag 0GTY and `Q` is the object of tag 0F8U; the statement
collects what the tags of Section 0F8R prove about them.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isProper_modification`: **Stacks tag
  0F9Y.**

## Implementation notes

The scheme, the divisor and the perfect object are the data of
`AlgebraicGeometry.ComplexAndDivisorSituation`, which carries no other hypothesis; the open `W`
is `AlgebraicGeometry.ComplexAndDivisorSituation.locallyFreeLocus`.  "Isomorphism over an open
`V`" is invertibility of `b.resLE V (b ⁻¹ᵁ V) le_rfl`.  Clause (3) is the existential witness
`hD'`, which the definition of `Q` in clause (4) consumes.  The closed subscheme `T` of clause
(6) is an ideal sheaf on `D'`, its closed immersion being `T.subschemeι`, and `Li^*Q` is the
derived pullback of `Q` along `T ⟶ D' ⟶ X'`; the rank at a point is
`AlgebraicGeometry.Scheme.Modules.fiberRank`.  Clause (8) is quantified over the affine charts
of the pulled-back triple `(X', D', Lb^*M)`, which is what the source's `(X', D', Lb^*N)` means.

Clause (9) of the source asks for a *bounded* complex representing `Q`.  That is not true as
written: on a disjoint union `X = ⨆ₙ Xₙ` of nonempty affine schemes with `D = ∅` and
`M|_{Xₙ} = 𝒪_{Xₙ}[n]`, the morphism `b` is an isomorphism and `Q = M` has nonzero cohomology in
every degree, so no bounded complex represents it.  The statement here asks for a *locally
bounded* complex, which is what Stacks tag 0GU0, the result the source collects for this clause,
asserts.

The partial statements in `ModificationProperties.lean` and `ModificationPropertiesOfRep.lean`
are no longer registered under tag 0F9Y.  The erratum for clause (9) is recorded in `errata.md`
(entry 0F9Y, last sentence, 2026-10-27).

## References

* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0GU0](https://stacks.math.columbia.edu/tag/0GU0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesHomology
attribute [local instance 100000] modulesHasDerivedCategory

/-- The morphism of Stacks tag 0GTY is an isomorphism over the locally free locus `W`, in the
`resLE` form: this is tag 0F8W, `isIso_pullback_snd_goodBlowupToBase_locallyFreeLocus`,
transported along the identification of `X' ×_X W` with `b⁻¹(W)`. -/
theorem isIso_resLE_goodBlowupToBase_locallyFreeLocus (S : ComplexAndDivisorSituation.{u, d}) :
    IsIso (S.goodBlowupToBase.resLE S.locallyFreeLocus
      (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus) le_rfl) := by
  have := S.isIso_pullback_snd_goodBlowupToBase_locallyFreeLocus
  rw [Scheme.Hom.resLE_eq_morphismRestrict, morphismRestrict]
  infer_instance

/-- **Stacks tag 0F9Y.**  Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor and `M` a
perfect object of `D(𝒪_X)`, and let `W ⊆ X` be the maximal open over which the cohomology
sheaves of `M` are locally free.  There are a proper morphism `b : X' ⟶ X` and an object `Q` of
`D(𝒪_{X'})` such that

1. `b` is an isomorphism over `X ∖ D`;
2. `b` is an isomorphism over `W`;
3. `D' = b⁻¹D` is an effective Cartier divisor;
4. `Q = Lη_{ℐ'}Lb^*M`, with `ℐ'` the ideal sheaf of `D'`;
5. `Q` is perfect;
6. there is a closed immersion `i : T ⟶ D'` of finite presentation with `D' ∩ b⁻¹(W) ⊆ T`
   scheme-theoretically, such that the cohomology sheaves of `Li^*Q` are finite locally free,
   and at a point `t ∈ T` over `W` the rank of `H^n(Li^*Q)` is the rank of `H^n(M)` at the image
   of `t`;
7. for every affine chart `(U, A, f, M^•)` of `(X, D, M)`, the part of `b` over `U` is the
   blowing up of `U` in `∏ᵢ I_i(M^•, f)`;
8. for every affine chart `(V, B, g, N^•)` of `(X', D', Lb^*M)` with principal `I_i(N^•, g)`,
   `Q|_V` is isomorphic to the complex associated with `η_g N^•`, and `T ∩ V` is cut out in
   `D' ∩ V` by `J(N^•, g) = ∑ᵢ J_i(N^•, g)`;
9. if `M` is represented by a locally bounded complex of finite locally free `𝒪_X`-modules, then
   `Q` is represented by a locally bounded complex of finite locally free `𝒪_{X'}`-modules.

Here `b` is `goodBlowupToBase` (tag 0GTY), properness is `isProper_goodBlowupToBase`, clause (1)
is `IsGoodBlowup.isIso_resLE_divisorComplement`, clause (2) is tag 0F8W, clause (5) is tag 0F8U,
clause (6) is tag 0F8X with the subscheme of tag 0GTZ for the pulled-back triple, clause (7) is
`exists_isPullback_blowUpToBase`, clause (8) is the second assertion of tag 0GTV for the
pulled-back triple together with the defining property of that subscheme, and clause (9) is tag
0GU0.  Clause (9) asks for a locally bounded rather than a bounded complex; see the module
docstring. -/
@[stacks 0F9Y "the full statement in existential form: a proper b : X' ⟶ X and Q with \
clauses (1)--(9). Clause (9) is stated in its corrected form, Q represented by a LOCALLY \
BOUNDED complex of finite locally free modules (as tag 0GU0 gives): the printed 'bounded' is \
false for an infinite disjoint union; see errata.md, entry 0F9Y (last sentence), 2026-10-27"]
theorem exists_isProper_modification (S : ComplexAndDivisorSituation.{u, d}) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ S.X), IsProper b ∧
      IsIso (b.resLE S.divisorComplement (b ⁻¹ᵁ S.divisorComplement) le_rfl) ∧
      IsIso (b.resLE S.locallyFreeLocus (b ⁻¹ᵁ S.locallyFreeLocus) le_rfl) ∧
      ∃ (hD' : Stacks.Divisors.IsEffectiveCartierDivisor (S.D.comap b))
        (Q : DerivedCategory X'.Modules),
        Q = S.etaDerivedPullbackObject b hD' ∧
        RingedSpace.IsPerfect (X := X'.toRingedSpace) Q ∧
        (∃ T : (S.pullback b hD').D.subscheme.IdealSheafData,
          LocallyOfFinitePresentation T.subschemeι ∧
          T.comap ((S.pullback b hD').D.subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ ∧
          (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            ((DerivedCategory.homologyFunctor T.subscheme.Modules n).obj
              ((derivedPullback
                (T.subschemeι ≫ (S.pullback b hD').D.subschemeι).toLRSHom.toShHom).obj Q))) ∧
          (∀ (n : ℤ) (t : T.subscheme),
            ((T.subschemeι ≫ (S.pullback b hD').D.subschemeι) ≫ b) t ∈ S.locallyFreeLocus →
            Scheme.Modules.fiberRank
                ((DerivedCategory.homologyFunctor T.subscheme.Modules n).obj
                  ((derivedPullback
                    (T.subschemeι ≫ (S.pullback b hD').D.subschemeι).toLRSHom.toShHom).obj Q))
                t =
              Scheme.Modules.fiberRank (S.cohomologySheaf n)
                (((T.subschemeι ≫ (S.pullback b hD').D.subschemeι) ≫ b) t)) ∧
          ∀ C : AffineChart (S.pullback b hD'), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
            T.ideal C.divisorAffineOpen = C.obstructionIdeal) ∧
        (∀ C : AffineChart S, ∃ e : blowUp C.blowupCentreIdealSheaf ⟶ X',
          IsPullback e (blowUpToBase C.blowupCentreIdealSheaf) b (C.U : S.X.Opens).ι) ∧
        (∀ C : AffineChart (S.pullback b hD'), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
          Nonempty ((RingedSpace.PseudoCoherence.restrictModules (S.pullback b hD').X.toRingedSpace
              C.U.1).mapDerivedCategory.obj Q ≅ DerivedCategory.Q.obj C.specEtaComplex)) ∧
        ((∃ ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
            Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
              Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M)) →
          ∃ 𝒬 : CochainComplex X'.Modules ℤ,
            Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
              Nonempty (DerivedCategory.Q.obj 𝒬 ≅ Q)) := by
  have hb := S.isGoodBlowup_goodBlowupToBase.isGoodOver
  obtain ⟨T, hT, hfp, -⟩ :=
    (S.pullback _ hb.pullbackDefined).exists_isGoodChartOpen_ideal_eq_obstructionIdeal
      hb.isGoodTriple
  refine ⟨S.goodBlowup, S.goodBlowupToBase, inferInstance,
    S.isGoodBlowup_goodBlowupToBase.isIso_resLE_divisorComplement,
    S.isIso_resLE_goodBlowupToBase_locallyFreeLocus, hb.pullbackDefined, _, rfl,
    S.isPerfect_etaDerivedPullbackObject_goodBlowup,
    ⟨T, hfp, S.comap_preimage_locallyFreeLocus_eq_bot hb.isGoodTriple hT,
      S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT,
      fun n t hw => ?_, hT⟩,
    S.exists_isPullback_blowUpToBase,
    fun C hC => ((S.pullback _ hb.pullbackDefined).chartDecalage_of_derivedEta _).nonempty_iso C hC,
    fun hrep => Stacks.BlowUpComplexes.exists_isLocallyBoundedFiniteLocallyFree_etaDerivedPullback
      S _ hb.pullbackDefined hb.isGoodTriple hrep⟩
  rw [← S.finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf
    hb.isGoodTriple hT n t hw]
  exact @Stacks.Chow.fiberRank_eq_moduleRank _ _
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT n) _

end AlgebraicGeometry.ComplexAndDivisorSituation

end
