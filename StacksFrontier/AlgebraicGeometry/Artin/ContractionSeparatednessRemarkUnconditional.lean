module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSeparatednessRemark
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectEffective

/-!
# The separatedness hypotheses of Artin's theorem on contractions (Stacks 0GIC)

Theorem Stacks 0GIB assumes `X'` and `W` separated over `S`. Remark **Stacks 0GIC** explains that
the proof uses this in two places:

* to show that the diagonal `Δ : F ⟶ F × F` of Artin's functor is representable (Stacks 0GHF);
  the remark replaces this use by the bootstrap for the diagonal, applying the theorem in the
  separated case to the triples of Stacks 0GHD (4)
  (`ContractionSituation.relativelyRepresentable_diag_contractionFunctor_of_solutions`);
* in Lemma 0GI8, to obtain the morphism `x' : V' ⟶ X'`; the existence of `x'` is the
  algebraization property `ContractionSituation.HasCompletionAlgebraization`, from which every
  formal object of `F` is effective
  (`ContractionSituation.hasEffectiveFormalObjects_of_hasCompletionAlgebraization`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.separatednessRemark`: Remark 0GIC. The diagonal of
  Artin's functor is representable for arbitrary `X'` and `W`; Artin's theorem holds for every
  `X'` admitting the morphisms `x'` of Lemma 0GI8, with `X'` and `W` arbitrary otherwise; and it
  holds for `X'` separated and `W` arbitrary.

## The quasi-separated case

The remark's closing sentences, that `x'` exists when `X'` is quasi-separated and hence that the
theorem holds with "separated" replaced by "quasi-separated", rest on More on Morphisms of Spaces,
Remark 0GHK, which appeals to algebraization theorems outside the Stacks project (Bhatt;
Hall–Rydh); the source defers them ("If we ever need this we will precisely state and carefully
prove this here"). They are recorded in `errata.md` (no proof in Stacks).

## References

* [Stacks Project, Tag 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
* [Stacks Project, Tag 0GIC](https://stacks.math.columbia.edu/tag/0GIC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **Stacks 0GIC.** In the situation of Stacks 0GH8, with the local rings of `S` at its finite
type points G-rings, and with `X'` and `W` arbitrary (separatedness is assumed in clause 3 alone):

1. the diagonal `Δ : F ⟶ F × F` of Artin's functor is representable (by schemes, a fortiori by
   algebraic spaces): the bootstrap of the remark, applying Artin's theorem in the separated case
   to the triples `E'`, `(E' ⟶ V)⁻¹Z`, `E'_{/Z} ⟶ E_W` of Stacks 0GHD;
2. "the proof of Lemma 0GI8 is the one place where separatedness of `X'` is used, and it is used
   to obtain `x' : V' ⟶ X'`": for every `X'` for which the morphisms `x'` exist (the
   algebraization property `HasCompletionAlgebraization`), Artin's theorem holds, for arbitrary
   `X'` and `W`;
3. Artin's theorem holds when `X'` is separated over `S`, `W` being arbitrary.

The solutions are the solutions of Stacks 0GIB whose open part `U` is the complement of `T` (the
corrected notion of Stacks 0GHB). On the remark's closing sentences (quasi-separated `X'`) see the
module documentation. -/
@[stacks 0GIC "Remark 0GIC: (1) the diagonal of Artin's functor F is representable for arbitrary \
X' and W (the bootstrap for the diagonal); (2) separatedness of X' enters the proof of 0GIB \
through the morphisms x' : V' -> X' of Lemma 0GI8: the theorem holds for every X' admitting these \
morphisms, with X' and W otherwise arbitrary; (3) the theorem holds for X' separated and W \
arbitrary. The closing sentences on quasi-separated X' cite Remark 0GHK (Bhatt; Hall-Rydh), which \
the source defers, and are recorded in errata.md"]
theorem separatednessRemark
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
        (diag (contractionFunctor c)) ∧
      (c.HasCompletionAlgebraization → ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (s : Solution c X), Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) ∧
      (Space.IsSeparated B S hS (terminal.from c.X') → ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (s : Solution c X), Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) := by
  have hsol : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      (∀ v : V, IsFiniteTypePoint v → IsGRing (V.presheaf.stalk v)) →
      Space.IsSeparated B V hV (terminal.from c'.X') →
      FormalSpace.IsSeparatedMorphism B V hV (terminal.from c'.W) →
      ∃ (E : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) (s : Solution c' E),
        Set.range (Space.pointsMap B V hV s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B V hV) E :=
    fun c' hG' hX hW => exists_solution_of_hasEffectiveFormalObjects c' hG' hX hW
      (c'.hasEffectiveFormalObjects hX)
  have hsolution : LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c) →
      ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
        Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ := by
    intro heff
    obtain ⟨X, s, hU, -⟩ := c.exists_solution_of_solutions hG hsol
      (limitPreserving_contractionFunctor c) heff (contractionFunctor_hasOpenVersality c)
    exact ⟨X, s, hU⟩
  exact ⟨c.relativelyRepresentable_diag_contractionFunctor_of_solutions hG hsol
      (limitPreserving_contractionFunctor c),
    fun halg => hsolution (c.hasEffectiveFormalObjects_of_hasCompletionAlgebraization halg),
    fun hX => hsolution (c.hasEffectiveFormalObjects hX)⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
