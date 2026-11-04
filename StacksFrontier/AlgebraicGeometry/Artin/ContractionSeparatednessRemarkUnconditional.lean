module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSeparatednessRemark
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectEffective

/-!
# The separatedness hypotheses of Artin's theorem on contractions (Stacks 0GIC)

Theorem Stacks 0GIB assumes `X'` and `W` separated over `S`. Remark **Stacks 0GIC** explains that
the proof uses this in two places:

* to show that the diagonal `Δ : F ⟶ F × F` of Artin's functor is representable (Stacks 0GHF);
  this use is avoided by the bootstrap for the diagonal, applying the theorem in the separated case
  to the triples of Stacks 0GHD (4)
  (`ContractionSituation.relativelyRepresentable_diag_contractionFunctor_of_solutions`);
* in Lemma 0GI8, and there only to obtain the morphism `x' : V' ⟶ X'`; the existence of `x'` is
  the algebraization property `ContractionSituation.HasCompletionAlgebraization`, from which every
  formal object of `F` is effective with no separatedness
  (`ContractionSituation.hasEffectiveFormalObjects_of_hasCompletionAlgebraization`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.separatednessRemark`: Artin's theorem on
  contractions holds without separatedness of `W`, and without separatedness of `X'` given the
  algebraization property; the diagonal of Artin's functor is representable unconditionally.

## What is not formalized

The remark's closing sentences, that `x'` exists when `X'` is merely quasi-separated and hence that
the theorem holds with "separated" replaced by "quasi-separated", rest on More on Morphisms of
Spaces, Remark 0GHK, which appeals to algebraization theorems outside the Stacks project (Bhatt;
Hall–Rydh) and which the source does not state or prove ("If we ever need this we will precisely
state and carefully prove this here"). For `W` no separatedness at all is needed below.

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

/-- In the situation of Stacks 0GH8, with the local rings of `S` at its finite type points G-rings
and **no separatedness assumed on `X'` or on `W`**:

1. the diagonal `Δ : F ⟶ F × F` of Artin's functor is representable (by schemes, a fortiori by
   algebraic spaces): the bootstrap of the remark, applying Artin's theorem in the separated case
   to the triples `E'`, `(E' ⟶ V)⁻¹Z`, `E'_{/Z} ⟶ E_W` of Stacks 0GHD;
2. "the proof of Lemma 0GI8 is the only place where separatedness of `X'` is used, and only to
   obtain `x' : V' ⟶ X'`": for every `X'` for which the morphisms `x'` exist (the algebraization
   property `HasCompletionAlgebraization`), Artin's theorem holds, with no separatedness of `X'`
   or `W`;
3. in particular Artin's theorem holds when `X'` alone is separated over `S`, `W` being arbitrary.

The solutions are the solutions of Stacks 0GIB whose open part `U` is the complement of `T` (the
corrected notion of Stacks 0GHB). The remark's closing sentences on quasi-separated `X'` rest on
Remark 0GHK, outside the Stacks project; see the module documentation. -/
@[stacks 0GIC "the diagonal of F is representable with no separatedness of X' or W; the theorem \
holds for every X' admitting the morphisms x' of Lemma 0GI8, with no separatedness of X' or W; the \
theorem holds with X' separated and W arbitrary. The closing sentences on quasi-separated X' rest \
on Remark 0GHK (algebraization results of Bhatt and of Hall-Rydh outside the Stacks project), which \
the source does not state or prove"]
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
