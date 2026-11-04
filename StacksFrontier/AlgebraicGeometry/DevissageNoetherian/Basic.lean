module

public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support

/-!
# The Noetherian induction of [Stacks, Tag 01YF]

[Stacks, Tag 01YF] says that every coherent module on a Noetherian scheme is built from direct
images of quasi-coherent ideal sheaves on integral closed subschemes. Its proof is a Noetherian
induction on the support, with two reduction steps. This file carries that induction, and
reduces 01YF — hence [Stacks, Tag 01YG], through
`Stacks.AlgebraicGeometry.DevissageBounded.property_of_forall_isIdealDevissable` — to the two
geometric steps, each stated as a named hypothesis.

## Main definitions

* `Stacks.AlgebraicGeometry.DevissageNoetherian.HasSupportSplitting`: the first reduction step,
  [Stacks, Tag 01YD].
* `Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`: the second reduction
  step, the irreducible case of [Stacks, Tag 01YF].

## Main results

* `Stacks.AlgebraicGeometry.DevissageNoetherian.isIdealDevissable_of_isCoherent`:
  **[Stacks, Tag 01YF] in its extension-closed form, conditional on the two reduction steps.**
* `Stacks.AlgebraicGeometry.DevissageNoetherian.property_of_devissageSteps`:
  **[Stacks, Tag 01YG], conditional on the two reduction steps** — the statement of 01YG with
  `HasSupportSplitting` and `HasIrreducibleDevissage` as its only added hypotheses.

## Implementation notes

The induction runs over `TopologicalSpace.Closeds X` with `WellFoundedLT`, which
`AlgebraicGeometry.IsNoetherian.noetherianSpace` supplies. It is phrased as

  for every closed `Z`, every coherent module whose support is contained in `Z` is dévissable,

rather than with `supp F = Z`: the containment form is what the induction hypothesis has to be
applied at, since the pieces produced by the two steps have supports contained in, not equal to,
the smaller closed sets. The equality case is recovered inside the proof — if the support is
strictly smaller than `Z` the induction hypothesis closes the goal outright, so one may assume
`supp F = Z`, which is what the irreducibility dichotomy is about.

The target predicate is
`Stacks.AlgebraicGeometry.DevissageBounded.IsIdealDevissable`, the extension-closed form of the
conclusion of 01YF, and not the filtration form `HasIdealDevissageLt`. Against the filtration
form the source's phrase "splicing them yields one for `F`" is a genuine obligation — preimages
of subobjects along the epimorphism, and a comparison of cokernels — whereas against the
extension-closed form it is the constructor `IsIdealDevissable.ext`. The two are comparable:
`Stacks.AlgebraicGeometry.DevissageBounded.isIdealDevissable_of_hasIdealDevissageLt` shows the
filtration form implies this one.

`HasSupportSplitting` asks for the first step as a monomorphism `ι : G ⟶ F` together with the
coherence of `G` and of `cokernel ι`, rather than as an abstract short exact sequence with
`S.X₂` isomorphic to `F`. The short complex
`ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)` then has `F` *syntactically* as its
middle term, so `IsIdealDevissable.ext` applies to it with no transport, as in the
implementation notes of `StacksFrontier/AlgebraicGeometry/CoherentDevissage/Devissage.lean`.

In `HasIrreducibleDevissage` the quotient class is `IsIdealPushforward` or "support strictly
smaller", which is what the source's steps 3 and 4 deliver: the filtration by the powers
`J ^ i • F` of the ideal of the reduced induced structure on the support reduces to the case
where that ideal annihilates `F` ([Stacks, Tag 01Y9] and [Stacks, Tag 01J3]), and in that case
[Stacks, Tag 01YE] produces a monomorphism into `F` from the direct image of a direct sum of `r`
copies of a coherent ideal sheaf on the reduced induced structure, which is an isomorphism near
the generic point — so the cokernel is supported strictly inside the support of `F`, and the sub
refines into its `r` factors.

`HasSupportSplitting` holds on every Noetherian scheme, by
`Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.DevissageNoetherian

variable {X : Scheme.{u}}

/-! ### The two reduction steps, as hypotheses -/

/-- **[Stacks, Tag 01YD], in the form the Noetherian induction of [Stacks, Tag 01YF] uses it.**
A coherent module whose support is the union of two closed sets `Z₁ ∪ Z₂` sits in a short exact
sequence of coherent modules whose sub is supported in `Z₁` and whose quotient is supported in
`Z₂`.

The sub is given as a monomorphism into `F` and the quotient as its cokernel, so that the short
complex built from them has `F` syntactically as its middle term.

The source pairs the two closed sets with the sub and the quotient the other way round — its
sub-object is supported in the *second* of the two closed sets it names. Since both are
universally quantified here the two readings differ only by the names of the bound variables. -/
def HasSupportSplitting (X : Scheme.{u}) : Prop :=
  ∀ F : X.Modules, F.IsCoherent → ∀ Z₁ Z₂ : Set X, IsClosed Z₁ → IsClosed Z₂ →
    SheafOfModules.supp F = Z₁ ∪ Z₂ →
      ∃ (G : X.Modules) (ι : G ⟶ F), Mono ι ∧ G.IsCoherent ∧ (cokernel ι).IsCoherent ∧
        SheafOfModules.supp G ⊆ Z₁ ∧ SheafOfModules.supp (cokernel ι) ⊆ Z₂

/-- **The irreducible case of [Stacks, Tag 01YF].** A coherent module with irreducible support
carries a bounded dévissage filtration each of whose successive quotients is either a direct
image of a quasi-coherent ideal sheaf on an integral closed subscheme, or supported strictly
inside the support of the module.

This is steps 3 and 4 of the source's proof: [Stacks, Tag 01Y9] and [Stacks, Tag 01J3] reduce to
the case where the ideal of the reduced induced structure on the support annihilates the module,
and [Stacks, Tag 01YE] handles that case. -/
def HasIrreducibleDevissage (X : Scheme.{u}) : Prop :=
  ∀ F : X.Modules, F.IsCoherent → IsIrreducible (SheafOfModules.supp F) →
    HasDevissageWith
      (fun M => IsIdealPushforward M ∨ SheafOfModules.supp M ⊂ SheafOfModules.supp F) F

/-! ### The induction -/

/-- **[Stacks, Tag 01YF], conditional on its two reduction steps.** Every coherent module on a
Noetherian scheme is ideal-dévissable, given the splitting of [Stacks, Tag 01YD]
(`HasSupportSplitting`) and the irreducible case (`HasIrreducibleDevissage`).

The two facts about supports the induction needs — that the support of a coherent module is
closed, and that a module with empty support is zero — are `forall_isClosed_supp` and
`forall_isZero_of_supp_eq_empty`.

The proof is the source's Noetherian induction on the support, run downwards over
`TopologicalSpace.Closeds X`. With the support equal to the closed set `Z` being inducted on,
either it is empty, or it is irreducible and `HasIrreducibleDevissage` applies, or it is covered
by two closed sets neither of which contains it and `HasSupportSplitting` applies; in the last
two cases the pieces produced have strictly smaller support, so the induction hypothesis
applies to them and `IsIdealDevissable.ext` assembles the result. -/
theorem isIdealDevissable_of_isCoherent [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissage X)
    (F : X.Modules) (hF : F.IsCoherent) : IsIdealDevissable F := by
  have hclosed := forall_isClosed_supp X
  have hvanish := forall_isZero_of_supp_eq_empty X
  have hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      IsIdealDevissable S.X₁ → IsIdealDevissable S.X₃ → IsIdealDevissable S.X₂ :=
    fun S hS h₁ h₂ h₃ hd₁ hd₃ => .ext S hS h₁ h₂ h₃ hd₁ hd₃
  suffices H : ∀ Z : Closeds X, ∀ G : X.Modules, G.IsCoherent →
      SheafOfModules.supp G ⊆ (Z : Set X) → IsIdealDevissable G from
    H ⟨_, hclosed F hF⟩ F hF subset_rfl
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z IH =>
    intro G hG hsub
    -- Either the support is strictly smaller than `Z`, in which case the induction hypothesis
    -- applies at once, or it is all of `Z`.
    by_cases hlt : (⟨SheafOfModules.supp G, hclosed G hG⟩ : Closeds X) < Z
    · exact IH _ hlt G hG subset_rfl
    have hZ : (Z : Set X) = SheafOfModules.supp G :=
      congrArg _ (eq_of_le_of_not_lt (SetLike.coe_subset_coe.mp hsub) hlt).symm
    -- The induction hypothesis, available at every closed set strictly inside the support.
    have IH' : ∀ M : X.Modules, M.IsCoherent →
        SheafOfModules.supp M ⊂ SheafOfModules.supp G → IsIdealDevissable M := by
      intro M hM hlt'
      exact IH ⟨SheafOfModules.supp M, hclosed M hM⟩
        (SetLike.coe_ssubset_coe.mp (hZ ▸ hlt')) M hM subset_rfl
    by_cases hne : (SheafOfModules.supp G).Nonempty
    swap
    · exact .zero (hvanish G (Set.not_nonempty_iff_eq_empty.mp hne)) hG
    by_cases hpre : IsPreirreducible (SheafOfModules.supp G)
    · refine property_of_hasDevissageWith IsIdealDevissable isIdealDevissable_terminal hext ?_ G
        (hirr G hG ⟨hne, hpre⟩)
      rintro M (hM | hM) hMc
      · exact .ideal hM hMc
      · exact IH' M hMc hM
    -- The support is reducible: it is covered by two closed sets, neither containing it.
    rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
    simp only [not_forall, not_or] at hpre
    obtain ⟨z₁, z₂, hz₁, hz₂, hcov, hn₁, hn₂⟩ := hpre
    -- Intersecting with a closed set not containing the support gives a smaller closed set.
    have hW : ∀ z : Set X, IsClosed z → ¬ SheafOfModules.supp G ⊆ z →
        IsClosed (SheafOfModules.supp G ∩ z) ∧
          SheafOfModules.supp G ∩ z ⊂ SheafOfModules.supp G :=
      fun z hz hn => ⟨(hclosed G hG).inter hz,
        ⟨Set.inter_subset_left, fun h => hn fun x hx => (h hx).2⟩⟩
    have hWcov : SheafOfModules.supp G =
        (SheafOfModules.supp G ∩ z₁) ∪ (SheafOfModules.supp G ∩ z₂) := by
      rw [← Set.inter_union_distrib_left]
      exact (Set.inter_eq_left.mpr hcov).symm
    obtain ⟨K, ι, hmono, hK, hcoker, hKsupp, hQsupp⟩ :=
      hsplit G hG _ _ (hW z₁ hz₁ hn₁).1 (hW z₂ hz₂ hn₂).1 hWcov
    exact hext (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι)
        mono_f := hmono
        epi_g := inferInstance }
      hK hG hcoker
      (IH' K hK (lt_of_le_of_lt hKsupp (hW z₁ hz₁ hn₁).2))
      (IH' _ hcoker (lt_of_le_of_lt hQsupp (hW z₂ hz₂ hn₂).2))

/-- **[Stacks, Tag 01YG], conditional on the two reduction steps of [Stacks, Tag 01YF].** A
property of modules on a Noetherian scheme that holds on the zero module, is stable under
extensions of coherent modules, and holds on the direct image of every quasi-coherent ideal
sheaf on every integral closed subscheme, holds on every coherent module.

This is the statement of 01YG, with the hypotheses of
`isIdealDevissable_of_isCoherent` added; the dévissage half is
`Stacks.AlgebraicGeometry.DevissageBounded.property_of_forall_isIdealDevissable`. -/
theorem property_of_devissageSteps [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissage X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  property_of_forall_isIdealDevissable P
    (isIdealDevissable_of_isCoherent hsplit hirr) hzero hext hideal

end Stacks.AlgebraicGeometry.DevissageNoetherian

end

end
