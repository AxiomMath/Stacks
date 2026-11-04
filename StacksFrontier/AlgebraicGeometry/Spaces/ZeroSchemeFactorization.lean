module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeMaximality

/-!
# Factoring through the zero scheme of a section, from chartwise vanishing

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `L` be an
`𝒪_X`-module and let `s` be a global section of `L`.  Stacks 0846 part (2) says that a morphism
`f : Y ⟶ X` of algebraic spaces factors through the zero scheme `Z(s)` of Stacks 0845 exactly
when `f^*s = 0`.

This file proves the *sufficiency* direction with the module-theoretic hypothesis `f^*s = 0`
replaced by its chartwise reading: on every affine étale chart `U` of `X`, the evaluation ideal
`AlgebraicGeometry.Space.sectionEvaluationIdealAt` of `s` at `U` is killed by pullback of
regular functions along every point of `Y` lying over `U`.  **No Stacks 0846 tag is placed
here**, and no part of Stacks 0846 is claimed: the implication proved below is strictly weaker
than part (2), because the equivalence of its hypothesis with the vanishing of `f^*s` is not
available (see the implementation notes).

What is notable about the statement is what it does *not* need.
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeMaximality.lean` records that the remaining
content of Stacks 0846 reduces to the surjectivity half of Stacks 03MB — that a quasi-coherent
ideal of `𝒪_X` is the defining ideal of some closed subspace — because without it nothing
identifies the defining ideal of `Z(s)` with the evaluation ideal of `s`.  The implication
below avoids that identification altogether: it goes through the *members* of the family whose
intersection is `Z(s)`, whose defining ideals are bounded by the evaluation ideal by
definition, and therefore needs no information about the defining ideal of the intersection.

## Main results

* `AlgebraicGeometry.Space.exists_comp_eq_zeroScheme_of_sectionEvaluationIdealAt_le`: if the
  evaluation ideal of `s` on every affine étale chart of `X` is killed by pullback along every
  point of `Y` over that chart, then `f` factors through the zero scheme of `s`.
* `AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_bot`: the evaluation ideal of a section
  whose value on every étale chart is zero is the zero ideal.
* `AlgebraicGeometry.Space.exists_sections_eval_eq_zero`: such a section exists — the zero
  section.
* `AlgebraicGeometry.Space.exists_comp_eq_zeroScheme_of_eval_eq_zero`: consequently every
  morphism to `X` factors through the zero scheme of the zero section.  This instantiates the
  hypothesis of the main result, so that hypothesis is satisfiable.
* `AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_bot_of_id`: conversely that hypothesis
  is not automatic — at the identity of `X` it forces the evaluation ideal to vanish.

## Implementation notes

The proof is `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le`,
the affine-chart form of the factorization criterion of Stacks 03MB, applied to each member of
the family intersected by `AlgebraicGeometry.Space.zeroSchemeSubfunctor`.  Membership in that
family bounds the member's defining ideal by the evaluation ideal on affine charts only, which
is exactly the quantification range of that criterion; the criterion quantifying over *all*
charts (`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le`) could not be used here.
A morphism factoring through every member factors through their intersection, since the range
of a morphism is below an intersection of subfunctors as soon as it is below each of them.

The converse implication is not proved and is not available.  It asks that `s` pull back to
zero along `Z(s) ⟶ X`, i.e. that the evaluation ideal be contained in the defining ideal of
`Z(s)`; since `Z(s)` is an intersection and the defining ideal is antitone, the family bounds
only a supremum of ideals from below, and the containment needs the family to contain a member
whose defining ideal *is* the evaluation ideal.  That is the surjectivity half of Stacks 03MB,
blocked on Stacks 03DX (2) and Stacks 03DW; the obstruction is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeMaximality.lean` and in the section "What is
not proved" of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealBijection.lean`.

The scheme-level statement is not the obstruction either: Stacks 02OR, which is Stacks 0846 for
schemes, is proved in both of its parts —
`AlgebraicGeometry.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme` and
`AlgebraicGeometry.zeroScheme_isGreatest_vanishingClosedSubscheme` in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeFactorization.lean` — with the vanishing
of the pulled-back section, not a chartwise surrogate, on the left of the equivalence.  What is
missing is the comparison carrying the chartwise ideals of those zero subschemes back onto the
small étale site of `X`.

No invertibility hypothesis on `L` appears, following
`AlgebraicGeometry.Space.zeroSchemeSubfunctor_isClosedSubspace` and the results of
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeMaximality.lean`, which are also stated for a
section of an arbitrary `𝒪_X`-module.

## References

* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sufficiency half of Stacks 0846 (2), with the vanishing of `f^*s` read chartwise.**
If for every affine étale scheme chart `U` of `X` and every point of `Y` over an object `a` of
the site whose image in `X` factors through `U` by `k : a ⟶ U`, the evaluation ideal of the
section `s` at `U` is killed by pullback of regular functions along `k`, then `f : Y ⟶ X`
factors through the zero scheme of `s`.

The hypothesis is the chartwise reading of `f^*s = 0`; it is not known to be equivalent to it,
so this is not Stacks 0846 (2) and carries no tag.  Unlike the rest of Stacks 0846 it needs no
information about the defining ideal of `Z(s)` itself, hence none of the surjectivity half of
Stacks 03MB: it applies the affine-chart factorization criterion of Stacks 03MB to each closed
subspace in the family whose intersection is `Z(s)`, where the bound on the defining ideal
holds by definition. -/
theorem exists_comp_eq_zeroScheme_of_sectionEvaluationIdealAt_le
    (X Y : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections)
    (f : Y ⟶ X)
    (hs : ∀ U : SmallEtale B S hS X.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        ∀ (a : BigFppfOver B S hS) (k : a ⟶ U.1.left) (y : yoneda.obj a ⟶ Y.1),
          yoneda.map k ≫ U.1.hom = y ≫ f.hom →
            sectionEvaluationIdealAt B S hS X L s U ≤
              RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom) :
    ∃ g : Y ⟶ (⟨(zeroScheme B S hS X L s).1.toFunctor,
        (zeroScheme B S hS X L s).2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk (zeroScheme B S hS X L s).1.ι = f := by
  have hrange : Subfunctor.range f.hom ≤ zeroSchemeSubfunctor B S hS X L s := by
    rw [zeroSchemeSubfunctor_eq_sInf]
    refine le_sInf ?_
    rintro W ⟨hW, hWle⟩
    obtain ⟨g, hg⟩ := (exists_comp_eq_iff_forall_isAffine_definingIdealAt_le
      B S hS X Y ⟨W, hW⟩ f).2
      (fun U hU a k y hy => (hWle U hU).trans (hs U hU a k y hy))
    have hgι : g.hom ≫ W.ι = f.hom := congrArg InducedCategory.Hom.hom hg
    intro T x hx
    obtain ⟨x₀, rfl⟩ := hx
    rw [← hgι]
    exact (g.hom.app T x₀).2
  exact ⟨ObjectProperty.homMk (Subfunctor.lift f.hom hrange),
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι f.hom hrange)⟩

/-- The evaluation ideal of a section whose value on every étale chart of `X` is zero is the
zero ideal, every linear functional sending the zero section to zero. -/
theorem sectionEvaluationIdealAt_eq_bot (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections)
    (hs : ∀ U : SmallEtale B S hS X.1, s.eval (op U) = 0)
    (U : SmallEtale B S hS X.1) :
    sectionEvaluationIdealAt B S hS X L s U = ⊥ := by
  rw [sectionEvaluationIdealAt, hs U, Ideal.span_eq_bot]
  rintro x ⟨l, rfl⟩
  exact map_zero l

/-- A section of an `𝒪_X`-module whose value on every étale chart of `X` is zero exists: the
zero section, which is compatible with restriction because the restriction maps are linear. -/
theorem exists_sections_eval_eq_zero (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) :
    ∃ s : L.sections, ∀ U : SmallEtale B S hS X.1, s.eval (op U) = 0 :=
  ⟨PresheafOfModules.sectionsMk (fun _ => 0)
      (fun _ _ f => map_zero (ConcreteCategory.hom (L.val.map f))), fun _ => rfl⟩

/-- **The hypothesis of the main result is a genuine constraint.** Taken at the identity of `X`
it forces the evaluation ideal of the section to vanish on every affine étale chart, since the
pullback of regular functions along the identity is injective.  Together with
`AlgebraicGeometry.Space.exists_comp_eq_zeroScheme_of_eval_eq_zero`, which exhibits a section
satisfying it, this shows the hypothesis is neither unsatisfiable nor automatic. -/
theorem sectionEvaluationIdealAt_eq_bot_of_id (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections)
    (hs : ∀ U : SmallEtale B S hS X.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        ∀ (a : BigFppfOver B S hS) (k : a ⟶ U.1.left) (y : yoneda.obj a ⟶ X.1),
          yoneda.map k ≫ U.1.hom = y ≫ (𝟙 X : X ⟶ X).hom →
            sectionEvaluationIdealAt B S hS X L s U ≤
              RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    sectionEvaluationIdealAt B S hS X L s U = ⊥ := by
  have h := hs U hU U.1.left (𝟙 _) U.1.hom (by simp)
  refine le_bot_iff.mp (h.trans (le_of_eq ?_))
  simp only [Functor.comp_obj, Over.forget_obj, ObjectProperty.ι_obj, Scheme.Γ_obj,
    Functor.comp_map, Over.forget_map, Over.id_left, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, op_id, Scheme.Γ_map, unop_id, Scheme.Hom.id_app,
    CommRingCat.hom_id]
  exact (RingHom.injective_iff_ker_eq_bot (RingHom.id _)).mp Function.injective_id

/-- **The main result is not vacuous.** Every morphism of algebraic spaces into `X` factors
through the zero scheme of a section whose value on every étale chart of `X` is zero, and such
a section exists by `AlgebraicGeometry.Space.exists_sections_eval_eq_zero`.  This is the
hypothesis of `AlgebraicGeometry.Space.exists_comp_eq_zeroScheme_of_sectionEvaluationIdealAt_le`
instantiated at a section for which it holds. -/
theorem exists_comp_eq_zeroScheme_of_eval_eq_zero
    (X Y : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections)
    (hs : ∀ U : SmallEtale B S hS X.1, s.eval (op U) = 0) (f : Y ⟶ X) :
    ∃ g : Y ⟶ (⟨(zeroScheme B S hS X L s).1.toFunctor,
        (zeroScheme B S hS X L s).2.1⟩ : AlgebraicSpaces B S hS),
      g ≫ ObjectProperty.homMk (zeroScheme B S hS X L s).1.ι = f :=
  exists_comp_eq_zeroScheme_of_sectionEvaluationIdealAt_le B S hS X Y L s f
    fun U _ _ _ _ _ => (sectionEvaluationIdealAt_eq_bot B S hS X L s hs U).le.trans bot_le

end AlgebraicGeometry.Space

end
