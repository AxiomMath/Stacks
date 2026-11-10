module

public import StacksFrontier.AlgebraicGeometry.Devissage.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.SheafPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic

/-!
# Clause (3) of the dévissage [Stacks, Tag 01YM] for `H¹`, discharged

`StacksFrontier/AlgebraicGeometry/Devissage/Basic.lean` reduces [Stacks, Tag 01YQ] to three
hypotheses:
the conclusions of [Stacks, Tag 01YE] and [Stacks, Tag 01YL], and clause (3) of the dévissage
[Stacks, Tag 01YM] for the property `𝒫(ℱ) ⇔ H¹(X, ℱ) = 0`. **This file proves that third
hypothesis outright**, so 01YQ now rests on 01YE and 01YL alone — the two tags whose own source
proofs are the remaining mathematics.

Clause (3) asks, for every integral closed subscheme `Z ⊆ X` with generic point `ξ`, for a
coherent `𝒢` with

1. `Supp(𝒢) = Z`,
2. `𝒢_ξ` annihilated by `𝔪_ξ`, and
3. for every quasi-coherent sheaf of ideals `𝒥` with `𝒥_ξ = 𝒪_{X,ξ}`, a coherent subsheaf
   `𝒢' ⊆ 𝒢` whose sections lie in `𝒥(U)·Γ(𝒢,U)`, whose stalk map at `ξ` is surjective, and with
   `H¹(X, 𝒢') = 0`.

Taking `𝒢 = f_*ℱ` for the `ℱ` produced by [Stacks, Tag 01YO] and `𝒢' = 𝒥 · 𝒢`, every one of
these is proved in the library:

| clause | supplied by |
|---|---|
| `𝒢` coherent | [Stacks, Tag 01Y6] on the `ℱ` of [Stacks, Tag 01YO] |
| `Supp(𝒢) = Z` | [Stacks, Tag 01YO] plus `Scheme.IdealSheafData.range_subschemeι` |
| `𝒢_ξ` annihilated | [Stacks, Tag 01YO], character for character |
| `𝒢'` coherent | `PushforwardIdealSubsheaf.isCoherent_idealPowSmul_pushforward` |
| sections of `𝒢'` | `IdealPowerSmul.obj_idealPowSmul` at `n = 1` |
| `H¹(X, 𝒢') = 0` | `PushforwardIdealSubsheaf.isZero_hgroup_idealPowSmul_pushforward` |
| stalk surjectivity | `surjective_stalk_idealPowSmul_of_notMem_support`, proved here |

## Main results

* `surjective_stalkFunctor_map_ι_of_forall_mem`: **the one piece of mathematics this file adds.**
  If a subsheaf `N ⊆ ℱ` contains *every* section of `ℱ` over every open inside some neighbourhood
  `V` of `x`, then the stalk map `N_x → ℱ_x` is surjective. Stated for an arbitrary submodule of
  an arbitrary module sheaf, with no quasi-coherence and no ideal in sight.
* `surjective_stalk_idealPowSmul_of_notMem_support`: its instance for `𝒥ⁿ · ℱ` at a point off
  the support of `𝒥` — the residue that
  `StacksFrontier/AlgebraicGeometry/SheafPushforward/Basic.lean`
  recorded as still owed.
* `exists_coherent_generic_of_isFinite_surjective`: **clause (3) of [Stacks, Tag 01YM] for `H¹`,
  unconditionally**, for `f : Y ⟶ X` finite and surjective with `Y` affine and `X` locally
  Noetherian.
* `isAffine_of_isFinite_surjective_of_h01YE_h01YL`: **[Stacks, Tag 01YQ] with exactly two
  hypotheses, the conclusions of [Stacks, Tag 01YE] and [Stacks, Tag 01YL].**

## Why clause (3) was not over-specified, unlike (3)(c)

`StacksFrontier/AlgebraicGeometry/SheafPushforward/Basic.lean` found 01YM's clause (3)(c) to be
*over*-specified in the record it inherited: the clause asks for some coherent `𝒢' ⊆ 𝒢` with
sections inside `𝒥(U)·Γ(𝒢,U)`, not for `𝒥·𝒢`, so only one inclusion of [Stacks, Tag 01YP] is needed.
The stalk clause admits no such weakening and none is needed: it is already stated as *surjectivity*
of `(𝒢')_ξ → 𝒢_ξ` rather than as the equality `(𝒢')_ξ = 𝒢_ξ` that the source asserts, and
surjectivity is the half the dévissage consumes. So the statement was minimal as written and the
work here is to prove it.

The proof is three lines once the right general statement is isolated, and the reason is that
`𝒥ⁿ · ℱ` is *not* merely generically equal to `ℱ` off `V(𝒥)` — it has **all** of its sections
there, by `IdealPowerComparison.mem_idealPowerMultiple`. So no colimit cofinality argument and no
germ-level ideal computation appear: a germ at `ξ` is represented by a section over some open,
that open is shrunk inside `idealComplement 𝒥` by `TopCat.Presheaf.exists_le_germ_eq`, and the
shrunken section already lies in the subsheaf.

## What remains, and it is exactly two tags

`isAffine_of_isFinite_surjective_of_h01YE_h01YL` carries two hypotheses Tag 01YQ does not grant,
so **no `stacks` attribute is attached**: Tag 01YQ has a single unlabelled assertion, so no
part of it is proved here on its own. The two are

* `Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X` — [Stacks, Tag 01YE], whose own residue
  is the global bijectivity of [Stacks, Tag 01YB], not yet proved in this library; and
* `Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X` — [Stacks, Tag 01YL], whose source proof
  also consumes 01YE.

Neither is touched here, but **one obstacle to 01YL recorded elsewhere is no longer an
obstacle.** `StacksFrontier/AlgebraicGeometry/Devissage/Basic.lean`'s item 2 says of
01YL that "the load-bearing missing statement is that a nonzero quasi-coherent sheaf of ideals on
an integral scheme has full support, which is already named as the blocker
for 01YH's own top stratum." That statement is proved in the library, in both the forms the
intersection
argument consumes: `Tag01YHFullSupport.supp_eq_univ_of_not_isZero` and
`Tag01YHFullSupport.genericPoint_mem_supp_of_not_isZero`. Of the three steps
the top stratum of 01YH requires, 01YL needs only two — 01YE, and the
intersection argument whose geometric input is the pair just named — because the third, the
multiplicity-one reduction through `Module.length` of a stalk (still genuinely absent), is
exactly what 01YL's condition (2) exists to remove. So 01YL's residue is 01YE plus sheaf
plumbing, not new geometry; that is not done here.

The dévissage's clauses (1) and (2) were already proved in
`StacksFrontier/AlgebraicGeometry/Devissage/Basic.lean`; with clause (3) now proved as well, nothing
cohomological and nothing about `f` is outstanding — **finiteness and surjectivity of `f`, and
affineness of `Y`, are used only in this file**, and only to build `𝒢` and to vanish `H¹(X, 𝒢')`.

## Implementation notes

**`mathlib_search` negatives.** "stalk map of a submodule inclusion is surjective when the
submodule is everything on a neighbourhood" returns only the plain-module subtype API
(`Submodule.subtypeₗᵢ_toLinearMap`, `SMulMemClass.subtype_injective`,
`Submodule.map_subtype_top`, nearest at distance 0.2731) — nothing sheaf-theoretic, and in
particular no transfer of a sections-level statement to a stalk. "a finite surjective morphism to
a Noetherian scheme from an affine scheme makes the target affine" returns
`AlgebraicGeometry.isAffine_of_isAffineHom` at distance 0.1848, which goes the **opposite**
direction — it concludes `IsAffine X` from `IsAffine Y` for `f : X ⟶ Y`, i.e. affineness descends
to the *source*, which is the trivial direction and not 01YQ.

**The quasi-coherence instance on `f_*ℱ` is left to instance search in every occurrence.** Both
`PushforwardIdealSubsheaf.isCoherent_idealPowSmul_pushforward` and
`isZero_hgroup_idealPowSmul_pushforward` mention `IdealPowerSmul.idealPowSmul 𝒥 1 (f_*ℱ)`,
whose
elaboration needs `(f_*ℱ).IsQuasicoherent`; introducing a local `have` for it would make the
subsheaf in the goal a *different term* from the one in those lemmas' conclusions, since
`idealPowSmul` takes the instance as an argument. So the instance is never named.

**The annihilation clause transfers by `exact`, with no bridge.** [Stacks, Tag 01YO]'s third
conclusion is written out inline, with the same `letI` module instance that
`Tag01YEStalkBridge.IsMaximalIdealAnnihilated` is defined by, so the latter unfolds to the former
at default transparency.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YO](https://stacks.math.columbia.edu/tag/01YO)
* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YQClauseThree

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}}

/-! ### Stalk surjectivity for a subsheaf that is everything near a point -/

/-- **A subsheaf containing every section over every open inside a neighbourhood of `x` has
surjective stalk map at `x`.** No quasi-coherence, no ideal, and no colimit cofinality argument:
a germ at `x` is a section over some open, `TopCat.Presheaf.exists_le_germ_eq` shrinks that open
inside `V`, and the shrunken section already lies in the subsheaf. -/
theorem surjective_stalkFunctor_map_ι_of_forall_mem
    {F : X.Modules} (N : F.Submodule) {x : X} {V : X.Opens} (hxV : x ∈ V)
    (hmem : ∀ W : X.Opens, W ≤ V → ∀ s : Γ(F, W), s ∈ N.toSubmodule.obj (op W)) :
    Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf N.ι)).hom) := by
  intro t
  obtain ⟨W, hWV, hxW, s, hs⟩ := (Scheme.Modules.presheaf F).exists_le_germ_eq t hxV
  exact ⟨(Scheme.Modules.presheaf N.toSheafOfModules).germ W x hxW ⟨s, hmem W hWV s⟩,
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW _ _).trans hs⟩

/-- **The stalk map of `𝒥ⁿ · ℱ ⟶ ℱ` is surjective at every point off the support of `𝒥`.** This
is the residue that `StacksFrontier/AlgebraicGeometry/SheafPushforward/Basic.lean` recorded as still
owed inside clause (3) of [Stacks, Tag 01YM]. Off `V(𝒥)` the subsheaf has *all* the sections of `ℱ`,
by `IdealPowerComparison.mem_idealPowerMultiple`, so the previous lemma applies with
`V = idealComplement 𝒥`. -/
theorem surjective_stalk_idealPowSmul_of_notMem_support
    (J : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent]
    {x : X} (hx : x ∉ J.support) :
    Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf (IdealPowerSmul.idealPowSmul J n F).ι)).hom) := by
  refine surjective_stalkFunctor_map_ι_of_forall_mem _
    (V := Stacks.LocalCohomology.idealComplement J) hx fun W hWV s ↦ ?_
  rw [← IdealPowerComparison.idealPowerMultiple_eq_idealPowSmul J n F]
  exact IdealPowerComparison.mem_idealPowerMultiple J n F hWV s

/-! ### Clause (3) of the dévissage, for `H¹` -/

/-- **Clause (3) of [Stacks, Tag 01YM] for `𝒫(ℱ) ⇔ H¹(X, ℱ) = 0`, unconditionally.** For
`f : Y ⟶ X` finite and surjective with `Y` affine and `X` locally Noetherian, and for every
integral closed subscheme of `X`, the coherent module `𝒢 = f_*ℱ` of [Stacks, Tag 01YO] has
support exactly that subscheme, annihilated generic stalk, and — for every quasi-coherent sheaf of
ideals `𝒥` not vanishing at the generic point — the subsheaf `𝒢' = 𝒥 · 𝒢` is coherent, has
sections inside `𝒥(U)·Γ(𝒢,U)`, is generically surjective onto `𝒢`, and has vanishing `H¹`. -/
theorem exists_coherent_generic_of_isFinite_surjective (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    ∃ G : X.Modules, G.IsCoherent ∧
      (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
      Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
        (I.subschemeι (genericPoint I.subscheme)) ∧
      (∀ J : X.IdealSheafData,
        I.subschemeι (genericPoint I.subscheme) ∉ J.support →
        ∃ G' : G.Submodule,
          G'.toSheafOfModules.IsCoherent ∧
          (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
            (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
              J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
          Function.Surjective
            (((TopCat.Presheaf.stalkFunctor Ab
              (I.subschemeι (genericPoint I.subscheme))).map
                (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
          IsZero (Hgroup X.ringCatSheaf ⊤ 1 G'.toSheafOfModules)) := by
  obtain ⟨F, hFcoh, hsupp, hann⟩ :=
    FiniteSurjectiveCoherentSupport.exists_isCoherent_supp_pushforward_eq_range f I.subschemeι
  have _ : F.IsCoherent := hFcoh
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine ⟨(Scheme.Modules.pushforward f).obj F,
    FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f F, fun x ↦ ?_, hann,
    fun J hJ ↦ ?_⟩
  · have hmem : x ∈ SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ↔
        x ∈ I.support := by
      rw [hsupp]
      simp
    exact hmem.symm.trans (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x)
  · refine ⟨IdealPowerSmul.idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj F),
      PushforwardIdealSubsheaf.isCoherent_idealPowSmul_pushforward f J F, fun U s ↦ ?_,
      surjective_stalk_idealPowSmul_of_notMem_support J 1 _ hJ,
      PushforwardIdealSubsheaf.isZero_hgroup_idealPowSmul_pushforward f J F 1 Nat.one_pos⟩
    have hobj := IdealPowerSmul.obj_idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj F) U
    rw [pow_one] at hobj
    exact hobj.le s.2

/-! ### [Stacks, Tag 01YQ] on [Stacks, Tag 01YE] and [Stacks, Tag 01YL] alone -/

/-- **[Stacks, Tag 01YQ] with exactly two hypotheses: the conclusions of [Stacks, Tag 01YE] and
[Stacks, Tag 01YL].** A Noetherian scheme receiving a finite surjective morphism from an affine
scheme is affine, given only those two.

Compared to `Tag01YQDevissage.isAffine_of_isFinite_surjective_of_hgeneric`, clause (3) of the
dévissage [Stacks, Tag 01YM] is no longer assumed: it is
`exists_coherent_generic_of_isFinite_surjective`. Everything else in the source's proof is
proved in the library — Serre's criterion [Stacks, Tag 01XF], the dévissage reduction [Stacks, Tag
01YM] on its
two named inputs, and clauses (1) and (2).

**No `stacks` attribute is attached:** Tag 01YQ carries one unlabelled assertion, so the
covering set is the whole theorem and the two remaining hypotheses are not granted by the tag. -/
theorem isAffine_of_isFinite_surjective_of_h01YE_h01YL (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X) :
    IsAffine X :=
  Tag01YQDevissage.isAffine_of_isFinite_surjective_of_hgeneric X f h01YE h01YL
    fun I _ ↦ exists_coherent_generic_of_isFinite_surjective f I

/-- **Faithfulness, in the binder order of Tag 01YQ.** The statement of Tag 01YQ is

    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
      : IsAffine X

and this `example` is that statement verbatim — same binders, same order, same four
typeclasses — with the two surviving hypotheses appended and nothing else changed. So exactly
two propositions stand between this file and the tagged statement, and both are named tags
whose own statements are formalized as predicates: [Stacks, Tag 01YE] and [Stacks, Tag 01YL]. -/
example {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
    [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X) :
    IsAffine X :=
  isAffine_of_isFinite_surjective_of_h01YE_h01YL f h01YE h01YL

end Stacks.AlgebraicGeometry.Tag01YQClauseThree

end
