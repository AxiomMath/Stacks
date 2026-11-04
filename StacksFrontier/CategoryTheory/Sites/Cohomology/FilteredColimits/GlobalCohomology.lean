module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOverASheafOfSets
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.CoveringSetOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Filtered colimits and global cohomology (Stacks 0GN3)

Stacks 0GN3 says that if a site `C` carries a set `S` of quasi-compact sheaves of sets which
covers the final sheaf and is stable in the four senses (1)-(4) of the source, then
`colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism in every degree `p`, for every
filtered diagram of abelian sheaves.

The vanishing lemma `isZero_rightDerived_globalSections_colimit_of_isIso` reduces the statement to
one input: that for every `K ∈ S` and every `r` the functors `Ext^q(ℤ_{K^r}, -)` commute with the
colimit. This file supplies that input and so completes the proof. There are two steps.

The first is the localization comparison of Stacks 07A0
(`Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`): cohomology over a sheaf of sets `K` — that
is, `Ext` out of the free abelian sheaf on `K` — is cohomology of the site `C/K` of elements of
`K` with coefficients in the inverse image `j⁻¹`. Since `j⁻¹` is a left adjoint
(`preservesColimitsOfSize_sheafOfSets_inverseImage`) it commutes with the colimit, so the input is
Stacks 0GN3 itself on the localized site `C/K^r`.

The second is that `C/K^r` again carries a set of sheaves of sets satisfying the five hypotheses,
which is `Stacks.Cohomology.CoveringSet.exists_localized_coveringSet`. So the degree drops while
the site changes, and the induction closes.

## Main results

* `Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_extFunctorObj_freeAbelianSheafOn`:
  the localization comparison in the form the vanishing input wants — Stacks 0GN3 in degree `q` on
  the site of elements of `K` implies that `Ext^q(ℤ_K, -)` commutes with colimits of shape `I`.
* `Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections`:
  **Stacks 0GN3.**

## Implementation notes

The induction is a *strong* induction on the degree with the site generalised, and both of those
are needed. The recursion runs

> Stacks 0GN3 in degree `n + 1` over `C`  ⟸  the vanishing of `H^{n+1}(C, colim E)` on pointwise
> injective `E`  ⟸  Stacks 0GN3 in all degrees `q ≤ n` over the localized sites `C/K^r`,

so the inductive hypothesis is consumed at a *different site* from the one the conclusion is
about, and at an arbitrary smaller degree rather than at the predecessor. The plain induction
`isIso_colimit_post_rightDerived_globalSections_of_acyclic` fixes the site and takes the vanishing
input as a hypothesis quantified over all degrees, so it cannot discharge that hypothesis from its
own conclusion; the induction is therefore run again here rather than reusing it, and consumes the
degree-stratified `isZero_rightDerived_globalSections_colimit_of_isIso` instead.

`(Presheaf.freeAbelianSheaf J).obj K.obj` — the spelling in which the Čech resolution and the
vanishing input are stated — and `Stacks.Cohomology.SheafOfSets.freeAbelianSheafOn J K` — the
spelling of Stacks 07A0 — are equal by `rfl`, so the comparison below applies to the vanishing
input with no transport.

Everything is at the small-site convention of the source: the site, the coefficients and the
index category of the diagram all live in one universe `u`.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] enoughInjectives_sheaf_ab additive_globalSections_ab

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks 0791.** The inverse image `j⁻¹` of the localization morphism of topoi attached to a
sheaf of sets `K` preserves colimits, being the left adjoint of the pushforward along the
cocontinuous projection `j`. -/
lemma preservesColimitsOfSize_sheafOfSets_inverseImage (K : Sheaf J (Type u)) :
    PreservesColimitsOfSize.{u, u} (SheafOfSets.inverseImage J K) :=
  ((CostructuredArrow.proj (yoneda (C := C)) K.obj).sheafAdjunctionCocontinuous
    AddCommGrpCat.{u} (SheafOfSets.localizedTopology J K) J).leftAdjoint_preservesColimits

/-- **The localization comparison of Stacks 07A0, in the shape the vanishing input of Stacks 0GN3
wants it.** Let `K` be a sheaf of sets on a small site `C` and let `I` be a filtered index
category. If degree-`q` cohomology of the site `C/K` of elements of `K` commutes with colimits of
shape `I`, then `Ext^q(ℤ_K, -)` commutes with colimits of shape `I` on `C`.

Stacks 07A0 identifies `Ext^q(ℤ_K, -)` with `j⁻¹ ⋙ H^q(C/K, -)`, and `j⁻¹` preserves colimits, so
the hypothesis transports along that identification. This is the step that lets the induction of
`isIso_colimit_post_rightDerived_globalSections` descend to the localized sites. -/
lemma isIso_colimit_post_extFunctorObj_freeAbelianSheafOn (K : Sheaf J (Type u)) (q : ℕ)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (h : ∀ D : I ⥤ Sheaf (SheafOfSets.localizedTopology J K) Ab.{u},
      IsIso (colimit.post D
        ((Sheaf.Γ (SheafOfSets.localizedTopology J K) Ab.{u}).rightDerived q)))
    (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F (Abelian.extFunctorObj.{u}
      (SheafOfSets.freeAbelianSheafOn J K) q)) := by
  let L := SheafOfSets.inverseImage J K
  let J' := SheafOfSets.localizedTopology J K
  have := preservesColimitsOfSize_sheafOfSets_inverseImage J K
  have := h (F ⋙ L)
  have : IsIso (colimit.post (F ⋙ L) (Sheaf.functorH J' q)) :=
    isIso_colimit_post_of_iso (F ⋙ L) (globalSectionsRightDerivedIsoFunctorH J' q)
  have := preservesColimit_of_isIso_post (Sheaf.functorH J' q) (F ⋙ L)
  have : PreservesColimit F (L ⋙ Sheaf.functorH J' q) := inferInstance
  have := preservesColimit_of_natIso F (SheafOfSets.cohomologyOnSheafIso J K q).symm
  infer_instance

/-- **Stacks 0GN3.** Let `C` be a site and let `S` be a set of sheaves of sets on `C` such that

1. some `K ∈ S` surjects onto the final sheaf,
2. every surjection `G ⟶ K` onto a member of `S` admits a map `K' ⟶ G` from a member of `S` whose
   composite to `K` is surjective,
3. every pair of members of `S` is covered by a member of `S` mapping onto their product,
4. the equalizer of every pair of maps between members of `S` is covered by a member of `S`, and
5. every member of `S` is quasi-compact.

Then `colim_λ H^p(C, F_λ) ⟶ H^p(C, colim_λ F_λ)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian sheaves.

The proof is the source's induction on the degree. The base case is Stacks 0GMR (4), as
`isIso_colimit_post_rightDerived_globalSections_zero`; the step is the long exact cohomology
sequence of a functorial injective embedding of the diagram, as
`isIso_colimit_post_rightDerived_globalSections_succ`, whose acyclicity input is
`isZero_rightDerived_globalSections_colimit_of_isIso`. That input needs cohomology over the self
powers `K^r` of a `K ∈ S` to commute with the colimit in the degrees already known, which is
Stacks 07A0 (`isIso_colimit_post_extFunctorObj_freeAbelianSheafOn`) applied to Stacks 0GN3 on the
localized site `C/K^r`, available because `C/K^r` again carries such a set
(`Stacks.Cohomology.CoveringSet.exists_localized_coveringSet`). The induction is therefore strong
in the degree and generalised over the site. -/
@[stacks 0GN3]
theorem isIso_colimit_post_rightDerived_globalSections
    (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_equalizer : ∀ {K K' : Sheaf J (Type u)} (a b : K ⟶ K'), K ∈ S → K' ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    (p : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Ab.{u})) :
    IsIso (colimit.post F ((Sheaf.Γ J (Ab.{u})).rightDerived p)) := by
  induction p using Nat.strong_induction_on generalizing C with
  | _ p ih =>
    match p with
    | 0 =>
        exact isIso_colimit_post_rightDerived_globalSections_zero J S h_terminal h_lift
          h_product h_quasiCompact F
    | (n + 1) =>
        refine isIso_colimit_post_rightDerived_globalSections_succ J n
          (fun G => ih n (Nat.lt_succ_self n) J S h_terminal h_lift h_product h_equalizer
            h_quasiCompact G) ?_ F
        intro G hG
        refine isZero_rightDerived_globalSections_colimit_of_isIso J S h_terminal h_lift n G hG ?_
        intro K hK r q hq D
        refine isIso_colimit_post_extFunctorObj_freeAbelianSheafOn J
          (CoveringSet.sheafPower J K r) q ?_ D
        intro D'
        obtain ⟨S', ht', hl', hp', he', hqc'⟩ :=
          CoveringSet.exists_localized_coveringSet J S h_terminal h_lift h_product h_equalizer
            h_quasiCompact hK r
        exact ih q hq _ S' ht' hl' hp' he' hqc' D'

end Stacks.Cohomology.ColimitsOfCohomology

end
