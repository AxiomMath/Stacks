module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.StacksAttribute

/-! # Global sections of a filtered colimit from a covering set of quasi-compact sheaves

Stacks 0GN3 puts the following hypotheses on a set `S` of sheaves of sets on a site `C`:

1. some `K ∈ S` surjects onto the final sheaf;
2. a surjection `G ⟶ K` onto a member of `S` admits a map `K' ⟶ G` from a member of `S` whose
   composite `K' ⟶ K` is still surjective;
3. two members of `S` admit a surjection onto their product from a member of `S`;
4. two parallel morphisms between members of `S` admit a surjection onto their equalizer from a
   member of `S`;
5. every member of `S` is quasi-compact (Stacks 0D07).

Under those hypotheses the degree-`p` cohomology of the site commutes with filtered colimits of
abelian sheaves for every `p`. This file proves the case `p = 0`, on sheaves of sets: the
canonical map `colim_i Γ(C, F i) ⟶ Γ(C, colim_i F i)` is bijective for every filtered diagram
`F` of sheaves of sets.

The work is to produce from (1)–(5) the hypothesis of part (4) of Stacks 0GMR, which is already
available as `CategoryTheory.Sheaf.injective_and_bijective_colimit_post_globalSections`. That
hypothesis asks for a set `S` such that

* every sheaf surjecting onto the final sheaf receives a map from a member of `S` which itself
  surjects onto the final sheaf, and
* `K ⨯ K` is quasi-compact for every `K ∈ S`.

The second point is (3) and (5) combined through Stacks 0GMP (2): a member of `S` surjecting
onto `K ⨯ K` is quasi-compact, hence so is `K ⨯ K`. The first point is the argument the source
gives while verifying its base case: if `G` surjects onto the final sheaf then so does the
projection `G ⨯ K ⟶ K` for any `K`, so (2) applied to that projection produces a `K' ∈ S` with
a map to `G ⨯ K` whose composite to `K` is surjective; composing with `G ⨯ K ⟶ G` gives the map
to `G`, and `K' ⟶ K ⟶ *` is surjective.

## Main results

* `CategoryTheory.Sheaf.isQuasiCompact_prod_self_of_coveringSet`: hypotheses (3) and (5) make
  `K ⨯ K` quasi-compact for every `K ∈ S`.
* `CategoryTheory.Sheaf.exists_mem_hom_isLocallySurjective_terminal_of_coveringSet`: hypotheses
  (1) and (2) give the lifting property for sheaves surjecting onto the final sheaf.
* `CategoryTheory.Sheaf.bijective_colimit_post_globalSections_of_coveringSet`: the resulting
  bijectivity of `colim_i Γ(C, F i) ⟶ Γ(C, colim_i F i)` — the case `p = 0` of Stacks 0GN3.

## Implementation notes

Surjectivity of a map of sheaves of sets is local surjectivity (Stacks 00WM (2)), i.e. Mathlib's
`CategoryTheory.Sheaf.IsLocallySurjective`, and quasi-compactness is
`CategoryTheory.Sheaf.IsQuasiCompact` (Stacks 0D07). The hypotheses are taken in exactly the
shape Stacks 0GN3 states them, so that this file can be applied verbatim as the base case of the
induction on `p`.

`Sheaf.IsLocallySurjective (Limits.prod.snd : G ⨯ K ⟶ K)` is the base change of
`G ⟶ *` along `K ⟶ *`; it is proved here from the definition, by pairing a section of `K` with a
local section of `G`, since local surjectivity of a product projection is not available in
Mathlib.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMP](https://stacks.math.columbia.edu/tag/0GMP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Sections of the final sheaf and of a binary product -/

/-- Alias of `Stacks.Sites.ColimitGlobalSections.exists_prod_section`. -/
alias exists_section_of_prod := Stacks.Sites.ColimitGlobalSections.exists_prod_section

/-! ### The hypothesis of Stacks 0GMR part (4) -/

/-- **Stacks 0GN3, hypotheses (3) and (5).** If two members of a set `S` of sheaves of sets admit
a surjection onto their product from a member of `S`, and every member of `S` is quasi-compact,
then `K ⨯ K` is quasi-compact for every `K ∈ S`: this is Stacks 0GMP (2) applied to that
surjection. -/
theorem isQuasiCompact_prod_self_of_coveringSet {S : Set (Sheaf J (Type max u v))}
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, IsQuasiCompact K) (K : Sheaf J (Type max u v)) (hK : K ∈ S) :
    IsQuasiCompact (K ⨯ K) := by
  obtain ⟨K'', hK'', f, hf⟩ := h_product K hK K hK
  exact isQuasiCompact_of_isLocallySurjective f hf (h_quasiCompact K'' hK'')

/-- **Stacks 0GN3, hypotheses (1) and (2).** Let `S` be a set of sheaves of sets containing a
member which surjects onto the final sheaf, and such that a surjection onto a member of `S`
admits a map from a member of `S` with surjective composite. Then every sheaf `G` surjecting onto
the final sheaf receives a map from a member of `S` which itself surjects onto the final sheaf.

This is the verification the source carries out for its base case: `G ⨯ K ⟶ K` is surjective
because `G ⟶ *` is, so hypothesis (2) applied to it produces `K' ∈ S` with a map to `G ⨯ K`
whose composite `K' ⟶ K` is surjective; then `K' ⟶ G ⨯ K ⟶ G` is the required map, and
`K' ⟶ K ⟶ *` is surjective. -/
theorem exists_mem_hom_isLocallySurjective_terminal_of_coveringSet
    {S : Set (Sheaf J (Type max u v))}
    (h_terminal : ∃ K ∈ S, IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type max u v)} (f : G ⟶ K), K ∈ S →
      IsLocallySurjective f → ∃ K' ∈ S, ∃ g : K' ⟶ G, IsLocallySurjective (g ≫ f))
    (G : Sheaf J (Type max u v)) (hG : IsLocallySurjective (terminal.from G)) :
    ∃ K ∈ S, Nonempty (K ⟶ G) ∧ IsLocallySurjective (terminal.from K) := by
  obtain ⟨K₀, hK₀, hK₀surj⟩ := h_terminal
  obtain ⟨K', hK', g, hg⟩ :=
    h_lift (Limits.prod.snd : G ⨯ K₀ ⟶ K₀) hK₀ (isLocallySurjective_prod_snd hG)
  refine ⟨K', hK', ⟨g ≫ Limits.prod.fst⟩, ?_⟩
  rw [show terminal.from K' = (g ≫ (Limits.prod.snd : G ⨯ K₀ ⟶ K₀)) ≫ terminal.from K₀ from
    terminal.hom_ext _ _]
  have := hg
  have := hK₀surj
  infer_instance

/-! ### Global sections of a filtered colimit -/

/-- **Stacks 0GN3 for `p = 0`.** Let `C` be a site and let `S` be a set of sheaves of sets on `C`
satisfying the five hypotheses of Stacks 0GN3: a member of `S` surjects onto the final sheaf,
surjections onto members of `S` are lifted by members of `S`, products and equalizers of members
of `S` receive surjections from members of `S`, and every member of `S` is quasi-compact. Then
for every filtered diagram `F` of sheaves of sets the canonical map
`colim_i Γ(C, F i) ⟶ Γ(C, colim_i F i)` is bijective.

This is part (4) of Stacks 0GMR, whose hypothesis is supplied by
`exists_mem_hom_isLocallySurjective_terminal_of_coveringSet` and
`isQuasiCompact_prod_self_of_coveringSet`. Hypothesis (4) of the source, on equalizers, plays no
role in degree zero and is therefore omitted; it is what makes the induction on `p` go. -/
theorem bijective_colimit_post_globalSections_of_coveringSet {I : Type w₁} [Category.{w₂} I]
    [IsFiltered I] [HasColimitsOfShape I (Type max u v)] (F : I ⥤ Sheaf J (Type max u v))
    {S : Set (Sheaf J (Type max u v))}
    (h_terminal : ∃ K ∈ S, IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type max u v)} (f : G ⟶ K), K ∈ S →
      IsLocallySurjective f → ∃ K' ∈ S, ∃ g : K' ⟶ G, IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, IsQuasiCompact K) :
    Function.Bijective (colimit.post F (Γ J (Type max u v))) :=
  (injective_and_bijective_colimit_post_globalSections J F).2.2.2
    ⟨S, fun G hG =>
        exists_mem_hom_isLocallySurjective_terminal_of_coveringSet h_terminal h_lift G hG,
      fun K hK => isQuasiCompact_prod_self_of_coveringSet h_product h_quasiCompact K hK⟩

end CategoryTheory.Sheaf

end
