module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Combinatorics.Quiver.ReflQuiver

@[expose] public section

/-
# Problem Description

Stacks Tag 05PM.

Let `𝒜` be an abelian category (with all pullbacks). The coverings of an object
`U` are taken to be the single-arrow families `{f : V ⟶ U}` with `f` surjective,
where "surjective" is interpreted (as is standard in a general abelian category)
as "epimorphism" (`CategoryTheory.Epi`).

The claim is that this assignment defines a (Grothendieck) pretopology on `𝒜`,
i.e. there is a term `K : CategoryTheory.Pretopology 𝒜` whose coverings are
exactly the single-epimorphism presieves.

A `CategoryTheory.Pretopology` (Stacks Tag 00VH, the notion of a "site") is a
function `coverings : (X : C) → Set (Presieve X)` satisfying:
1. (`has_isos`) for every isomorphism `f : Y ⟶ X`, `Presieve.singleton f` is a
   covering of `X`;
2. (`pullbacks`) if `S` is a covering of `X` and `f : Y ⟶ X` is any morphism,
   then `Presieve.pullbackArrows f S` is a covering of `Y`;
3. (`transitive`) if `S` is a covering of `X` and for each arrow `f : Y ⟶ X` in
   `S` we are given a covering `Ti f` of `Y`, then `S.bind Ti` is a covering of
   `X`.
-/

-- Background and context (as comments):
-- * "Surjective" = "epimorphism": in a general abelian category the correct
--   categorical rendering of "surjective" is "epimorphism".
-- * Single-arrow covering families `{f : V → U}` correspond to
--   `Presieve.singleton f`.
-- * Cited dependencies (not re-proved here):
--   - Stacks 00VH: `CategoryTheory.Pretopology`.
--   - Stacks 05PK (base change of a surjection is a surjection):
--     `CategoryTheory.Abelian.epi_pullback_of_epi_f`.

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.EpiPretopology

variable (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜] [HasPullbacks 𝒜]

-- Main Definition(s)

/-- The set of coverings of `U` is the set of presieves consisting of a single
epimorphism with target `U`. This encodes the Stacks single-arrow covering
family `{f : V → U}` with `f` surjective (= epi). -/
def EpiCoverings (U : 𝒜) : Set (Presieve U) :=
  { S | ∃ (V : 𝒜) (f : V ⟶ U), Epi f ∧ S = Presieve.singleton f }

-- Main Statement(s)

-- The three axioms, stated explicitly (the content of the proof below).

omit [Abelian 𝒜] [HasPullbacks 𝒜] in
/-- Axiom 1 (isomorphisms are coverings): for every isomorphism `f : V ⟶ U`,
the presieve `Presieve.singleton f` lies in `EpiCoverings U`. -/
theorem epiCoverings_has_isos {U V : 𝒜} (f : V ⟶ U) [IsIso f] :
    Presieve.singleton f ∈ EpiCoverings 𝒜 U :=
  ⟨V, f, inferInstance, rfl⟩

/-- Axiom 2 (stability under base change): if `S ∈ EpiCoverings U` and
`g : W ⟶ U` is any morphism, then `Presieve.pullbackArrows g S ∈ EpiCoverings W`. -/
theorem epiCoverings_pullbacks {U W : 𝒜} (g : W ⟶ U) (S : Presieve U)
    (hS : S ∈ EpiCoverings 𝒜 U) :
    Presieve.pullbackArrows g S ∈ EpiCoverings 𝒜 W := by
  obtain ⟨V, f, hf, rfl⟩ := hS
  exact ⟨pullback f g, pullback.snd f g, Abelian.epi_pullback_of_epi_f f g,
    Presieve.pullback_singleton g f⟩

omit [Abelian 𝒜] [HasPullbacks 𝒜] in
/-- Axiom 3 (stability under composition / transitivity): if `S ∈ EpiCoverings U`
and for each arrow `f : V ⟶ U` in `S` we are given `Ti f ∈ EpiCoverings V`, then
`S.bind Ti ∈ EpiCoverings U`. -/
theorem epiCoverings_transitive {U : 𝒜} (S : Presieve U)
    (Ti : ⦃Y : 𝒜⦄ → (f : Y ⟶ U) → S f → Presieve Y)
    (hS : S ∈ EpiCoverings 𝒜 U)
    (hTi : ∀ ⦃Y : 𝒜⦄ (f : Y ⟶ U) (H : S f), Ti f H ∈ EpiCoverings 𝒜 Y) :
    S.bind Ti ∈ EpiCoverings 𝒜 U := by
  obtain ⟨V, f, hf, rfl⟩ := hS
  have hfmem : Presieve.singleton f f := Presieve.singleton.mk
  obtain ⟨W, h, hh, hTeq⟩ := hTi f hfmem
  refine ⟨W, h ≫ f, ?_, ?_⟩
  · exact epi_comp h f
  · funext Z
    ext k
    constructor
    · rintro ⟨Y, p, q, H, hpq, rfl⟩
      cases H
      rw [hTeq] at hpq
      cases hpq
      exact Presieve.singleton.mk
    · rintro ⟨⟩
      refine ⟨V, h, f, hfmem, ?_, rfl⟩
      rw [hTeq]
      exact Presieve.singleton.mk

/-- **Statement 1 (Stacks Tag 05PM).** The assignment `U ↦ EpiCoverings U`
satisfies the three pretopology axioms and hence determines a pretopology on the
abelian category `𝒜`, with coverings given exactly by `EpiCoverings`. -/
@[stacks 05PM]
theorem exists_pretopology_epiCoverings :
    ∃ K : Pretopology 𝒜, ∀ U : 𝒜, K.coverings U = EpiCoverings 𝒜 U :=
  ⟨{ coverings := EpiCoverings 𝒜
     has_isos := fun _ _ f _ => epiCoverings_has_isos 𝒜 f
     pullbacks := fun _ _ f S hS => epiCoverings_pullbacks 𝒜 f S hS
     transitive := fun _ S Ti hS hTi => epiCoverings_transitive 𝒜 S Ti hS hTi }, fun _ => rfl⟩

end Stacks.Sites.EpiPretopology
