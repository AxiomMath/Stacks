module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Deduplicating a covering family, and finite affine refinements of étale coverings

Two pieces of bookkeeping shared by every proof that the affine objects of a site form a
dense subsite.

The first is purely combinatorial. A `CategoryTheory.PreZeroHypercover` is a family of
arrows into a fixed object indexed by an arbitrary type, so the same arrow may occur many
times and the index type may be far larger than the set of arrows actually used. Replacing
the index type by that set of arrows changes neither the family's presieve nor its
finiteness, and makes the index type inject into the index type of any family the original
is combinatorially equivalent to. That injection is what bounds the cardinality of a
refinement by the cardinality of the family it refines, which is the condition a *chosen*
covering of a big site has to meet.

The second is geometric: an étale covering of an affine scheme has a finite refinement by
affine schemes, with each refining arrow an open immersion. This is Mathlib's
`AlgebraicGeometry.QuasiCompactCover.exists_hom`, once the étale precoverage is known to be
jointly surjective and étale morphisms are known to be open.

## Main definitions

* `AlgebraicGeometry.deduplicateFamily`: the family reindexed by the set of source-and-arrow
  pairs it uses.

## Main results

* `AlgebraicGeometry.deduplicateFamily_presieve₀`,
  `AlgebraicGeometry.deduplicateFamily_finite` and
  `AlgebraicGeometry.deduplicateFamily_card_le`: deduplicating preserves the presieve and
  finiteness, and bounds the cardinality of the index type by that of any combinatorially
  equivalent family.
* `AlgebraicGeometry.finite_affine_refinement_etaleCover`: an étale covering of an affine
  scheme is refined by a finite affine one through open immersions.

## Implementation notes

The deduplicated index type is `Set.range fun i => (⟨E.X i, E.f i⟩ : Σ Y, Y ⟶ T)`, a
subtype of a sigma type, so an element of it carries its own witness that some index of the
original family produces it; `AlgebraicGeometry.deduplicateFamily_index` extracts that
witness and is the only way the three statements about the deduplicated family are proved.
The cardinality bound needs `AlgebraicGeometry.pair_eq_of_combIndex_eq`, which says that a
combinatorial equivalence cannot identify two indices carrying different source-and-arrow
pairs, and therefore descends to an injection out of the deduplicated index type.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Deduplicating a family -/

/-- The family obtained from `E` by reindexing it by the set of source-and-arrow pairs it
actually uses, so that its index type injects into any family it is combinatorially equivalent
to. -/
noncomputable def deduplicateFamily
    {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T) :
    PreZeroHypercover T := {
  I₀ := Set.range fun i => (⟨E.X i, E.f i⟩ : Σ Y : C, Y ⟶ T)
  X p := p.1.1
  f p := p.1.2
}

/-- Every index of the deduplicated family comes from an index of the original one. -/
theorem deduplicateFamily_index
    {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T)
    (i : (deduplicateFamily E).I₀) :
    ∃ k : E.I₀, i = ⟨⟨E.X k, E.f k⟩, ⟨k, rfl⟩⟩ := by
  obtain ⟨k, hk⟩ := i.property
  exact ⟨k, Subtype.ext hk.symm⟩

/-- Deduplicating a family does not change the presieve it generates. -/
theorem deduplicateFamily_presieve₀
    {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T) :
    (deduplicateFamily E).presieve₀ = E.presieve₀ := by
  funext Y f
  refine propext ⟨?_, ?_⟩
  · rintro ⟨p⟩
    obtain ⟨i, rfl⟩ := deduplicateFamily_index E p
    exact ⟨i⟩
  · rintro ⟨i⟩
    exact ⟨(⟨_, i, rfl⟩ : (deduplicateFamily E).I₀)⟩

/-- Deduplicating a finite family leaves it finite. -/
theorem deduplicateFamily_finite
    {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T)
    [Finite E.I₀] : Finite (deduplicateFamily E).I₀ := by
  exact Finite.Set.finite_range _

/-- A combinatorial equivalence of families identifies two indices only when they carry the
same source-and-arrow pair. -/
theorem pair_eq_of_combIndex_eq
    {C : Type*} [Category C] {T : C}
    {E F : PreZeroHypercover T}
    (α : E.I₀ → F.I₀) (hX : ∀ i, E.X i = F.X (α i))
    (hf : ∀ i, E.f i = eqToHom (hX i) ≫ F.f (α i))
    (i j : E.I₀) (hij : α i = α j) :
    (⟨E.X i, E.f i⟩ : Σ Y : C, Y ⟶ T) = ⟨E.X j, E.f j⟩ := by
  have hXj : E.X j = F.X (α i) := by simpa [hij] using hX j
  have hs : E.X i = E.X j := (hX i).trans hXj.symm
  apply Sigma.ext hs
  simpa [hf] using congr_arg_heq F.f hij

/-- The index type of a deduplicated family is no larger than the index type of any family it
is combinatorially equivalent to. -/
theorem deduplicateFamily_card_le
    {C : Type*} [Category C] {T : C}
    {E F : PreZeroHypercover T}
    (h : PreZeroHypercover.CombinatoriallyEquivalent E F) :
    Cardinal.mk (deduplicateFamily E).I₀ ≤ Cardinal.mk F.I₀ := by
  obtain ⟨α, hX, hf⟩ := h.1
  let rep (p : (deduplicateFamily E).I₀) : E.I₀ := Classical.choose p.property
  let m (p : (deduplicateFamily E).I₀) : F.I₀ := α (rep p)
  have hm : Function.Injective m := by
    intro p q hpq
    apply Subtype.ext
    calc
      p.1 = ⟨E.X (rep p), E.f (rep p)⟩ := (Classical.choose_spec p.property).symm
      _ = ⟨E.X (rep q), E.f (rep q)⟩ :=
        pair_eq_of_combIndex_eq α hX hf (rep p) (rep q) hpq
      _ = q.1 := Classical.choose_spec q.property
  exact Cardinal.mk_le_of_injective hm

/-! ### Finite affine refinements of an étale covering -/

/-- An étale covering of an affine scheme is refined, through open immersions, by a finite
covering by affine schemes. -/
theorem finite_affine_refinement_etaleCover
    {T : Scheme.{u}} [IsAffine T]
    (U : Scheme.Cover Scheme.etalePrecoverage T) :
    ∃ (V : Scheme.AffineCover @Etale T) (f : V.cover ⟶ U),
      Finite V.I₀ ∧ ∀ i, IsOpenImmersion (f.h₀ i) := by
  have : Scheme.JointlySurjective Scheme.etalePrecoverage := by
    constructor
    intro Y R hR x
    change R ∈ Scheme.jointlySurjectivePrecoverage Y ∧ _ at hR
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    exact hR.1 x
  have : MorphismProperty.RespectsLeft @Etale @IsOpenImmersion := by
    constructor
    intro A C D i hi f hf
    exact Etale.etale_comp (f := i) (g := f)
  have : QuasiCompactCover U.toPreZeroHypercover := by
    refine QuasiCompactCover.of_isOpenMap (𝒰 := U) fun i => ?_
    have : Etale (U.f i) := U.map_prop i
    exact (U.f i).isOpenMap
  exact QuasiCompactCover.exists_hom U

end AlgebraicGeometry

end
