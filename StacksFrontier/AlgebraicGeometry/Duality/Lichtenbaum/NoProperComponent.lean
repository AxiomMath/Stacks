module

public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.IntegralDevissage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm

/-!
# Top cohomology vanishes when no top-dimensional component is proper

Let `X` be a separated scheme of finite type over a field `k` with `dim X = d`. This file proves
the implication (3) ⇒ (1) of [Stacks, Tag 0G5F] — if no irreducible component of `X` of dimension
`d` is proper over `k`, then `H^d(X, F) = 0` for every coherent `F` — from
[Stacks, Tag 0G5E], taken here as a hypothesis and discharged where the theorem is assembled.

The argument is the source's. By the dévissage of
`Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_forall_integral_ideal` it suffices to show
`H^d(Z, 𝓘) = 0` for an integral closed subscheme `i : Z ⟶ X` and a nonzero coherent ideal
`𝓘 ⊆ 𝒪_Z`. `Z` is a variety over `k`; were `H^d(Z, 𝓘)` nonzero, [Stacks, Tag 0G5E] would give
`dim Z ≥ d`, hence `dim Z = d` since `dim Z ≤ dim X`, and `Z` proper over `k`. An integral closed
subset of `X` of the full dimension `d` is an irreducible component, and `Z` is the reduced
induced closed subscheme on it, so that component would be proper over `k`.

## Main results

* `Stacks.Duality.Lichtenbaum.isProper_subschemeι_vanishingIdeal_range_comp_iff`: a closed
  immersion `i : Z ⟶ X` from a reduced scheme is isomorphic over `X` to the reduced induced
  closed subscheme on its image, so properness over any base transfers between the two.
* `Stacks.Duality.Lichtenbaum.range_mem_irreducibleComponents_of_topologicalKrullDim_eq`: an
  integral closed subscheme of the full dimension `d = dim X` has an irreducible component as
  its image, and `topologicalKrullDim_subscheme_vanishingIdeal_range` that the reduced induced
  subscheme on that image has the dimension of `Z`.
* `Stacks.Duality.Lichtenbaum.exists_topologicalKrullDim_eq_natCast`: a nonempty scheme of
  finite type over a field has a natural number as its dimension.
* `Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_forall_not_isProper_of_lichtenbaum`:
  (3) ⇒ (1) of [Stacks, Tag 0G5F], given [Stacks, Tag 0G5E].

## Implementation notes

An irreducible component `X' ⊆ X` is viewed, as in the source, as an integral closed subscheme
through its reduced induced structure `(Scheme.IdealSheafData.vanishingIdeal X').subscheme`.

## References

* [Stacks Project, Tag 0G5F](https://stacks.math.columbia.edu/tag/0G5F)
* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality.Lichtenbaum

/-- **A closed immersion from a reduced scheme is the reduced induced subscheme on its image**,
so its composite with any morphism `f` is proper exactly when that of the reduced induced
closed subscheme on `Set.range i` is. -/
theorem isProper_subschemeι_vanishingIdeal_range_comp_iff {Z X Y : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsReduced Z] (f : X ⟶ Y) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩).subschemeι ≫ f) ↔
      IsProper (i ≫ f) := by
  have hker : i.ker = Scheme.IdealSheafData.vanishingIdeal
      ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩ := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact Closeds.ext i.isClosedEmbedding.isClosed_range.closure_eq
  have hi : i ≫ f = i.toImage ≫ i.ker.subschemeι ≫ f := by
    rw [← Category.assoc, i.toImage_imageι]
  rw [← hker, hi]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper i.toImage _).symm

/-- **An integral closed subscheme of the full dimension is an irreducible component.** If
`i : Z ⟶ X` is a closed immersion with `Z` irreducible and `dim Z = dim X = d` finite, then the
image of `i` is an irreducible component of `X`. -/
theorem range_mem_irreducibleComponents_of_topologicalKrullDim_eq {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IrreducibleSpace Z] (d : ℕ)
    (hX : topologicalKrullDim X = d) (hZ : topologicalKrullDim Z = d) :
    Set.range i ∈ irreducibleComponents X := by
  have hrange : topologicalKrullDim (Set.range i) = d :=
    (topologicalKrullDim_range_eq i).trans hZ
  refine mem_irreducibleComponents_of_topologicalKrullDim_eq ?_
    i.isClosedEmbedding.isClosed_range ?_ (hrange.trans hX.symm)
  · simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ Z).image i i.continuous.continuousOn
  · rw [hrange]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)

/-- The reduced induced closed subscheme on the image of a closed immersion `i : Z ⟶ X` has the
dimension of `Z`. -/
theorem topologicalKrullDim_subscheme_vanishingIdeal_range {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩).subscheme = topologicalKrullDim Z := by
  rw [← topologicalKrullDim_range_eq (Scheme.IdealSheafData.vanishingIdeal
      ⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩).subschemeι,
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
  exact topologicalKrullDim_range_eq i

/-- **The dimension of a nonempty scheme of finite type over a field is a natural number.** -/
theorem exists_topologicalKrullDim_eq_natCast (k : Type u) [Field k] {X : Scheme.{u}}
    [Nonempty X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ d : ℕ, topologicalKrullDim X = d := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp
    (show e ≠ ⊤ by rintro rfl; exact htop he.symm)
  exact ⟨d, he.symm⟩

/-- **[Stacks, Tag 0G5F], (3) ⇒ (1), given [Stacks, Tag 0G5E].** Let `X` be a separated scheme
of finite type over a field `k` with `dim X = d`. If no irreducible component of `X` of
dimension `d`, with its reduced induced structure
`(Scheme.IdealSheafData.vanishingIdeal X').subscheme`, is proper over `k`, then `H^d(X, F) = 0` for
every coherent `𝒪_X`-module `F`.

The hypothesis `lichtenbaum` is the statement of [Stacks, Tag 0G5E]: on a variety `Z` over `k`,
nonzero `H^d(Z, G)` for a coherent `G` forces `dim Z ≥ d`, and properness when `dim Z = d`. -/
theorem isZero_rightDerived_of_forall_not_isProper_of_lichtenbaum (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (d : ℕ) (hd : topologicalKrullDim X = d)
    (lichtenbaum : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) [IsVariety k g] (G : Z.Modules)
      [G.IsCoherent], ¬ IsZero (((moduleGlobalSections Z).rightDerived d).obj G) →
        (d : WithBot ℕ∞) ≤ topologicalKrullDim Z ∧ (topologicalKrullDim Z = d → IsProper g))
    (h : ∀ Z : irreducibleComponents X,
      let C := Scheme.IdealSheafData.vanishingIdeal (X := X)
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
      topologicalKrullDim C.subscheme = d → ¬ IsProper (C.subschemeι ≫ f))
    (F : X.Modules) [F.IsCoherent] :
    IsZero (((moduleGlobalSections X).rightDerived d).obj F) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  refine isZero_rightDerived_of_forall_integral_ideal X d ?_ F
  intro Z i _ _ I hI _
  by_contra hne
  have : IsVariety k (i ≫ f) := {}
  obtain ⟨hle, hproper⟩ := lichtenbaum Z (i ≫ f) I.toSheafOfModules hne
  have hZ : topologicalKrullDim Z = d :=
    le_antisymm (hd ▸ i.isClosedEmbedding.isInducing.topologicalKrullDim_le) hle
  have := hproper hZ
  have hC := range_mem_irreducibleComponents_of_topologicalKrullDim_eq i d hd hZ
  refine h ⟨_, hC⟩ ?_ ((isProper_subschemeι_vanishingIdeal_range_comp_iff i f).mpr this)
  exact (topologicalKrullDim_subscheme_vanishingIdeal_range i).trans hZ

end Stacks.Duality.Lichtenbaum
