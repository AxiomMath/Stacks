module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ample sheaves on the irreducible components of a scheme of dimension at most one

The proof of [Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX) opens by taking the
irreducible components `Z_i` of `X`, viewing them as *reduced* closed subschemes, and applying
[Tag 09ND](https://stacks.math.columbia.edu/tag/09ND) to obtain ample invertible sheaves on
them. This file carries out that step.

The reduced induced structure is `(Scheme.IdealSheafData.vanishingIdeal Z).subscheme`, whose
reducedness and support are
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` and
`range_subschemeι_vanishingIdeal`, and whose local Noetherianness is
`isLocallyNoetherian_subscheme`. This file proves compactness, separatedness and the dimension
bound for the source of a closed immersion; integrality for an *irreducible* closed subset; and
Tag 09ND with the dimension hypothesis relaxed to `≤ 1`.

Tag 09ND assumes `topologicalKrullDim X = 1`, and an irreducible component of a
one-dimensional scheme may be zero-dimensional — a reduced point, say, glued to a line. So Tag
09ND is relaxed here to `≤ 1`: in the zero-dimensional case the scheme is irreducible with every
point closed, hence a single point, hence affine, and the structure sheaf of an affine scheme is
already ample.

## Main results

* `StacksTag09NX.compactSpace_of_isClosedImmersion`,
  `StacksTag09NX.isSeparated_of_isClosedImmersion`,
  `StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion`: compactness, separatedness and
  the Krull dimension bound pass to the source of a closed immersion.
* `StacksTag09NX.isNoetherian_subscheme`: a closed subscheme of a Noetherian scheme is
  Noetherian.
* `StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible`: the reduced induced
  subscheme on an irreducible closed subset is integral.
* `StacksTag09NX.exists_isAmple_of_topologicalKrullDim_le_one`: **Tag 09ND with `≤ 1` in place
  of `= 1`.**
* `StacksTag09NX.exists_isAmple_subscheme_vanishingIdeal_irreducibleComponent`: **every
  irreducible component of a Noetherian separated scheme of dimension at most one, with its
  reduced induced structure, has an ample invertible sheaf** — the first step of the proof of
  Tag 09NX.

## Implementation notes

`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` is the
special case of `isIntegral_subscheme_vanishingIdeal_of_isIrreducible` where the closed set is
the closure of a point; the general statement is given here.

The reducedness of `X` plays no part: the reduced induced structure on a closed subset is
reduced whatever `X` is, so the results below ask only that `X` be Noetherian and separated.
Tag 09NX's own `IsReduced X` hypothesis is used later in its proof, where the components have to
cover `X` *as schemes* and not merely as sets.

The zero-dimensional case is reached through sobriety rather than through an affineness
criterion: an irreducible scheme all of whose points are closed is the closure of its generic
point and therefore a single point, and a scheme on one point is covered by one affine open,
which must be everything.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace StacksTag09NX

section ClosedImmersion

variable {X Y : Scheme.{u}}

/-- The source of a closed immersion into a compact scheme is compact. -/
public theorem compactSpace_of_isClosedImmersion (f : Y ⟶ X) [IsClosedImmersion f]
    [CompactSpace X] : CompactSpace Y :=
  Topology.IsClosedEmbedding.compactSpace f.isClosedEmbedding

/-- **The source of a closed immersion into a separated scheme is separated**: its structure
morphism to the terminal scheme factors through the immersion. -/
public theorem isSeparated_of_isClosedImmersion (f : Y ⟶ X) [IsClosedImmersion f]
    [X.IsSeparated] : Y.IsSeparated := by
  constructor
  have he : terminal.from Y = f ≫ terminal.from X := terminal.hom_ext _ _
  rw [he]
  infer_instance

/-- **The source of a closed immersion has no larger Krull dimension than its target.** -/
public theorem topologicalKrullDim_le_of_isClosedImmersion (f : Y ⟶ X) [IsClosedImmersion f] :
    topologicalKrullDim (Y : Type u) ≤ topologicalKrullDim (X : Type u) :=
  f.isClosedEmbedding.isInducing.topologicalKrullDim_le

end ClosedImmersion

/-- **A closed subscheme of a Noetherian scheme is Noetherian.** Local Noetherianness is
`AlgebraicGeometry.Scheme.IdealSheafData.isLocallyNoetherian_subscheme`; compactness comes from
the closed immersion. -/
@[ega "I 6.1.4" "special case"]
public theorem isNoetherian_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsNoetherian X] : IsNoetherian I.subscheme :=
  have : IsLocallyNoetherian I.subscheme := I.isLocallyNoetherian_subscheme
  have : CompactSpace I.subscheme := compactSpace_of_isClosedImmersion I.subschemeι
  ⟨⟩

/-- **The reduced induced closed subscheme on an irreducible closed subset is integral.** It is
reduced by `isReduced_subscheme_vanishingIdeal` and irreducible because its underlying space is
homeomorphic to the subset. -/
public theorem isIntegral_subscheme_vanishingIdeal_of_isIrreducible {X : Scheme.{u}}
    (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (vanishingIdeal Z).subscheme :=
  have : IrreducibleSpace (vanishingIdeal Z).subscheme :=
    irreducibleSpace_subscheme X _ (by rwa [range_subschemeι_vanishingIdeal])
  isIntegral_of_irreducibleSpace_of_isReduced _

section ZeroDimensional

/-- In `WithBot ℕ∞` — the home of `topologicalKrullDim` — anything strictly below one is at most
zero. -/
public theorem le_zero_of_lt_one {x : WithBot ℕ∞} (h : x < 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    have ha : a < 1 := by exact_mod_cast h
    rw [Order.lt_one_iff.mp ha]
    exact le_of_eq (by norm_cast)

/-- **An irreducible scheme of Krull dimension at most zero has exactly one point**: it is the
closure of its generic point, and that point is closed. -/
@[ega "IV 10.7.1" "partial"]
public theorem subsingleton_of_topologicalKrullDim_le_zero (X : Scheme.{u}) [IrreducibleSpace X]
    (hdim : topologicalKrullDim (X : Type u) ≤ 0) : Subsingleton X := by
  have hcl : IsClosed ({genericPoint X} : Set X) :=
    Stacks.Topology.Dimension.isClosed_singleton_of_topologicalKrullDim_le_zero hdim _
  have huniv : ({genericPoint X} : Set X) = Set.univ := by
    rw [← hcl.closure_eq]
    exact (genericPoint_spec X).def
  have h : ∀ x : X, x = genericPoint X := fun x ↦
    Set.mem_singleton_iff.mp (huniv ▸ Set.mem_univ x)
  exact ⟨fun x y ↦ (h x).trans (h y).symm⟩

/-- **A nonempty scheme on a single point is affine**: an affine open around that point is the
whole space. -/
public theorem isAffine_of_subsingleton (X : Scheme.{u}) [Nonempty X] [Subsingleton X] :
    IsAffine X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (show x ∈ (⊤ : X.Opens) from trivial)
  have hUtop : U = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y ↦ ?_)
    rw [Subsingleton.elim y x]
    exact hxU
  subst hUtop
  have : IsAffine (⊤ : X.Opens).toScheme := hU
  exact IsAffine.of_isIso X.topIso.inv

end ZeroDimensional

/-- A Noetherian integral separated scheme of topological Krull dimension at most one has an
ample invertible sheaf: [Stacks, Tag 09ND] with `≤ 1` in place of `= 1`. -/
public theorem exists_isAmple_of_topologicalKrullDim_le_one (X : Scheme.{u}) [IsNoetherian X]
    [IsIntegral X] [X.IsSeparated] (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
          L),
      @AlgebraicGeometry.Scheme.Modules.IsAmple X L hL := by
  rcases lt_or_eq_of_le hdim with hlt | heq
  · have : Subsingleton X :=
      subsingleton_of_topologicalKrullDim_le_zero X (le_zero_of_lt_one hlt)
    have : IsAffine X := isAffine_of_subsingleton X
    exact AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_isAffine X
  · exact AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X heq

/-- **Every irreducible component of a Noetherian separated scheme of dimension at most one,
taken with its reduced induced structure, has an ample invertible sheaf.** This is the first
step of the proof of [Stacks, Tag 09NX]: "by Lemma 09ND there exist ample invertible sheaves
`L_i` on `Z_i`". -/
public theorem exists_isAmple_subscheme_vanishingIdeal_irreducibleComponent (X : Scheme.{u})
    [IsNoetherian X] [X.IsSeparated] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents (X : Type u))
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        (vanishingIdeal
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme.toRingedSpace.presheaf
        (structureSheafRing
          (vanishingIdeal
            ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme.toRingedSpace).property
        L),
      @AlgebraicGeometry.Scheme.Modules.IsAmple
        (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme L hL :=
  have : IsNoetherian
      (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme :=
    isNoetherian_subscheme _
  have : IsIntegral
      (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme :=
    isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hZ.1
  have : (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme.IsSeparated :=
    isSeparated_of_isClosedImmersion
      (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι
  exists_isAmple_of_topologicalKrullDim_le_one _
    ((topologicalKrullDim_le_of_isClosedImmersion
      (vanishingIdeal ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι).trans hdim)

end StacksTag09NX

end
