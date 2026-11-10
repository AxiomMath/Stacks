module

public import Mathlib.Order.Zorn
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# A minimal non-schematic closed subspace

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` which is not a
scheme. Then `X` has a closed subspace `Z` which is not a scheme but all of whose proper closed
subspaces are schemes. This is Stacks 0B7Y, and it is the companion of Stacks 0B7Z
(`StacksFrontier/AlgebraicGeometry/Spaces/MinimalNonSchematicSpace.lean`), whose hypotheses it
produces.

Being a scheme is `CategoryTheory.Functor.IsRepresentable` of the presheaf underlying the space.
A *proper* closed subspace is a closed subspace `W` with `W ≠ ⊤` as a subfunctor — strictly
smaller than the whole space in the scheme-theoretic sense, which is what "proper closed subspace
`Z ⊂ X`" means in the source and which has nothing to do with the morphism property of being
proper. The two occurrences of the word in the source statement are nested: the outer subspace is
a closed subspace of `X`, and the inner quantifier runs over the proper closed subspaces *of that
subspace*, which here are the subfunctors of `Z.toFunctor`.

## Main definitions

No new definitions are introduced.

## Main results

No public results are left here. Stacks 0B7Y is
`AlgebraicGeometry.Space.exists_isClosedSubspace_minimal_not_isRepresentable` of
`StacksFrontier/AlgebraicGeometry/Spaces/MinimalNonSchematicClosedSubspaceExistence.lean`.

## Implementation notes

The argument is the source's, by Zorn's lemma applied to the set of closed subspaces of `X`
which are not schemes, ordered by inclusion. It is nonempty because `⊤` is a closed subspace
(`AlgebraicGeometry.Space.isClosedSubspace_top_subfunctor`) isomorphic to `X`, which is not a
scheme by hypothesis — this is the only place the hypothesis that `X` is not a scheme is used,
and it is what keeps the conclusion from being about an empty poset. A chain has the infimum of
its members as a lower bound: that infimum is again a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_sInf`, and it is not a scheme because it is the inverse
limit of the chain, by `AlgebraicGeometry.Space.isLimitClosedSubspaceCone`, so Stacks 07SR would
make one member of the chain a scheme. The empty chain is bounded below by `⊤`. Minimality is
then turned into the inner clause by pushing a proper closed subspace `Z'` of the minimal `Z`
forward to `CategoryTheory.Subfunctor.range (Z'.ι ≫ Z.ι)`, a closed subspace of `X` isomorphic
to `Z'` and contained in `Z`; were it not a scheme, minimality would force it to equal `Z`, and
hence `Z'` to be `⊤`.

Stacks 07SR — that a stage of a limit situation is a scheme as soon as the limit is — is **not
available in this library**, and neither is Stacks 07SQ, which its proof uses. It is therefore
carried as the named hypothesis `h07SR`, in the form the argument above needs: for a limiting
cone over an inverse system of quasi-compact, quasi-separated algebraic spaces whose transition
morphisms are closed immersions, a representable vertex forces a representable stage. Compared
with Stacks 07SR in Situation 084R (`AlgebraicGeometry.Space.LimitSituation`) this asks the
transition morphisms to be closed immersions rather than merely affine, which makes it apply to
fewer systems and so assumes less; it differs in the other direction only in the universe of the
index, which is `Type (u + 1)` rather than `Type u` because `CategoryTheory.Subfunctor X` lives
in `Type (u + 1)` and the chain is indexed by its own members. Re-indexing inside `Type u` would
need `Small.{u} (CategoryTheory.Subfunctor X)`, which this library does not have, although the
library instance `AlgebraicGeometry.BigFppfOver.essentiallySmall` is what a proof of it would
start from.

Quasi-compactness and quasi-separatedness of `X` are load-bearing, and both are used in exactly
one place: they are passed to the stages of the chain, each of which is a closed subspace of `X`,
by `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion` and by
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated` applied to the
quasi-separated morphism `AlgebraicGeometry.Space.isQuasiSeparated_of_isClosedImmersion`. They
are what makes the system a system of the kind Stacks 07SR speaks about. This is in contrast with
Stacks 0B7Z, where the reducedness half of the source proof uses neither.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0B7Y](https://stacks.math.columbia.edu/tag/0B7Y)
* [Stacks Project, Tag 0B7Z](https://stacks.math.columbia.edu/tag/0B7Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry.Space

/-- A subfunctor of the source of a morphism which is injective in every degree is recovered
from its image. -/
theorem preimage_image_of_injective {C : Type w} [Category.{v} C]
    {F F' : Cᵒᵖ ⥤ Type u} (p : F ⟶ F') (hp : ∀ i, Function.Injective (p.app i))
    (G : Subfunctor F) :
    (G.image p).preimage p = G := by
  ext i x
  simp only [Subfunctor.preimage_obj, Subfunctor.image_obj, Set.mem_preimage, Set.mem_image]
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hxy⟩
  exact hp i hxy ▸ hy

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chain step of Stacks 0B7Y.** The infimum of a nonempty chain of closed subspaces of a
quasi-compact quasi-separated algebraic space, none of which is a scheme, is not a scheme.

The infimum is the inverse limit of the chain, so Stacks 07SR — carried here as `h07SR` — would
make one member of the chain a scheme. -/
theorem not_isRepresentable_sInf_of_isChain (hT : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hT X)
    (h07SR : ∀ {ι : Type (u + 1)} [Preorder ι] [IsDirected ι (· ≤ ·)] (_i₀ : ι)
      (D : ιᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (κ : Cone D), IsLimit κ →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hT (D.obj i)) →
      (∀ {i j : ιᵒᵖ} (f : i ⟶ j), IsClosedImmersion B S hS (D.map f)) →
      κ.pt.IsRepresentable → ∃ i, (D.obj i).IsRepresentable)
    {c : Set (Subfunctor X)} (hne : c.Nonempty)
    (htotal : ∀ W ∈ c, ∀ W' ∈ c, W ≤ W' ∨ W' ≤ W)
    (hclosed : ∀ W ∈ c, IsClosedSubspace B S hS W)
    (hnot : ∀ W ∈ c, ¬ W.toFunctor.IsRepresentable) :
    ¬ (sInf c).toFunctor.IsRepresentable := by
  intro hrep
  obtain ⟨W₀, hW₀⟩ := hne
  have : IsDirected ((↥c)ᵒᵈ) (· ≤ ·) := by
    refine ⟨fun i j => ?_⟩
    rcases htotal _ (OrderDual.ofDual i).2 _ (OrderDual.ofDual j).2 with h | h
    · exact ⟨i, le_rfl, h⟩
    · exact ⟨j, h, le_rfl⟩
  set Z : (↥c)ᵒᵈ → Subfunctor X := fun i => (OrderDual.ofDual i).1
  have hmem : ∀ i : (↥c)ᵒᵈ, Z i ∈ c := fun i => (OrderDual.ofDual i).2
  have hanti : ∀ ⦃i j : (↥c)ᵒᵈ⦄, i ≤ j → Z j ≤ Z i := fun _ _ h => h
  have hle : ∀ i, sInf c ≤ Z i := fun i => sInf_le (hmem i)
  have hge : (⨅ i, Z i) ≤ sInf c :=
    le_sInf fun W hW => iInf_le Z (OrderDual.toDual (⟨W, hW⟩ : ↥c))
  obtain ⟨i, hi⟩ := h07SR (OrderDual.toDual (⟨W₀, hW₀⟩ : ↥c))
    (closedSubspaceDiagram B S hS Z hanti)
    (closedSubspaceCone B S hS Z hanti (sInf c) hle)
    (isLimitClosedSubspaceCone B S hS (OrderDual.toDual (⟨W₀, hW₀⟩ : ↥c)) Z hanti (sInf c) hle
      hge)
    (fun i => (hclosed _ (hmem i.unop)).1)
    (fun i => isQuasiCompactSpace_of_isClosedImmersion B S hS hqc (Z i.unop).ι
      (hclosed _ (hmem i.unop)).2)
    (fun i => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hT
      (hclosed _ (hmem i.unop)).1 hqs
      (isQuasiSeparated_of_isClosedImmersion B S hS (hclosed _ (hmem i.unop)).2))
    (fun {i _} f => isClosedImmersion_homOfLe' B S hS (hclosed _ (hmem i.unop)).2
      (hanti (leOfHom f.unop)))
    hrep
  exact hnot _ (hmem i.unop) hi

end AlgebraicGeometry.Space

end
