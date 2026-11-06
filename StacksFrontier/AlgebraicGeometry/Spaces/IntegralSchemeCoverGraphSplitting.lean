module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# The graph of an étale morphism splits off the fibre product

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` with `f` and
`f ≫ g` étale and `g` separated. Then the graph `Γ : X ⟶ X ×_Z Y` of `f` over `g` is

* **a closed immersion**, because `g` is separated — this is Stacks 03KO part (3); and
* **étale**, because `X ×_Z Y ⟶ Y` is a base change of the étale `f ≫ g` and `Γ` composed with
  it is the étale `f`, so Stacks 03FV applies.

Hence the point set of `Γ` is open and closed in the point space of `X ×_Z Y`, and `X ×_Z Y`
splits as the range of `Γ` together with a complementary open-and-closed subspace. Since `Γ` is
in addition a monomorphism — it is a section of the first projection — it is an *open immersion*
by Stacks 025G, so its range is `X` itself and the splitting reads

```
X ×_Z Y = X ⨿ W.
```

This is the decomposition `U ×_X Y = U ⨿ W` which opens the inductive step of Stacks 09YB,
taken with `f = j : U ⟶ Y` the quasi-compact open immersion of the relative compactification,
`g = π : Y ⟶ X` the integral morphism it is followed by, and `f ≫ g = p : U ⟶ X` the étale
chart.

## Main results

* `AlgebraicGeometry.Space.isEtale_graph`: the graph of an étale morphism over a morphism whose
  composite with it is étale is étale.
* `AlgebraicGeometry.Space.isOpenImmersion_graph`: that graph is an open immersion.
* `AlgebraicGeometry.Space.isClopen_range_pointsMap_graph`: its point set is open and closed
  when the morphism it is taken over is separated.
* `AlgebraicGeometry.Space.exists_graphComplement_decomposition`: the splitting of `X ×_Z Y`
  into the range of the graph and a complementary open-and-closed subspace, with the range of
  the graph identified with `X`.
* `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_range_of_isEtale`: the image of
  an étale morphism *from an arbitrary algebraic space* is an open subspace of the target. The
  library has this for the inclusion of an open subspace
  (`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale`); this is
  the form the complementary piece `W` needs, its inclusion into `X ×_Z Y` being étale but not
  the datum of an open subspace of `Y`.
* `AlgebraicGeometry.Space.union_range_pointsMap_graph_range_pointsMap_comp_eq_univ`: the point
  space of `Y` is the union of the image of `f` and the image of the complementary piece. This
  is the source's "`Y ∖ V` is contained in `j(U)`".

## Implementation notes

**The range of the graph, not an abstract piece.** The underlying decomposition lemma
`AlgebraicGeometry.Space.exists_clopen_subspace_decomposition_of_isClopen` returns the two
subfunctors cut out by a clopen set of points and its complement. The piece cut out by the point
set of `Γ` is reconciled with `CategoryTheory.Subfunctor.range Γ` by
`AlgebraicGeometry.Space.range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace`,
the arbitrary-source form of Stacks 03BZ part (1) at an open immersion; the library has the
representable-source form only. That is what turns the lattice-theoretic splitting into the
source's `U ⨿ W` with the first summand *being* `U`.

**Monomorphy of the graph is free.** `AlgebraicGeometry.Space.graph_comp_fst` exhibits `Γ` as a
section of the first projection, so `CategoryTheory.mono_of_mono_fac` applies with the identity.
No separatedness is needed for that, and none is needed for étaleness either; separatedness of
`g` enters only through closedness of the point set.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_IntegralSchemeCoverGraphSplitting :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_IntegralSchemeCoverGraphSplitting
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_IntegralSchemeCoverGraphSplitting B S hS).has_limit _

/-! ### The image of an étale morphism from an arbitrary algebraic space -/

section EtaleImage

variable {A G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of an étale morphism of algebraic spaces is an open subspace.** For an étale
morphism `k : A ⟶ G` of algebraic spaces over `S` the subfunctor of `G` cut out by the image of
the point set of `A` is an open subspace of `G`.

`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale` is the same
statement for the composite of the inclusion of an open subspace with an étale morphism; this is
the form needed when the source is an arbitrary algebraic space, as the complementary piece of
a clopen decomposition is. -/
theorem isOpenSubspace_openSubspaceOfPoints_range_of_isEtale
    (hA : IsAlgebraicSpace B S hS A) (hG : IsAlgebraicSpace B S hS G) {k : A ⟶ G}
    (hk : IsEtale B S hS k) :
    IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS G (Set.range (pointsMap B S hS A k))) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hG _
    (isOpen_range_pointsMap_of_isEtale B S hS k hA hG hk)

/-- **Stacks 03BZ, part (1), at an open immersion with arbitrary source.** The range of an open
immersion of algebraic spaces over `S` is the open subspace cut out by its point set.

`AlgebraicGeometry.Space.range_eq_openSubspaceOfPoints_of_isOpenImmersion` is the same statement
for a representable source. -/
theorem range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace
    (hA : IsAlgebraicSpace B S hS A) {k : A ⟶ G} (hk : IsOpenImmersion B S hS k) :
    Subfunctor.range k =
      openSubspaceOfPoints B S hS G (Set.range (pointsMap B S hS A k)) := by
  have hmono : Mono k := mono_of_isOpenImmersion B S hS k hk
  have hopen : IsOpenSubspace B S hS (Subfunctor.range k) :=
    ⟨isAlgebraicSpace_range_of_mono B S hS k hA, prop_range_ι_of_mono B S hS _ k hk⟩
  refine le_antisymm (range_le_openSubspaceOfPoints_range_pointsMap k) ?_
  refine le_of_range_pointsMap_ι_subset B S hS hopen ?_
  rw [range_pointsMap_ι_openSubspaceOfPoints, range_pointsMap_ι_range]

end EtaleImage

/-! ### The graph -/

section Graph

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The graph of an étale morphism is étale.** For `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` and
`f ≫ g` étale, the graph `X ⟶ X ×_Z Y` of `f` over `g` is étale.

The second projection `X ×_Z Y ⟶ Y` is a base change of `f ≫ g`, hence étale by Stacks 03FU, and
the graph composed with it is `f`; Stacks 03FV then recognizes the graph as étale, both its
source and target being étale over `Y`. -/
theorem isEtale_graph (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f)
    (hfg : IsEtale B S hS (f ≫ g)) :
    IsEtale B S hS (graph B S hS f g) :=
  have hP : IsAlgebraicSpace B S hS (pullback (f ≫ g) g) :=
    isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ
  isEtale_of_isEtale_over B S hS hX hP hY (graph B S hS f g) f
    (pullback.snd (f ≫ g) g) hf
    (isEtale_pullback_snd B S hS hY hZ hX (f ≫ g) g hfg)
    (graph_comp_snd B S hS f g)

/-- **The graph of an étale morphism is an open immersion.** It is étale, and it is a
monomorphism because it is a section; Stacks 025G, in the form
`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_mono`, concludes. -/
theorem isOpenImmersion_graph (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f)
    (hfg : IsEtale B S hS (f ≫ g)) :
    IsOpenImmersion B S hS (graph B S hS f g) :=
  isOpenImmersion_of_isEtale_of_mono B S hS (graph B S hS f g) hX
    (isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ)
    (isEtale_graph B S hS hX hY hZ f g hf hfg) (mono_graph B S hS f g)

/-- **The point set of the graph of an étale morphism over a separated morphism is open and
closed.** Openness is Stacks 03IR applied to the étale graph, closedness is Stacks 04CD applied
to the closed immersion of Stacks 03KO part (3). -/
theorem isClopen_range_pointsMap_graph (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f) (hfg : IsEtale B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsClopen (Set.range (pointsMap B S hS X (graph B S hS f g))) :=
  ⟨isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ) (graph B S hS f g)
      (isClosedImmersion_graph_of_isSeparated B S hS f g hg),
    isOpen_range_pointsMap_of_isEtale B S hS (graph B S hS f g) hX
      (isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ)
      (isEtale_graph B S hS hX hY hZ f g hf hfg)⟩

/-- The range of the graph of an étale morphism is the open subspace cut out by its point set. -/
private theorem range_graph_eq_openSubspaceOfPoints (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f) (hfg : IsEtale B S hS (f ≫ g)) :
    Subfunctor.range (graph B S hS f g) =
      openSubspaceOfPoints B S hS (pullback (f ≫ g) g)
        (Set.range (pointsMap B S hS X (graph B S hS f g))) :=
  range_eq_openSubspaceOfPoints_of_isOpenImmersion_of_isAlgebraicSpace B S hS hX
    (isOpenImmersion_graph B S hS hX hY hZ f g hf hfg)

/-- **The range of the graph of an étale morphism is an open-and-closed subspace.** -/
theorem isOpenSubspace_isClosedSubspace_range_graph (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f) (hfg : IsEtale B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsOpenSubspace B S hS (Subfunctor.range (graph B S hS f g)) ∧
      IsClosedSubspace B S hS (Subfunctor.range (graph B S hS f g)) := by
  have hclopen := isClopen_range_pointsMap_graph B S hS hX hY hZ f g hf hfg hg
  have hP : IsAlgebraicSpace B S hS (pullback (f ≫ g) g) :=
    isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ
  have hrange := range_graph_eq_openSubspaceOfPoints B S hS hX hY hZ f g hf hfg
  rw [hrange]
  exact ⟨isOpenSubspace_openSubspaceOfPoints B S hS hP _ hclopen.2,
    isClosedSubspace_openSubspaceOfPoints B S hS hP _ hclopen.2 hclopen.1⟩

/-- **The decomposition `X ×_Z Y = X ⨿ W` of the inductive step of Stacks 09YB.** For `f` and
`f ≫ g` étale and `g` separated, the fibre product `X ×_Z Y` carries a subfunctor `C` which,
together with the range of the graph of `f` over `g`, is a pair of complementary
open-and-closed subspaces: both are open subspaces and closed subspaces, their join sheafifies
to the whole fibre product, their meet is the sheafification of the bottom subfunctor, and
their point sets are complementary. The range of the graph is `X` itself, the graph being an
open immersion.

This is the shape the source's `U ×_X Y = U ⨿ W` is used in; the lattice form rather than an
isomorphism onto a coproduct, exactly as
`AlgebraicGeometry.Space.exists_diagonalComplement_decomposition` states the corresponding
decomposition for the diagonal of a separated étale morphism. -/
theorem exists_graphComplement_decomposition (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f) (hfg : IsEtale B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    ∃ C : Subfunctor (pullback (f ≫ g) g),
      IsOpenSubspace B S hS C ∧ IsClosedSubspace B S hS C ∧
      IsOpenSubspace B S hS (Subfunctor.range (graph B S hS f g)) ∧
      IsClosedSubspace B S hS (Subfunctor.range (graph B S hS f g)) ∧
      (C ⊔ Subfunctor.range (graph B S hS f g)).sheafify
        (BigFppfOver.topology B S hS) = ⊤ ∧
      C ⊓ Subfunctor.range (graph B S hS f g) =
        (⊥ : Subfunctor (pullback (f ≫ g) g)).sheafify (BigFppfOver.topology B S hS) ∧
      Set.range (pointsMap B S hS C.toFunctor C.ι) =
        (Set.range (pointsMap B S hS X (graph B S hS f g)))ᶜ := by
  have hclopen := isClopen_range_pointsMap_graph B S hS hX hY hZ f g hf hfg hg
  have hP : IsAlgebraicSpace B S hS (pullback (f ≫ g) g) :=
    isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ
  have hrange := range_graph_eq_openSubspaceOfPoints B S hS hX hY hZ f g hf hfg
  refine ⟨openSubspaceOfPoints B S hS (pullback (f ≫ g) g)
      (Set.range (pointsMap B S hS X (graph B S hS f g)))ᶜ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpenSubspace_openSubspaceOfPoints B S hS hP _ hclopen.1.isOpen_compl
  · exact isClosedSubspace_openSubspaceOfPoints B S hS hP _ hclopen.1.isOpen_compl
      hclopen.2.isClosed_compl
  · exact (isOpenSubspace_isClosedSubspace_range_graph B S hS hX hY hZ f g hf hfg hg).1
  · exact (isOpenSubspace_isClosedSubspace_range_graph B S hS hX hY hZ f g hf hfg hg).2
  · rw [hrange]
    exact sheafify_sup_openSubspaceOfPoints_eq_top B S hS _ hclopen.2 hclopen.1
  · rw [hrange]
    exact inf_openSubspaceOfPoints_eq_sheafify_bot B S hS _
  · exact range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- **`Y ∖ V` is contained in the image of `f`.** If the second projection `X ×_Z Y ⟶ Y` is
surjective and `C` is a subfunctor of `X ×_Z Y` whose point set is the complement of the point
set of the graph of `f` over `g`, then the point space of `Y` is the union of the image of `f`
and the image of `C`.

This is the source's observation that the open subspace `V ⊆ Y` cut out by the image of the
complementary piece `W` contains `Y ∖ j(U)`: the two images cover `|Y|`, because the point set
of `X ×_Z Y` is covered by the graph and its complement and the projection is surjective. -/
theorem union_range_pointsMap_graph_range_pointsMap_comp_eq_univ (f : X ⟶ Y) (g : Y ⟶ Z)
    (hsurj : IsSurjective B S hS (pullback.snd (f ≫ g) g))
    (C : Subfunctor (pullback (f ≫ g) g))
    (hC : Set.range (pointsMap B S hS C.toFunctor C.ι) =
      (Set.range (pointsMap B S hS X (graph B S hS f g)))ᶜ) :
    Set.range (pointsMap B S hS X f) ∪
        Set.range (pointsMap B S hS C.toFunctor (C.ι ≫ pullback.snd (f ≫ g) g)) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨w, hw⟩ := hsurj y
  by_cases hmem : w ∈ Set.range (pointsMap B S hS X (graph B S hS f g))
  · obtain ⟨x, rfl⟩ := hmem
    refine Or.inl ⟨x, ?_⟩
    rw [← hw, ← pointsMap_comp_apply, graph_comp_snd]
  · refine Or.inr ?_
    obtain ⟨c, hc⟩ : w ∈ Set.range (pointsMap B S hS C.toFunctor C.ι) := hC ▸ hmem
    exact ⟨c, by rw [pointsMap_comp_apply, hc, hw]⟩

end Graph

end AlgebraicGeometry.Space

end
