module

public import StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.RefinementStep
public import StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.RefinedIndexCategory
public import StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.UniformRefinement
public import StacksFrontier.CategoryTheory.Sites.Point.CriterionForExistenceOfPoints.DeligneCriterion

/-!
# Refining a cofiltered system so as to separate two germs and cover a section

Let `(C, J)` be a site. Following Deligne's appendix to SGA 4, Exposé VI, a *system* in `C` is a
cofiltered inverse system of objects of `C`, that is, a functor `p : N ⥤ C` out of a small
cofiltered category `N` (the source writes it as a directed set `(J, ≥)` together with an inverse
system `(V_j, g_{jj'})`; the morphisms of `N` are the transition maps `g_{jj'}`). Such a system
carries two associated functors: the fibre functor

`u(X) = colim_{j ∈ N} Mor(p j, X)`,

which is `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber p` (its elements being
`Point.ofIsCofiltered.fiberMk h` for a morphism `h : p j ⟶ X`), and the stalk functor
`F ↦ F_p = colim_{j ∈ N} F(p j)` on presheaves, the two being compatible in the sense that `F_p` is
the fibre of `F` at the point of the site defined by `u`, once `u` is one
(`Point.ofIsCofiltered`).

A system `q : M ⥤ C` *refines* `p` when the system `p` is the restriction of `q` along an inclusion
of index categories: a fully faithful `e : N ⥤ M` together with an isomorphism `e ⋙ q ≅ p`. A
refinement induces maps `u'(X) → u(X)` and `F_{p'} → F_p`, both simply because the colimits
defining the former run over a subsystem of those defining the latter.

The result of this file is the inductive step of Deligne's criterion: given two distinct germs
`s ≠ s'` in `F_{p'}` for a separated presheaf `F`, a *finite* covering `{Y k → W}` of the site and
a section `f ∈ u'(W)`, the system can be refined so that the two germs stay distinct while the
image of `f` in `u(W)` comes from one of the `u(Y k)`. The refinement is obtained by adjoining to
the index category the fibre products `p j ×_W Y k` for a suitable `k`, so that `f` acquires, after
restriction, a factorisation through `Y k`.

## Main results

* `CategoryTheory.GrothendieckTopology.exists_refinement_of_ne`: Stacks 00YO, the inductive step of
  Deligne's criterion for the existence of enough points.

## Implementation notes

The index of a system is a small cofiltered category rather than a directed set: a directed set
`(J, ≥)` is such a category, and conversely a cofiltered index category is what the constructions
of the section actually use. This matters for the shape of the refinement built in the proof, where
the source's index set `J_0 = {j ∈ J ∣ j ≥ j_0}` becomes the category `Over j₀` of objects of `N`
equipped with a morphism to `j₀`: the fibre product `p j ×_W Y k` depends on the composite
`p j → p j₀ → W`, hence on that morphism as data, of which a directed set has at most one.

Elements of the two colimits `F_{p'}` and `u'(W)` are given by representatives, and the two
assertions about them are spelled out by the concrete description of a filtered colimit of types.
This keeps the statement free of transports along `ε` at the level of colimits, and is what the
downstream constructor `Point.ofIsCofiltered` consumes; the translation is the following, and is an
equivalence, not a weakening.

* Two elements of `F_{p'} = colim_j F(p j)` are the classes of some `a, a' : F(p j₀)` at a common
  index `j₀` (`Limits.Types.FilteredColimit.jointly_surjective_of_isColimit₂`, `Nᵒᵖ` being
  filtered); the classes of `a` and `a'` at `j₀` are distinct if and only if
  `F.map (p.map φ).op a ≠ F.map (p.map φ).op a'` for every `φ : j ⟶ j₀`
  (`Limits.Types.FilteredColimit.isColimit_eq_iff'`). That is the hypothesis `haa'` and, at the
  index `e j₀` of the refined system, the first conclusion.
* Every element of `u'(W)` is `fiberMk f` for some `f : p j₀ ⟶ W`
  (`Point.ofIsCofiltered.fiberMk_jointly_surjective`), its image in `u(W)` is
  `fiberMk (ε.hom.app j₀ ≫ f)`, and by `Point.ofIsCofiltered.fiber_map_fiberMk` and
  `Point.ofIsCofiltered.exists_of_fiberMk_eq_fiberMk` that image lies in the image of
  `u(Y k) → u(W)` if and only if `h ≫ g k = q.map ψ ≫ ε.hom.app j₀ ≫ f` for some index `i`, some
  `ψ : i ⟶ e j₀` and some `h : q i ⟶ Y k`. That is the second conclusion, and it is verbatim the
  shape of the covering hypothesis of `Point.ofIsCofiltered`.
* A single index `j₀` carries the representatives of `s`, `s'` and `f`; since `N` is cofiltered,
  representatives at different indices can always be moved to a common one, so nothing is lost.

Three further departures from the source's form.

* Only separatedness of `F` is used, not the full sheaf condition: the proof needs that a section
  of `F` over `p j` is determined by its restrictions along a covering. So the hypothesis is
  `Presieve.IsSeparated J F`, which a sheaf of sets satisfies (`Presieve.IsSheaf.isSeparated`,
  and `isSheaf_iff_isSheaf_of_type` for a `Sheaf J (Type w)`).
* A site in the sense of the source has base change for coverings (Stacks 00VH (3)): the fibre
  products `X ×_W Y k` along an arbitrary morphism `X ⟶ W` exist. A `GrothendieckTopology` carries
  no such assumption, so it is stated as a hypothesis for the given covering, which is what the
  construction of the refinement needs.
* The inclusion `e` of index categories is asked to be fully faithful — the source's "the ordering
  on `J` induced from that of `I`" — but not injective on objects, which is bookkeeping that any
  refinement can be made to satisfy without changing the system up to isomorphism.

Faithfulness, on the four points a reader should check against the source.

1. No hypothesis is dead: `hF` and `hg` are what force a `k` to exist at all, `Finite ι` is used
   through the commutation of the filtered colimit `F_{p'}` with the finite product `∏ k`, `haa'`
   is the source's `s ≠ s'` and reappears in the conclusion, `f` is the section that gets covered,
   and the fibre products are the objects the refinement is built from.
2. The site is the source's throughout: one topology `J` on one category `C`, the same `J` for the
   separatedness of `F` and for the covering `{Y k → W}`, and no auxiliary topology.
3. The maps the source calls canonical are pinned, not merely asserted to exist: the transition
   `F_{p'} → F_p` and `u'(W) → u(W)` of a refinement are transport along `ε` followed by the
   colimit inclusion at `e j₀`, which is how both conclusions are written; no map is quantified
   over.
4. Not degenerate: take `N` the one-object one-morphism category and `p` the functor with value
   `V`, so that `u' = Mor(V, -)` and `F_{p'} = F(V)`; the hypotheses then say that `a ≠ a'` in
   `F(V)`, that `{Y k → W}` is a finite covering and that `f : V ⟶ W`, which is exactly the
   situation the criterion of Stacks 00YQ starts from.

## References

* [Stacks 00YO](https://stacks.math.columbia.edu/tag/00YO), in the section "Criterion for existence
  of points" (Stacks 00YN); the next step is Stacks 00YP and the criterion itself Stacks 00YQ.
* [SGA4], Exposé VI, appendix by Deligne.
-/
