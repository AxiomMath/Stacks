module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.CounitHomExt
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence

/-!
# Compatibility of the cup product of an adjunction with a base change square

Consider a square of categories, functors and adjunctions

```
        Lf                            Rf
  P  -------→  Q               P  ←-------  Q
  |            |               |            |
  | Lg         | Lg'           | Lg         | Lg'
  v            v               v            v
  P' -------→  Q'              P' ←-------  Q'
        Lf'                           Rf'
```

with `adj : Lf ⊣ Rf` and `adj' : Lf' ⊣ Rf'`, and bifunctors `AP`, `AQ`, `AP'`, `AQ'` on the four
categories, compared along the four functors by
`αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ` and its three companions.  The cup product of
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct` is then available for
`adj` and for `adj'`, and the base change morphism of functors `β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` of
`StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare` for the square.

This file proves that the two are compatible: the square

```
                        Lg (cup)                                     β
  Lg (AP (Rf K, Rf L)) ---------→ Lg (Rf (AQ (K, L))) ---------→ Rf' (Lg' (AQ (K, L)))
          |                                                                |
          | αg                                                             | Rf' αg'
          v                                                                v
  AP' (Lg Rf K, Lg Rf L)                                         Rf' (AQ' (Lg' K, Lg' L))
          |                                                                ^
          | AP' (β, β)                                                     | cup'
          v                                                                |
  AP' (Rf' Lg' K, Rf' Lg' L) --------------------------------------------- ⌐
```

commutes, and this is the abstract content of [Stacks, Tag 0H9A] for a commutative square of
ringed topoi.

## Main results

All in the namespace `Stacks.Cohomology.RelativeCupProductOnRingedTopoi`.

* `adjunctionCupProduct_baseChange` — **the square above commutes**, given two hypotheses: that
  `β` transposes to the comparison `θ : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` of the two composites around the
  square followed by `Lg'` of the counit of `adj`, and that `θ` carries the comparison of the
  bifunctors along `Lg ⋙ Lf'` to the one along `Lf ⋙ Lg'`.
* `adjunctionCupProduct_baseChangeMap` — the same for the canonical base change map
  `Stacks.CategoryTheory.BaseChange.map` of a square in which both composites around the square
  are identified with one functor `Lc`.  Only the second hypothesis is left, and it is stated
  with the composite comparison `compComparison` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductCoherence.lean`:
  it says exactly that the two composite comparisons agree under the identification
  `eg.hom ≫ ef.inv`.

## Implementation notes

*No associator enters.*  The source diagram of [Stacks, Tag 0H9A] has only binary tensor
products: both of its vertical identifications are the comparison of [Stacks, Tag 07A4] at a
single pair of objects, and nothing is reassociated.  So — unlike the associativity of the cup
product, [Stacks, Tag 0FPL] — the statement needs no hexagon for the comparison and no monoidal
structure beyond the four bare comparisons `αf`, `αf'`, `αg`, `αg'`.  That is why this file
exists in the form it does: the whole of the diagram, transposed across `Lf' ⊣ Rf'`, is the
hypothesis `hθ`, and nothing else.

*Why the hypothesis is not discharged here.*  `hθ` is the statement that the comparison along a
composite is the composite of the comparisons, for the two ways around the square.  For the
canonical comparison `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso` of
[Stacks, Tag 07A4] on ringed topoi that is not available in this tree: that isomorphism carries
only naturality (`derivedPullbackTensorModelIso_naturality` and the naturality implicit in its
type), and no compatibility with the composition isomorphism
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso` of
[Stacks, Tag 0D6D], at the derived level or at the underived one — the comparison of total
tensor complexes `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` likewise has only
`pullbackToposTensorTotalIso_hom_naturality`.  It is the *same* missing input that
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_comp` leaves open for
[Stacks, Tag 0FPN], recorded there; discharging it once settles both.  The ringed-space
development, in the namespace `Stacks.Cohomology.DerivedPullbackTensor`, carries a comparison of
its own with its own composition isomorphism, and is of no help here: neither its comparison nor
its composition isomorphism is the one above.

*Why these carry no project tag.*  [Stacks, Tag 0H9A] asserts the diagram for the canonical cup
product of [Stacks, Tag 0B6C], the canonical base change map of [Stacks, Tag 07A7] and the
canonical comparison of [Stacks, Tag 07A4].  The results below take the coherence of that
comparison as a hypothesis, and that coherence is an essential input of the tag rather than part
of its statement, so these are the reduction and not the tag.  No attribute is attached.

*The transpose is again what makes the proof short.*
`Stacks.Adjunction.hom_ext_of_map_comp_counit` reduces the diagram to an equality of maps out of
`Lf' (Lg (AP (Rf K, Rf L)))`, and `adjunctionCupProduct_transpose` computes the transpose of each
of the two cup products.  After that every step is naturality — of `θ`, of `αf'`, of `αg'`, and of
the counit of `adj'`.

*Both composite comparisons are `compComparison`.*  The composite of two comparisons along two
composable functors is already available as
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.compComparison`, and its component is
`compComparison_app`; both are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductCoherence.lean`, and
nothing is redefined here.  That definition takes its bifunctors in the order target, middle,
source, so the two composites around the square are spelled `compComparison AQ' AP' AP αf' αg`
(down then across) and `compComparison AQ' AQ AP αg' αf` (across then down).

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0FPN](https://stacks.math.columbia.edu/tag/0FPN)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

/-! ### The base change square -/

section BaseChange

variable {P : Type*} {Q : Type*} {P' : Type*} {Q' : Type*}
  [Category P] [Category Q] [Category P'] [Category Q']
  {Lf : P ⥤ Q} {Rf : Q ⥤ P} {Lf' : P' ⥤ Q'} {Rf' : Q' ⥤ P'}
  {Lg : P ⥤ P'} {Lg' : Q ⥤ Q'}
  (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf')
  (AP : P × P ⥤ P) (AQ : Q × Q ⥤ Q) (AP' : P' × P' ⥤ P') (AQ' : Q' × Q' ⥤ Q')
  (αf : AP ⋙ Lf ⟶ Lf.prod Lf ⋙ AQ) (αf' : AP' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ AQ')
  (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ')

/-- **The cup product of an adjunction is compatible with a base change square.**

Let `θ : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` compare the two composites around the square, let
`β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` be a base change morphism whose transpose under `adj'` is `θ`
followed by `Lg'` of the counit of `adj` (`hβ`), and suppose `θ` carries the comparison of the
bifunctors along `Lg ⋙ Lf'` to the one along `Lf ⋙ Lg'` (`hθ`).  Then going round the square
one way — the cup product of `adj`, then base change, then `Rf'` of `αg'` — agrees with going
round it the other way — `αg`, then base change in each tensor factor, then the cup product of
`adj'`.

This is the abstract content of [Stacks, Tag 0H9A].  No associator and no symmetry enters: the
diagram has binary tensor products only, and `hθ` is exactly what the diagram becomes after
transposing across `adj'`. -/
theorem adjunctionCupProduct_baseChange
    (θ : Lg ⋙ Lf' ⟶ Lf ⋙ Lg') (β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')
    (hβ : ∀ M : Q, Lf'.map (β.app M) ≫ adj'.counit.app (Lg'.obj M) =
      θ.app (Rf.obj M) ≫ Lg'.map (adj.counit.app M))
    (hθ : ∀ M N : P,
      Lf'.map (αg.app (M, N)) ≫ αf'.app (Lg.obj M, Lg.obj N) ≫
          AQ'.map (θ.app M ×ₘ θ.app N) =
        θ.app (AP.obj (M, N)) ≫ Lg'.map (αf.app (M, N)) ≫ αg'.app (Lf.obj M, Lf.obj N))
    (K L : Q) :
    Lg.map (adjunctionCupProduct adj AP AQ αf K L) ≫ β.app (AQ.obj (K, L)) ≫
        Rf'.map (αg'.app (K, L)) =
      αg.app (Rf.obj K, Rf.obj L) ≫ AP'.map (β.app K ×ₘ β.app L) ≫
        adjunctionCupProduct adj' AP' AQ' αf' (Lg'.obj K) (Lg'.obj L) := by
  apply Stacks.Adjunction.hom_ext_of_map_comp_counit adj'
  have hcup := adjunctionCupProduct_transpose adj AP AQ αf K L
  have hcup' := adjunctionCupProduct_transpose adj' AP' AQ' αf' (Lg'.obj K) (Lg'.obj L)
  have hc' := adj'.counit.naturality (αg'.app (K, L))
  have hnθ := θ.naturality (adjunctionCupProduct adj AP AQ αf K L)
  have hng' := αg'.naturality ((adj.counit.app K ×ₘ adj.counit.app L) :
    ((Lf.obj (Rf.obj K), Lf.obj (Rf.obj L)) : Q × Q) ⟶ (K, L))
  have hnf' := αf'.naturality ((β.app K ×ₘ β.app L) :
    ((Lg.obj (Rf.obj K), Lg.obj (Rf.obj L)) : P' × P') ⟶
      (Rf'.obj (Lg'.obj K), Rf'.obj (Lg'.obj L)))
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.prod_obj,
    Functor.prod_map] at hcup hcup' hc' hnθ hng' hnf'
  have hinner : ((Lf'.map (β.app K) ×ₘ Lf'.map (β.app L)) ≫
        (adj'.counit.app (Lg'.obj K) ×ₘ adj'.counit.app (Lg'.obj L)) :
      ((Lf'.obj (Lg.obj (Rf.obj K)), Lf'.obj (Lg.obj (Rf.obj L))) : Q' × Q') ⟶
        (Lg'.obj K, Lg'.obj L)) =
      (θ.app (Rf.obj K) ×ₘ θ.app (Rf.obj L)) ≫
        (Lg'.map (adj.counit.app K) ×ₘ Lg'.map (adj.counit.app L)) :=
    Prod.ext (hβ K) (hβ L)
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  calc _ = Lf'.map (αg.app (Rf.obj K, Rf.obj L)) ≫
        αf'.app (Lg.obj (Rf.obj K), Lg.obj (Rf.obj L)) ≫
        AQ'.map (θ.app (Rf.obj K) ×ₘ θ.app (Rf.obj L)) ≫
        AQ'.map (Lg'.map (adj.counit.app K) ×ₘ Lg'.map (adj.counit.app L)) := by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hc',
          reassoc_of% (hβ (AQ.obj (K, L))), reassoc_of% hnθ, ← Functor.map_comp_assoc, hcup,
          Functor.map_comp_assoc, hng', ← reassoc_of% (hθ (Rf.obj K) (Rf.obj L))]
    _ = _ := by
        symm
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcup',
          reassoc_of% hnf', ← Functor.map_comp, hinner, Functor.map_comp]

variable {Lc : P ⥤ Q'} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The cup product of an adjunction is compatible with the canonical base change map.**

Here the two composites around the square are both identified with a functor `Lc`, by `eg` and
`ef`, and the base change map is the canonical one of
`Stacks.CategoryTheory.BaseChange.map` — the mate of `eg.hom ≫ ef.inv`.  Its transpose is then
forced, so only the coherence of the comparisons survives as a hypothesis, and it says exactly
that the two composite comparisons `compComparison` agree under `eg.hom ≫ ef.inv`.

This is the form [Stacks, Tag 0H9A] takes for a commutative square of ringed topoi, where `Lc`
is the derived pullback along the common composite and `eg`, `ef` are the two composition
isomorphisms of [Stacks, Tag 0D6D]; the surviving hypothesis is then the compatibility of the
comparison of [Stacks, Tag 07A4] with that composition isomorphism, which is the same input
[Stacks, Tag 0FPN] still needs. -/
theorem adjunctionCupProduct_baseChangeMap
    (hθ : ∀ M N : P,
      (compComparison AQ' AP' AP αf' αg).app (M, N) ≫
          AQ'.map ((eg.hom ≫ ef.inv).app M ×ₘ (eg.hom ≫ ef.inv).app N) =
        (eg.hom ≫ ef.inv).app (AP.obj (M, N)) ≫
          (compComparison AQ' AQ AP αg' αf).app (M, N))
    (K L : Q) :
    Lg.map (adjunctionCupProduct adj AP AQ αf K L) ≫
        Stacks.CategoryTheory.BaseChange.map adj adj' eg ef (AQ.obj (K, L)) ≫
        Rf'.map (αg'.app (K, L)) =
      αg.app (Rf.obj K, Rf.obj L) ≫
        AP'.map (Stacks.CategoryTheory.BaseChange.map adj adj' eg ef K ×ₘ
          Stacks.CategoryTheory.BaseChange.map adj adj' eg ef L) ≫
        adjunctionCupProduct adj' AP' AQ' αf' (Lg'.obj K) (Lg'.obj L) := by
  refine adjunctionCupProduct_baseChange adj adj' AP AQ AP' AQ' αf αf' αg αg'
    (eg.hom ≫ ef.inv) (Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef) ?_ ?_ K L
  · intro M
    have h := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map adj adj' eg ef M
    rw [Adjunction.homEquiv_counit] at h
    rw [NatTrans.comp_app, Category.assoc]
    exact h
  · intro M N
    simpa only [compComparison_app, Category.assoc] using hθ M N

end BaseChange

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
