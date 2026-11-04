module

public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant
public import StacksFrontier.RingTheory.Flat.TowerLTensor

@[expose] public section

/-!
# Flatness of a base change of local rings that does not change the maximal ideal

Let

```
S  →  S'
↑     ↑
R  →  R'
```

be a commutative diagram of rings with `R`, `R'` and `S'` local, let `M` be a finite `S`-module and
let `M'` be the base change `M ⊗_S S'`. This file proves Stacks tag 0GEB: if `R → R'` and `S → S'`
are flat, `M` is flat over `R`, `𝔪_R R' = 𝔪_{R'}` and `R'` and `S'` are Noetherian, then `M'` is
flat over `R'`.

The proof is the source's. Two general facts carry it, neither of which Mathlib states; both are
proved in the project modules named below.

* `Module.Flat.tensorProduct_of_flat_left`, from `StacksFrontier.RingTheory.Flat.TowerLTensor`, is
  Lemma 0584 (1), stated for a tower `A → C` with `D` and `P` modules over `C`: flatness over the
  base `A` survives base change along a flat map `C → D`, because the associativity isomorphism
  `(D ⊗_C P) ⊗_A X ≅ D ⊗_C (P ⊗_A X)` is natural in `X` and both `P ⊗_A -` and `D ⊗_C -` preserve
  injections. At `A = R`, `C = S`, `D = S'`, `P = M` it makes `M'` a finite `S'`-module which is
  flat over `R`, so that `𝔪_R ⊗_R M' → M'` is injective.
* `Ideal.rTensor_subtype_map_injective`, from
  `StacksFrontier.RingTheory.Flat.LocalCriterionVariant`, converts that into the injectivity
  of `𝔪_{R'} ⊗_{R'} M' → M'`, which is the hypothesis the local criterion of flatness consumes. The
  source rewrites `𝔪_R ⊗_R M' = (𝔪_R ⊗_R R') ⊗_{R'} M' = 𝔪_{R'} ⊗_{R'} M'` using the flatness of
  `R → R'` and hypothesis (3). What the argument needs of that chain is only that the canonical
  `R`-linear map `I ⊗_R X → IR' ⊗_{R'} X` is *surjective*, which holds for any ring map, any ideal
  `I ⊆ R` and any `R'`-module `X`: the extension `IR'` is generated over `R'` by the image of `I`.
  Injectivity of `IR' ⊗_{R'} X → X` therefore follows from injectivity of the composite
  `I ⊗_R X → X`, that is, from flatness of `X` over `R` alone.

## Main results

* `Stacks.Flatness.LocalBaseChange.solution`: the statement of tag 0GEB.

## Implementation notes

Flatness of `R → R'`, hypothesis (1) of the source, is never used. It enters the source's proof
only to identify `𝔪_R ⊗_R R'` with the extension `𝔪_R R'`, and the argument above needs of that
identification just the surjectivity of `I ⊗_R X → IR' ⊗_{R'} X`, which is unconditional. The
hypothesis is kept because it is part of the statement of the tag.

The local criterion is used in the variant form 00ML, at the ideal `I = 𝔪_{R'}`: it asks for the
injectivity of `I ⊗_{R'} M' → R' ⊗_{R'} M'` and for flatness of `M'/IM'` over `R'/I`, the second of
which is free over the residue field. That is exactly the composite of Remark 00M6 with 00MK which
the source's proof performs — 00ML at `I = 𝔪` *is* 00MK read through 00M6 — and it is the form in
which the siblings 00MO and 00MP use the criterion. The `Tor` spelling of 00MK is not available
here: it forms `Tor₁^{R'}(κ_{R'}, M')` in `ModuleCat.{u} R'`, which forces `M'` into the universe
of `R'`, while the statement of 0GEB keeps the six types in independent universes.

`M'` is reduced to the concrete base change `S' ⊗_S M` at the outset, along the `R'`-linear
equivalence `IsBaseChange.equiv`. On the concrete module the `R`- and `R'`-module structures and
their scalar towers are found by instance search from the two towers of the square, so no
restriction of scalars has to be built by hand.

`TensorProduct.AlgebraTensorModule.assoc_comp_lTensor`,
`TensorProduct.AlgebraTensorModule.lTensor_baseChange_injective_iff` and
`Module.Flat.tensorProduct_of_flat_left`, all in `StacksFrontier.RingTheory.Flat.TowerLTensor`, are
Mathlib's proof of `Module.Flat.trans` with the naturality of
`TensorProduct.AlgebraTensorModule.cancelBaseChange` replaced by that of
`TensorProduct.AlgebraTensorModule.assoc`. Mathlib records neither the naturality nor the flatness
statement, which is why they are stated there.

## References

* [StacksProject 0GEB](https://stacks.math.columbia.edu/tag/0GEB)
* [StacksProject 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [StacksProject 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [StacksProject 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flatness.LocalBaseChange

/-- **Stacks 0GEB.** -/
public theorem solution
    {R S R' S' M M' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R'] [IsNoetherianRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R' S')]
    [Module.Flat R R'] [Module.Flat S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M]
    [AddCommGroup M'] [Module S M'] [Module R' M'] [Module S' M']
    [IsScalarTower S S' M'] [IsScalarTower R' S' M']
    (hm : (IsLocalRing.maximalIdeal R).map (algebraMap R R') = IsLocalRing.maximalIdeal R')
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f) :
    Module.Flat R' M' := by
  -- `M'` is the concrete base change `S' ⊗_S M`, on which all four rings act by instance search.
  have hconcrete : Module.Flat R' (S' ⊗[S] M) := by
    -- Lemma 0584 (1): `S' ⊗_S M` is flat over `R`, hence `𝔪_R ⊗_R M' → M'` is injective, and
    -- hypothesis (3) turns that into injectivity of `𝔪_{R'} ⊗_{R'} M' → M'`.
    have : Module.Flat R (S' ⊗[S] M) :=
      Module.Flat.tensorProduct_of_flat_left (A := R) (C := S) (D := S') (P := M)
    have hinj : Function.Injective
        ((IsLocalRing.maximalIdeal R').subtype.rTensor (S' ⊗[S] M)) := by
      rw [← hm]
      exact Ideal.rTensor_subtype_map_injective R' _ _
        (Module.Flat.rTensor_preserves_injective_linearMap _
          (IsLocalRing.maximalIdeal R).injective_subtype)
    have hmax : (IsLocalRing.maximalIdeal R').IsMaximal := IsLocalRing.maximalIdeal.isMaximal R'
    refine Module.Flat.of_rTensor_subtype_injective_of_flat_quotient S' (S' ⊗[S] M)
      (IsLocalRing.maximalIdeal R') hmax.ne_top hinj ?_
    -- Over the residue field of `R'` every module is flat.
    let _ : Field (R' ⧸ IsLocalRing.maximalIdeal R') := Ideal.Quotient.field _
    infer_instance
  exact Module.Flat.of_linearEquiv (hf.equiv.restrictScalars R').symm

end Stacks.Flatness.LocalBaseChange

end

/-!
# Flatness of a base change of local rings that does not change the maximal ideal

Let

```
S  →  S'
↑     ↑
R  →  R'
```

be a commutative diagram of local rings and local homomorphisms, let `M` be a finite `S`-module
and set `M' = M ⊗_S S'`. Assume the two horizontal arrows `R → R'` and `S → S'` are flat, that `M`
is flat over `R`, that `𝔪_R R' = 𝔪_{R'}`, and that `R'` and `S'` are Noetherian. Then `M'` is flat
over `R'`.

This is one more application of the local criterion of flatness 00MK, and the hypothesis
`𝔪_R R' = 𝔪_{R'}` is what feeds it: since `R → R'` is flat, `𝔪_R ⊗_R R' = 𝔪_R R' = 𝔪_{R'}`. The
module `M'` is a finite `S'`-module which is flat over `R` by Lemma 0584, applied to the flat map
`S → S'` of `R`-algebras, so `𝔪_R ⊗_R M' → M'` is injective. Rewriting
`𝔪_R ⊗_R M' = (𝔪_R ⊗_R R') ⊗_{R'} M' = 𝔪_{R'} ⊗_{R'} M'` turns this into injectivity of
`𝔪_{R'} ⊗_{R'} M' → M'`, that is, into `Tor_1^{R'}(κ_{R'}, M') = 0` by Remark 00M6. The local
criterion 00MK over the Noetherian local ring `R'`, with the Noetherian local `R'`-algebra `S'`
and the finite `S'`-module `M'`, then gives flatness of `M'` over `R'`.

Unlike its neighbours 00MO and 00MQ, this lemma assumes nothing relating `S'` to `S ⊗_R R'`: the
square is an arbitrary commutative one, and `M'` is the base change of `M` along `S → S'` alone.

## Main results

* `Module.Flat.baseChange_of_map_maximalIdeal_eq_maximalIdeal`: Stacks 0GEB.

## Implementation notes

*Four of the source's hypotheses are dropped, none of them used*: `S` local, locality of `R → S`,
locality of `S → S'`, and locality of `R → R'`. What the argument needs of the square is that `R'`
and `S'` are Noetherian local with `R' → S'` local, which is what the local criterion 00MK
consumes, and that `R` is local, which is what makes `𝔪_R` and hypothesis (3) writable; `S` enters
only through the finiteness of `M` over it, the flatness of `S → S'`, and the tower. The three
`S`-side hypotheses are spent nowhere: Lemma 0584 is locality-free, and so is the ideal criterion
00HD/00HG. Locality of `R → R'` is dropped for a stronger reason — it is a *consequence* of
hypothesis (3), being item 3 of `IsLocalRing.local_hom_TFAE` applied to `le_of_eq hm`, so keeping
it would state a hypothesis the equality already carries. In particular the lemma applies to a
square whose upper row is a map of algebras of finite type, with `S'` a localization or completion
at a point; this follows the sibling 00MO, which drops the same `S`-side locality.

*The commutative square.* The four arrows are the `algebraMap`s of `Algebra R S`, `Algebra R R'`,
`Algebra S S'` and `Algebra R' S'`, and the commutativity of the square is the pair of towers
`IsScalarTower R S S'` and `IsScalarTower R R' S'` over a diagonal `Algebra R S'`: both say that
the corresponding composite into `S'` is `algebraMap R S'`, hence that the two composites agree.
This is the same presentation as in the sibling 00MO. "Local homomorphism" is
`IsLocalHom (algebraMap · ·)`, as in 00MO, 00MP and 00MQ; only the leg `R' → S'` survives the
pruning above.

*`M' = M ⊗_S S'` is an abstract base change*, a pair of an `S'`-module `M'` and an `S`-linear map
`f : M →ₗ[S] M'` with `IsBaseChange S' f`, again as in 00MO. Taking `M' = S' ⊗[S] M` with
`TensorProduct.mk S S' M` — or any module already presented as a base change in another shape —
recovers the source's module with no intermediate isomorphism to insert. The `R'`-module structure
on `M'`, which the conclusion is about, is the restriction along `R' → S'`, pinned by
`IsScalarTower R' S' M'`; the `R`-module structure on `M`, which hypothesis (2) is about, is the
restriction along `R → S`, pinned by `IsScalarTower R S M`. There is deliberately no `Module R M'`
in the signature: the conclusion does not mention the `R`-action on `M'`, so a proof builds it
through `Algebra R S'` where Lemma 0584 needs it.

*`𝔪_R R'` is `Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R)`*, the ideal of `R'`
generated by the image of `𝔪_R`, as in 00MP and 046Z. It is stated as the source's equality, which
is the form the proof rewrites with, and which — as noted above — subsumes locality of `R → R'`.

*Flatness of a ring map is flatness of the target as a module*, `Module.Flat R R'` and
`Module.Flat S S'`, as in 00MQ and 0584.

*Universes.* The six types are in independent universes; no hypothesis and no part of the
conclusion couples them, exactly as in 00MO.

Faithfulness to [StacksProject 0GEB], on the four points a reader should check.

1. Hypotheses. Each surviving hypothesis is load-bearing. Flatness of `S → S'` is essential: for
   `R = R' = S = k⟦t⟧` and `S' = k⟦t⟧/(t²)` all four rings are Noetherian local, all four maps are
   local, `R → R'` is flat, (3) holds, and `M = S` is a finite `S`-module flat over `R`, while
   `M' = k⟦t⟧/(t²)` has torsion and is not flat over `R'`. Hypothesis (2) is essential: for
   `R = R' = S = S' = k⟦t⟧` the finite `S`-module `M = k⟦t⟧/(t)` gives `M' = M`, not flat over
   `R'`. Hypothesis (3) is essential: for `R = k`, `S = k[y]_{(y)}`, `R' = S' = k⟦t⟧` with `y ↦ t`
   both horizontal arrows are flat and `M = S/yS = k` is flat over the field `R`, while
   `M' = S'/tS' = k` is not flat over `R' = k⟦t⟧`; here `𝔪_R R' = 0 ≠ 𝔪_{R'}`. Noetherianity of
   `R'` and of `S'` and finiteness of `M` over `S` are the hypotheses of the local criterion 00MK,
   which is false without them; `IsLocalRing R'`, `IsLocalRing S'` and locality of `R' → S'` are
   what 00MK consumes, and `IsLocalRing R` is what makes `𝔪_R` and hypothesis (3) writable. The
   four hypotheses of the source's diagram that the proof never spends are dropped rather than
   decorating the statement; see the implementation note.
2. Scalars and base. `Module.Flat R M` is the flatness of `M` for the `R`-action through `R → S`,
   not for its `S`-action, and `Module.Flat R' M'` the flatness of `M'` for the `R'`-action
   through `R' → S'`; `M` is base changed along `S → S'`, and not along `R → R'`, and hypothesis
   (3) is an equality of ideals of `R'`.
3. Canonical maps are pinned. `M'` carries the map `f : M →ₗ[S] M'` realizing it as the base
   change, rather than being a module merely isomorphic to `M ⊗_S S'`; the legs of the square
   are the `algebraMap`s of the algebra instances; `𝔪_R R'` is the canonical extension
   `Ideal.map (algebraMap R R')` of `𝔪_R` and not some ideal with the same radical.
4. The instantiation is not degenerate. Let `k` be a field, `R = k[x]_{(x)}`,
   `S = k[x, y]_{(x, y)}`, `R' = k⟦x⟧` and `S' = (k⟦x⟧[y])_{(x, y)}`. All four rings are local,
   all four maps are local, `R → R'` and `S → S'` are flat, `R'` and `S'` are Noetherian, and
   `𝔪_R R' = xk⟦x⟧ = 𝔪_{R'}`, so the hypotheses hold; for `M = S`, a finite `S`-module flat over
   `R`, the conclusion is the flatness over `k⟦x⟧` of `M' = S'`, an `R'`-module of infinite rank.
   For `M = S/xS`, flat over neither `R` nor `R'`, hypothesis (2) fails, so the statement is not
   vacuous on this square.

## References

* [StacksProject 0GEB](https://stacks.math.columbia.edu/tag/0GEB)
* [StacksProject 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [StacksProject 0584](https://stacks.math.columbia.edu/tag/0584)
* [StacksProject 00M6](https://stacks.math.columbia.edu/tag/00M6)
-/

namespace Module.Flat

/-- **Stacks 0GEB.** Let `S ← R → R'`, `S → S'`, `R' → S'` be a commutative diagram of local
rings and local homomorphisms, let `M` be a finite `S`-module and let `f : M → M'` realize `M'` as
the base change `M ⊗_S S'`. Assume the horizontal arrows `R → R'` and `S → S'` are flat, that `M`
is flat over `R`, that `𝔪_R R' = 𝔪_{R'}` and that `R'` and `S'` are Noetherian. Then `M'` is flat
over `R'`. -/
@[stacks 0GEB "The commutative square is presented by the two scalar towers into `S'`, `M ⊗_S S'`
by `IsBaseChange S' f` as in the sibling 00MO, and `𝔪_R R'` by
`Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R)`. The source's unused hypotheses `S`
local, `R → S` local and `S → S'` local are dropped, and `R → R'` local is implied by `hm`. See
the module docstring."]
public theorem baseChange_of_map_maximalIdeal_eq_maximalIdeal
    {R S R' S' M M' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R'] [IsNoetherianRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R' S')]
    [Module.Flat R R'] [Module.Flat S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M]
    [AddCommGroup M'] [Module S M'] [Module R' M'] [Module S' M']
    [IsScalarTower S S' M'] [IsScalarTower R' S' M']
    (hm : (IsLocalRing.maximalIdeal R).map (algebraMap R R') = IsLocalRing.maximalIdeal R')
    (f : M →ₗ[S] M') (hf : IsBaseChange S' f) :
    Module.Flat R' M' :=
  Stacks.Flatness.LocalBaseChange.solution hm f hf

end Module.Flat
