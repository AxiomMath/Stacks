module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AdicTowerSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicBaseChangeSituation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.BaseChangeMateIdentity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# The base change of `β`, and the square `hδ`, of the second paragraph of Stacks 088B

Let `B` be a Noetherian ring, `J ⊆ B` an ideal, `g = Spec B ^∧ ⟶ Spec B`, `π : X' ⟶ Spec B`
proper and `𝓕` a coherent `𝒪_{X'}`-module. `CompletionProper/AdicBaseChangeSituation.lean` builds
the base change

```
X'' --g'--> X'
|           |
π'          π
v           v
Spec B ^∧ -g-> Spec B
```

together with `𝓕' = g'^*𝓕` and the two comparisons

`ι : (π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` and
`θ_n : π'_*(𝓕' / ℐ' ⁿ⁺¹ 𝓕') ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`

of the direct images, and reduces the second paragraph of the proof of Stacks 088B to two squares
`hδ` and `hγ` written at those comparisons, for a *binder* `β'` playing the role of the base
change of `β`. This file constructs that base change and discharges **both** squares, so that the
second paragraph is left with only the support datum `𝒦` and the hypothesis `hc` on the unit away
from it.

## Main results

* `Stacks.Algebraization.completionProjection_comp_directImageQuotientComparison` — for a proper
  morphism, the projection of `f_*𝓕` onto the `n`-th term of its completion followed by the
  comparison `δ` is the direct image of the quotient projection of `𝓕`.
* `Stacks.Algebraization.π_comp_pullbackIdealPowerQuotientIsoOfEq_inv` — the inverse form of
  `Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom`, and
  `…π_comp_adicBaseChangeIdealPowerQuotientIso_inv` the same at the base change.
* `Stacks.Algebraization.completedComparison_comp_directImageQuotientComparison` — **the square
  `hδ` from its two sides**, for arbitrary `ι` and `θ` between the completions of two direct
  images: it holds as soon as the composites of `ι` and of `θ` with the projection onto the
  `n`-th term are two morphisms which agree.
* `Stacks.Algebraization.completionProjection_comp_levelComparison` — that `θ` side, for a `θ`
  factored as `f₂_*χ ≫ ν`.
* `Stacks.Algebraization.completionProjection_adicBaseChangeCompletedComparison` — **the
  normalization of `ι`**: composed with the projection of `π'_*𝓕'` onto the `n`-th term of its
  completion it is the inverse of the degree-zero flat base change followed by the pullback along
  `g` of the projection of `π_*𝓕` onto the `n`-th term of *its* completion.
* `Stacks.Algebraization.adicBaseChangeLevelComparison_eq` — the factorization of `θ` into the
  direct image of the identification of the levels and the flat base change at the level.
* `Stacks.Algebraization.adicBaseChangePushforwardIso_inv_naturality` — the degree-zero flat base
  change of this square is natural in the module, read on the inverses; at the quotient
  projection of `𝓕` this is what makes the two computed morphisms agree.
* `Stacks.Algebraization.adicBaseChangeCompletedComparison_directImageQuotientComparison` —
  **the square `hδ`**, one of the two remaining binders of
  `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares`: `ι` and `θ`
  carry the `δ` of the situation over `Spec B ^∧` to the pullback along `g` of the `δ` of the
  situation over `Spec B`.
* `Stacks.Algebraization.adicBaseChangeAlgebraizationIso` — **the base change `β'` of `β`**,
  `β` pulled back along `g'` read through that composition isomorphism and through Stacks 0887,
  with `…_hom_hom`, `…_hom_hom_app` and `…adicBaseChangeAlgebraizationIso_tail_app` reading its
  components.
* `Stacks.Algebraization.unit_comp_adicBaseChangePushforwardBaseChange`,
  `…eqToHom_pushforward_completion_obj_adicBaseChange`,
  `…adicBaseChangeLevelComparison_eq_pullbackIdealPowerQuotientIsoOfEq` and
  `…pushforwardBaseChange_comp_adicBaseChangePushforwardIso_inv` — **the remaining hypotheses of
  `Stacks.Algebraization.directImageComparison_square_of_factorizations` at this base change**,
  that is of the reduction of `hγ`.
* `Stacks.Algebraization.completionProjection_comp_pullbackIdealPowerQuotientIsoOfEq_inv` — the
  projection onto a term of the completion of a pullback, followed by the transport of that term
  and the inverse of the identification of the levels, is the pullback of the quotient projection.
* `Stacks.Algebraization.completionPullbackIso_inv_app_comp_adicBaseChange` — **the level
  identification at the base change**, with the transport of ideal sheaves as a binder, proved by
  its own epimorphism-cancelling argument rather than by instantiating
  `Stacks.Algebraization.completionPullbackIso_inv_app_comp`; see "What the kernel's budget is
  sensitive to".
* `Stacks.Algebraization.unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app` — **the unit
  half of `hγ` at the base change**: the unit of `(π')^* ⊣ (π')_*` at `g^*(𝒢_n)` followed by
  `π'_*(β'_n)` is the pullback along `g` of `γ_n`, followed by the degree-zero base-change
  comparison at the `n`-th term of `𝓕 ^∧` and by `π'_*` of the tail of `β'_n`.
* `Stacks.Algebraization.eqToHom_comp_adicBaseChangeLevelComparison`,
  `…pushforwardBaseChange_comp_pushforward_map_adicBaseChange`,
  `…map_comp_map_comp_adicBaseChange`, `…pushforward_map_comp_adicBaseChange` and
  `…pushforwardBaseChange_comp_adicBaseChange` — **the level half of `hγ` at the base change**,
  in the five pieces the kernel's budget allows.
* `Stacks.Algebraization.comp_eq_map_comp_adicBaseChange` — the two halves chained, both `γ`'s
  still written out as the unit followed by a direct image.
* `Stacks.Algebraization.adicBaseChangeDirectImageComparison_square` — **the square `hγ` at the
  actual base change**, the last binder of the second paragraph to be discharged.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma` — **the second
  paragraph of Stacks 088B with `β'` constructed and both squares proved**, so that the only
  binders left are the support datum `𝒦` and the hypothesis `hc` on the unit away from it.

## How `hδ` is proved

The projection `p : π'_*𝓕' ⟶ (π'_*𝓕') / (J B ^∧) ⁿ⁺¹ (π'_*𝓕')` onto the `n`-th term of the
completion is an epimorphism (`Stacks.Algebraization.epi_completionProjection`), so it is enough
to prove the square after composing with `p`. Both composites are then computed to the single
morphism

`π'_*𝓕' ⟶ g^*(π_*𝓕) ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`,

the inverse of the flat base change followed by the pullback along `g` of the direct image of the
quotient projection of `𝓕`:

* on the side of `ι`, `p ≫ ι_n` is the inverse of the flat base change followed by the pullback
  of the projection of `π_*𝓕` onto the `n`-th term of its completion, and that projection
  followed by `δ` is the direct image of the quotient projection of `𝓕`;
* on the side of `θ`, `p` followed by `δ` over `Spec B ^∧` is the direct image of the quotient
  projection of `𝓕'`, which the identification of the levels carries to the pullback along `g'`
  of the quotient projection of `𝓕`
  (`Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom`);
* and the two agree by the naturality
  `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` of the degree-zero
  base-change comparison in the module, read at that quotient projection.

## Why the assembly is stated for arbitrary `ι` and `θ`

The base change `X'' = X' ×_{Spec B} Spec B ^∧` is not a variable scheme, and the kernel's
reduction budget does not survive a declaration at the base change whose statement has to be
matched, by unfolding, against the statement it is proved from: assembling the square in a single
declaration times out, and so does every version in which the final application still has to
identify `ι`, or `θ`, or `𝓕'`, with the shape the general statement is written in.

So the assembly `Stacks.Algebraization.completedComparison_comp_directImageQuotientComparison`
takes `ι` and `θ` themselves as binders, together with the factorization of `θ`, the two
computations and their agreement. Its conclusion is then the statement of `hδ` under substitution
alone, and each of its four hypotheses is discharged by a declaration which needs at most one
identification of modules on the base change. For the same reason the normalization of the
identification of the levels is split in two, into
`Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso_inv_eq` and
`Stacks.Algebraization.π_comp_adicBaseChangeIdealPowerQuotientIso_inv`: one such identification
per declaration is affordable and two are not.

## How `hγ` is proved

`hγ` asserts that `ι` and `θ` carry the `γ` of the situation over `Spec B ^∧` built from `β'` to
the pullback along `g` of the `γ` built from `β`; it is a theorem only for the `β'` constructed
from `β`, which is why `Stacks.Algebraization.adicBaseChangeAlgebraizationIso` is a definition
and not a binder. The ingredient that construction needs, the composition isomorphism
`g'^*π^* ≅ π'^*g^*` for `Stacks.Coherent.coherentAdicPullback`, is
`Stacks.Modules.pullbackSquareIso` whiskered with the diagram of `(𝒢_n)`: the pullback functor on
coherent adic systems is termwise pullback (`Stacks.Coherent.coherentAdicPullback_obj_obj`), so
the composition isomorphism for systems is the one for modules, and only the identification
`Stacks.Algebraization.comap_comap_adicBaseChangeMap` of the two ideal sheaves on the base change
has to be carried along.

By `Stacks.Coherent.directImageComparison_app` both sides of `hγ` are the unit of `π^* ⊣ π_*`,
resp. of `(π')^* ⊣ (π')_*`, followed by a direct image of a component of `β`, resp. of `β'`. So
`hγ` reduces to the compatibility of the degree-zero base-change comparison with the *unit of the
adjunction for the morphism being base changed* — for a coherent `𝒪_{Spec B}`-module `𝒢`,

`g^*(𝒢) ⟶ g^*(π_*π^*𝒢) ⟶ π'_*(g'^*π^*𝒢) ≅ π'_*((π')^*g^*𝒢)`

is the unit of `(π')^* ⊣ (π')_*` at `g^*𝒢` — which is
`Stacks.Algebraization.unit_comp_pushforwardBaseChange`, read off the mate identity
`Stacks.Modules.map_unit_comp_baseChangeNatTrans_app` already in the library.

With that identity, `hγ` is `Stacks.Algebraization.directImageComparison_square_of_factorizations`,
which takes the comparison maps as binders. That reduction is **not applied in one piece**: the
kernel's reduction budget does not survive it, nor its two halves chained inside one declaration.
It is applied in the five steps

* `Stacks.Algebraization.completionPullbackIso_inv_app_comp_adicBaseChange` — the level
  identification,
* `…map_comp_map_comp_adicBaseChange` and `…pushforward_map_comp_adicBaseChange` — its direct
  image along `π'`, and that together with the tail
  `…eqToHom_comp_adicBaseChangeLevelComparison`,
* `…pushforwardBaseChange_comp_adicBaseChange` — the level half, that together with
  `…pushforwardBaseChange_comp_pushforward_map_adicBaseChange`,
* `…comp_eq_map_comp_adicBaseChange` — the level half chained with the unit half
  `…unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app`,
* `…adicBaseChangeDirectImageComparison_square` — the two `γ`'s read through
  `Stacks.Coherent.directImageComparison_app`,

each of which is inside the budget, at 1.0–1.3 s per declaration.

## What the kernel's budget is sensitive to

The base change `X'' = X' ×_{Spec B} Spec B ^∧` is not a variable scheme, and the cost of
a declaration here is **not** in elaborating its statement, nor in checking the term that proves
it, but in the kernel's definitional comparison of the two. Both halves are cheap on their own and
their conjunction is not: for the level identification at `g'`, stating the conclusion alone
(as a hypothesis of a trivial declaration) takes 0.6 s, naming the general lemma at `g'` without
asserting anything about its type takes 0.6 s, and the declaration which states that conclusion
and proves it by that lemma takes 51 s and fails with `(kernel) deterministic timeout`.

Two things make a declaration here affordable.

**Take the transport of ideal sheaves as a binder.** The level identification is
`Stacks.Algebraization.completionPullbackIso_inv_app_comp` at `f := g'` with
`h = (comap_comap_adicBaseChangeMap B J π).symm`, and that `h` is not definitional: the kernel
cannot discharge the `Eq.rec` by its K-like reduction, the two ideal sheaves on the base change
being equal but not definitionally so. Instantiating the general lemma at that `h` is over the
budget in every shape tried — as one application of `…pushforward_map_comp_of_factorizations`, as
a two-piece split, with the lemma given its own declaration and used by name, and with the lemma
fused with its consumer. With `h` and the ideal sheaf it names left as **binders**, the same
statement at `g'` is inside the budget, and the actual transport is substituted into it only
where a declaration whose own statement already carries it consumes it, here
`…pushforward_map_comp_adicBaseChange`. That is what
`Stacks.Algebraization.completionPullbackIso_inv_app_comp_adicBaseChange` and
`…map_comp_map_comp_adicBaseChange` do.

**Prove it where the transport is a binder, rather than transporting a proof.** With `h` a
binder, that statement cannot be had from the general lemma by substitution either — the general
lemma is proved by `subst h`, so its instance at a non-trivial `h` is exactly what the kernel
cannot reduce. It is proved instead by its own epimorphism-cancelling argument, the way
`Stacks.Algebraization.π_comp_adicBaseChangeIdealPowerQuotientIso_inv` is: a morphism out of the
`n`-th term of a completion is pinned by its composite with the projection
(`Stacks.Algebraization.epi_completionProjection`), and
`Stacks.Algebraization.comp_comp_eq_of_epi_factorizations` performs that cancellation with all of
its data implicit, so that each of its four equations is a general lemma at `g'` and the
application demands no identification of its own.

**The two presentations of the modules are not the obstruction.** The objects of these composites
come in two presentations — the one `β'` and `θ` carry (through
`Stacks.Algebraization.adicBaseChangeCoherent`) and the one the general level lemmas produce
(through `Stacks.Coherent.pullbackCoherentModules`). They are literally the same term:
`adicBaseChangeCoherent` carries no `haveI` in its body, so the abbrev unfolds to
`(pullbackCoherentModules g').obj 𝓕`. Each of the following checks in one declaration, well under a
second each:
`(adicBaseChangeCoherent B J π 𝓕).obj = (Scheme.Modules.pullback g').obj 𝓕.obj`, the same
underneath `idealPowerQuotient` and underneath `π'_*`, the two-fold
`Stacks.Coherent.coherentAdicPullback` at a level against `π'^*g^*` of the level, the sources of
the two whiskered isomorphisms `β'` is built from, and the `⋙`-versus-`.obj` readings of a
completion pushed forward — all `rfl`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### Two computations about one morphism -/

/-- If `a ≫ b` is `m` and `m ≫ c` is `z`, then `a ≫ b ≫ c` is `z`. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X}
    {b : X ⟶ Y} {c : Y ⟶ Z} {m : W ⟶ Y} {z : W ⟶ Z} (h₁ : a ≫ b = m) (h₂ : m ≫ c = z) :
    a ≫ b ≫ c = z := by
  rw [← Category.assoc, h₁, h₂]

/-- **The projection onto a term of the completion of a direct image, followed by `δ`.** For a
proper morphism `f : X ⟶ Y` of Noetherian schemes, a quasi-coherent sheaf of ideals `𝒦` on `Y`
and a coherent `𝒪_X`-module `𝓕`, the projection of `f_*𝓕` onto the `n`-th term of its completion
followed by the comparison `δ_{n+1} : (f_*𝓕)/𝒦 ⁿ⁺¹(f_*𝓕) ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)` is the direct image
of the quotient projection of `𝓕`.

Both factors are normalizations: `Stacks.Algebraization.completionProjection_comp_eqToHom` reads
the projection as the quotient projection of `f_*𝓕`, and
`Stacks.Coherent.directImageQuotientComparison_π` is the defining property of `δ`. -/
public theorem completionProjection_comp_directImageQuotientComparison {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f] (K : Y.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection Y K (properPushforwardCoherent f F) n ≫
        (eqToHom (completionFunctor_obj Y K (properPushforwardCoherent f F) n) ≫
          directImageQuotientComparison f K (n + 1) F.obj) =
      (Scheme.Modules.pushforward f).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple (K.comap f) (n + 1) F.obj).ι) :=
  comp_comp_eq_of_comp_eq
    (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ K
      (properPushforwardCoherent f F) n)
    (directImageQuotientComparison_π f K (n + 1) F.obj)

/-- **The inverse form of the normalization of
`Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq`.** The quotient projection of `f^*M`
followed by the inverse of the identification `f^*(M/𝒦 ⁿ M) ≅ (f^*M)/ℐ ⁿ (f^*M)` is the pullback
of the quotient projection of `M`. -/
public theorem π_comp_pullbackIdealPowerQuotientIsoOfEq_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Y.IdealSheafData) {I : X.IdealSheafData} (h : K.comap f = I) (n : ℕ) (M : Y.Modules) :
    cokernel.π (C := X.Modules)
          (idealPowerMultiple I n ((Scheme.Modules.pullback f).obj M)).ι ≫
        (pullbackIdealPowerQuotientIsoOfEq f K h n M).inv =
      (Scheme.Modules.pullback f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple K n M).ι) :=
  (Iso.comp_inv_eq _).2 (map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom f K h n M).symm

/-- **The projection onto a term of the completion of a pullback, followed by the transport of
that term and the inverse of the identification of the levels.** It is the pullback along `f` of
the quotient projection of `𝒢`.

This is `Stacks.Algebraization.completionProjection_comp_eqToHom`, reading the projection as the
quotient projection of `f^*𝒢`, followed by
`Stacks.Algebraization.π_comp_pullbackIdealPowerQuotientIsoOfEq_inv`. -/
public theorem completionProjection_comp_pullbackIdealPowerQuotientIsoOfEq_inv
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (K : Y.IdealSheafData)
    {I : X.IdealSheafData} (h : K.comap f = I)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    completionProjection X I ((pullbackCoherentModules f).obj G) n ≫
        (eqToHom (completionFunctor_obj X I ((pullbackCoherentModules f).obj G) n) ≫
          (pullbackIdealPowerQuotientIsoOfEq f K h (n + 1) G.obj).inv) =
      (Scheme.Modules.pullback f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple K (n + 1) G.obj).ι) :=
  comp_comp_eq_of_comp_eq
    (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ I
      ((pullbackCoherentModules f).obj G) n)
    (π_comp_pullbackIdealPowerQuotientIsoOfEq_inv f K h (n + 1) G.obj)

/-! ### The square from its two sides -/

/-- **The side of `θ` of a square `hδ`, after the projection onto the `n`-th term.** For a proper
`f₂ : X₂ ⟶ Y₂` of Noetherian schemes, a quasi-coherent sheaf of ideals `𝒦₂` on `Y₂`, a coherent
`𝒪_{X₂}`-module `𝓕₂`, a morphism `χ` out of the level `𝓕₂ / ℐ₂ ⁿ⁺¹ 𝓕₂` and an arbitrary morphism
`ν` out of `f₂_*` of its target, the projection of `f₂_*𝓕₂` onto the `n`-th term of its
completion followed by the comparison `δ`, by `f₂_*χ` and by `ν` is `f₂_*P ≫ ν`, where `P` is the
composite of the quotient projection of `𝓕₂` with `χ`.

`χ` is not assumed to be an isomorphism, nor `ν` to be a base-change comparison: the computation
carries them along. -/
public theorem completionProjection_comp_levelComparison {X₂ Y₂ : Scheme.{u}} [IsNoetherian X₂]
    [IsNoetherian Y₂] (f₂ : X₂ ⟶ Y₂) [IsProper f₂] (K₂ : Y₂.IdealSheafData)
    (F₂ : AlgebraicGeometry.SheafOfModules.CoherentModules X₂.ringCatSheaf) (n : ℕ)
    {W : X₂.Modules} (χ : idealPowerQuotient (K₂.comap f₂) (n + 1) F₂.obj ⟶ W)
    {T : Y₂.Modules} (ν : (Scheme.Modules.pushforward f₂).obj W ⟶ T) {P : F₂.obj ⟶ W}
    (hχ : cokernel.π (C := X₂.Modules)
          (idealPowerMultiple (K₂.comap f₂) (n + 1) F₂.obj).ι ≫ χ = P) :
    completionProjection Y₂ K₂ (properPushforwardCoherent f₂ F₂) n ≫
        ((eqToHom (completionFunctor_obj Y₂ K₂ (properPushforwardCoherent f₂ F₂) n) ≫
              directImageQuotientComparison f₂ K₂ (n + 1) F₂.obj) ≫
            ((Scheme.Modules.pushforward f₂).map χ ≫ ν)) =
      (Scheme.Modules.pushforward f₂).map P ≫ ν :=
  comp_comp_eq_of_comp_eq (completionProjection_comp_directImageQuotientComparison f₂ K₂ F₂ n)
    ((Category.assoc (obj := Y₂.Modules) _ _ _).symm.trans
      (congrArg (fun k => k ≫ ν)
        (((Scheme.Modules.pushforward f₂).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward f₂).map hχ))))

/-- **The square `hδ` from its two sides.** Let

```
X₂         X
|          |
f₂         f
v          v
Y₂ --g---> Y
```

be schemes and morphisms with `X`, `Y`, `X₂`, `Y₂` Noetherian and `f`, `f₂` proper, let `𝒦` be a
quasi-coherent sheaf of ideals on `Y`, let `𝓕` and `𝓕₂` be coherent modules on `X` and on `X₂`,
and let

`ι : (f₂_*𝓕₂) ^∧ ⟶ g^*((f_*𝓕) ^∧)` and
`θ : f₂_*(𝓕₂ / ℐ₂ ⁿ⁺¹ 𝓕₂) ⟶ g^*(f_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`

be arbitrary morphisms. Write `p` for the projection of `f₂_*𝓕₂` onto the `n`-th term of its
completion. If

* `p ≫ ι_n` is some `μ` followed by the pullback along `g` of the projection of `f_*𝓕` onto the
  `n`-th term of its completion (`hι`),
* `θ` factors as `f₂_*χ ≫ ν` (`hθ`) with `χ` carrying the quotient projection of `𝓕₂` to some
  `P` (`hχ`), and
* `μ` followed by the pullback along `g` of the direct image of the quotient projection of `𝓕` is
  `f₂_*P ≫ ν` (`hμ`),

then `ι` and `θ` carry the `δ` over `Y₂` to the pullback along `g` of the `δ` over `Y`.

`p` is an epimorphism, so it suffices to prove the square after composing with it; `hι` and
`Stacks.Algebraization.completionProjection_comp_directImageQuotientComparison` turn the side of
`ι` into the left-hand side of `hμ`, and
`Stacks.Algebraization.completionProjection_comp_levelComparison` turns the side of `θ` into its
right-hand side.

No relation between `ι`, `θ`, `μ`, `χ`, `ν` and `P` beyond these four equations is used, and
none of `ι`, `θ`, `χ`, `ν` is assumed to be an isomorphism. -/
public theorem completedComparison_comp_directImageQuotientComparison {X Y X₂ Y₂ : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X₂] [IsNoetherian Y₂] (f : X ⟶ Y)
    [IsProper f] (g : Y₂ ⟶ Y) (f₂ : X₂ ⟶ Y₂) [IsProper f₂] (K : Y.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F₂ : AlgebraicGeometry.SheafOfModules.CoherentModules X₂.ringCatSheaf) (n : ℕ)
    {ι : ((completionFunctor Y₂ (K.comap g)).obj (properPushforwardCoherent f₂ F₂)).obj ⟶
      ((coherentAdicPullback g K).obj
        ((completionFunctor Y K).obj (properPushforwardCoherent f F))).obj}
    {θ : (Scheme.Modules.pushforward f₂).obj
          (idealPowerQuotient ((K.comap g).comap f₂) (n + 1) F₂.obj) ⟶
        (Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pushforward f).obj
            (idealPowerQuotient (K.comap f) (n + 1) F.obj))}
    {μ : (properPushforwardCoherent f₂ F₂).obj ⟶
      (Scheme.Modules.pullback g).obj (properPushforwardCoherent f F).obj}
    {W : X₂.Modules} {χ : idealPowerQuotient ((K.comap g).comap f₂) (n + 1) F₂.obj ⟶ W}
    {ν : (Scheme.Modules.pushforward f₂).obj W ⟶
      (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (idealPowerQuotient (K.comap f) (n + 1) F.obj))}
    {P : F₂.obj ⟶ W}
    (hι : completionProjection Y₂ (K.comap g) (properPushforwardCoherent f₂ F₂) n ≫
          ι.app (op n) =
        μ ≫ (Scheme.Modules.pullback g).map
          (completionProjection Y K (properPushforwardCoherent f F) n))
    (hθ : θ = (Scheme.Modules.pushforward f₂).map χ ≫ ν)
    (hχ : cokernel.π (C := X₂.Modules)
          (idealPowerMultiple ((K.comap g).comap f₂) (n + 1) F₂.obj).ι ≫ χ = P)
    (hμ : μ ≫ (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pushforward f).map
            (cokernel.π (C := X.Modules)
              (idealPowerMultiple (K.comap f) (n + 1) F.obj).ι)) =
        (Scheme.Modules.pushforward f₂).map P ≫ ν) :
    ι.app (op n) ≫
        (Scheme.Modules.pullback g).map
          (eqToHom (completionFunctor_obj Y K (properPushforwardCoherent f F) n) ≫
            directImageQuotientComparison f K (n + 1) F.obj) =
      (eqToHom (completionFunctor_obj Y₂ (K.comap g)
            (properPushforwardCoherent f₂ F₂) n) ≫
          directImageQuotientComparison f₂ (K.comap g) (n + 1) F₂.obj) ≫ θ := by
  subst hθ
  refine (@cancel_epi _ _ _ _ _
    (completionProjection Y₂ (K.comap g) (properPushforwardCoherent f₂ F₂) n)
    (Stacks.Algebraization.epi_completionProjection Y₂ (K.comap g)
      (properPushforwardCoherent f₂ F₂) n) _ _).mp ?_
  refine Eq.trans ?_
    (completionProjection_comp_levelComparison f₂ (K.comap g) F₂ n χ ν hχ).symm
  exact ((Category.assoc (obj := Y₂.Modules) _ _ _).symm.trans
    ((congrArg
        (fun k => k ≫ (Scheme.Modules.pullback g).map
          (eqToHom (completionFunctor_obj Y K (properPushforwardCoherent f F) n) ≫
            directImageQuotientComparison f K (n + 1) F.obj)) hι).trans
      ((Category.assoc (obj := Y₂.Modules) _ _ _).trans
        (congrArg (fun k => μ ≫ k)
          (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
            (congrArg (Scheme.Modules.pullback g).map
              (completionProjection_comp_directImageQuotientComparison f K F n))))))).trans hμ

/-! ### The three sides at the base change -/

section Squares

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B) {X' : Scheme.{u}}
  [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- **The normalization of the comparison `ι` of the two completed direct images.** Composing the
`n`-th component of

`ι : (π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)`

with the projection of `π'_*𝓕'` onto the `n`-th term of its completion gives the inverse of the
degree-zero flat base change `π'_*𝓕' ≅ g^*(π_*𝓕)` followed by the pullback along `g` of the
projection of `π_*𝓕` onto the `n`-th term of its completion.

The projection is an epimorphism (`Stacks.Algebraization.epi_completionProjection`), so this
determines `ι`. It is the two normalizations `ι` is assembled from:
`Stacks.Algebraization.completionFunctor_map_quotient`, which describes the completion of the
flat base change as the induced map on successive quotients, and
`Stacks.Coherent.completionProjection_completionPullbackComparison`, the normalization of the
identification of completion with pullback. -/
public theorem completionProjection_adicBaseChangeCompletedComparison
    [𝓕.obj.IsQuasicoherent] (n : ℕ) :
    completionProjection (Spec (.of (AdicCompletion J B)))
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
          (properPushforwardCoherent (adicBaseChangeMap B J π)
            (adicBaseChangeCoherent B J π 𝓕)) n ≫
        (adicBaseChangeCompletedComparison B J π 𝓕).app (op n) =
      (adicBaseChangePushforwardIso B J π 𝓕.obj).inv ≫
        (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          (completionProjection (Spec (.of B)) (adicIdealSheaf B J)
            (properPushforwardCoherent π 𝓕) n) := by
  have h1 := completionFunctor_map_quotient (Spec (.of (AdicCompletion J B)))
    ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
    (adicBaseChangeProperPushforwardIso B J π 𝓕).hom n
  have h2 := completionProjection_completionPullbackComparison
    (adicCompletionSpecMap B J) (adicIdealSheaf B J) (properPushforwardCoherent π 𝓕) (op n)
  refine Eq.trans ?_ (congrArg
    (fun k => (adicBaseChangeProperPushforwardIso B J π 𝓕).hom.hom ≫ k) h2)
  refine Eq.trans ?_ (Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _)
  refine Eq.trans ?_ (congrArg (fun k => k ≫
    (completionPullbackComparison (adicCompletionSpecMap B J) (adicIdealSheaf B J)
      (properPushforwardCoherent π 𝓕)).hom.app (op n)) h1)
  exact (Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _).symm

/-- **The factorization of the comparison `θ` of the two direct images of the levels.** By
construction `θ_n` is the direct image along `π'` of the inverse of the identification
`Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` of the levels, followed by the
inverse of the degree-zero flat base change at the level `𝓕 / ℐ ⁿ⁺¹ 𝓕`. -/
public theorem adicBaseChangeLevelComparison_eq (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    adicBaseChangeLevelComparison B J π 𝓕 n =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          (adicBaseChangeIdealPowerQuotientIso B J π (n + 1) 𝓕.obj).inv ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv := rfl

omit [IsNoetherianRing B] [AlgebraicGeometry.IsNoetherian X'] [IsProper π] in
/-- The identification of the levels at the base change *is* the generic
`Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq` along `g'`, by definition. -/
public theorem adicBaseChangeIdealPowerQuotientIso_inv_eq (n : ℕ) :
    (adicBaseChangeIdealPowerQuotientIso B J π (n + 1) 𝓕.obj).inv =
      (pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π)
        ((adicIdealSheaf B J).comap π) (comap_comap_adicBaseChangeMap B J π).symm
        (n + 1) 𝓕.obj).inv :=
  rfl

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- **The normalization of the identification of the levels at the base change.** The quotient
projection of `𝓕' = g'^*𝓕` followed by the inverse of the identification
`Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` of the levels is the pullback along
`g'` of the quotient projection of `𝓕`.

This is `Stacks.Algebraization.π_comp_pullbackIdealPowerQuotientIsoOfEq_inv` at `g'`, read
through `Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso_inv_eq`. The two steps are
separate declarations because the kernel's reduction budget does not cover both identifications
of modules on `X' ×_{Spec B} Spec B ^∧` in one. -/
public theorem π_comp_adicBaseChangeIdealPowerQuotientIso_inv (n : ℕ) :
    cokernel.π (C := (adicBaseChange B J π).Modules)
          (idealPowerMultiple (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
            (adicBaseChangeMap B J π)) (n + 1) (adicBaseChangeCoherent B J π 𝓕).obj).ι ≫
        (adicBaseChangeIdealPowerQuotientIso B J π (n + 1) 𝓕.obj).inv =
      (Scheme.Modules.pullback (adicBaseChangeFst B J π)).map
        (cokernel.π (C := X'.Modules)
          (idealPowerMultiple ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).ι) := by
  rw [adicBaseChangeIdealPowerQuotientIso_inv_eq B J π 𝓕 n]
  exact π_comp_pullbackIdealPowerQuotientIsoOfEq_inv (adicBaseChangeFst B J π)
    ((adicIdealSheaf B J).comap π) (comap_comap_adicBaseChangeMap B J π).symm (n + 1) 𝓕.obj

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- **The degree-zero flat base change of this square is natural in the module, on the
inverses.** For a morphism `t : 𝓕 ⟶ 𝓔` of `𝒪_{X'}`-modules, the inverse of the base change at
`𝓕` followed by the pullback along `g` of the direct image of `t` is the direct image along `π'`
of the pullback along `g'` of `t`, followed by the inverse of the base change at `𝓔`.

This is `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` read on the
inverses of the two isomorphisms. At the quotient projection of `𝓕` it is the agreement of the
two morphisms computed for the two sides of `hδ`. -/
public theorem adicBaseChangePushforwardIso_inv_naturality
    {𝓔 : X'.Modules} [𝓕.obj.IsQuasicoherent] [𝓔.IsQuasicoherent] (t : 𝓕.obj ⟶ 𝓔) :
    (adicBaseChangePushforwardIso B J π 𝓕.obj).inv ≫
        (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((Scheme.Modules.pushforward π).map t) =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).map t) ≫
        (adicBaseChangePushforwardIso B J π 𝓔).inv :=
  have hnat : (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((Scheme.Modules.pushforward π).map t) ≫
        (adicBaseChangePushforwardIso B J π 𝓔).hom =
      (adicBaseChangePushforwardIso B J π 𝓕.obj).hom ≫
        (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).map t) :=
    pushforwardBaseChange_naturality (adicBaseChange_isPullback B J π).w t
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 hnat).trans
      (Category.assoc (obj := (Spec (.of (AdicCompletion J B))).Modules) _ _ _))

/-! ### The square `hδ` at the base change -/

/-- **The square `hδ` of the reduction, at the actual base change.** The comparisons

`ι : (π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` and
`θ_n : π'_*(𝓕' / ℐ' ⁿ⁺¹ 𝓕') ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`

of `Stacks.Algebraization.adicBaseChangeCompletedComparison` and
`Stacks.Algebraization.adicBaseChangeLevelComparison` carry the comparison `δ` of
`Stacks.Coherent.directImageQuotientComparison` over `Spec B ^∧` to the pullback along `g` of
the one over `Spec B`.

This is `Stacks.Algebraization.completedComparison_comp_directImageQuotientComparison` at the
computations above: the normalization of `ι`, the factorization of `θ`, the normalization
`Stacks.Algebraization.π_comp_adicBaseChangeIdealPowerQuotientIso_inv` of the
identification of the levels, and the naturality of the degree-zero flat base change at the
quotient projection of `𝓕`.

This is the second remaining binder of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares`. -/
public theorem adicBaseChangeCompletedComparison_directImageQuotientComparison (n : ℕ) :
    (adicBaseChangeCompletedComparison B J π 𝓕).app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            (eqToHom (completionFunctor_obj (Spec (.of B)) (adicIdealSheaf B J)
                (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π (adicIdealSheaf B J) (n + 1) 𝓕.obj) =
        (eqToHom (completionFunctor_obj (Spec (.of (AdicCompletion J B)))
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (properPushforwardCoherent (adicBaseChangeMap B J π)
                (adicBaseChangeCoherent B J π 𝓕)) n) ≫
            directImageQuotientComparison (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)) (n + 1)
              (adicBaseChangeCoherent B J π 𝓕).obj) ≫
          adicBaseChangeLevelComparison B J π 𝓕 n := by
  have : 𝓕.obj.IsCoherent := 𝓕.property
  have : 𝓕.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsCoherent :=
    (coherentAnnihilatedBy_idealPowerQuotient ((adicIdealSheaf B J).comap π) n 𝓕.obj
      𝓕.property).1
  have : (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  exact completedComparison_comp_directImageQuotientComparison π (adicCompletionSpecMap B J)
    (adicBaseChangeMap B J π) (adicIdealSheaf B J) 𝓕 (adicBaseChangeCoherent B J π 𝓕) n
    (completionProjection_adicBaseChangeCompletedComparison B J π 𝓕 n)
    (adicBaseChangeLevelComparison_eq B J π 𝓕 n)
    (π_comp_adicBaseChangeIdealPowerQuotientIso_inv B J π 𝓕 n)
    (adicBaseChangePushforwardIso_inv_naturality B J π 𝓕
      (cokernel.π (C := X'.Modules)
        (idealPowerMultiple ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).ι))

/-! ### The base change of `β` -/

/-- **The base change of `β`.** Given an algebraization `β : π^*(𝒢_n) ≅ 𝓕 ^∧` over `Spec B`, the
corresponding isomorphism over `Spec B ^∧`:

`(π')^*(g^*(𝒢_n)) ≅ (𝓕') ^∧`   for `𝓕' = g'^*𝓕`.

It is `β` pulled back along `g'` and read through two identifications. The first is the
composition isomorphism

`(π')^*g^* ≅ (g')^*π^*`

for the termwise pullback of adic systems, which is `Stacks.Modules.pullbackSquareIso` at
the cartesian square of the base change whiskered with the diagram of `(𝒢_n)`; the pullback
functor on coherent adic systems is termwise pullback
(`Stacks.Coherent.coherentAdicPullback_obj_obj`), so no further comparison is needed to read it
on systems. The second is `Stacks.Coherent.completionPullbackIso` (Stacks 0887) at `g'`, which
identifies `(g')^*(𝓕 ^∧)` with `(g'^*𝓕) ^∧`, followed by
`Stacks.Algebraization.completionFunctorObjCongr` at
`Stacks.Algebraization.comap_comap_adicBaseChangeMap` — the two routes from `J 𝒪_{Spec B}` to an
ideal sheaf on the base change — which is what makes the result an adic system along
`(J B ^∧) 𝒪` pulled back along `π'` rather than along `g'`.

**Why `β'` has to be this and not a binder.** The square `hγ` asserts that `ι` and `θ` carry the
`γ` of the situation over `Spec B ^∧` built from `β'` to the pullback along `g` of the `γ` built
from `β`; for a `β'` unrelated to `β` that is false, so `β'` must be constructed from `β`, and
the composition isomorphism above is the ingredient that construction needs. -/
public def adicBaseChangeAlgebraizationIso (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) :
    (coherentAdicPullback (adicBaseChangeMap B J π)
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G) ≅
      (completionFunctor (adicBaseChange B J π)
        (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
          (adicBaseChangeMap B J π))).obj (adicBaseChangeCoherent B J π 𝓕) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft G.obj
        (Stacks.Modules.pullbackSquareIso π (adicBaseChangeMap B J π)
          (adicCompletionSpecMap B J) (adicBaseChangeFst B J π)
          (adicBaseChange_isPullback B J π).w) ≪≫
      Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
          (Scheme.Modules.pullback (adicBaseChangeFst B J π)) ≪≫
        (ObjectProperty.ι _).mapIso
            (completionPullbackIso (adicBaseChangeFst B J π)
              ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
          completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
            ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕))

/-! ### The square `hγ` at the base change -/

/-- **The components of the base change `β'` of `β`.** At level `n`, `β'` is the composition
isomorphism `π'^*g^* ≅ g'^*π^*`, followed by the pullback along `g'` of `β_n`, followed by the
inverse of the level `n` of Stacks 0887 and the transport between the two ideal sheaves on the
base change.

This is `Stacks.Algebraization.adicBaseChangeAlgebraizationIso` read on components, and holds by
`rfl`: it is the one identification of modules on `X' ×_{Spec B} Spec B ^∧` which the
factorization of `β'` demanded by
`Stacks.Algebraization.directImageComparison_square_of_factorizations` needs, and it is a
separate declaration because the kernel's reduction budget does not cover it together with the
rest of that application. The composition isomorphism is `Stacks.Modules.pullbackSquareIso`,
which is the spelling the mate identity is stated at. -/
public theorem adicBaseChangeAlgebraizationIso_hom_hom
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) :
    (adicBaseChangeAlgebraizationIso B J π 𝓕 G β).hom.hom =
      (Functor.isoWhiskerLeft G.obj
            (Stacks.Modules.pullbackSquareIso π (adicBaseChangeMap B J π)
              (adicCompletionSpecMap B J) (adicBaseChangeFst B J π)
              (adicBaseChange_isPullback B J π).w) ≪≫
          Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
              (Scheme.Modules.pullback (adicBaseChangeFst B J π)) ≪≫
            (ObjectProperty.ι _).mapIso
                (completionPullbackIso (adicBaseChangeFst B J π)
                  ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
              completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
                ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom :=
  rfl

/-- **The components of the base change `β'` of `β`.** At level `n`, `β'` is the composition
isomorphism `π'^*g^* ≅ g'^*π^*` at `𝒢_n`, followed by the pullback along `g'` of `β_n`, followed
by the inverse of the level `n` of Stacks 0887 and by the transport between the two ideal sheaves
on the base change.

This is `Stacks.Algebraization.adicBaseChangeAlgebraizationIso_hom_hom` read at `op n`. The two
steps are separate declarations because the kernel's reduction budget covers the identification
of the two natural transformations, and the decomposition of a component into a composite in
`(X' ×_{Spec B} Spec B ^∧).Modules`, only one at a time. -/
public theorem adicBaseChangeAlgebraizationIso_hom_hom_app
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) (n : ℕ) :
    (adicBaseChangeAlgebraizationIso B J π 𝓕 G β).hom.hom.app (op n) =
      (Functor.isoWhiskerLeft G.obj
          (Stacks.Modules.pullbackSquareIso π (adicBaseChangeMap B J π)
            (adicCompletionSpecMap B J) (adicBaseChangeFst B J π)
            (adicBaseChange_isPullback B J π).w)).hom.app (op n) ≫
        (Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
              (Scheme.Modules.pullback (adicBaseChangeFst B J π)) ≪≫
            (ObjectProperty.ι _).mapIso
                (completionPullbackIso (adicBaseChangeFst B J π)
                  ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
              completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
                ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n) :=
  congr_app (adicBaseChangeAlgebraizationIso_hom_hom B J π 𝓕 G β) (op n)

/-- **The tail of the base change `β'` of `β` at level `n`.** The last three factors of `β'`
split off the pullback along `g'` of `β_n`; `rfl`, and one composition in
`(X' ×_{Spec B} Spec B ^∧).Modules`. -/
public theorem adicBaseChangeAlgebraizationIso_tail_app
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) (n : ℕ) :
    (Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
            (Scheme.Modules.pullback (adicBaseChangeFst B J π)) ≪≫
          (ObjectProperty.ι _).mapIso
              (completionPullbackIso (adicBaseChangeFst B J π)
                ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
            completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
              ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n) =
      (Scheme.Modules.pullback (adicBaseChangeFst B J π)).map (β.hom.hom.app (op n)) ≫
        ((ObjectProperty.ι _).mapIso
              (completionPullbackIso (adicBaseChangeFst B J π)
                ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
            completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
              ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n) :=
  rfl

omit [IsNoetherianRing B] [AlgebraicGeometry.IsNoetherian X'] [IsProper π] in
/-- **The mate identity at the base change, at the level `𝒢_n`.** This is
`Stacks.Algebraization.unit_comp_pushforwardBaseChange` at the cartesian square of the base
change and at the `n`-th term of `(𝒢_n)`, read through the whiskering by the diagram of
`(𝒢_n)` which is the first factor of `β'`. -/
public theorem unit_comp_adicBaseChangePushforwardBaseChange
    (G : CoherentAdicSystems (adicIdealSheaf B J)) (n : ℕ) :
    (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app (G.obj.obj (op n))) ≫
        pushforwardBaseChange (adicBaseChange_isPullback B J π).w
          ((Scheme.Modules.pullback π).obj (G.obj.obj (op n))) =
      (Scheme.Modules.pullbackPushforwardAdjunction (adicBaseChangeMap B J π)).unit.app
          ((Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj (G.obj.obj (op n))) ≫
        (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((Functor.isoWhiskerLeft G.obj
            (Stacks.Modules.pullbackSquareIso π (adicBaseChangeMap B J π)
              (adicCompletionSpecMap B J) (adicBaseChangeFst B J π)
              (adicBaseChange_isPullback B J π).w)).hom.app (op n)) :=
  unit_comp_pushforwardBaseChange π (adicBaseChangeMap B J π) (adicCompletionSpecMap B J)
    (adicBaseChangeFst B J π) (adicBaseChange_isPullback B J π).w (G.obj.obj (op n))

/-- `Stacks.Algebraization.adicBaseChangeLevelComparison_eq` with the identification of the
levels read as the generic `Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq` along `g'`,
which is the spelling `Stacks.Algebraization.completionPullbackIso_inv_app_comp` produces. -/
public theorem adicBaseChangeLevelComparison_eq_pullbackIdealPowerQuotientIsoOfEq (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    adicBaseChangeLevelComparison B J π 𝓕 n =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          (pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π)
            ((adicIdealSheaf B J).comap π) (comap_comap_adicBaseChangeMap B J π).symm
            (n + 1) 𝓕.obj).inv ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv :=
  (adicBaseChangeLevelComparison_eq B J π 𝓕 n).trans
    (congrArg (fun k => (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map k ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv)
      (adicBaseChangeIdealPowerQuotientIso_inv_eq B J π 𝓕 n))

/-- **The level identification of the level half of the square `hγ`, at the base change.** The
tail of `β'_n` — the inverse of the level `n` of Stacks 0887 along `g'` followed by the transport
between the two ideal sheaves on the base change — composed with the transport of the `n`-th term
of the completion of `𝓕'` and the inverse of the identification of the levels, is the pullback
along `g'` of the transport of the `n`-th term of the completion of `𝓕`.

This is `Stacks.Algebraization.completionPullbackIso_inv_app_comp` at `g'`, but **not** by
instantiating it: the transport `(comap_comap_adicBaseChangeMap B J π).symm` is not definitional,
and a declaration which carries that transport *and* identifies the two presentations of the
level on `X' ×_{Spec B} Spec B ^∧` exhausts the kernel's reduction budget, as the module docstring
records.

Instead the epimorphism-cancelling proof of that lemma is carried out here at the base change,
with one identification per declaration, the way
`Stacks.Algebraization.π_comp_adicBaseChangeIdealPowerQuotientIso_inv` is: a morphism out of the
`n`-th term of a completion is pinned by its composite with the projection
(`Stacks.Algebraization.epi_completionProjection`), and
`Stacks.Algebraization.comp_comp_eq_of_epi_factorizations` performs the cancellation with all of
its data implicit, so that each of its four equations is a general lemma at `g'` and no
identification is demanded of the application itself:

* the transport is carried by
  `Stacks.Algebraization.completionProjection_comp_completionFunctorObjCongr`, which identifies
  the projections along the two equal ideal sheaves;
* the two presentations of the level meet only in
  `Stacks.Algebraization.completionProjection_comp_completionPullbackIso_hom_app_comp`, at `g'`
  and with no transport in sight;
* and `Stacks.Algebraization.completionProjection_comp_pullbackIdealPowerQuotientIsoOfEq_inv`
  computes the other composite, both to the pullback along `g'` of the quotient projection of
  `𝓕`. -/
public theorem completionPullbackIso_inv_app_comp_adicBaseChange
    {I : (adicBaseChange B J π).IdealSheafData}
    (h : ((adicIdealSheaf B J).comap π).comap (adicBaseChangeFst B J π) = I) (n : ℕ) :
    ((ObjectProperty.ι _).mapIso
            (completionPullbackIso (adicBaseChangeFst B J π)
              ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
          completionFunctorObjCongr h
            ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n) ≫
        (eqToHom (completionFunctor_obj (adicBaseChange B J π) I
            ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n) ≫
          (pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π)
            ((adicIdealSheaf B J).comap π) h (n + 1) 𝓕.obj).inv) =
      (Scheme.Modules.pullback (adicBaseChangeFst B J π)).map
        (eqToHom (completionFunctor_obj X' ((adicIdealSheaf B J).comap π) 𝓕 n)) :=
  comp_comp_eq_of_epi_factorizations
    (completionProjection (adicBaseChange B J π)
      (((adicIdealSheaf B J).comap π).comap (adicBaseChangeFst B J π))
      ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n)
    (epi_completionProjection (adicBaseChange B J π)
      (((adicIdealSheaf B J).comap π).comap (adicBaseChangeFst B J π))
      ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n)
    (completionProjection_comp_completionFunctorObjCongr h
      ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n)
    (completionPullbackIso_inv_hom_id_app (adicBaseChangeFst B J π)
      ((adicIdealSheaf B J).comap π) 𝓕 (op n))
    (completionProjection_comp_pullbackIdealPowerQuotientIsoOfEq_inv (adicBaseChangeFst B J π)
      ((adicIdealSheaf B J).comap π) h 𝓕 n)
    (completionProjection_comp_completionPullbackIso_hom_app_comp (adicBaseChangeFst B J π)
      ((adicIdealSheaf B J).comap π) 𝓕 n)

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- The degree-zero flat base change at the level is invertible, read with its `hom` spelled as
the canonical comparison `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange`. -/
public theorem pushforwardBaseChange_comp_adicBaseChangePushforwardIso_inv (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    pushforwardBaseChange (adicBaseChange_isPullback B J π).w
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj) ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv = 𝟙 _ :=
  Iso.hom_inv_id (adicBaseChangePushforwardIso B J π
    (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj))

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- The transport of the `n`-th term of the completion of `𝓕'` through the direct image along
`π'` is the direct image of the transport; `CategoryTheory.eqToHom_map`. -/
public theorem eqToHom_pushforward_completion_obj_adicBaseChange (n : ℕ) :
    eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
        ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
        (adicBaseChangeCoherent B J π 𝓕) n) =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
        (eqToHom (completionFunctor_obj (adicBaseChange B J π)
          (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
            (adicBaseChangeMap B J π))
          ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n)) :=
  (eqToHom_map (Scheme.Modules.pushforward (adicBaseChangeMap B J π))
    (completionFunctor_obj (adicBaseChange B J π)
      (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
        (adicBaseChangeMap B J π))
      ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n)).symm

/-- **The unit half of the square `hγ` at the base change.** The unit of `(π')^* ⊣ (π')_*` at
`g^*(𝒢_n)` followed by `π'_*(β'_n)` is the pullback along `g` of `γ_n`, followed by the
degree-zero base-change comparison at the `n`-th term of `𝓕 ^∧` and by `π'_*` of the tail of
`β'_n`.

This is `Stacks.Algebraization.unit_comp_map_of_factorizations` at the mate identity
`Stacks.Algebraization.unit_comp_adicBaseChangePushforwardBaseChange` and the two factorizations
`Stacks.Algebraization.adicBaseChangeAlgebraizationIso_hom_hom_app` and
`…adicBaseChangeAlgebraizationIso_tail_app` of `β'_n`. The composite spelled on the right of the
pullback of `γ_n` is the intermediate morphism at which this half is to meet the level half, the
third piece of which is not yet a theorem; see "What is not here". -/
public theorem unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (adicBaseChangeMap B J π)).unit.app
          ((Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj (G.obj.obj (op n))) ≫
        (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((adicBaseChangeAlgebraizationIso B J π 𝓕 G β).hom.hom.app (op n)) =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app (G.obj.obj (op n)) ≫
            (Scheme.Modules.pushforward π).map (β.hom.hom.app (op n))) ≫
        (pushforwardBaseChange (adicBaseChange_isPullback B J π).w
              (((completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕).obj.obj (op n)) ≫
          (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
            (((ObjectProperty.ι _).mapIso
                  (completionPullbackIso (adicBaseChangeFst B J π)
                    ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
                completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
                  ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app
              (op n))) :=
  unit_comp_map_of_factorizations π (adicBaseChangeMap B J π) (adicCompletionSpecMap B J)
    (adicBaseChangeFst B J π) (adicBaseChange_isPullback B J π).w (G.obj.obj (op n))
    (unit_comp_adicBaseChangePushforwardBaseChange B J π G n)
    (adicBaseChangeAlgebraizationIso_hom_hom_app B J π 𝓕 G β n)
    (adicBaseChangeAlgebraizationIso_tail_app B J π 𝓕 G β n)

/-- **The tail of the level half of the square `hγ`, at the base change.** The transport of the
`n`-th term of the completion of `𝓕'` followed by `θ_n` is the direct image along `π'` of that
transport composed with the inverse of the identification of the levels, followed by the inverse
of the degree-zero flat base change at the level.

This is `Stacks.Algebraization.comp_eq_map_comp_comp_of_factorizations` at the reading
`Stacks.Algebraization.eqToHom_pushforward_completion_obj_adicBaseChange` of the transport and at
the factorization
`Stacks.Algebraization.adicBaseChangeLevelComparison_eq_pullbackIdealPowerQuotientIsoOfEq` of
`θ_n`. No comparison map built from `β` occurs. -/
public theorem eqToHom_comp_adicBaseChangeLevelComparison (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
          (adicBaseChangeCoherent B J π 𝓕) n) ≫
        adicBaseChangeLevelComparison B J π 𝓕 n =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          (eqToHom (completionFunctor_obj (adicBaseChange B J π)
              (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
                (adicBaseChangeMap B J π))
              ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n) ≫
            (pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π)
              ((adicIdealSheaf B J).comap π) (comap_comap_adicBaseChangeMap B J π).symm (n + 1)
              𝓕.obj).inv) ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv :=
  comp_eq_map_comp_comp_of_factorizations (adicBaseChangeMap B J π)
    (eqToHom_pushforward_completion_obj_adicBaseChange B J π 𝓕 n)
    (adicBaseChangeLevelComparison_eq_pullbackIdealPowerQuotientIsoOfEq B J π 𝓕 n)

/-- **The base-change comparison inside the level half of the square `hγ`, at the base change.**
The degree-zero base-change comparison at the `n`-th term of `𝓕 ^∧`, followed by the direct image
along `π'` of the pullback along `g'` of the transport of the `n`-th term of the completion of
`𝓕` and by the inverse of the degree-zero flat base change at the level, is the pullback along
`g` of the transport of the `n`-th term of the completion of `𝓕`.

This is `Stacks.Algebraization.pushforwardBaseChange_comp_map_of_factorizations` at the reading
`CategoryTheory.eqToHom_map` of the transport and at the invertibility
`Stacks.Algebraization.pushforwardBaseChange_comp_adicBaseChangePushforwardIso_inv` of the
comparison at the level. No comparison map on the base change occurs. -/
public theorem pushforwardBaseChange_comp_pushforward_map_adicBaseChange (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    pushforwardBaseChange (adicBaseChange_isPullback B J π).w
          (((completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕).obj.obj (op n)) ≫
        ((Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
            ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).map
              (eqToHom (completionFunctor_obj X' ((adicIdealSheaf B J).comap π) 𝓕 n))) ≫
          (adicBaseChangePushforwardIso B J π
            (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv) =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
        (eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n)) :=
  pushforwardBaseChange_comp_map_of_factorizations π (adicBaseChangeMap B J π)
    (adicCompletionSpecMap B J) (adicBaseChangeFst B J π) (adicBaseChange_isPullback B J π).w
    (eqToHom_map (Scheme.Modules.pushforward π)
      (completionFunctor_obj X' ((adicIdealSheaf B J).comap π) 𝓕 n)).symm
    (pushforwardBaseChange_comp_adicBaseChangePushforwardIso_inv B J π 𝓕 n)

/-- **The level identification of the level half of the square `hγ`, after the direct image along
`π'`.** The direct image of the tail of `β'_n`, followed by the direct image of the transport of
the level composed with the inverse of the identification of the levels and by the inverse of the
degree-zero flat base change at the level, is the direct image of the pullback along `g'` of the
transport of the `n`-th term of the completion of `𝓕`, followed by that same inverse.

This is `Stacks.Algebraization.map_comp_map_comp_of_factorization` at
`Stacks.Algebraization.completionPullbackIso_inv_app_comp_adicBaseChange`; the transport of ideal
sheaves is still a binder, so no identification is demanded of the application. -/
public theorem map_comp_map_comp_adicBaseChange
    {I : (adicBaseChange B J π).IdealSheafData}
    (h : ((adicIdealSheaf B J).comap π).comap (adicBaseChangeFst B J π) = I) (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          (((ObjectProperty.ι _).mapIso
                (completionPullbackIso (adicBaseChangeFst B J π)
                  ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
              completionFunctorObjCongr h
                ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n)) ≫
        ((Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
            (eqToHom (completionFunctor_obj (adicBaseChange B J π) I
                ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕) n) ≫
              (pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π)
                ((adicIdealSheaf B J).comap π) h (n + 1) 𝓕.obj).inv) ≫
          (adicBaseChangePushforwardIso B J π
            (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv) =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).map
            (eqToHom (completionFunctor_obj X' ((adicIdealSheaf B J).comap π) 𝓕 n))) ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv :=
  map_comp_map_comp_of_factorization (adicBaseChangeMap B J π) (adicBaseChangeFst B J π)
    (completionPullbackIso_inv_app_comp_adicBaseChange B J π 𝓕 h n)

/-- **The level identification together with the tail of the level half of the square `hγ`, at
the base change.** The direct image along `π'` of the tail of `β'_n`, followed by the transport of
the `n`-th term of the completion of `𝓕'` and by `θ_n`, is the direct image of the pullback along
`g'` of the transport of the `n`-th term of the completion of `𝓕`, followed by the inverse of the
degree-zero flat base change at the level.

This is `Stacks.Algebraization.comp_eq_of_factorizations_right` at
`Stacks.Algebraization.map_comp_map_comp_adicBaseChange`, instantiated at the transport
`Stacks.Algebraization.comap_comap_adicBaseChangeMap`, and at the tail
`Stacks.Algebraization.eqToHom_comp_adicBaseChangeLevelComparison`. Together they are
`Stacks.Algebraization.pushforward_map_comp_of_factorizations` at this base change; they are two
declarations because the transport can be a binder in the first and not in the second. -/
public theorem pushforward_map_comp_adicBaseChange (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          (((ObjectProperty.ι _).mapIso
                (completionPullbackIso (adicBaseChangeFst B J π)
                  ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
              completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
                ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app (op n)) ≫
        (eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (adicBaseChangeCoherent B J π 𝓕) n) ≫
          adicBaseChangeLevelComparison B J π 𝓕 n) =
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
          ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).map
            (eqToHom (completionFunctor_obj X' ((adicIdealSheaf B J).comap π) 𝓕 n))) ≫
        (adicBaseChangePushforwardIso B J π
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv :=
  comp_eq_of_factorizations_right (eqToHom_comp_adicBaseChangeLevelComparison B J π 𝓕 n)
    (map_comp_map_comp_adicBaseChange B J π 𝓕 (comap_comap_adicBaseChangeMap B J π).symm n)

/-- **The level half of the square `hγ`, at the base change.** The degree-zero base-change
comparison at the `n`-th term of `𝓕 ^∧` followed by the direct image along `π'` of the tail of
`β'_n`, then by the transport of the `n`-th term of the completion of `𝓕'` and by `θ_n`, is the
pullback along `g` of the transport of the `n`-th term of the completion of `𝓕`.

This is `Stacks.Algebraization.comp_comp_eq_of_factorizations` at
`Stacks.Algebraization.pushforward_map_comp_adicBaseChange` and
`…pushforwardBaseChange_comp_pushforward_map_adicBaseChange`, that is
`Stacks.Algebraization.pushforwardBaseChange_comp_of_factorizations` at this base change. The
composite on the left of `e' ≫ θ` is the intermediate morphism at which this half meets the unit
half `Stacks.Algebraization.unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app`. -/
public theorem pushforwardBaseChange_comp_adicBaseChange (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    (pushforwardBaseChange (adicBaseChange_isPullback B J π).w
            (((completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕).obj.obj (op n)) ≫
          (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
            (((ObjectProperty.ι _).mapIso
                  (completionPullbackIso (adicBaseChangeFst B J π)
                    ((adicIdealSheaf B J).comap π) 𝓕).symm ≪≫
                completionFunctorObjCongr (comap_comap_adicBaseChangeMap B J π).symm
                  ((pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕)).hom.app
              (op n))) ≫
        (eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (adicBaseChangeCoherent B J π 𝓕) n) ≫
          adicBaseChangeLevelComparison B J π 𝓕 n) =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
        (eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n)) :=
  comp_comp_eq_of_factorizations (pushforward_map_comp_adicBaseChange B J π 𝓕 n)
    (pushforwardBaseChange_comp_pushforward_map_adicBaseChange B J π 𝓕 n)

/-- **The square `hγ` at the base change, with both `γ`'s written out as the unit followed by a
direct image.** The unit of `(π')^* ⊣ (π')_*` at `g^*(𝒢_n)` followed by `π'_*(β'_n)`, then by the
transport of the `n`-th term of the completion of `𝓕'` and by `θ_n`, is the pullback along `g` of
the unit of `π^* ⊣ π_*` at `𝒢_n` followed by `π_*(β_n)` and by the transport of the `n`-th term of
the completion of `𝓕`.

This is `Stacks.Algebraization.comp_eq_map_comp_of_factorizations` at the unit half
`Stacks.Algebraization.unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app` and the level
half `Stacks.Algebraization.pushforwardBaseChange_comp_adicBaseChange`, which meet at the
intermediate morphism `pushforwardBaseChange w ((𝓕 ^∧)_n) ≫ π'_*(tail of β'_n)`; its data being
implicit, the chaining costs nothing beyond naming the two halves. -/
public theorem comp_eq_map_comp_adicBaseChange (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) (n : ℕ)
    [(idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent] :
    ((Scheme.Modules.pullbackPushforwardAdjunction (adicBaseChangeMap B J π)).unit.app
            ((Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj (G.obj.obj (op n))) ≫
          (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
            ((adicBaseChangeAlgebraizationIso B J π 𝓕 G β).hom.hom.app (op n))) ≫
        (eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (adicBaseChangeCoherent B J π 𝓕) n) ≫
          adicBaseChangeLevelComparison B J π 𝓕 n) =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app (G.obj.obj (op n)) ≫
            (Scheme.Modules.pushforward π).map (β.hom.hom.app (op n))) ≫
          eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n)) :=
  comp_eq_map_comp_of_factorizations (Scheme.Modules.pullback (adicCompletionSpecMap B J))
    (unit_comp_pushforward_adicBaseChangeAlgebraizationIso_app B J π 𝓕 G β n)
    (pushforwardBaseChange_comp_adicBaseChange B J π 𝓕 n)

/-- **The square `hγ` of the reduction, at the actual base change.** The comparisons

`ι : (π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` and
`θ_n : π'_*(𝓕' / ℐ' ⁿ⁺¹ 𝓕') ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`

carry the map `γ_n` of the situation over `Spec B ^∧` built from the base change
`Stacks.Algebraization.adicBaseChangeAlgebraizationIso` of `β` to the pullback along `g` of the
`γ_n` built from `β`.

Both `γ`'s are the unit of the adjunction followed by a direct image of a component of `β`, resp.
of `β'` (`Stacks.Coherent.directImageComparison_app`), so this is
`Stacks.Algebraization.comp_eq_map_comp_adicBaseChange` read through that description on each
side.

This is the last remaining binder of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeGamma`. -/
public theorem adicBaseChangeDirectImageComparison_square
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕) (n : ℕ) :
    (directImageComparison (adicBaseChangeMap B J π)
            ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
            ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G)
            (adicBaseChangeCoherent B J π 𝓕)
            (adicBaseChangeAlgebraizationIso B J π 𝓕 G β)).app (op n) ≫
        eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
          (adicBaseChangeCoherent B J π 𝓕) n) ≫
        adicBaseChangeLevelComparison B J π 𝓕 n =
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
        ((directImageComparison π (adicIdealSheaf B J) G 𝓕 β).app (op n) ≫
          eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n)) := by
  have : 𝓕.obj.IsCoherent := 𝓕.property
  have : 𝓕.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsCoherent :=
    (coherentAnnihilatedBy_idealPowerQuotient ((adicIdealSheaf B J).comap π) n 𝓕.obj
      𝓕.property).1
  have : (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  refine Eq.trans (congrArg (fun k => k ≫
      (eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
          (adicBaseChangeCoherent B J π 𝓕) n) ≫
        adicBaseChangeLevelComparison B J π 𝓕 n))
    (directImageComparison_app (adicBaseChangeMap B J π)
      ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G)
      (adicBaseChangeCoherent B J π 𝓕)
      (adicBaseChangeAlgebraizationIso B J π 𝓕 G β) (op n))) ?_
  exact (comp_eq_map_comp_adicBaseChange B J π 𝓕 G β n).trans
    (congrArg (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
      (congrArg (fun k => k ≫ eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n))
        (directImageComparison_app π (adicIdealSheaf B J) G 𝓕 β (op n)).symm))

/-! ### The second paragraph of Stacks 088B with `β'` built and `hδ` discharged -/

/-- **The second paragraph of the proof of Stacks 088B at the actual base change, with the
base-changed `β'` constructed and both squares proved.**

`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` leaves the
five binders `β'`, `𝒦`, `hc`, `hδ` and `hγ`. Here `β'` is
`Stacks.Algebraization.adicBaseChangeAlgebraizationIso`, the base change of `β`, `hδ` is
`Stacks.Algebraization.adicBaseChangeCompletedComparison_directImageQuotientComparison` and `hγ`
is `Stacks.Algebraization.adicBaseChangeDirectImageComparison_square`, so the only binders that
remain are `𝒦` and `hc` — the support datum and the isomorphy of the unit away from it, which
belong to the solution over `Spec B ^∧` and not to this paragraph. -/
public theorem exists_isDirectImageCharacterized_of_adicBaseChangeGamma
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    (𝒦 : (Spec (.of (AdicCompletion J B))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion J B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion J B)))
            ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (adicBaseChangeMap B J π)).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α :=
  exists_isDirectImageCharacterized_of_adicBaseChangeSquares B J π 𝓕 G β
    (adicBaseChangeAlgebraizationIso B J π 𝓕 G β) 𝒦 hc
    (adicBaseChangeCompletedComparison_directImageQuotientComparison B J π 𝓕)
    (adicBaseChangeDirectImageComparison_square B J π 𝓕 G β)

end Squares

end Stacks.Algebraization

end
