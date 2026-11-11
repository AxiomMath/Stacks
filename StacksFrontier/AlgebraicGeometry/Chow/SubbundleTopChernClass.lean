module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# Chern classes and sections: the class of a subbundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules. Dualising and taking relative
spectra of symmetric algebras gives the vector bundles `N' = Spec_X(Sym((𝒩')^∨))` and
`N = Spec_X(Sym(𝒩^∨))` with their projections `p' : N' ⟶ X` and `p : N ⟶ X`, and a canonical
morphism `i : N' ⟶ N` over `X`, which is a closed embedding. [Stacks, Tag 0FAA] says that for
`α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`.

This file constructs `i`, `p`, `p'` and states that equality in constant ranks, from two
named inputs. The tag itself, for arbitrary ranks and with no inputs assumed, is
`Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback` in
`StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.CanonicalFlatPullback`, and the closed
embedding is proved outright as `Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact`.

## Main definitions

* `Stacks.Chow.dualVectorBundle`, `Stacks.Chow.dualVectorBundleToBase` — the vector bundle
  `𝐕(𝒩^∨) = Spec_X(Sym(𝒩^∨))` of a finite locally free module `𝒩` and its projection to `X`.
  These are `AlgebraicGeometry.Scheme.Modules.vectorBundle` and `vectorBundleToBase` of
  `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, with the quasi-coherence of the dual
  supplied from finite local freeness.
* `Stacks.Chow.subbundleEmbedding` — **the morphism `i : N' ⟶ N` of the tag**, namely
  `𝐕` applied to the dual `𝒩^∨ ⟶ (𝒩')^∨` of the given inclusion.
* `Stacks.Chow.VectorBundleEpiClosedImmersion` — the general input the tag's closed embedding
  needs: a surjection of quasi-coherent modules induces a closed immersion of the associated
  vector bundles.
* `Stacks.Chow.TopChernCapFlatPullbackOfBundle` — [Stacks, Tag 02U8] for the top Chern class of
  `ℰ` along the projection `p`: the cap product commutes with `p^*`.
* `Stacks.Chow.SubbundleChernCapStep` — the step the source takes from [Stacks, Tag 0FA9]:
  `i_*(p')^*α = c_top(p^*ℰ) ∩ p^*α` in `CH_*(N)`.

## Main results

* `Stacks.Chow.subbundleEmbedding_comp_dualVectorBundleToBase` and
  `Stacks.Chow.subbundleEmbedding_comp_base` — `i` is a morphism over `X`, so `i ≫ p = p'`.
* `Stacks.Chow.epi_dualMap_of_subbundleShortExact` — the dual `𝒩^∨ ⟶ (𝒩')^∨` of the inclusion
  is surjective. This is where the short exact sequence enters the construction of `i`.
* `Stacks.Chow.isClosedImmersion_subbundleEmbedding` — `i` is a closed embedding, from that
  surjectivity and `Stacks.Chow.VectorBundleEpiClosedImmersion`; the closed embedding is proved
  without that input as `Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact`.
* `Stacks.Chow.subbundleRank_add` and `Stacks.Chow.subbundleDegree_eq` — the rank of `𝒩` is the
  sum of the ranks of `𝒩'` and `ℰ`, and the two sides of the tag's equality therefore sit in the
  same Chow degree.
* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernCap` — the equality
  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)` in `CH_{k+r'}(N)` in constant ranks, from the two steps
  `hstep` and `hflat`. The tag is proved in general as
  `Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback`.

## Implementation notes

### Where the short exact sequence is used

In two places, both load-bearing.

* The morphism `i` is a *closed* embedding only because `𝒩^∨ ⟶ (𝒩')^∨` is surjective, which is
  the content of [Stacks, Tag 0FV8] for the given sequence; it is
  `Stacks.AlgebraicGeometry.ReflexiveModules.epi_dualMap_of_shortExact`, applied in
  `Stacks.Chow.epi_dualMap_of_subbundleShortExact`. Without it there is no `i_*` and the tag's
  equality cannot even be written down.
* The ranks satisfy `r = r' + rank(ℰ)`, by
  `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, and that is exactly what makes the
  two sides of the equality live in the same Chow group: the left-hand side is a class of degree
  `k + r'` and the right-hand side one of degree `(k - rank ℰ) + r`. The transport between the
  two degrees is `Stacks.Chow.subbundleDegree_eq`, which is proved from the sequence.

Rank additivity is read at a point of `X`, as
`AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact` is, so a point of `X` is an argument of
the statements that use it. On an empty `X` the ranks are unconstrained by the sequence and the
two sides of the equality have no common degree, so this is not a restriction of the tag but the
hypothesis under which the equality is a statement at all.

### Constant ranks

The ranks of `𝒩'`, `𝒩` and `ℰ` are assumed constant, which is the case the source reduces to in
the first line of its proof: `c_top(ℰ)` is by definition (Stacks 0FA4,
`Stacks.Chow.topChernClassOfInvertible`) assembled from the `r`-th Chern classes of the
restrictions of `ℰ` to the loci where its rank is `r`, so a module of non-constant rank is handled
by that decomposition and on each piece the rank is constant. For non-constant ranks the displayed
equality has no single Chow degree, which is why `Stacks.Chow.topChernClassOfInvertible` is
valued in the *completed* bivariant group of Stacks 0FE0.

### The cap product with `c_top(ℰ)`

For a module of constant rank `e` the top Chern class is `c_e(ℰ)`, and the cap product with it is
`Stacks.Chow.HigherChernCapRule` evaluated at the top index `Fin.last e`, exactly as in the
statement of [Stacks, Tag 0FA9] for a cap product rule
(`Stacks.Chow.TopChernCapEqZeroScheme` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection`). That rule is the standing parameter of
this directory for `chernClassCapOnChow`. The cap products with the higher Chern classes are
constructed as `Stacks.Chow.GenuineChern.chernCap` (Stacks 02U6), and their commutation with Gysin
maps, Stacks 0B7G, is `Stacks.Chow.GenuineChern.chernCap_gysin`; the statements of this file are
written against an arbitrary rule, of which `Stacks.Chow.GenuineChern.chernCap` is one, as in every
other file of this directory.

The same is true of [Stacks, Tag 02U8], which is formalized as
`Stacks.Chow.isChernCapFamily_flatPullback`: that statement is about the families
`Stacks.Chow.IsChernCapFamily` characterized by the projective bundle relation of Stacks 02U6,
and a `Stacks.Chow.HigherChernCapRule` is not one of those families by definition. So the
flat-pullback compatibility of the cap product has to be assumed again at the spelling used here;
that is `Stacks.Chow.TopChernCapFlatPullbackOfBundle`.

### What is assumed, and why

The source's proof runs: `p^*ℰ` carries a canonical global section `s` whose vanishing scheme is
`N' ⊆ N`; for an integral closed subscheme `Y ⊆ X` one has `p^*[Y] = [p^{-1}Y]` and
`(p')^*[Y] = [(p')^{-1}Y]`, and `(p')^{-1}Y ⟶ p^{-1}Y` is a regular immersion cut out by the
restriction of `s`; so [Stacks, Tag 0FA9] gives `(p')^*[Y] = c_{r-r'}(p^*ℰ) ∩ p^*[Y]` in
`CH_*(N)`, which finishes the argument. Of those ingredients this repository has none: the
canonical section of `p^*ℰ` is not constructed, the flat-pullback formula for the cycle of a
prime cycle is not available, and [Stacks, Tag 0FA9] itself is formalized only with its reduced case
assumed and only at rank one (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection`). The displayed equation the source
derives from Tag 0FA9 is therefore carried here as the named hypothesis
`Stacks.Chow.SubbundleChernCapStep`, and the passage from it to the tag's own equality — which is
the flat-pullback compatibility of the Chern classes, [Stacks, Tag 02U8] — is the named
hypothesis `Stacks.Chow.TopChernCapFlatPullbackOfBundle`. The two are different statements: the
first caps on `N` with `p^*ℰ`, the second moves the cap product past `p^*`, and composing them is
what the theorem below does.

That `i` is a closed immersion is deduced, not assumed: what is assumed is the general lemma
`Stacks.Chow.VectorBundleEpiClosedImmersion` that a surjection of quasi-coherent modules gives a
closed immersion of vector bundles, which is not in this repository, and the short exact sequence
supplies its hypothesis for the dual of the inclusion.

Flatness, local finite type and the relative dimension of the two bundle projections are carried
as hypotheses, as [Stacks, Tag 02TY] is not in this repository; the same is done, for the same
reason and at the same morphism, by
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleGysinClass`. The two
instances of [Stacks, Tag 02S1] that flat pullback on Chow groups needs are quantified over,
exactly as they are in the fields of `Stacks.Chow.BivariantClass`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### Instances the vector bundle of a dual needs -/

/-- The dual of a finite locally free module on a scheme is quasi-coherent: such a module is of
finite presentation, and the dual of a module of finite presentation is quasi-coherent. This is
what lets the vector bundle `𝐕(𝒩^∨)` be formed. -/
@[sga "3 III 0.6" "special case"]
instance isQuasicoherent_dualSheaf_of_isFiniteLocallyFree {X : Scheme.{u}} (N : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    (dualSheaf N).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.InternalHomModules.isQuasicoherent_dualSheaf N
    (AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree N h)

/-- **[Stacks, Tag 01CK] at the `AlgebraicGeometry.Scheme.Modules` spelling of the category of
`𝒪_X`-modules.** This is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf`,
restated for a module written as a term of `X.Modules`; that spelling is a `def` with its own
category structure, so instance search does not cross between the two. -/
instance isQuasicoherent_symmetricAlgebraSheaf_modules {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      (Scheme.Modules.symmetricAlgebraSheaf X E) :=
  Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf X E

/-- **[Stacks, Tag 02U9], rank preservation.** The pullback of a finite locally free module of
constant rank `r` is again of rank `r`. This is
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback` as an instance, so that the cap product
with the Chern classes of `p^*ℰ` can be written without supplying it by hand. -/
instance isFiniteLocallyFreeOfRank_pullback_obj {Y X : Scheme.{u}} (g : Y ⟶ X) (E : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r

/-- A heterogeneous equality of Chow classes in two degrees known to be equal is an equality
after transport along that equality of degrees. -/
private theorem eq_eq_mp_of_heq {F : ℤ → Type u} {i j : ℤ} (h : i = j) {a : F j} {b : F i}
    (hab : HEq a b) : a = Eq.mp (congrArg F h) b := by
  subst h
  exact eq_of_heq hab

/-! ### The vector bundle of a dual, and the embedding of a subbundle -/

section Embedding

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The vector bundle `N = 𝐕(𝒩^∨) = Spec_X(Sym(𝒩^∨))` of a finite locally free module `𝒩`**,
the scheme over `X` that [Stacks, Tag 0FAA] is about. It is
`AlgebraicGeometry.Scheme.Modules.vectorBundle` of the dual sheaf, the dual being quasi-coherent
by `Stacks.Chow.isQuasicoherent_dualSheaf_of_isFiniteLocallyFree`. -/
@[ega "II 1.7.8" "special case", sga "5 VII 4.6"]
def dualVectorBundle : Scheme.{u} :=
  Scheme.Modules.vectorBundle X (dualSheaf N)

/-- **The projection `p : 𝐕(𝒩^∨) ⟶ X`** of the vector bundle of the dual of `𝒩`. -/
def dualVectorBundleToBase : dualVectorBundle N ⟶ X :=
  Scheme.Modules.vectorBundleToBase X (dualSheaf N)

/-- **The morphism `i : N' ⟶ N` of [Stacks, Tag 0FAA]**: the morphism of vector bundles over `X`
induced by the dual `𝒩^∨ ⟶ (𝒩')^∨` of an inclusion `𝒩' ⟶ 𝒩`, that is, the relative spectrum of
`Sym(𝒩^∨) ⟶ Sym((𝒩')^∨)`.

That it is a *closed* embedding is `Stacks.Chow.isClosedImmersion_subbundleEmbedding`, and it is
there that the short exact sequence of the tag is used. -/
def subbundleEmbedding (inc : N' ⟶ N) : dualVectorBundle N' ⟶ dualVectorBundle N :=
  (Scheme.Modules.vectorBundleMap X (dualMap inc)).left

/-- `i` is a morphism of schemes over `X`: `i ≫ p = p'`. -/
theorem subbundleEmbedding_comp_dualVectorBundleToBase (inc : N' ⟶ N) :
    subbundleEmbedding N' N inc ≫ dualVectorBundleToBase N = dualVectorBundleToBase N' :=
  Scheme.Modules.vectorBundleMap_left_comp X (dualMap inc)

/-- `i` is compatible with any morphism out of `X`, in particular with the structure morphism to
the base scheme of the Chow situation: `i ≫ (p ≫ q) = p' ≫ q`. -/
theorem subbundleEmbedding_comp_base {Y : Scheme.{u}} (q : X ⟶ Y) (inc : N' ⟶ N) :
    subbundleEmbedding N' N inc ≫ (dualVectorBundleToBase N ≫ q) =
      dualVectorBundleToBase N' ≫ q := by
  rw [← Category.assoc, subbundleEmbedding_comp_dualVectorBundleToBase]

/-- **[Stacks, Tag 0FV8] for the sequence of the tag**: the dual `𝒩^∨ ⟶ (𝒩')^∨` of the inclusion
of a short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free modules is surjective.
This is the surjection of symmetric algebras that makes `i : N' ⟶ N` a closed embedding. -/
theorem epi_dualMap_of_subbundleShortExact (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) : Epi (dualMap inc) :=
  epi_dualMap_of_shortExact inc pr w hseq.mono_f hseq.epi_g hseq.exact
    (inferInstance) (inferInstance) (inferInstance)

/-- **A surjection of quasi-coherent modules induces a closed immersion of the associated vector
bundles.** This is the general statement that a surjection of quasi-coherent algebra sheaves
gives a closed immersion of relative spectra, specialised to `Sym`. The closed embedding of
[Stacks, Tag 0FAA] does not need it: it is
`Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact`, a base change of a zero
section. -/
def VectorBundleEpiClosedImmersion : Prop :=
  ∀ {Y : Scheme.{u}} (F G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
    Epi f → IsClosedImmersion (Scheme.Modules.vectorBundleMap Y f).left

/-- **The closed embedding of the setup of [Stacks, Tag 0FAA], from
`Stacks.Chow.VectorBundleEpiClosedImmersion`.** Given a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free `𝒪_X`-modules, the canonical morphism
`i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` is a closed immersion.

The sequence is used through `Stacks.Chow.epi_dualMap_of_subbundleShortExact`: it makes the dual
`𝒩^∨ ⟶ (𝒩')^∨` surjective, and a surjection of modules gives a closed immersion of vector
bundles, which is the hypothesis `hci`. The same conclusion without `hci` is
`Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact`. -/
theorem isClosedImmersion_subbundleEmbedding (hci : VectorBundleEpiClosedImmersion.{u})
    (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) :
    IsClosedImmersion (subbundleEmbedding N' N inc) :=
  hci (dualSheaf N) (dualSheaf N') (dualMap inc)
    (epi_dualMap_of_subbundleShortExact N' N E inc pr w hseq)

end Embedding

/-! ### Additivity of the ranks, and the common Chow degree -/

section Rank

variable {X : Scheme.{u}} (N' N E : X.Modules) (r' r e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]

/-- The rank of `𝒩` is the sum of the ranks of `𝒩'` and `ℰ`, read at a point of `X`. This is
`AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact` for the sequence of the tag. -/
theorem subbundleRank_add (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) (x : X) : r = r' + e :=
  AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact (ShortComplex.mk inc pr w) hseq
    r' r e x

/-- **The two sides of the tag's equality sit in the same Chow degree.** The left-hand side
`i_*(p')^*α` of a class `α ∈ CH_k(X)` has degree `k + r'`, the right-hand side
`p^*(c_top(ℰ) ∩ α)` has degree `(k - e) + r`, and the short exact sequence makes them equal
because `r = r' + e`. -/
theorem subbundleDegree_eq (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) (x : X) (k : ℤ) :
    k - (e : ℤ) + (r : ℤ) = k + (r' : ℤ) := by
  have h := subbundleRank_add N' N E r' r e inc pr w hseq x
  omega

end Rank

/-! ### Stacks 0FAA -/

section ChernCap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules) (r' r e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  [LocallyOfFiniteType (dualVectorBundleToBase N')] [Flat (dualVectorBundleToBase N')]
  [LocallyOfFiniteType (dualVectorBundleToBase N)] [Flat (dualVectorBundleToBase N)]
  (hp' : AlgebraicGeometry.RelativeDimension (dualVectorBundleToBase N') r')
  (hp : AlgebraicGeometry.RelativeDimension (dualVectorBundleToBase N) r)
  (cap : HigherChernCapRule C e) (k : ℤ)

/-- **[Stacks, Tag 02U8] for the top Chern class of `ℰ` along the projection `p : N ⟶ X`**: the
cap product with `c_top(ℰ) = c_e(ℰ)` commutes with flat pullback along `p`.

This is condition (2) of [Stacks, Tag 0B76] for the Chern classes, at the spelling of
`Stacks.Chow.HigherChernCapRule`; `Stacks.Chow.IdentityCapRule.FlatNaturality` is the library's
form of the same statement, differing only in how the structure morphism of the test scheme is
written. It is a heterogeneous equality because the flat pullback of a class of degree `k` has
degree `k + r`, so the two sides sit in degrees `(k + r) - e` and `(k - e) + r`, which are the
same integer and not the same term. Both instances of [Stacks, Tag 02S1] are quantified over, as
they are in the fields of `Stacks.Chow.BivariantClass`. -/
def TopChernCapFlatPullbackOfBundle : Prop :=
  ∀ (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp (k - (e : ℤ)))
    (α : chowGroup C sX k),
    HEq
      (cap (dualVectorBundleToBase N ≫ sX)
        ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) (k + (r : ℤ)) (Fin.last e)
        (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
          hp k hfac α))
      (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp
        (k - (e : ℤ)) hfacp (cap sX E k (Fin.last e) α))

/-- **The step the source of [Stacks, Tag 0FAA] takes from [Stacks, Tag 0FA9]**: in `CH_*(N)`

  `i_*(p')^*α = c_top(p^*ℰ) ∩ p^*α`.

The source obtains it as follows: `p^*ℰ` carries a canonical global section `s` whose vanishing
scheme is `N' ⊆ N`; for an integral closed subscheme `Y ⊆ X` the preimages `p^{-1}Y` and
`(p')^{-1}Y` are integral with the expected `δ`-dimensions, so that `p^*[Y] = [p^{-1}Y]` and
`(p')^*[Y] = [(p')^{-1}Y]`, and the restriction of `s` to `p^{-1}Y` cuts out `(p')^{-1}Y` by a
regular sequence; Tag 0FA9 then gives the displayed equality. None of those ingredients is in
this repository — the canonical section of `p^*ℰ` is not constructed, and Tag 0FA9 is formalized
only
with its reduced case assumed and only at rank one — so the equality is carried as a hypothesis.

It is not the tag's own equality: the cap product here is taken on the test scheme `N` with the
pulled-back module `p^*ℰ`, whereas the tag's equality has it on `X` with `ℰ`, and the passage
between the two is [Stacks, Tag 02U8], `Stacks.Chow.TopChernCapFlatPullbackOfBundle`. -/
def SubbundleChernCapStep (inc : N' ⟶ N)
    (hclosed : IsClosedImmersion (subbundleEmbedding N' N inc)) : Prop :=
  letI := hclosed
  ∀ (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl r' hp' k)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp k)
    (α : chowGroup C sX k),
    HEq
      (chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
        (flatPullbackChow C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl
          r' hp' k hfac' α))
      (cap (dualVectorBundleToBase N ≫ sX)
        ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) (k + (r : ℤ)) (Fin.last e)
        (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
          hp k hfac α))

/-- **[Stacks, Tag 0FAA] in constant ranks, from the source's two steps.** The tag itself, for
arbitrary ranks and with nothing assumed, is
`Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback`.
Let `(S, δ)` be the base situation of chapter 42, let `X` be locally
of finite type over `S` and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally
free `𝒪_X`-modules, of constant ranks `r'`, `r` and `e`. Let
`i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` be the canonical closed embedding and
`p' : N' ⟶ X`, `p : N ⟶ X` the structure morphisms. Then for `α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`

in `CH_{k+r'}(N)`, the two degrees `k + r'` and `(k - e) + r` agreeing because `r = r' + e`.

All of `i`, `p`, `p'` are the canonical constructed morphisms: `p` and `p'` are
`Stacks.Chow.dualVectorBundleToBase`, i.e. `AlgebraicGeometry.Scheme.Modules.vectorBundleToBase`
of the dual sheaves, and `i` is `Stacks.Chow.subbundleEmbedding`, i.e.
`AlgebraicGeometry.Scheme.Modules.vectorBundleMap` of the dual of the inclusion. The short exact
sequence is consumed twice: it makes `i` a closed immersion, through
`Stacks.Chow.epi_dualMap_of_subbundleShortExact`, and it gives the degree identity
`Stacks.Chow.subbundleDegree_eq` without which the equality is not even a well-formed statement.

The two named hypotheses are the source's own two steps: `hstep` is the equality Tag 0FA9 gives
on `N` for the canonical section of `p^*ℰ`, and `hflat` is the flat-pullback compatibility of the
Chern classes, Tag 02U8. See the implementation notes of this file for what each of them needs
and why it is not available here. -/
theorem subbundleEmbedding_pushforward_flatPullback_eq_topChernCap
    (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hci : VectorBundleEpiClosedImmersion.{u}) (x : X)
    (hstep : SubbundleChernCapStep C sX N' N E r' r e hp' hp cap k inc
      (isClosedImmersion_subbundleEmbedding N' N E hci inc pr w hseq))
    (hflat : TopChernCapFlatPullbackOfBundle C sX N E r e hp cap k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl r' hp' k)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C
      (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r hp (k - (e : ℤ)))
    (α : chowGroup C sX k) :
    letI := isClosedImmersion_subbundleEmbedding N' N E hci inc pr w hseq
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
        (flatPullbackChow C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl
          r' hp' k hfac' α) =
      Eq.mp (congrArg (chowGroup C (dualVectorBundleToBase N ≫ sX))
          (subbundleDegree_eq N' N E r' r e inc pr w hseq x k))
        (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
          hp (k - (e : ℤ)) hfacp (cap sX E k (Fin.last e) α)) :=
  eq_eq_mp_of_heq (subbundleDegree_eq N' N E r' r e inc pr w hseq x k)
    ((hstep hfac' hfac α).trans (hflat hfac hfacp α))

end ChernCap

end Stacks.Chow

end
