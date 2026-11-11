module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass

/-!
# The Gysin class of a subbundle of a virtual normal bundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal sheaf `𝒩` in the
sense of Stacks 0FBQ, and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_Z`-modules such that the surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` of the virtual normal sheaf factors as `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` through a
surjection `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}`, so that `𝒩'` is a virtual normal sheaf too. **Stacks 0FBL**
asserts that then

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`

as bivariant classes.

The proof follows the source: the surjection `𝒩^∨ ⟶ (𝒩')^∨` gives a closed immersion `j : N' ⟶ N`
of the vector bundles, the factorization of `σ` through `σ'` makes the closed immersion `C_ZX ⟶ N`
of the normal cone factor as `C_ZX ⟶ N' ⟶ N`, and the identity follows from Stacks 0FAA. It is
carried out against the characterizing relation `Stacks.Chow.IsVirtualNormalGysinClass` of Stacks
0FBK, which reads `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C` on each bundle: the factorization of `ι`
turns the right-hand side for `𝒩` into `j_*` of the one for `𝒩'`, Stacks 0FAA moves `j_*` past the
two flat pullbacks at the cost of `c_top(ℰ)`, and injectivity of `p^*` (Stacks 02TY) divides.

## Main definitions

* `Stacks.Chow.subbundleTestBaseChange` — the base change `N' ×_X T ⟶ N ×_X T` along a test
  scheme of a morphism `j : N' ⟶ N` of schemes over `Z`.
* `Stacks.Chow.subbundleTestPushforward` — proper pushforward on Chow groups along that base
  change, for `j` a closed immersion.
* `Stacks.Chow.subbundleTopChernCap` — the cap product with the top Chern class `c_top(ℰ)` on the
  base change `Z ×_X T`, at the degrees of the Gysin class of `𝒩'`.
* `Stacks.Chow.SubbundleGysinFactorization` — the geometric consequence of the factorization of
  `σ` through `σ'` that the proof uses: `ι_* ∘ j^* ∘ C` for `𝒩` is `j_*` of the one for `𝒩'`.
* `Stacks.Chow.SubbundleGysinTopChernStep` — **Stacks 0FAA** for the base changes of the two
  bundle projections along a test scheme.

## Main results

* `Stacks.Chow.isPullback_subbundleTestBaseChange` — the base change of `j : N' ⟶ N` along a test
  scheme is a base change of `j` in the categorical sense, so that closed immersions,
  flatness and the rest descend to it.
* `Stacks.Chow.subbundleVirtualNormalDegree_eq` — the two sides of the tag's identity sit in the
  same Chow degree, because the short exact sequence makes `m = m' + e`.
* `Stacks.Chow.virtualNormalGysinCap_eq_topChernCap_comp` — **Stacks 0FBL**, on cap operations:
  for every test scheme, degree and class,
  `c(Z ⟶ X, 𝒩) ∩ α = c_top(ℰ) ∩ (c(Z ⟶ X, 𝒩') ∩ α)`.
* `Stacks.Chow.virtualNormalGysinClass_eq_of_isTopChernComposition` — **Stacks 0FBL**, as an
  equality in `A^m(Z ⟶ X)`: a bivariant class whose cap operation is cap with
  `c(Z ⟶ X, 𝒩')` followed by `c_top(ℰ)` *is* `c(Z ⟶ X, 𝒩)`.

## Implementation notes

### The two bundles and the embedding are data

The bundle projections `q : N ⟶ Z`, `q' : N' ⟶ Z` enter through
`Stacks.Chow.VirtualNormalBundleProjection`, which records a flat morphism of relative dimension
the rank, and the embedding `j : N' ⟶ N` is a closed immersion subject to `j ≫ q = q'`. The
canonical morphisms `Stacks.Chow.subbundleEmbedding` and `Stacks.Chow.dualVectorBundleToBase`
satisfy these hypotheses (`Stacks.Chow.isClosedImmersion_subbundleEmbedding`,
`Stacks.Chow.subbundleEmbedding_comp_dualVectorBundleToBase`).

### The short exact sequence and the factorization of `σ`

* The sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` gives, through `Stacks.Chow.subbundleRank_add`, the relation
  `m = m' + e` between the three ranks, which puts the two sides of the conclusion in the same Chow
  group: the left-hand side has degree `k - m` and the right-hand side `(k - m') - e`. This is
  `Stacks.Chow.subbundleVirtualNormalDegree_eq`.
* The factorization `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` is the hypothesis `hsigma`, at the sheaf level.
  The proof uses its geometric consequence, that the closed immersion `C_ZX ⟶ N` factors through
  `N'` and hence `ι_* ∘ j^* ∘ C = j_* ∘ (ι'_* ∘ j^* ∘ C)`, which is the hypothesis
  `Stacks.Chow.SubbundleGysinFactorization`: a statement about the classes `E` and `E'` alone.

### The step of Stacks 0FAA

`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernCap` gives
`j_* (p')^* α = p^* (c_top(ℰ) ∩ α)` for the canonical bundles `Spec_W(Sym(-))` of a short exact
sequence of finite locally free modules on a scheme `W`. The proof needs this identity on
`Z ×_X T` for each test scheme `g : T ⟶ X`, at the base changes of `q`, `q'` and `j`; it is the
hypothesis `Stacks.Chow.SubbundleGysinTopChernStep`, a formula in `A_*(N ×_X T)`. The hypothesis
`hexcess` of `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass_excess` has the same shape.

### The flat pullbacks

The flat pullbacks are `Stacks.Chow.bundleFlatPullback`, the flat pullback along
`Stacks.Chow.bundleTestBaseChange`, which `Stacks.Chow.isPullback_bundleTestBaseChange` identifies
as a base change of the bundle projection. Only the injectivity of that pullback is assumed, the
half of Stacks 02TY that the division defining the class rests on.

### The degree of `E` and `E'`

Both have degree `0`, the value they have in the source: the flat pullback raises degrees by the
rank, so it takes `A_{k-m}` to `A_k`, and the relation of Stacks 0FBK types its target as
`A_{k-e}`.

### The cap product with `c_top(ℰ)`

The ranks of `𝒩'`, `𝒩` and `ℰ` are constant, the case the source reduces to: `c_top(ℰ)` is by
definition (Stacks 0FA4, `Stacks.Chow.topChernClassOfInvertible`) assembled from the `r`-th
Chern classes of the restrictions of `ℰ` to the loci where its rank is `r`. For constant rank `e`
the top Chern class is `c_e(ℰ)`, and the cap product with it is a
`Stacks.Chow.HigherChernCapRule` evaluated at the top index `Fin.last e`, as in
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernCap`.

## References

* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The base change of a morphism of bundles along a test scheme -/

section BaseChange

variable {Z X N N' : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z) {q' : N' ⟶ Z}

/-- The base change `N' ×_X T ⟶ N ×_X T` along a test scheme `g : T ⟶ X` of a morphism
`j : N' ⟶ N` of schemes over `Z`, taken at the chosen pullbacks that
`Stacks.Chow.BivariantClass` uses: it is `j` on the first factor and the identity on the second.
-/
def subbundleTestBaseChange (j : N' ⟶ N) (hj : j ≫ q = q') {T : Scheme.{u}} (g : T ⟶ X) :
    pullback (q' ≫ i) g ⟶ pullback (q ≫ i) g :=
  pullback.lift (pullback.fst (q' ≫ i) g ≫ j) (pullback.snd (q' ≫ i) g) <| by
    rw [Category.assoc, ← Category.assoc j q i, hj]
    exact pullback.condition

/-- The base change of `j` along a test scheme followed by the first projection to `N` is the first
projection to `N'` followed by `j`. -/
@[simp]
theorem subbundleTestBaseChange_fst (j : N' ⟶ N) (hj : j ≫ q = q') {T : Scheme.{u}} (g : T ⟶ X) :
    subbundleTestBaseChange i q j hj g ≫ pullback.fst (q ≫ i) g =
      pullback.fst (q' ≫ i) g ≫ j :=
  pullback.lift_fst _ _ _

/-- The base change of `j` along a test scheme commutes with the second projections to `T`. -/
@[simp]
theorem subbundleTestBaseChange_snd (j : N' ⟶ N) (hj : j ≫ q = q') {T : Scheme.{u}} (g : T ⟶ X) :
    subbundleTestBaseChange i q j hj g ≫ pullback.snd (q ≫ i) g =
      pullback.snd (q' ≫ i) g :=
  pullback.lift_snd _ _ _

/-- The base change of `j : N' ⟶ N` along a test scheme is a base change of `j` in the
categorical sense: the square with `N' ×_X T ⟶ N'`, `N' ×_X T ⟶ N ×_X T`, `j` and `N ×_X T ⟶ N`
is cartesian, that is `N' ×_N (N ×_X T) = N' ×_X T`. -/
theorem isPullback_subbundleTestBaseChange (j : N' ⟶ N) (hj : j ≫ q = q') {T : Scheme.{u}}
    (g : T ⟶ X) :
    IsPullback (pullback.fst (q' ≫ i) g) (subbundleTestBaseChange i q j hj g) j
      (pullback.fst (q ≫ i) g) := by
  have hcomp : j ≫ q ≫ i = q' ≫ i := by rw [← Category.assoc, hj]
  have hs : IsPullback (pullback.fst (q' ≫ i) g)
      (subbundleTestBaseChange i q j hj g ≫ pullback.snd (q ≫ i) g) (j ≫ q ≫ i) g := by
    rw [hcomp, subbundleTestBaseChange_snd]
    exact IsPullback.of_hasPullback (q' ≫ i) g
  exact hs.of_bot (subbundleTestBaseChange_fst i q j hj g).symm
    (IsPullback.of_hasPullback (q ≫ i) g)

/-- The base change of a closed immersion of bundles along a test scheme is a closed
immersion. -/
theorem isClosedImmersion_subbundleTestBaseChange (j : N' ⟶ N) [IsClosedImmersion j]
    (hj : j ≫ q = q') {T : Scheme.{u}} (g : T ⟶ X) :
    IsClosedImmersion (subbundleTestBaseChange i q j hj g) :=
  MorphismProperty.of_isPullback (isPullback_subbundleTestBaseChange i q j hj g)
    (P := @IsClosedImmersion) inferInstance

/-- The base change of `j` along a test scheme is a morphism over the base of chapter 42. -/
theorem subbundleTestBaseChange_comp_structureMorphism {C : ChowSituation.{u}} (sZ : Z ⟶ C.S)
    (sN : N ⟶ C.S) (sN' : N' ⟶ C.S) (hq : q ≫ sZ = sN) (hq' : q' ≫ sZ = sN') (j : N' ⟶ N)
    (hj : j ≫ q = q') {T : Scheme.{u}} (g : T ⟶ X) :
    subbundleTestBaseChange i q j hj g ≫ (pullback.fst (q ≫ i) g ≫ sN) =
      pullback.fst (q' ≫ i) g ≫ sN' := by
  have hjs : j ≫ sN = sN' := by rw [← hq, ← Category.assoc, hj, hq']
  rw [← Category.assoc, subbundleTestBaseChange_fst, Category.assoc, hjs]

end BaseChange

/-! ### The ranks of a short exact sequence of virtual normal bundles -/

/-- **The two sides of Stacks 0FBL sit in the same Chow degree.** For a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free modules of constant ranks `m'`, `m` and `e`, the
cap product with `c(Z ⟶ X, 𝒩)` lands in degree `k - m` and the composite of the cap product with
`c(Z ⟶ X, 𝒩')` and the one with `c_top(ℰ)` in degree `(k - m') - e`; the sequence makes the two
equal, because `m = m' + e`. -/
theorem subbundleVirtualNormalDegree_eq {Z X N N' : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]
    {q : N ⟶ Z} [LocallyOfFiniteType q] {q' : N' ⟶ Z} [LocallyOfFiniteType q'] {m m' e : ℕ}
    (P : VirtualNormalBundleProjection i q m) (P' : VirtualNormalBundleProjection i q' m')
    (Eb : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
    (inc : P'.normalBundle.bundle ⟶ P.normalBundle.bundle)
    (pr : P.normalBundle.bundle ⟶ Eb) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) (x : Z) (k : ℤ) :
    (k - (m' : ℤ)) - (e : ℤ) = k - (m : ℤ) := by
  have := P.rank
  have := P'.rank
  have h := subbundleRank_add P'.normalBundle.bundle P.normalBundle.bundle Eb m' m e inc pr w
    hseq x
  omega


/-! ### Stacks 0FBL -/

/-- Proper pushforward on Chow groups along the base change `N' ×_X T ⟶ N ×_X T` of a closed
immersion `j : N' ⟶ N` of schemes over `Z`. This is the `j_*` of Stacks 0FAA, base changed to a
test scheme. -/
def subbundleTestPushforward (C : ChowSituation.{u}) {Z X N N' : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (sN' : N' ⟶ C.S)
    [LocallyOfFiniteType sN'] (i : Z ⟶ X) (q : N ⟶ Z) (q' : N' ⟶ Z) (hq : q ≫ sZ = sN)
    (hq' : q' ≫ sZ = sN') (j : N' ⟶ N) [IsClosedImmersion j] (hj : j ≫ q = q')
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst (q' ≫ i) g ≫ sN') k →+
      chowGroup C (pullback.fst (q ≫ i) g ≫ sN) k :=
  letI := isClosedImmersion_subbundleTestBaseChange i q j hj g
  chowPushforwardOfIsClosedImmersion C (pullback.fst (q' ≫ i) g ≫ sN')
    (pullback.fst (q ≫ i) g ≫ sN) (subbundleTestBaseChange i q j hj g)
    (subbundleTestBaseChange_comp_structureMorphism i q sZ sN sN' hq hq' j hj g) k

/-- The cap product with the top Chern class `c_top(ℰ) = c_e(ℰ)` on the base change `Z ×_X T` of
`Z` along a test scheme `g : T ⟶ X`, at the degrees of the Gysin class of `𝒩'`: it takes
`A_{k-m'}(Z ×_X T)` to `A_{(k-m')-e}(Z ×_X T)`. The module is the pullback of `ℰ` to `Z ×_X T`,
and the operation is the Chern cap rule at its top index. -/
def subbundleTopChernCap (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (i : Z ⟶ X) (m' e : ℕ) (Eb : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
    (cap : HigherChernCapRule C e) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ sZ) (k - (m' : ℤ)) →+
      chowGroup C (pullback.fst i g ≫ sZ) ((k - (m' : ℤ)) - (e : ℤ)) :=
  cap (pullback.fst i g ≫ sZ) ((Scheme.Modules.pullback (pullback.fst i g)).obj Eb)
    (k - (m' : ℤ)) (Fin.last e)

/-- **The geometric consequence of the factorization of `σ` through `σ'`.** The class
`ι_* ∘ j^* ∘ C` attached to `𝒩` is the pushforward along `j : N' ⟶ N` of the one attached to
`𝒩'`: capping with `E` is capping with `E'` and pushing forward along the base change of `j`.

In the source this is the factorization `C_ZX ⟶ N' ⟶ N` of the closed immersion of the normal
cone, which the hypothesis `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` of Stacks 0FBL provides, followed by
functoriality of proper pushforward. -/
def SubbundleGysinFactorization (C : ChowSituation.{u}) (G : GysinSystem C)
    {Z X N N' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (sN' : N' ⟶ C.S)
    [LocallyOfFiniteType sN'] (i : Z ⟶ X) [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)
    (q : N ⟶ Z) [LocallyOfFiniteType q] (q' : N' ⟶ Z) [LocallyOfFiniteType q']
    (hq : q ≫ sZ = sN) (hq' : q' ≫ sZ = sN') (j : N' ⟶ N) [IsClosedImmersion j]
    (hj : j ≫ q = q')
    (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq hi) 0)
    (E' : BivariantClass C G sN' sX (q' ≫ i) (comp_comp_structureMorphism_eq hq' hi) 0) :
    Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k),
    E.cap g k α =
      subbundleTestPushforward C sZ sN sN' i q q' hq hq' j hj g (k - (0 : ℤ)) (E'.cap g k α)

/-- **Stacks 0FAA for the base changes of the two bundle projections along a test scheme.** With
`p : N ×_X T ⟶ Z ×_X T` and `p' : N' ×_X T ⟶ Z ×_X T` the base changes of the two bundle
projections and `j` the base change of the embedding,

  `j_* (p')^* β = p^* (c_top(ℰ) ∩ β)`

in `A_*(N ×_X T)`, the two degrees agreeing because `m = m' + e`. -/
def SubbundleGysinTopChernStep (C : ChowSituation.{u}) {Z X N N' : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (sN' : N' ⟶ C.S)
    [LocallyOfFiniteType sN'] (i : Z ⟶ X) [IsImmersion i] (q : N ⟶ Z) [LocallyOfFiniteType q]
    (q' : N' ⟶ Z) [LocallyOfFiniteType q'] (hq : q ≫ sZ = sN) (hq' : q' ≫ sZ = sN')
    (j : N' ⟶ N) [IsClosedImmersion j] (hj : j ≫ q = q') (m m' e : ℕ) (Eb : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
    (cap : HigherChernCapRule C e) (hdesc : FlatPullbackDescends C)
    (P : VirtualNormalBundleProjection i q m) (P' : VirtualNormalBundleProjection i q' m') :
    Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (hdeg : (k - (m' : ℤ)) - (e : ℤ) = k - (m : ℤ))
    (β : chowGroup C (pullback.fst i g ≫ sZ) (k - (m' : ℤ))),
    subbundleTestPushforward C sZ sN sN' i q q' hq hq' j hj g (k - (0 : ℤ))
        (bundleFlatPullback C sZ sN' i q' hq' m' P'.flat P'.relativeDimension hdesc g k β) =
      bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc g k
        (chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ) hdeg
          (subbundleTopChernCap C sZ i m' e Eb cap g k β))

section Main

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X N N' : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (sN' : N' ⟶ C.S) [LocallyOfFiniteType sN']
  (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)
  (q : N ⟶ Z) [LocallyOfFiniteType q] (q' : N' ⟶ Z) [LocallyOfFiniteType q']
  (hq : q ≫ sZ = sN) (hq' : q' ≫ sZ = sN') (j : N' ⟶ N) [IsClosedImmersion j]
  (hj : j ≫ q = q') (m m' e : ℕ) (Eb : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (cap : HigherChernCapRule C e) (hdesc : FlatPullbackDescends C)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq hi) 0)
  (E' : BivariantClass C G sN' sX (q' ≫ i) (comp_comp_structureMorphism_eq hq' hi) 0)
  (P : VirtualNormalBundleProjection i q m) (P' : VirtualNormalBundleProjection i q' m')
  (inc : P'.normalBundle.bundle ⟶ P.normalBundle.bundle) (pr : P.normalBundle.bundle ⟶ Eb)

/-- **Stacks 0FBL**, on cap operations. Let `(S, δ)` be the base situation of chapter 42, let `X`
be locally of finite type over `S`, let `i : Z ⟶ X` be a closed subscheme with virtual normal
sheaf `𝒩` of constant rank `m`, and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite
locally free `𝒪_Z`-modules of constant ranks `m'`, `m` and `e` whose inclusion dualizes to a
factorization `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)` of the conormal surjection of `𝒩` through that of `𝒩'`.
Then, for the classes `c = c(Z ⟶ X, 𝒩)` and `c' = c(Z ⟶ X, 𝒩')` of Stacks 0FBK,

  `c ∩ α = c_top(ℰ) ∩ (c' ∩ α)`

on every test scheme `g : T ⟶ X`, in every degree and for every `α ∈ A_k(T)`. Since a bivariant
class is determined by its cap operations (`Stacks.Chow.BivariantClass.ext`), this is the tag's
equality `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')` of bivariant classes; see
`Stacks.Chow.virtualNormalGysinClass_eq_of_isTopChernComposition`. -/
@[stacks 0FBL "c(Z -> X, N) = c_top(E) composed with c(Z -> X, N') for a short exact sequence
0 -> N' -> N -> E -> 0 of finite locally free O_Z-modules of constant ranks m', m, e whose
conormal surjection factors. The short exact sequence IS consumed: it gives m = m' + e, which
is what puts the two sides in the same Chow group. Both classes are the ones CHARACTERIZED by
Tag 0FBK, neither being constructed in this repository, and the composite is spelled by the
top Chern cap rule at `Fin.last e` as Tag 0FAA spells it. CARRIED: Tag 0FAA at the
base changes of the two bundle projections (`SubbundleGysinTopChernStep`) -- 0FAA is proved
only over the base scheme for the canonical bundles, with no identification of a base-changed
vector bundle with the bundle of a pulled-back module; the geometric consequence of the tag's
own factoring hypothesis, i_* = j_* composed with i'_* (`SubbundleGysinFactorization`), Tags
0637, 0FBH and 0F9J being absent. THE TAG'S SHEAF-LEVEL FACTORING HYPOTHESIS IS PRESENT AS
`_hsigma` BUT UNUSED: the proof runs on that carried geometric consequence instead. Also
carried: Tag 02TY injectivity only, Tag 02S1 descent, Tag 0B7G as this directory's standing
cap-rule parameter"]
theorem virtualNormalGysinCap_eq_topChernCap_comp
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (_hsigma : dualMap inc ≫ P'.normalBundle.surjection = P.normalBundle.surjection) (x : Z)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc g k))
    (hfactor : SubbundleGysinFactorization C G sZ sX sN sN' i hi q q' hq hq' j hj E E')
    (hstep : SubbundleGysinTopChernStep C sZ sN sN' i q q' hq hq' j hj m m' e Eb cap hdesc P P')
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    {c' : BivariantClass C G sZ sX i hi (m' : ℤ)}
    (hc : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq m 0 E
      (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc) P c)
    (hc' : IsVirtualNormalGysinClass C G sZ sX sN' i hi q' hq' m' 0 E'
      (bundleFlatPullback C sZ sN' i q' hq' m' P'.flat P'.relativeDimension hdesc) P' c')
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    c.cap g k α =
      chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ)
        (subbundleVirtualNormalDegree_eq P P' Eb inc pr w hseq x k)
        (subbundleTopChernCap C sZ i m' e Eb cap g k (c'.cap g k α)) := by
  refine hinj g k ?_
  rw [hc g k α, hfactor g k α, ← hc' g k α,
    hstep g k (subbundleVirtualNormalDegree_eq P P' Eb inc pr w hseq x k) (c'.cap g k α)]

/-- **Stacks 0FBL**, as an equality in `A^m(Z ⟶ X)`. If `d` is a bivariant class of degree `m`
for `i : Z ⟶ X` whose cap operation is cap with `c(Z ⟶ X, 𝒩')` followed by `c_top(ℰ)`, that is
if `d` is the composite `c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`, then `d = c(Z ⟶ X, 𝒩)`.

The composite is described by its cap operation, in the idiom of
`Stacks.Chow.IsBivariantClassComposition`. -/
@[stacks 0FBL "c(Z -> X, N) = c_top(E) composed with c(Z -> X, N') for a short exact sequence
0 -> N' -> N -> E -> 0 of finite locally free O_Z-modules of constant ranks m', m, e whose
conormal surjection factors. The short exact sequence IS consumed: it gives m = m' + e, which
is what puts the two sides in the same Chow group. Read as an equality of classes in
A^m(Z -> X) via `BivariantClass.ext`. Both classes are the ones CHARACTERIZED by
Tag 0FBK, neither being constructed in this repository, and the composite is spelled by the
top Chern cap rule at `Fin.last e` as Tag 0FAA spells it. CARRIED: Tag 0FAA at the
base changes of the two bundle projections (`SubbundleGysinTopChernStep`) -- 0FAA is proved
only over the base scheme for the canonical bundles, with no identification of a base-changed
vector bundle with the bundle of a pulled-back module; the geometric consequence of the tag's
own factoring hypothesis, i_* = j_* composed with i'_* (`SubbundleGysinFactorization`), Tags
0637, 0FBH and 0F9J being absent. THE TAG'S SHEAF-LEVEL FACTORING HYPOTHESIS IS PRESENT AS
`_hsigma` BUT UNUSED: the proof runs on that carried geometric consequence instead. Also
carried: Tag 02TY injectivity only, Tag 02S1 descent, Tag 0B7G as this directory's standing
cap-rule parameter"]
theorem virtualNormalGysinClass_eq_of_isTopChernComposition
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ P'.normalBundle.surjection = P.normalBundle.surjection) (x : Z)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc g k))
    (hfactor : SubbundleGysinFactorization C G sZ sX sN sN' i hi q q' hq hq' j hj E E')
    (hstep : SubbundleGysinTopChernStep C sZ sN sN' i q q' hq hq' j hj m m' e Eb cap hdesc P P')
    {c d : BivariantClass C G sZ sX i hi (m : ℤ)}
    {c' : BivariantClass C G sZ sX i hi (m' : ℤ)}
    (hc : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq m 0 E
      (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc) P c)
    (hc' : IsVirtualNormalGysinClass C G sZ sX sN' i hi q' hq' m' 0 E'
      (bundleFlatPullback C sZ sN' i q' hq' m' P'.flat P'.relativeDimension hdesc) P' c')
    (hd : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k),
      d.cap g k α =
        chowGroupDegreeEquiv C (pullback.fst i g ≫ sZ)
          (subbundleVirtualNormalDegree_eq P P' Eb inc pr w hseq x k)
          (subbundleTopChernCap C sZ i m' e Eb cap g k (c'.cap g k α))) :
    d = c := by
  refine BivariantClass.ext C G sZ sX i hi (m : ℤ) ?_
  intro T g _ k α
  rw [hd g k α]
  exact (virtualNormalGysinCap_eq_topChernCap_comp (C := C) (G := G) (sZ := sZ) (sX := sX)
    (sN := sN) (sN' := sN') (i := i) (hi := hi) (q := q) (q' := q') (hq := hq) (hq' := hq')
    (j := j) (hj := hj) (m := m) (m' := m') (e := e) (Eb := Eb) (cap := cap) (hdesc := hdesc)
    (E := E) (E' := E') (P := P) (P' := P') (inc := inc) (pr := pr) w hseq hsigma x hinj hfactor
    hstep hc hc' g k α).symm

end Main

end Stacks.Chow

end
