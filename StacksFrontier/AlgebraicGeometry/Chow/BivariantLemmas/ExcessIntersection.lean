module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The excess intersection formula

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion carrying a virtual normal sheaf `𝒩`
of constant rank `m` in the sense of Stacks 0FBQ, and let `g : Y ⟶ X` be locally of finite type.
Assume `Z ×_X Y ⟶ Y` is a regular closed immersion, so that its conormal sheaf is finite locally
free; if it has constant rank `r` then the surjection of Stacks 0FBQ restricts to a short exact
sequence

  `0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z ×_X Y} ⟶ 𝒞_{Z ×_X Y / Y} ⟶ 0`

on `Z ×_X Y` whose quotient `𝒩|_{Z ×_X Y} ⟶ ℰ` is the *excess normal sheaf*. **Stacks 0FBM**
asserts that if moreover `dim_δ(Y) = n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`

in `CH_*(Z ×_X Y)`, both sides lying in `CH_{n - m}(Z ×_X Y)`.

This module proves that formula from the characterizing relation of Stacks 0FBK, which the
repository now has as `Stacks.Chow.IsVirtualNormalGysinClass`, by carrying out the source's final
step: the relation says `p^* ∘ c = ι_* ∘ j^* ∘ C` with `p : N ⟶ Z` the projection of the vector
bundle `𝒩` defines, and the source evaluates both sides on `[Y]_n`, getting the fundamental class
of the normal cone on the right and the flat pullback of the right-hand side of the formula on the
left. Two things are needed and both are proved here: that the map `p^*` of the relation really is
flat pullback along the base change of the bundle projection, and that flat pullback carries a
fundamental class to a fundamental class.

## Main definitions

* `Stacks.Chow.bundleFlatPullbackChow` — flat pullback along `Stacks.Chow.bundleTestBaseChange`,
  the base change `N ×_X Y ⟶ Z ×_X Y` of the bundle projection. This is the map `p^*` of the
  construction preceding Stacks 0FBK, which that module could only carry as an arbitrary family
  `π` of additive maps.
* `Stacks.Chow.bundleFlatPullback` — the same map with the degrees of
  `Stacks.Chow.IsVirtualNormalGysinClass` at `e = 0`, so that it can be fed to that relation as
  its `π`.

## Main results

* `Stacks.Chow.isPullback_bundleTestBaseChange` — the base change of the bundle projection along a
  test scheme is a base change of the projection in the categorical sense. This is the
  identification that the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass` record as not
  carried out there, and it is what makes `π` an honest flat pullback: flatness and relative
  dimension `m` descend along it from `q`.
* `Stacks.Chow.flatPullback_fundamentalCycle` and
  `Stacks.Chow.flatPullbackChow_fundamentalChowClass` — **flat pullback of a fundamental class is
  a fundamental class**: for `f : X' ⟶ X` flat of relative dimension `m` with
  `dim_δ(X) ≤ k`, `f^*[X]_k = [X']_{k + m}`. This is the source's step `p^*[Z]_{n-r} = [C_ZX]_n`.
* `Stacks.Chow.eq_of_isVirtualNormalGysinClass_cap` — the division that defines the class: a class
  satisfying the relation of Stacks 0FBK takes a prescribed value on a given class as soon as the
  flat pullback of the candidate value agrees with the cap product of `ι_* ∘ j^* ∘ C`.
* `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass` — **Stacks 0FBM at vanishing excess**:
  when `m = r`, so that `ℰ = 0` and `c_top(ℰ) = 1`, the formula reads
  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - r}` and is proved here.
* `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass_excess` — **Stacks 0FBM**, the formula
  with excess.

## Implementation notes

### What is proved and what is carried

The vanishing-excess formula `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass` is proved
from three named hypotheses, none of which is the conclusion or mentions the bivariant class:

* `hinj`, injectivity of flat pullback along the bundle projection on Chow groups. This is Stacks
  02TY, which the source itself cites at exactly this point, and which this repository proves only
  in rank zero (`Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle_zero`). Stacks 0FBK
  already carries it, in the stronger bijective form that the prescribed cap operation needs.
* `hcone`, the value of `E = ι_* ∘ j^* ∘ C` on the fundamental class: `E ∩ [Y]_n` is the
  fundamental class of `N ×_X Y`. This is the whole of the source's calculation
  `C ∩ [X]_n = i_∞^*[W]_{n+1} = [W_∞]_n`, restricted to the open `C_ZX ⊆ W_∞`, together with the
  identification `𝒞_{Z/X,*} = Sym(𝒞_{Z/X})` of Divisors Lemma 31.22.5 (Stacks 063M) that makes the
  normal cone the vector bundle.

  Most of the ingredients of that calculation are now in the library: the relative projective
  line is `Stacks.Chow.relativeProjectiveLine`; Stacks 0F9J is formalized as
  `Stacks.Chow.gysinCapOfLift` and `Stacks.Chow.GysinAtInfinityData`
  (`Chow/GysinAtInfinity.lean:326, 432`); the deformation space `W`, its structure morphism `b`,
  the exceptional divisor `E`, the fibre at infinity `W_∞` with its effective-Cartier property
  and the map `i : 𝐏¹_Y ⟶ W` are constructed for Stacks 0FBG
  (`Chow/InfinityCentreBlowup.lean:209-410`); the first equality of Stacks 0FBH and the affine
  chart computation `A[s][J/s] ⧸ (s) ≅ ⨁ₙ Iⁿ/Iⁿ⁺¹` behind its other two are proved
  (`Chow/InfinityCentreNormalCone.lean:110, 216, 352, 705`); and part (1) of Stacks 02TB, the
  Gysin map of an effective Cartier divisor on a fundamental class, is proved
  (`Chow/GysinCartierIntersection.lean:2173`, `Chow/GysinCoherentSheaf.lean:1116, 1157`).

  What is still missing is exactly the step producing the map `j : C_ZX ⟶ W_∞`, which is why
  Stacks 0FBK carries `E` as an arbitrary bivariant class and why this hypothesis is not yet
  dischargeable: the global identification `E ∖ X' = Spec_Z(𝒞_{Z/X,*}) = C_ZX` of Stacks 0FBH is
  not obtained, resting as it does on clause (5) of Stacks 0FBG, the presentation of `E` as the
  relative `Proj` of `𝒞_{Z/X,*}[S]`, and on clause (4), `W_∞ = X' + E`, of which the library has
  only the existential form
  `Stacks.Chow.exists_isEffectiveCartierDivisor_fibreIdealAtInfinity_eq`; see the "What is not
  proved here" section of `StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalCone`. Of
  Stacks 063M only conditions (1) and (2) are proved
  (`RegularImmersion/FinitePresentation.lean:105`,
  `MoreMorphisms/LocalCompleteIntersection/UnramifiedConormal.lean:98`); condition (3), which is
  the isomorphism `Sym(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` needed here, is not.

  The hypothesis is a statement about `E` alone: it mentions neither `c`, nor flat pullback, nor
  `Z ×_X Y`.
* `hdim`, the bound `dim_δ(Z ×_X Y) ≤ n - r`. This is hypothesis (3) of Stacks 0FEA; under the
  hypotheses of Stacks 0FBM it is a consequence of `dim_δ(Y) = n` and the regularity of
  `Z ×_X Y ⟶ Y`, by the dimension theory of Stacks 02R8 for the bundle projection. It is a
  statement about δ-dimension only.

Everything else is proved: the base-change square, flatness and relative dimension of the
base-changed projection, the fundamental-class computation for flat pullback, and the division by
`p^*`.

### Why the general excess case needs one more carried input

`Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass_excess` carries, in addition, exactly one
statement: **Stacks 0FAA**, that for a short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite
locally free modules and the corresponding closed embedding `N' ⟶ N` of vector bundles,

  `ι_* (p')^* α = p^* (c_top(ℰ) ∩ α)`.

This is the lemma the source's own proof of Stacks 0FBM rests on, through the reduction of Stacks
0FBL. It does have a carrier:
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernCap`
(`Chow/SubbundleTopChernClass.lean:429`) states exactly `ι_*(p')^*α = p^*(c_top(ℰ) ∩ α)`, and
Stacks 0FA9 behind it is proved too, at rank one and with its reduced case assumed
(`Chow/ChernClassOfSection.lean:228, 279, 423, 501`).

That carrier is not the discharge of `hexcess`, for a reason of shape rather than of content.
There the three bundles are the canonical constructed ones — `p` and `p'` are
`Stacks.Chow.dualVectorBundleToBase` and `ι` is `Stacks.Chow.subbundleEmbedding`, built from a
short exact sequence of finite locally free modules of constant ranks — whereas `hexcess` here is
stated at an arbitrary rank-`r` sub-bundle `CN ⟶ N ×_X Y` of the base-changed bundle, presented
by the data `ιC`, `pC` and `cTop` below. Instantiating it at the constructed bundles would
specialize this statement rather than strengthen it, so the hypothesis stays; what is missing for
a genuine discharge is the identification of the base change `N ×_X Y` of the bundle of `𝒩` with
the `dualVectorBundle` of `𝒩|_{Z ×_X Y}`, and of `CN` with the sub-bundle the short exact
sequence of the excess sheaf produces. `hexcess` is a statement about vector bundles, flat
pullback and the top Chern class; it mentions no Gysin class and no `E`, and it is not the
conclusion — on the nose it is a formula in `CH_*(N ×_X Y)`, one bundle level above the formula
being proved.

The top Chern class is carried as the additive map `cTop` rather than constructed, but not for
want of Stacks 0FA4, which is formalized: `Stacks.Chow.topChernClassOfInvertible`
(`Chow/TopChernClassOfInvertible.lean`) defines `c_top(ℰ) = Σ_r c_r(ℰ|_{X_r})` in the completed
bivariant group of Stacks 0FE0 from the Chern classes of Stacks 0ESW, for the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`. The statements here are for an arbitrary Gysin system, for
which the higher Chern classes are only the characterization `Stacks.Chow.IsChernClassBivariant`
and the carried cap datum `Stacks.Chow.HigherChernCapRule`. So carrying `cTop` directly carries
one level less than carrying a family of such classes and assembling it with
`Stacks.Chow.topChernClass`, which takes the family as a parameter. Only `c_top(ℰ)`'s degree
enters the formula, and that is fixed by the typing: it takes `CH_{n-r}(Z ×_X Y)` to
`CH_{n-m}(Z ×_X Y)`, so it has degree `m - r`, the rank of the excess sheaf.

### The letters

The rank of `𝒩` is `m` here, where `Stacks.Chow.VirtualNormalBundleProjection` calls it `r`; `r`
is reserved for the rank of the conormal sheaf `𝒞_{Z ×_X Y / Y}`, as in the source. The excess
sheaf then has rank `m - r`, the cap product `c(Z ⟶ X, 𝒩) ∩ [Y]_n` lands in `CH_{n-m}`, and the
degree of `E = ι_* ∘ j^* ∘ C` is `0`, which is the source's value and the only one for which the
relation of Stacks 0FBK can be fed the genuine flat pullback: that pullback raises degrees by `m`,
so it takes `CH_{k-m}` to `CH_k`, and the relation types its target as `CH_{k-e}`.

### The regular immersion and the excess sheaf as data

The hypotheses of Stacks 0FBM that bear on the sheaves — that `Z ×_X Y ⟶ Y` is a regular closed
immersion with conormal sheaf of constant rank `r`, and that `ℰ` is the quotient in the displayed
short exact sequence — enter the proof only through their consequences, and those consequences are
what the statements below take: that the normal cone of `Z ×_X Y` in `Y` is a vector bundle of
rank `r` over `Z ×_X Y` sitting inside `N ×_X Y` as a closed subscheme (the data `CN`, `ιC`, `pC`
below), and that `c_top(ℰ)` has degree `m - r`. Carrying the sheaf-level data instead would add
the hypotheses without shortening any proof, since neither the conormal sheaf nor the dual of a
kernel is connected to the Chow development here.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of the bundle projection is a base change -/

/-- The morphism `N ×_X T ⟶ Z ×_X T` of `Stacks.Chow.bundleTestBaseChange` is the base change of
the bundle projection `q : N ⟶ Z` along `Z ×_X T ⟶ Z`, in the categorical sense: the square

  `N ×_X T ⟶ N`, `N ×_X T ⟶ Z ×_X T`, `q : N ⟶ Z`, `Z ×_X T ⟶ Z`

is cartesian. Both corners compute `N ×_Z (Z ×_X T) = N ×_X T`, and the identification is the
pasting isomorphism `CategoryTheory.Limits.pullbackRightPullbackFstIso`.

This is the identification the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass` record as not
carried out there, which is why the flat pullback along this morphism had to be carried as an
arbitrary family of additive maps. With it, flatness and relative dimension descend and the
pullback is the genuine one. -/
theorem isPullback_bundleTestBaseChange {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)
    {T : Scheme.{u}} (g : T ⟶ X) :
    IsPullback (pullback.fst (q ≫ i) g) (bundleTestBaseChange i q g) q (pullback.fst i g) := by
  refine IsPullback.of_iso_pullback ⟨(bundleTestBaseChange_fst i q g).symm⟩
    (pullbackRightPullbackFstIso i g q).symm ?_ ?_
  · exact pullbackRightPullbackFstIso_inv_fst i g q
  · refine pullback.hom_ext ?_ ?_
    · rw [Iso.symm_hom, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst i g q,
        bundleTestBaseChange_fst i q g]
    · rw [Iso.symm_hom, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd i g q,
        bundleTestBaseChange_snd i q g]

/-- The base change of the bundle projection along a test scheme is locally of finite type. -/
theorem locallyOfFiniteType_bundleTestBaseChange {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)
    [LocallyOfFiniteType q] {T : Scheme.{u}} (g : T ⟶ X) :
    LocallyOfFiniteType (bundleTestBaseChange i q g) :=
  MorphismProperty.of_isPullback (isPullback_bundleTestBaseChange i q g)
    (P := @LocallyOfFiniteType) inferInstance

/-- The base change of the bundle projection along a test scheme is flat. -/
theorem flat_bundleTestBaseChange {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)
    (hq : AlgebraicGeometry.Flat q) {T : Scheme.{u}} (g : T ⟶ X) :
    AlgebraicGeometry.Flat (bundleTestBaseChange i q g) :=
  MorphismProperty.of_isPullback (isPullback_bundleTestBaseChange i q g)
    (P := @AlgebraicGeometry.Flat) hq

/-- The base change of the bundle projection along a test scheme has the same relative dimension
as the projection: Stacks 02NK. -/
theorem relativeDimension_bundleTestBaseChange {Z X N : Scheme.{u}} (i : Z ⟶ X) (q : N ⟶ Z)
    [LocallyOfFiniteType q] {m : ℕ} (hq : AlgebraicGeometry.RelativeDimension q m)
    {T : Scheme.{u}} (g : T ⟶ X) :
    letI := locallyOfFiniteType_bundleTestBaseChange i q g
    AlgebraicGeometry.RelativeDimension (bundleTestBaseChange i q g) m :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_bundleTestBaseChange i q g) hq

/-! ### Flat pullback of a fundamental class -/

/-- **Flat pullback of a fundamental cycle is a fundamental cycle.** If `f : X' ⟶ X` is flat of
relative dimension `m` over the base of a Chow situation and `dim_δ(X) ≤ k`, then
`f^*[X]_k = [X']_{k+m}`.

This is the source's step `p^*[Z]_{n-r} = [C_ZX]_n` in the proof of Stacks 0FBM. It is the case
`i = 𝟙 X` of `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`, Stacks 02RB,
followed by the observation that `X' ×_X X ⟶ X'` is an isomorphism, so that the cycle of the
pullback of `X` as a closed subscheme of itself is the fundamental cycle of `X'`. -/
theorem flatPullback_fundamentalCycle (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (hbase : f ≫ sX = sX')
    (m : ℕ) (hf : AlgebraicGeometry.RelativeDimension f m) (k : ℤ)
    (hdim : schemeDeltaDimension C sX ≤ (k : EInt)) :
    flatPullback C sX' sX f hbase m hf k (fundamentalCycle C sX k) =
      fundamentalCycle C sX' (k + (m : ℤ)) := by
  rw [fundamentalCycle,
    flatPullback_cycleAssociatedToClosedSubscheme_of_le C sX' sX f hbase m hf (𝟙 X) k
      (by simpa using hdim),
    fundamentalCycle]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C sX' (pullback.fst f (𝟙 X)) (𝟙 X')
    (asIso (pullback.fst f (𝟙 X))) (by simp) (k + (m : ℤ))

/-- **Flat pullback of a fundamental class is a fundamental class**, on Chow groups: for
`f : X' ⟶ X` flat of relative dimension `m` with `dim_δ(X) ≤ k`,
`f^*[X]_k = [X']_{k+m}` in `A_{k+m}(X')`. -/
theorem flatPullbackChow_fundamentalChowClass (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (hbase : f ≫ sX = sX')
    (m : ℕ) (hf : AlgebraicGeometry.RelativeDimension f m) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase m hf k)
    (hdim : schemeDeltaDimension C sX ≤ (k : EInt)) :
    flatPullbackChow C sX' sX f hbase m hf k hfac (fundamentalChowClass C sX k) =
      fundamentalChowClass C sX' (k + (m : ℤ)) := by
  rw [fundamentalChowClass, flatPullbackChow_mk,
    flatPullback_fundamentalCycle C sX' sX f hbase m hf k hdim, fundamentalChowClass]

/-! ### Flat pullback along the bundle projection -/

section BundlePullback

variable (C : ChowSituation.{u}) {Z X N : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : Z ⟶ X) (q : N ⟶ Z) [LocallyOfFiniteType q] (hq : q ≫ sZ = sN) (m : ℕ)
  (hflat : AlgebraicGeometry.Flat q) (hrd : AlgebraicGeometry.RelativeDimension q m)
  (hdesc : FlatPullbackDescends C)

/-- **The map `p^*` of the construction preceding Stacks 0FBK.** Flat pullback along
`Stacks.Chow.bundleTestBaseChange`, the base change `N ×_X T ⟶ Z ×_X T` of the projection of the
vector bundle that the virtual normal sheaf defines. It raises degrees by the relative dimension
`m` of the projection, which is the rank of the virtual normal sheaf.

`Stacks.Chow.IsVirtualNormalGysinClass` carries this map as an arbitrary family `π` of additive
maps, because the identification of `N ×_X T` with `N ×_Z (Z ×_X T)` was not available there; it
is `Stacks.Chow.isPullback_bundleTestBaseChange` above. -/
def bundleFlatPullbackChow {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ sZ) k →+
      chowGroup C (pullback.fst (q ≫ i) g ≫ sN) (k + (m : ℤ)) :=
  letI := locallyOfFiniteType_bundleTestBaseChange i q g
  letI := flat_bundleTestBaseChange i q hflat g
  flatPullbackChow C (pullback.fst (q ≫ i) g ≫ sN) (pullback.fst i g ≫ sZ)
    (bundleTestBaseChange i q g) (bundleTestBaseChange_comp_structureMorphism i q sZ sN hq g) m
    (relativeDimension_bundleTestBaseChange i q hrd g) k
    (hdesc (pullback.fst (q ≫ i) g ≫ sN) (pullback.fst i g ≫ sZ) (bundleTestBaseChange i q g)
      (bundleTestBaseChange_comp_structureMorphism i q sZ sN hq g) m
      (relativeDimension_bundleTestBaseChange i q hrd g) k)

/-- The flat pullback of the bundle projection, written with the degrees that
`Stacks.Chow.IsVirtualNormalGysinClass` asks of its family `π` when the degree `e` of
`ι_* ∘ j^* ∘ C` is `0`, the value it has in the source. It is
`Stacks.Chow.bundleFlatPullbackChow` followed by the transport
`(k - m) + m = k - 0` of degrees. -/
def bundleFlatPullback {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (pullback.fst i g ≫ sZ) (k - (m : ℤ)) →+
      chowGroup C (pullback.fst (q ≫ i) g ≫ sN) (k - (0 : ℤ)) :=
  (chowGroupDegreeEquiv C (pullback.fst (q ≫ i) g ≫ sN)
      (by omega : (k - (m : ℤ)) + (m : ℤ) = k - (0 : ℤ))).toAddMonoidHom.comp
    (bundleFlatPullbackChow C sZ sN i q hq m hflat hrd hdesc g (k - (m : ℤ)))

/-- The flat pullback of the bundle projection at the degrees of Stacks 0FBK is the one of
`Stacks.Chow.bundleFlatPullbackChow`, transported along `(k - m) + m = k - 0`. -/
theorem bundleFlatPullback_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (pullback.fst i g ≫ sZ) (k - (m : ℤ))) :
    bundleFlatPullback C sZ sN i q hq m hflat hrd hdesc g k β =
      chowGroupDegreeEquiv C (pullback.fst (q ≫ i) g ≫ sN)
        (by omega : (k - (m : ℤ)) + (m : ℤ) = k - (0 : ℤ))
        (bundleFlatPullbackChow C sZ sN i q hq m hflat hrd hdesc g (k - (m : ℤ)) β) :=
  rfl

/-- The flat pullback of the bundle projection carries the fundamental class of `Z ×_X T` to the
fundamental class of `N ×_X T`, as soon as `dim_δ(Z ×_X T)` is at most the degree. This is the
source's `p^*[Z]_{n-r} = [C_ZX]_n`, at the base change along a test scheme. -/
theorem bundleFlatPullbackChow_fundamentalChowClass {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ)
    (hdim : schemeDeltaDimension C (pullback.fst i g ≫ sZ) ≤ (k : EInt)) :
    bundleFlatPullbackChow C sZ sN i q hq m hflat hrd hdesc g k
        (fundamentalChowClass C (pullback.fst i g ≫ sZ) k) =
      fundamentalChowClass C (pullback.fst (q ≫ i) g ≫ sN) (k + (m : ℤ)) :=
  let _ := locallyOfFiniteType_bundleTestBaseChange i q g
  let _ := flat_bundleTestBaseChange i q hflat g
  flatPullbackChow_fundamentalChowClass C (pullback.fst (q ≫ i) g ≫ sN)
    (pullback.fst i g ≫ sZ) (bundleTestBaseChange i q g)
    (bundleTestBaseChange_comp_structureMorphism i q sZ sN hq g) m
    (relativeDimension_bundleTestBaseChange i q hrd g) k _ hdim

end BundlePullback

/-! ### The excess intersection formula -/

section Excess

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X N : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sX = sZ)
  (q : N ⟶ Z) [LocallyOfFiniteType q] (hq : q ≫ sZ = sN) (m : ℕ)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq hi) 0)
  (P : VirtualNormalBundleProjection i q m) (hdesc : FlatPullbackDescends C)

/-- **The division that defines `c(Z ⟶ X, 𝒩)`, evaluated.** A bivariant class satisfying the
characterizing relation of Stacks 0FBK against an injective `π` takes a prescribed value on a
given Chow class: if the flat pullback of a candidate `β` agrees with `(ι_* ∘ j^* ∘ C) ∩ α`, then
`c ∩ α = β`.

This is the source's "`c ∩ α` is the unique `β` with `p^* β = ι_* j^* (C ∩ α)`", read as a rule
for computing `c ∩ α`. Only injectivity of `π` is used, which is the half of Stacks 02TY that the
uniqueness clause of the construction rests on. -/
theorem eq_of_isVirtualNormalGysinClass_cap
    (π : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      chowGroup C (pullback.fst i g ≫ sZ) (k - (m : ℤ)) →+
        chowGroup C (pullback.fst (q ≫ i) g ≫ sN) (k - (0 : ℤ)))
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective (π g k))
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    (hc : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq m 0 E π P c)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) (β : chowGroup C (pullback.fst i g ≫ sZ) (k - (m : ℤ)))
    (hβ : π g k β = E.cap g k α) :
    c.cap g k α = β :=
  hinj g k ((hc g k α).trans hβ.symm)

/-- **Stacks 0FBM at vanishing excess.** In the situation of the virtual normal sheaf, let
`g : Y ⟶ X` be locally of finite type and assume that `Z ×_X Y ⟶ Y` is cut out by a regular
sequence of length `m`, so that the excess normal sheaf vanishes and `c_top(ℰ) = 1`. If
`dim_δ(Z ×_X Y) ≤ n - m` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - m}`

in `A_{n-m}(Z ×_X Y)`, for the class `c` of Stacks 0FBK, that is for any bivariant class of
degree `m` satisfying the characterizing relation of that tag against the genuine flat pullback
`Stacks.Chow.bundleFlatPullback` of the bundle projection.

The proof is the source's: the relation says `p^*(c ∩ [Y]_n) = (ι_* ∘ j^* ∘ C) ∩ [Y]_n`, the
right-hand side is the fundamental class of `N ×_X Y` — the hypothesis `hcone` — and the left-hand
side is `p^*` of the candidate, which is that same fundamental class by
`Stacks.Chow.bundleFlatPullbackChow_fundamentalChowClass`; now divide by `p^*`.

See the implementation notes for what `hcone`, `hinj` and `hdim` are and why none of them is this
conclusion. -/
@[stacks 0FBM "at vanishing excess, where `c_top(ℰ) = 1`: `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n-m}` \
for the class of Stacks 0FBK, proved from its characterizing relation; carried: `ι_* j^* C` on \
`[Y]_n` — 0F9J, 02TB and most of 0FBG and 0FBH are proved, but the map `j : C_ZX ⟶ W_∞` is not, \
needing clauses (4) and (5) of 0FBG and condition (3) of 063M; see the implementation notes — \
injectivity of `p^*` (02TY), the δ-dim bound"]
theorem virtualNormalGysinCap_fundamentalChowClass
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc g k))
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    (hc : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq m 0 E
      (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc) P c)
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ)
    (hdim : schemeDeltaDimension C (pullback.fst i g ≫ sZ) ≤ ((n - (m : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) g ≫ sN)
        (by omega : n - (0 : ℤ) = (n - (m : ℤ)) + (m : ℤ))
        (E.cap g n (fundamentalChowClass C (g ≫ sX) n)) =
      fundamentalChowClass C (pullback.fst (q ≫ i) g ≫ sN) ((n - (m : ℤ)) + (m : ℤ))) :
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - (m : ℤ)) := by
  refine eq_of_isVirtualNormalGysinClass_cap C G sZ sX sN i hi q hq m E P _ hinj hc g n _ _ ?_
  rw [bundleFlatPullback_apply,
    bundleFlatPullbackChow_fundamentalChowClass C sZ sN i q hq m P.flat P.relativeDimension
      hdesc g (n - (m : ℤ)) hdim]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  exact ((chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).1 hcone).symm

/-- **Stacks 0FBM.** In the situation of the virtual normal sheaf, let `g : Y ⟶ X` be locally of
finite type, assume `Z ×_X Y ⟶ Y` is a regular closed immersion whose conormal sheaf has constant
rank `r`, and let `ℰ` be the excess normal sheaf, of rank `m - r`. If `dim_δ(Y) = n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`

in `A_{n-m}(Z ×_X Y)`.

The regular immersion and the excess sheaf enter through the data they produce: the normal cone
`C_{Z ×_X Y} Y` is a vector bundle `CN` of rank `r` over `Z ×_X Y`, by the identification
`𝒞_{*} = Sym(𝒞)` of Stacks 063M, embedded in `N ×_X Y` over `Z ×_X Y` by `ιC` and `pC`; and the
cap product with `c_top(ℰ)` is the additive map `cTop`, of degree `m - r` by its typing. See the
implementation notes.

Besides the three hypotheses of `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass` the proof
carries one statement, `hexcess`, which is **Stacks 0FAA** for the embedding `CN ⟶ N ×_X Y` of
vector bundles over `Z ×_X Y`: `ι_* (p')^* α = p^*(c_top(ℰ) ∩ α)`. That lemma is proved, as
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernCap`, but at the canonical
constructed bundles of a short exact sequence rather than at an arbitrary sub-bundle `CN`, so it
does not discharge the hypothesis as stated here; see the implementation notes. It is a formula in
`A_*(N ×_X Y)`, one bundle level above this conclusion, and mentions no bivariant class for
`Z ⟶ X`. -/
@[stacks 0FBM "with excess: `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n-r}`, the normal cone \
given as a rank-`r` sub-bundle `CN` (063M) and `c_top(ℰ)` as the map `cTop` — `Stacks.Chow.\
topChernClassOfInvertible` of 0FA4 is proved, but at the Gysin system of the first Chern class, \
while the higher Chern classes for the Gysin system here are carried as elsewhere in this \
directory; carried also: Stacks 0FAA for `CN ⟶ N ×_X Y`, proved at the \
constructed bundles of a short exact sequence but not at an arbitrary sub-bundle"]
theorem virtualNormalGysinCap_fundamentalChowClass_excess
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc g k))
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    (hc : IsVirtualNormalGysinClass C G sZ sX sN i hi q hq m 0 E
      (bundleFlatPullback C sZ sN i q hq m P.flat P.relativeDimension hdesc) P c)
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ) (r : ℕ)
    (hdim : schemeDeltaDimension C (pullback.fst i g ≫ sZ) ≤ ((n - (r : ℤ) : ℤ) : EInt))
    {CN : Scheme.{u}} (ιC : CN ⟶ pullback (q ≫ i) g) [IsClosedImmersion ιC]
    (pC : CN ⟶ pullback i g) [LocallyOfFiniteType pC] [AlgebraicGeometry.Flat pC]
    (hpC : AlgebraicGeometry.RelativeDimension pC r)
    (hCN : ιC ≫ bundleTestBaseChange i q g = pC)
    (cTop : chowGroup C (pullback.fst i g ≫ sZ) (n - (r : ℤ)) →+
      chowGroup C (pullback.fst i g ≫ sZ) (n - (m : ℤ)))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) g ≫ sN)
        (by omega : n - (0 : ℤ) = (n - (r : ℤ)) + (r : ℤ))
        (E.cap g n (fundamentalChowClass C (g ≫ sX) n)) =
      chowPushforwardOfIsClosedImmersion C (pC ≫ (pullback.fst i g ≫ sZ))
        (pullback.fst (q ≫ i) g ≫ sN) ιC
        (by rw [← bundleTestBaseChange_comp_structureMorphism i q sZ sN hq g,
          ← Category.assoc, hCN]) ((n - (r : ℤ)) + (r : ℤ))
        (fundamentalChowClass C (pC ≫ (pullback.fst i g ≫ sZ)) ((n - (r : ℤ)) + (r : ℤ))))
    (hexcess : ∀ α : chowGroup C (pullback.fst i g ≫ sZ) (n - (r : ℤ)),
      chowGroupDegreeEquiv C (pullback.fst (q ≫ i) g ≫ sN)
          (by omega : (n - (m : ℤ)) + (m : ℤ) = (n - (r : ℤ)) + (r : ℤ))
          (bundleFlatPullbackChow C sZ sN i q hq m P.flat P.relativeDimension hdesc g
            (n - (m : ℤ)) (cTop α)) =
        chowPushforwardOfIsClosedImmersion C (pC ≫ (pullback.fst i g ≫ sZ))
          (pullback.fst (q ≫ i) g ≫ sN) ιC
          (by rw [← bundleTestBaseChange_comp_structureMorphism i q sZ sN hq g,
            ← Category.assoc, hCN]) ((n - (r : ℤ)) + (r : ℤ))
          (flatPullbackChow C (pC ≫ (pullback.fst i g ≫ sZ)) (pullback.fst i g ≫ sZ) pC rfl r hpC
            (n - (r : ℤ))
            (hdesc (pC ≫ (pullback.fst i g ≫ sZ)) (pullback.fst i g ≫ sZ) pC rfl r hpC
              (n - (r : ℤ))) α)) :
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      cTop (fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - (r : ℤ))) := by
  refine eq_of_isVirtualNormalGysinClass_cap C G sZ sX sN i hi q hq m E P _ hinj hc g n _ _ ?_
  have hfund := flatPullbackChow_fundamentalChowClass C (pC ≫ (pullback.fst i g ≫ sZ))
    (pullback.fst i g ≫ sZ) pC rfl r hpC (n - (r : ℤ))
    (hdesc (pC ≫ (pullback.fst i g ≫ sZ)) (pullback.fst i g ≫ sZ) pC rfl r hpC (n - (r : ℤ)))
    hdim
  have hkey := hexcess (fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - (r : ℤ)))
  rw [hfund] at hkey
  rw [bundleFlatPullback_apply]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  exact ((chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).1 hkey).trans
    ((chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).1 hcone).symm

end Excess

end Stacks.Chow

end
