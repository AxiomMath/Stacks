module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeChern
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernClassDual
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterDual

/-!
# The characteristic classes of a termwise dual complex

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be a scheme
locally of finite type over `S` and let `𝓔^•` be a locally bounded complex of finite locally
free `𝒪_Y`-modules. Its *termwise dual* is a complex `𝓕^•` with `𝓕^n ≅ (𝓔^{-n})^∨`. This file
proves the three sign rules

  `c_p(𝓕^•) = (-1)^p c_p(𝓔^•)`,  `P_p(𝓕^•) = (-1)^p P_p(𝓔^•)`  in  `A^p(Y)`,
  `ch_p(𝓕^•) = (-1)^p ch_p(𝓔^•)`  in  `A^p(Y) ⊗ 𝐐`,

which are the three conclusions of [Stacks, Tag 0FAE] at the level of complexes: what the first
proof of that lemma obtains by reducing to a complex of finite locally free modules and applying
[Stacks, Tag 0FA5].

**Tag 0FAE is not registered by this file**, but by
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualChernClasses`, which reads these
results at an envelope presentation of `E^∨`. The lemma is about a perfect object `E` of
`D(𝒪_X)` whose Chern classes are defined, and getting from here to there needs such a
presentation; see the last implementation note.

## Main definitions

* `Stacks.Chow.TotalChowClass.signScale` — the `(-1)^p`-scaling of a total Chow cohomology class,
  and `Stacks.Chow.TotalChowClass.signScaleRingHom`, the ring endomorphism it is.
* `Stacks.Chow.pullbackComplex_termwiseDualIso` — the termwise dual isomorphisms pull back.

## Main results

* `Stacks.Chow.totalChern_dualSheaf` — [Stacks, Tag 0FA5] read on the total Chow cohomology
  classes `Stacks.Chow.totalChern` of a finite locally free module.
* `Stacks.Chow.complexChernBounded_of_termwiseDual` — the sign rule for the total Chern class of
  a bounded complex of constant ranks.
* `Stacks.Chow.complexChern_of_termwiseDual` — the sign rule for the total Chern class of a
  locally bounded complex, and `Stacks.Chow.complexChern_apply_of_termwiseDual`, the same
  degreewise.
* `Stacks.Chow.complexRankClass_of_termwiseDual` — the alternating rank is unchanged by
  dualizing, which is the degree-zero power sum.
* `Stacks.Chow.complexPowerSum_of_termwiseDual` and
  `Stacks.Chow.complexPowerSumComponent_of_termwiseDual` — the sign rule for the power-sum
  classes `P_p`.
* `Stacks.Chow.complexChernCharacterComponent_of_termwiseDual` — the sign rule for the Chern
  character `ch_p`.

## Implementation notes

### No relation between the two rank functions is assumed

`Stacks.Chow.complexChernBounded_of_termwiseDual` carries rank functions for `𝓔^•` and for
`𝓕^•` with no hypothesis relating them. None is needed: on a nonempty scheme the ranks are
determined by the modules, so `Stacks.AlgebraicGeometry.ReflexiveModules`'s rank of a dual forces
`ρ'(n) = ρ(-n)`, and on an empty scheme there is only one total class. This is the device of
`Stacks.Chow.complexChernBounded_congr_rank`.

### Why only termwise isomorphisms are needed

The total Chern class of a complex of finite locally free modules depends only on its terms —
`Stacks.Chow.complexChernBounded_congr` and `Stacks.Chow.complexChern_congr` ask for
isomorphisms `𝓔^n ≅ 𝓔'^n` and nothing about the differentials. So the hypothesis here is the
family of isomorphisms `𝓕^n ≅ (𝓔^{-n})^∨` alone, and the signed transpose differential of the
dual complex of [Stacks, Tag 0FPR] — `Stacks.SheafOfModules.Strict.dualComplex` — never enters.
That makes the statement independent of which construction of the dual complex is used, and in
particular of the ringed-site vocabulary that one lives in.

### The sign scaling

`Stacks.Chow.TotalChowClass.signScale` is the function
`Stacks.Chow.chowSeriesSignScale` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterDual` at the Gysin system of the first Chern
class of an invertible module, which is what `Stacks.Chow.TotalChowClass` is the series type of.
What is new here is that it is multiplicative for the Cauchy product of
`Stacks.Chow.TotalChowClass.instRing`: that ring is not the one
`Stacks.Chow.ChowCohomologySeriesRing.chowSeriesSignScale_mul` is stated for, and the identity is
proved instead from `Stacks.Chow.capFamilySignScale_mul` on the operations, through
`Stacks.Chow.TotalChowClass.ext_op`.

### How the power sums and the Chern character follow

`Stacks.Chow.complexPowerSum` is Newton's recursion of [Stacks, Tag 0F9B],
`AlgebraicGeometry.newtonPowerSum`, applied to the alternating rank class and to the homogeneous
components of the total Chern class, and `AlgebraicGeometry.map_newtonPowerSum` carries that
recursion along any ring homomorphism. So the sign rule for `P_p` is the sign rule for `c` plus
`Stacks.Chow.TotalChowClass.homComponent_signScale` on the Chern classes and
`Stacks.Chow.complexRankClass_of_termwiseDual` with
`Stacks.Chow.signScale_complexRankClass` on the rank. The Chern character is `P_p/p!`, so its
rule is the one for `P_p` pushed through the tensor factor.

The rank is genuinely unchanged rather than scaled: the alternating rank of `𝓕^•` is
`∑_n (-1)^n ρ(-n)`, and `n ↦ -n` is a bijection of the degrees under which `(-1)^n` is
invariant. That is the degree-zero case `P_0(𝓕^•) = (-1)^0 P_0(𝓔^•)` of the source.

### How Tag 0FAE is reached from here

The source's `c_p(E)`, `P_p(E)` and `ch_p(E)` are
`Stacks.Chow.perfectChernClass`, `Stacks.Chow.perfectPowerSum` and
`Stacks.Chow.perfectChernCharacter`, each characterized by its restriction along the envelope of
an envelope presentation of `E` (`Stacks.Chow.res_perfectChernClass` and its companions). Reading
the results of this file there needs an envelope presentation of `E^∨` whose complex is a
termwise dual of the presenting complex of `E`, that is an isomorphism
`Lf^*(E^∨) ≅ Q(𝓔^{•∨})`. None of the criteria of [Stacks, Tag 0GUE] in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria` produces a presentation from
perfectness alone, so that isomorphism has to be supplied.

**It is now supplied, and Tag 0FAE is registered**, in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualChernClasses`:
`Stacks.Chow.EnvelopePresentation.derivedDual` is the presentation, and
`Stacks.Chow.perfectChernClass_apply_derivedDual`,
`Stacks.Chow.perfectPowerSumComponent_derivedDual` and
`Stacks.Chow.perfectChernCharacterComponent_derivedDual` are the three sign identities, each
obtained by reading the corresponding result of this file at that presentation. The rest of this
note records the two halves of the construction and is accurate; only its former claim that the
first half stops at a missing monoidal structure was superseded, as the paragraph on that half
now says.

The shape the construction should take is already in the tree one case over:
`Stacks.Chow.EnvelopePresentation.twist` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible` turns a presentation of
`E` into a presentation of `E ⊗ ℒ` on the same envelope, with the termwise twisted complex, and
its `representation` field is exactly the composite of the two isomorphisms below with the
twist in place of the dual. What is wanted here is the same declaration for the dual.

Its two halves, and what the repository already has for each:

* `Lf^*(E^∨) ≅ (Lf^*E)^∨`. The derived dual is available on these very objects:
  `Stacks.SheafOfModules.derivedDual X.sheaf E` is an object of `DerivedCategory X.Modules`, and
  for perfect `E` it is a left dual by `Stacks.SheafOfModules.derivedDual_isLeftDual`,
  [Stacks, Tag 0FPC]. `CategoryTheory.ExactPairing.map` would carry that pairing along the
  derived pullback and `[F.Monoidal]` is its only hypothesis, so what is needed is a monoidal
  structure on the derived pullback — and that is where the chain stops. The pieces that do
  exist: `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is the tensorator
  `Lf^*(K ⊗^𝐋 L) ≅ Lf^*K ⊗^𝐋 Lf^*L` of [Stacks, Tag 079U], with no hypothesis on `f`, applied at
  a morphism of schemes already in `Stacks.Chow.derivedPullbackDerivedTwistIso` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible`; its associativity and
  braiding coherences are proved; and the unit *comparison* is proved too —
  `Stacks.Sheaves.DerivedPullback.derivedPullbackUnitMap` with
  `isIso_derivedPullbackUnitMap`, the identification `Lf^*(𝒪[0]) ≅ 𝒪[0]`.

  That monoidal structure is assembled as follows. Against
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor product is
  `derivedTensorProductFunctor` and whose unit is `𝒪[0]` — both by `rfl`, so the tensorator and
  the unit comparison typecheck there without transport — `CategoryTheory.Functor.CoreMonoidal`
  asks for the tensorator, a unit isomorphism, naturality in each variable, associativity, and
  the two unitalities. All but left unitality are available as follows, unconditionally:

  - associativity is `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator`
    of `…DerivedPullback.PullbackTensorComparisonAssociator`, already stated at the associator of
    `canonicalDerivedMonoidal`;
  - the braiding compatibility is `…derivedPullbackTensorIso_braiding`, and the composition law
    `…derivedPullbackTensorIso_comp`;
  - the unit isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` is
    `Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso`;
  - **right** unitality is
    `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject`, stated at that
    same unit isomorphism and carrying no hypothesis;
  - naturality in each variable is free, the tensorator being an isomorphism of bifunctors.

  **This half is proved.** Left unitality at the derived level does not need the descent of
  `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_leftUnitor` along the K-flat
  localization modelled on
  `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat`: the derived tensor product of [Stacks, Tag 0FPT] is
  symmetric on both spaces (`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`)
  and the comparison of [Stacks, Tag 079U] is already known to be braided, so left unitality is
  right unitality read across the braiding —
  `Stacks.CategoryTheory.Monoidal.left_unitality_of_braided` applied to
  `Stacks.Cohomology.DerivedPullbackTensor.rightUnitorCoherence_canonical` gives
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_leftUnitor`. The spelling
  bridge between
  `Stacks.RingedSpace.derivedTensorRightUnitorNatIso` and the right unitor of
  `canonicalDerivedMonoidal`, is
  `Stacks.Cohomology.DerivedPullbackTensor.derivedTensorRightUnitorNatIso_hom_app_eq_canonical`;
  that one did need the K-flat identification. With all four clauses in hand,
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal` makes `Lf^*` a monoidal
  functor, and `Stacks.SheafOfModules.derivedPullbackDerivedDualIso` is
  `Lf^*(E^∨) ≅ (Lf^*E)^∨` for a perfect `E` with perfect derived pullback — the whole of this
  half.

  Two things that look like obstacles and are not. The several monoidal structures on `D(𝒪_X)`
  do not block the transport: `Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory`
  and `AlgebraicGeometry.RingedSite.derivedMonoidalStructure` are the same term by `rfl`, and the
  re-seated `Stacks.SheafOfModules.derivedMonoidalStructure` is reached by
  `CategoryTheory.MonoidalCategory.reseatMonoidal` composed with
  `CategoryTheory.ExactPairing.map` at the identity functor, while
  `CategoryTheory.exactPairingCongr` moves a pairing along isomorphisms of its two objects. And
  `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, which the repository does
  record as open, belongs to the ringed-topos setting of [Stacks, Tag 07A4] and is not needed for
  the ringed-space setting of [Stacks, Tag 079U] that the Chow chapter's derived pullback lives in.

  The route through `CategoryTheory.Functor.mapDerivedCategoryMonoidal` — the one
  `Stacks.Cohomology.LeftDualPerfect.exactPairingRestrictOpen` takes for restriction to an open —
  is **not** available here, and not merely awkward: `CategoryTheory.Functor.mapDerivedCategory`
  requires `[PreservesFiniteLimits F]`, and the module pullback along a general morphism is not
  left exact. The repository's own
  `Stacks.Cohomology.DerivedFlatDegreewise.derivedPullbackIsoMapDerivedCategory` is gated on
  `AlgebraicGeometry.IsFlat f` for exactly that reason, and the envelope of a presentation is
  not assumed flat.

  [Stacks, Tag 08JF] does not short-circuit this either:
  `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap` is the canonical map
  `Lh^*RSheafHom(K, L) ⟶ RSheafHom(Lh^*K, Lh^*L)`, and its own module records that the tag
  asserts nothing beyond the map's existence — that it is invertible for perfect `K`, which is
  what is wanted here, is not proved.
* `(Q 𝓔^•)^∨ ≅ Q(𝓔^{•∨})`. **This half is proved too**, and again not by the route an earlier
  version of this note prescribed. That version called it "a monoidality of the passage from
  complexes to the derived category", to be had from
  `Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect` of
  [Stacks, Tag 0FPR]. It is not: the identification is [Stacks, Tag 08DM], whose own reduction is
  to a *quasi-isomorphism of complexes*, which is local on the site — unlike invertibility in
  `D(𝒪_X)`, which is why no monoidal structure enters. So the global bound and the global
  splittings of that tag are replaced by their covering forms in
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_coversTop`, and
  `Stacks.Chow.derivedDualQIsoOfLocallyBounded` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualOfAPresentationComplex` is the
  result at the complex of an envelope presentation. The dual complex it produces is
  `SheafHom^•(𝓔^•, 𝒪_Y)` — which does carry the signed transpose differential, as it must, the
  statement being about the derived category; but the sign rules of this file need only its
  terms, and those are `(𝓔^{-n})^∨` by `Stacks.Chow.dualPresentationComplexXIso`.

## References

* [Stacks Project, Tag 0FAE](https://stacks.math.columbia.edu/tag/0FAE)
* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.Chow

/-! ### Products along a permuted list of pairwise-commuting entries -/

/-- **A product along a list of pairwise-commuting entries is invariant under permutation.** This
is `List.Perm.prod_eq'` with the pairwise commutation supplied by a commutation that holds for
every pair of indices. -/
theorem list_prod_map_of_perm_of_commute {M α : Type*} [Monoid M] {l l' : List α} (f : α → M)
    (hperm : l.Perm l') (h : ∀ x y, Commute (f x) (f y)) :
    (l.map f).prod = (l'.map f).prod := by
  refine (hperm.map f).prod_eq' (List.pairwise_map.2 ?_)
  clear hperm l'
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih => exact List.Pairwise.cons (fun _ _ ↦ h a _) ih

/-! ### The reflected rank function -/

/-- The value at `n` of the rank function `ρ` reindexed by `m ↦ -m`. -/
theorem equivMapDomain_neg_apply (τ : ℤ →₀ ℕ) (n : ℤ) :
    Finsupp.equivMapDomain (Equiv.neg ℤ) τ n = τ (-n) := by
  rw [Finsupp.equivMapDomain_apply]
  rfl

/-! ### The `(-1)^p`-scaling of a total Chow cohomology class -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

/-- **The `(-1)^p`-scaling of a total Chow cohomology class**: the class whose degree-`p`
component is `(-1)^p` times that of `c`. It is `Stacks.Chow.chowSeriesSignScale` at the Gysin
system of the first Chern class of an invertible module. -/
def signScale (c : TotalChowClass C sY) : TotalChowClass C sY :=
  chowSeriesSignScale (C := C) (G := gysinSystemOfInvertible C) (sX := sY) c

/-- The degree-`p` component of the scaling is `(-1)^p` times that of the class. -/
@[simp] theorem signScale_apply (c : TotalChowClass C sY) (p : ℕ) :
    signScale c p = ((-1 : ℤ) ^ p) • c p := rfl

/-- **The operation of the scaling is the scaling of the operation**: on a test scheme the
`(-1)^p`-scaling of a total class operates by the `(-1)^p`-scaling
`Stacks.Chow.capFamilySignScale` of its graded cap family. -/
theorem op_signScale (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] :
    (signScale c).op g = capFamilySignScale (c.op g) := by
  funext k p
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [capFamilySignScale_apply, op_apply, op_apply, signScale_apply,
    BivariantClass.idRule_zsmul]

/-- **The scaling fixes the unit.** -/
theorem signScale_one : signScale (1 : TotalChowClass C sY) = 1 :=
  ext_op fun g _ ↦ by rw [op_signScale, op_one, capFamilySignScale_one]

/-- **The scaling is multiplicative.** On a test scheme this is
`Stacks.Chow.capFamilySignScale_mul` for graded cap families. -/
theorem signScale_mul (c d : TotalChowClass C sY) :
    signScale (c * d) = signScale c * signScale d :=
  ext_op fun g _ ↦ by
    rw [op_signScale, op_mul, op_mul, capFamilySignScale_mul, op_signScale, op_signScale]

/-- **The `(-1)^p`-scaling as a ring endomorphism** of the total Chow cohomology classes. -/
def signScaleRingHom : TotalChowClass C sY →+* TotalChowClass C sY where
  toFun := signScale
  map_one' := signScale_one
  map_mul' := signScale_mul
  map_zero' := by ext p; rw [signScale_apply, zero_apply, smul_zero]
  map_add' c d := by
    ext p
    rw [signScale_apply, add_apply, add_apply, signScale_apply, signScale_apply, smul_add]

/-- The ring endomorphism `Stacks.Chow.TotalChowClass.signScaleRingHom` is the scaling. -/
@[simp] theorem signScaleRingHom_apply (c : TotalChowClass C sY) :
    (signScaleRingHom (C := C) (sY := sY)) c = signScale c := rfl

/-- **The scaling commutes with restriction**, the restriction map of Stacks 0B7F being additive
in every degree. -/
theorem res_signScale (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) : res h hs (signScale c) = signScale (res h hs c) := by
  subst hs
  ext p
  rw [res_rfl_apply, signScale_apply, signScale_apply, res_rfl_apply, map_zsmul]

/-- **The scaling commutes with integer multiples**, being additive. -/
theorem signScale_zsmul (m : ℤ) (c : TotalChowClass C sY) :
    signScale (m • c) = m • signScale c :=
  map_zsmul (signScaleRingHom (C := C) (sY := sY)) m c

/-- **An integer multiple of the unit is fixed by the scaling**: the unit sits in degree `0`,
where the factor is `(-1)^0 = 1`. -/
theorem signScale_zsmul_one (m : ℤ) :
    signScale (m • (1 : TotalChowClass C sY)) = m • 1 := by
  rw [signScale_zsmul, signScale_one]

/-- **The scaling commutes with taking a homogeneous component.** Both sides are `(-1)^i c_i` in
degree `i` and zero elsewhere. -/
theorem homComponent_signScale (i : ℕ) (c : TotalChowClass C sY) :
    homComponent i (signScale c) = signScale (homComponent i c) := by
  ext p
  rw [homComponent_apply, signScale_apply, signScale_apply, homComponent_apply]
  by_cases hp : p = i
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, smul_zero]

end TotalChowClass

/-! ### The sign rule for a module, on total classes -/

section Module

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **[Stacks, Tag 0FA5] on total Chow cohomology classes**: for `ℰ` finite locally free of rank
`r` the total Chern class of `ℰ^∨` is the `(-1)^p`-scaling of that of `ℰ`. This is
`Stacks.Chow.GenuineChern.chernClass_dualSheaf` read degreewise through
`Stacks.Chow.totalChern_apply`, the components above `r` vanishing on both sides. -/
theorem totalChern_dualSheaf (F : Y.Modules) (r : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF
    totalChern C sY (dualSheaf F) r = TotalChowClass.signScale (totalChern C sY F r) := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF
  ext p
  rw [TotalChowClass.signScale_apply]
  by_cases hp : p < r + 1
  · rw [show (p : ℕ) = ((⟨p, hp⟩ : Fin (r + 1)) : ℕ) from rfl, totalChern_apply,
      totalChern_apply, GenuineChern.chernClass_dualSheaf]
  · rw [totalChern_apply_of_lt C sY (dualSheaf F) r (by omega),
      totalChern_apply_of_lt C sY F r (by omega), smul_zero]

/-- **The total Chern class of a dual as a unit.** -/
theorem totalChernUnit_dualSheaf (F : Y.Modules) (r : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF
    totalChernUnit C sY (dualSheaf F) r =
      Units.map (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
        (totalChernUnit C sY F r) := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF
  refine Units.ext ?_
  rw [Units.coe_map, val_totalChernUnit, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    TotalChowClass.signScaleRingHom_apply, val_totalChernUnit]
  exact totalChern_dualSheaf C sY F r

end Module

/-! ### The sign rule for a bounded complex -/

/-- A module isomorphic to the dual of a finite locally free module of rank `r` has rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_of_iso_dualSheaf {Y : Scheme.{u}} {F G : Y.Modules}
    {r : ℕ} (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
    (e : G ≅ dualSheaf F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
    (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf F r hF)

section Bounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (P P' : CochainComplex Y.Modules ℤ)

/-- **The factor of degree `n` of a termwise dual complex.** If `𝓕^n ≅ (𝓔^{-n})^∨` then

  `c(𝓕^n)^{(-1)^n}` is the `(-1)^p`-scaling of `c(𝓔^{-n})^{(-1)^{-n}}`,

by [Stacks, Tag 0FA5] on the terms and `Int.negOnePow_neg` for the exponent. -/
theorem complexChernFactor_of_termwiseDual (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hP' : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n)
      (ρ (-n)))
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (n : ℤ) :
    complexChernFactor C sY P' (fun m ↦ ρ (-m)) hP' n =
      Units.map (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
        (complexChernFactor C sY P ρ hP (-n)) := by
  have := hP (-n)
  have := hP' n
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    (P.X (-n)) (ρ (-n)) (hP (-n))
  have hu : totalChernUnit C sY (P'.X n) (ρ (-n)) =
      Units.map (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
        (totalChernUnit C sY (P.X (-n)) (ρ (-n))) := by
    refine Eq.trans (Units.ext ?_) (totalChernUnit_dualSheaf C sY (P.X (-n)) (ρ (-n)))
    rw [val_totalChernUnit, val_totalChernUnit]
    exact totalChern_congr C sY (e n) rfl
  show totalChernUnit C sY (P'.X n) (ρ (-n)) ^ ((n.negOnePow : ℤˣ) : ℤ) =
    Units.map (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
      (totalChernUnit C sY (P.X (-n)) (ρ (-n)) ^ (((-n).negOnePow : ℤˣ) : ℤ))
  rw [hu, map_zpow, Int.negOnePow_neg]

/-- **The sign rule for a bounded complex of constant ranks.** If `𝓕^n ≅ (𝓔^{-n})^∨` for every
`n` then `c(𝓕^•)` is the `(-1)^p`-scaling of `c(𝓔^•)`.

No relation between the two rank functions is assumed; see the implementation notes. -/
theorem complexChernBounded_of_termwiseDual (ρ ρ' : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hP' : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P'.X n)
      (ρ' n))
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) :
    complexChernBounded C sY P' ρ' hP' =
      TotalChowClass.signScale (complexChernBounded C sY P ρ hP) := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sY).elim _ _
  -- the ranks of the dual terms are the reflected ranks of the terms
  have hdual : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P'.X n) (ρ (-n)) := fun n ↦
    isFiniteLocallyFreeOfRank_of_iso_dualSheaf (hP (-n)) (e n)
  obtain rfl : ρ' = Finsupp.equivMapDomain (Equiv.neg ℤ) ρ := Finsupp.ext fun n ↦
    Scheme.Modules.isFiniteLocallyFreeOfRank_unique (P'.X n) (hP' n) (hdual n) y
  -- both sides as ordered products over the support of `ρ` and its reflection
  have hsupp : ∀ n ∉ ρ.support.image (fun m : ℤ ↦ -m),
      (Finsupp.equivMapDomain (Equiv.neg ℤ) ρ) n = 0 := by
    intro n hn
    have h : -n ∉ ρ.support := fun h ↦ hn (Finset.mem_image.2 ⟨-n, h, neg_neg n⟩)
    rw [equivMapDomain_neg_apply]
    exact Finsupp.notMem_support_iff.1 h
  rw [complexChernBounded_eq_prod C sY P' _ hP' _ hsupp,
    complexChernBounded_eq_prod C sY P ρ hP ρ.support (fun n hn ↦
      Finsupp.notMem_support_iff.1 hn)]
  -- compare the two ordered products as units
  have key : complexChernProd C sY P' (Finsupp.equivMapDomain (Equiv.neg ℤ) ρ) hP'
        (ρ.support.image (fun m : ℤ ↦ -m)) =
      Units.map (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
        (complexChernProd C sY P ρ hP ρ.support) := by
    set φ := (TotalChowClass.signScaleRingHom (C := C) (sY := sY)).toMonoidHom
    set t := ρ.support.image (fun m : ℤ ↦ -m) with ht
    have hfac : (t.sort (· ≤ ·)).map
          (complexChernFactor C sY P' (Finsupp.equivMapDomain (Equiv.neg ℤ) ρ) hP') =
        (t.sort (· ≤ ·)).map fun n ↦ Units.map φ (complexChernFactor C sY P ρ hP (-n)) :=
      List.map_congr_left fun n _ ↦
        complexChernFactor_of_termwiseDual C sY P P' ρ hP hdual e n
    have hmap : (t.sort (· ≤ ·)).map
          (fun n ↦ Units.map φ (complexChernFactor C sY P ρ hP (-n))) =
        (((t.sort (· ≤ ·)).map (fun n : ℤ ↦ -n)).map
          (complexChernFactor C sY P ρ hP)).map (Units.map φ) := by
      simp only [List.map_map, Function.comp_def]
    rw [complexChernProd, complexChernProd, hfac, hmap, ← map_list_prod (Units.map φ)]
    refine congrArg (Units.map φ) ?_
    -- the reflected sorted support is a permutation of the sorted support
    refine list_prod_map_of_perm_of_commute (complexChernFactor C sY P ρ hP) ?_ ?_
    · refine (List.perm_ext_iff_of_nodup (((t.sort_nodup _)).map (neg_injective))
        (ρ.support.sort_nodup _)).2 fun m ↦ ?_
      simp only [List.mem_map, Finset.mem_sort, ht, Finset.mem_image]
      refine ⟨?_, fun hm ↦ ⟨-m, ⟨m, hm, rfl⟩, neg_neg m⟩⟩
      rintro ⟨n, ⟨k, hk, rfl⟩, rfl⟩
      simpa using hk
    · exact fun x y ↦ commute_complexChernFactor C sY P P ρ ρ hP hP x y
  rw [key, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    TotalChowClass.signScaleRingHom_apply]

end Bounded

/-! ### The sign rule for a locally bounded complex -/

section LocallyBounded

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P P' : CochainComplex Y.Modules ℤ}

/-- **The termwise dual isomorphisms pull back.** If `𝓕^n ≅ (𝓔^{-n})^∨` then
`(g^*𝓕)^n ≅ ((g^*𝓔)^{-n})^∨` for every `g : Z ⟶ Y`, by the base-change isomorphism
`g^*(ℰ^∨) ≅ (g^*ℰ)^∨` of [Stacks, Tag 0GMX]. -/
def pullbackComplex_termwiseDualIso (hP : IsLocallyBoundedFiniteLocallyFree P)
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) {Z : Scheme.{u}} (g : Z ⟶ Y) (n : ℤ) :
    (pullbackComplex g P').X n ≅ dualSheaf ((pullbackComplex g P).X (-n)) :=
  (Scheme.Modules.pullback g).mapIso (e n) ≪≫
    @asIso _ _ _ _ (pullbackDualMap g (P.X (-n)))
      (pullbackDualMap_isIso g (P.X (-n)) (hP.1 (-n)))

/-- **On a rank locus of `𝓔^•` the dual complex has the reflected constant ranks.** The term
`(𝓕|_{Y_ρ})^n` is the dual of `(𝓔|_{Y_ρ})^{-n}`, which has constant rank `ρ(-n)`, so it has
constant rank `ρ(-n)` by the dual-at-a-constant-rank clause of [Stacks, Tag 0FA7]. -/
theorem isFiniteLocallyFreeOfRank_pullbackComplex_complexRankLocus_of_termwiseDual
    (hP : IsLocallyBoundedFiniteLocallyFree P)
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (ρ : ℤ →₀ ℕ) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((pullbackComplex (complexRankLocus hP ρ).ι P').X n)
      (Finsupp.equivMapDomain (Equiv.neg ℤ) ρ n) := by
  rw [equivMapDomain_neg_apply]
  exact isFiniteLocallyFreeOfRank_of_iso_dualSheaf
    (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ (-n))
    (pullbackComplex_termwiseDualIso hP e (complexRankLocus hP ρ).ι n)

/-- **The sign rule for the total Chern class of a termwise dual complex.** Let `𝓔^•` and `𝓕^•`
be locally bounded complexes of finite locally free `𝒪_Y`-modules with `𝓕^n ≅ (𝓔^{-n})^∨` for
every `n`. Then

  `c(𝓕^•) = (-1)^p c(𝓔^•)`

in `∏_{p ≥ 0} A^p(Y)`.

The identity is checked on the rank loci of `𝓔^•`, where both complexes are bounded with
constant ranks — the rank of `𝓕^n` there being the rank of `𝓔^{-n}` by the dual-at-a-constant-rank
clause of [Stacks, Tag 0FA7] — and there it is
`Stacks.Chow.complexChernBounded_of_termwiseDual`. The termwise dual isomorphisms restrict to the
loci by the base-change isomorphism `g^*(ℰ^∨) ≅ (g^*ℰ)^∨` of [Stacks, Tag 0GMX]. -/
theorem complexChern_of_termwiseDual (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) :
    complexChern C sY hP' = TotalChowClass.signScale (complexChern C sY hP) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [TotalChowClass.res_signScale, res_complexChern_complexRankLocus C sY hP ρ.down,
    res_complexChern_eq_complexChernBounded C sY hP' (complexRankLoci hP ρ).ι rfl
      (Finsupp.equivMapDomain (Equiv.neg ℤ) ρ.down)
      (isFiniteLocallyFreeOfRank_pullbackComplex_complexRankLocus_of_termwiseDual hP e ρ.down)]
  exact complexChernBounded_of_termwiseDual C _ (pullbackComplex (complexRankLoci hP ρ).ι P)
    (pullbackComplex (complexRankLoci hP ρ).ι P') ρ.down _
    (isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down) _
    (pullbackComplex_termwiseDualIso hP e (complexRankLocus hP ρ.down).ι)

/-- **The sign rule degreewise**, as the source states it: `c_p(𝓕^•) = (-1)^p c_p(𝓔^•)` in
`A^p(Y)`. -/
theorem complexChern_apply_of_termwiseDual (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (p : ℕ) :
    complexChern C sY hP' p = ((-1 : ℤ) ^ p) • complexChern C sY hP p := by
  rw [complexChern_of_termwiseDual C sY hP hP' e, TotalChowClass.signScale_apply]

/-! ### The alternating rank class is unchanged -/

/-- **The `(-1)^p`-scaling fixes the alternating rank class.** The class is an integer multiple
of the unit on every rank locus, and the unit sits in degree `0`. -/
theorem signScale_complexRankClass (hP : IsLocallyBoundedFiniteLocallyFree P) :
    TotalChowClass.signScale (complexRankClass C sY hP) = complexRankClass C sY hP := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [TotalChowClass.res_signScale, res_complexRankClass_complexRankLocus C sY hP ρ.down,
    TotalChowClass.signScale_zsmul_one]

/-- **The alternating rank of a termwise dual complex is the alternating rank of the complex.**
On a rank locus `Y_ρ` of `𝓔^•` the dual complex has constant ranks `n ↦ ρ(-n)`, so its
alternating rank there is `∑_n (-1)^n ρ(-n) = ∑_n (-1)^n ρ(n)`: the substitution `n ↦ -n` is a
bijection of the index set and `(-1)^{-n} = (-1)^n`.

This is the degree-zero third of [Stacks, Tag 0FAE] at the level of complexes: `P_0(𝓕^•) =
(-1)^0 P_0(𝓔^•)`, the rank of a complex not being changed by dualizing. -/
theorem complexRankClass_of_termwiseDual (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) :
    complexRankClass C sY hP' = complexRankClass C sY hP := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_complexRankLoci hP) fun ρ ↦ ?_
  rw [res_complexRankClass_complexRankLocus C sY hP ρ.down]
  refine res_complexRankClass_eq_zsmul_one C sY hP' (complexRankLoci hP ρ).ι rfl _ ?_
  rintro σ ⟨y, hy⟩
  have hmem : complexRank hP' ((complexRankLocus hP ρ.down).ι y) = σ :=
    (mem_complexRankLocus hP').mp hy
  -- the ranks of the dual complex on the locus are the reflected ranks of `𝓔^•`
  have hσ : ∀ n : ℤ, σ n = ρ.down (-n) := by
    intro n
    -- the restriction to the locus has the same constant rank as the pullback
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((P'.X n).restrict (complexRankLocus hP ρ.down).ι) (ρ.down (-n)) := by
      rw [← equivMapDomain_neg_apply ρ.down n]
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        ((Scheme.Modules.restrictFunctorIsoPullback
          (complexRankLocus hP ρ.down).ι).app (P'.X n)).symm
        (isFiniteLocallyFreeOfRank_pullbackComplex_complexRankLocus_of_termwiseDual
          hP e ρ.down n)
    rw [← hmem, complexRank_apply,
      ← Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict
        (complexRankLocus hP ρ.down).ι (P'.X n) y]
    exact Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ _ y
  calc (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ))
      = ∑ᶠ n : ℤ, (((-n).negOnePow : ℤ) * (ρ.down (-n) : ℤ)) := by
        refine finsum_congr fun n ↦ ?_
        rw [hσ n, Int.negOnePow_neg]
    _ = ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ.down n : ℤ) :=
        finsum_comp_equiv (f := fun m : ℤ ↦ (m.negOnePow : ℤ) * (ρ.down m : ℤ)) (Equiv.neg ℤ)

/-! ### The sign rule for the power sums and the Chern character -/

/-- **The sign rule for the power-sum classes of a termwise dual complex.** `P_p(𝓕^•)` is the
`(-1)^p`-scaling of `P_p(𝓔^•)`.

The power sums are Newton's recursion of [Stacks, Tag 0F9B] applied to the alternating rank and
the homogeneous components of the total Chern class
(`Stacks.Chow.complexPowerSum`), and `Stacks.Chow.TotalChowClass.signScaleRingHom` is a ring
homomorphism, so it carries the recursion to the recursion
(`AlgebraicGeometry.map_newtonPowerSum`). Its two inputs are carried by
`Stacks.Chow.complexRankClass_of_termwiseDual` together with
`Stacks.Chow.signScale_complexRankClass` for the rank, and by
`Stacks.Chow.complexChern_of_termwiseDual` with
`Stacks.Chow.TotalChowClass.homComponent_signScale` for the Chern classes. -/
theorem complexPowerSum_of_termwiseDual (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (p : ℕ) :
    complexPowerSum C sY hP' p = TotalChowClass.signScale (complexPowerSum C sY hP p) := by
  have h0 : complexRankClass C sY hP' =
      TotalChowClass.signScaleRingHom (C := C) (sY := sY) (complexRankClass C sY hP) := by
    rw [TotalChowClass.signScaleRingHom_apply, signScale_complexRankClass]
    exact complexRankClass_of_termwiseDual C sY hP hP' e
  have h1 : (fun i : ℕ+ ↦ TotalChowClass.homComponent (i : ℕ) (complexChern C sY hP')) =
      fun i : ℕ+ ↦ TotalChowClass.signScaleRingHom (C := C) (sY := sY)
        (TotalChowClass.homComponent (i : ℕ) (complexChern C sY hP)) := by
    funext i
    rw [TotalChowClass.signScaleRingHom_apply, complexChern_of_termwiseDual C sY hP hP' e,
      TotalChowClass.homComponent_signScale]
  rw [complexPowerSum, complexPowerSum, h0, h1,
    ← map_newtonPowerSum (TotalChowClass.signScaleRingHom (C := C) (sY := sY)),
    TotalChowClass.signScaleRingHom_apply]

/-- **The sign rule degreewise for the power sums**, as the source states it:
`P_p(𝓕^•) = (-1)^p P_p(𝓔^•)` in `A^p(Y)`. -/
theorem complexPowerSumComponent_of_termwiseDual (hP : IsLocallyBoundedFiniteLocallyFree P)
    (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (p : ℕ) :
    complexPowerSumComponent C sY hP' p =
      ((-1 : ℤ) ^ p) • complexPowerSumComponent C sY hP p := by
  rw [complexPowerSumComponent, complexPowerSumComponent,
    complexPowerSum_of_termwiseDual C sY hP hP' e p, TotalChowClass.signScale_apply]

/-- **The sign rule for the Chern character of a termwise dual complex**, as the source states
it: `ch_p(𝓕^•) = (-1)^p ch_p(𝓔^•)` in `A^p(Y) ⊗ 𝐐`. The Chern character component is
`P_p/p!`, so the sign passes through the tensor factor. -/
theorem complexChernCharacterComponent_of_termwiseDual
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (p : ℕ) :
    complexChernCharacterComponent C sY hP' p =
      ((-1 : ℤ) ^ p) • complexChernCharacterComponent C sY hP p := by
  rw [complexChernCharacterComponent, complexChernCharacterComponent,
    complexPowerSumComponent_of_termwiseDual C sY hP hP' e p, TensorProduct.tmul_smul]

/-- **The Chern character sign rule with the rational scalar**, which is how the source writes
it: `ch_p(𝓕^•) = (-1)^p ch_p(𝓔^•)` with `(-1)^p` read in `𝐐`. The two readings agree because
`(-1)^p` is an integer and the `𝐐`-action on `A^p(Y) ⊗ 𝐐` restricts to the `𝐙`-action. -/
theorem complexChernCharacterComponent_of_termwiseDual'
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hP' : IsLocallyBoundedFiniteLocallyFree P')
    (e : ∀ n : ℤ, P'.X n ≅ dualSheaf (P.X (-n))) (p : ℕ) :
    complexChernCharacterComponent C sY hP' p =
      ((-1 : ℚ) ^ p) • complexChernCharacterComponent C sY hP p := by
  rw [complexChernCharacterComponent_of_termwiseDual C sY hP hP' e p,
    show ((-1 : ℚ) ^ p) = ((((-1 : ℤ) ^ p : ℤ) : ℚ)) by push_cast; ring,
    Int.cast_smul_eq_zsmul]

end LocallyBounded

end Stacks.Chow

end
