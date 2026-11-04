module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedGradingProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCase
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DirectSum
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.TotalLocalizedChernClassData
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree

/-!
# The Whitney formula for the classes `c^{(p)}(E)` of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with
`X = X₁ ∪ X₂` set-theoretically. For `E ∈ D(𝒪_X)` whose Chern classes are defined, and whose
restriction to `X₁ ∩ X₂` is a finite locally free module of rank `< p` in degree `0`, Stacks 0FAL
considers the element

  `c^{(p)}(E) = 1 + c_1(E) + … + c_{p-1}(E) + c'_p(E|_{X₂}) + c'_{p+1}(E|_{X₂}) + …`

of the group `A^{(p)}(X₂ ⟶ X)` of Stacks 0FA0, with `c'_i` the classes of Stacks 0F9H, and states
the Whitney formula `c^{(p+q)}(E ⊕ F) = c^{(p)}(E) c^{(q)}(F)` for the multiplication of
Stacks 0FA0 (`Stacks.Chow.localizedGradingMul`).

As stated in the source, with the rank hypothesis on `X₁ ∩ X₂`, the formula is false; see the
docstring of `Stacks.Chow.closedCoverTotalChernClass_biprod` for a counterexample. It holds, and
is proved here, under the hypothesis that `E|_{X₁}` and `F|_{X₁}` are finite locally free of
ranks `< p` and `< q` in degree `0` — the hypothesis of Stacks 0F9I, to which the source's
"`𝒪_{X₁}`-modules" points. The hypothesis on `X₁ ∩ X₂` is derived from it.

## Main definitions

* `Stacks.Chow.closedCoverTotalChernClass` — the class `c^{(p)}(E) ∈ A^{(p)}(X₂ ⟶ X)`.
* `Stacks.Chow.TotalChowClass.intComponent` — the component of a total Chow class in a degree
  `n ∈ ℤ`, zero for `n < 0`.
* `Stacks.Chow.derivedPullbackSingleIsoOfIsFiniteLocallyFree` — `Lg^*(M[0]) ≅ (g^*M)[0]` for a
  finite locally free `M`.

## Main results

* `Stacks.Chow.closedCoverTotalChernClass_biprod` — **Stacks 0FAL**, corrected.
* `Stacks.Chow.IsFiniteLocallyFreeOfRankLT.pullback`,
  `Stacks.Chow.IsFiniteLocallyFreeOfRankLT.biprod`
  — ranks `< p` are preserved by pullback, and add under direct sums.
* `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd`,
  `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod` — the hypotheses of
  Stacks 0F9H on `E|_{X₂}` and on `(E ⊕ F)|_{X₂}`, from those on `E|_{X₁}` and `F|_{X₁}`.
* `Stacks.Chow.TotalChowClass.intComponent_mul` — `(c d)_n = ∑_{0 ≤ i ≤ n} c_i d_{n-i}`.
* `Stacks.Chow.IsClosedCoverExtension.supportedRightComp`,
  `Stacks.Chow.IsClosedCoverExtension.ambientSupportedMul` — the first two multiplications of
  Stacks 0FA0 on extensions.
* `Stacks.Chow.localizedGradingPush_closedCoverTotalChernClass` — the pushed components of
  `c^{(p)}(E)` are the `c_i(E)` (Stacks 0F9I).

## Implementation notes

The proof is the one of the source, "immediate from the characterization of the classes in
Lemma 0F9H and the additivity in Lemma 0F9F". Below the cutoff the pushed components of
`c^{(p)}(E)` and `c^{(q)}(F)` are the Chern classes of `E` and `F` (by Stacks 0F9I in the degrees
from the cutoff on), so the components agree by `c(E ⊕ F) = c(E) c(F)`. From the cutoff on, both
sides extend `c_n((E ⊕ F)|_{X₂}) = ∑ c_i(E|_{X₂}) c_{n-i}(F|_{X₂})` along the closed cover, summand
by summand, and an extension is unique.

The source assumes `E` and `F` perfect; only the definedness of their Chern classes is used, so
perfectness is not assumed (as in `StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCase`).

## References

* [Stacks Project, Tag 0FAL](https://stacks.math.columbia.edu/tag/0FAL)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Finite locally free modules of rank `< p` -/

section Rank

/-- On an open subscheme `U` of `Y`, the restriction of an `𝒪_Y`-module to `U` (in the
ringed-space spelling of `Stacks.Chow.IsFiniteLocallyFreeOfRankLT`) has the rank of its pullback
along `U ⟶ Y`. -/
private theorem isFiniteLocallyFreeOfRank_pullback_ι {Y : Scheme.{u}} (U : Y.Opens)
    {M : Y.Modules} {r : ℕ}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((RingedSpace.restrictModules Y.toRingedSpace U).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj M) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) h

/-- The converse spelling of `isFiniteLocallyFreeOfRank_pullback_ι`. -/
private theorem isFiniteLocallyFreeOfRank_restrictModules_of_pullback_ι {Y : Scheme.{u}}
    (U : Y.Opens) {M : Y.Modules} {r : ℕ}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((RingedSpace.restrictModules Y.toRingedSpace U).obj M) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm h

/-- A module of rank `r` on an open `U` has rank `r` on every smaller open `V ≤ U`, in the
pullback spelling. -/
private theorem isFiniteLocallyFreeOfRank_pullback_ι_of_le {Y : Scheme.{u}} {U V : Y.Opens}
    (hVU : V ≤ U) {M : Y.Modules} {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj M) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj M) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp (Y.homOfLE hVU) U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (Y.homOfLE_ι hVU)).app M)
    (isFiniteLocallyFreeOfRank_pullback (Y.homOfLE hVU) _ r)

/-- **A direct sum of finite locally free modules of ranks `< p` and `< q` has rank `< p + q`.** -/
theorem IsFiniteLocallyFreeOfRankLT.biprod {Y : Scheme.{u}} {M N : Y.Modules} {p q : ℕ}
    (hM : IsFiniteLocallyFreeOfRankLT M p) (hN : IsFiniteLocallyFreeOfRankLT N q) :
    IsFiniteLocallyFreeOfRankLT (M ⊞ N : Y.Modules) (p + q) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := hM.1
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N := hN.1
  refine ⟨AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod M N, fun x => ?_⟩
  obtain ⟨U₀, hxU, r, hr, hU⟩ := hM.2 x
  obtain ⟨V₀, hxV, s, hs, hV⟩ := hN.2 x
  let U : Y.Opens := U₀
  let V : Y.Opens := V₀
  have := isFiniteLocallyFreeOfRank_pullback_ι U hU
  have := isFiniteLocallyFreeOfRank_pullback_ι V hV
  have := isFiniteLocallyFreeOfRank_pullback_ι_of_le (inf_le_left : U ⊓ V ≤ U) (M := M) (r := r)
  have := isFiniteLocallyFreeOfRank_pullback_ι_of_le (inf_le_right : U ⊓ V ≤ V) (M := N) (r := s)
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, r + s, by omega, ?_⟩
  refine isFiniteLocallyFreeOfRank_restrictModules_of_pullback_ι (U ⊓ V) ?_
  have := preservesBinaryBiproducts_of_preservesBiproducts (Scheme.Modules.pullback (U ⊓ V).ι)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullback (U ⊓ V).ι).mapBiprod M N).symm
    (isFiniteLocallyFreeOfRank_biprod _ _ r s)

end Rank

/-! ### Restrictions of a module of rank `< p` placed in degree `0` -/

section Derived

/-- **The derived pullback of a finite locally free module placed in degree `0`** is its pullback
placed in degree `0`: the module, in degree `0`, is a K-flat complex. -/
def derivedPullbackSingleIsoOfIsFiniteLocallyFree {W Y : Scheme.{u}} (g : W ⟶ Y)
    (M : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pullback g).obj M) :=
  (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app M) ≪≫
    Cohomology.derivedPullbackIsoPullbackOfKFlat g.toLRSHom.toShHom _
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _
        (isLocallyBoundedFiniteLocallyFree_single M)) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pullback g) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app _).symm

/-- **Restriction along a commutative square.** If `a ≫ i = b ≫ j` and `E|_Z` (the derived
pullback along `i : Z ⟶ X`) is isomorphic to a finite locally free module of rank `< p` placed in
degree `0`, then so is the restriction `(E|_Y)|_W` along `j : Y ⟶ X` and then `b : W ⟶ Y`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq
    {W X Y Z : Scheme.{u}} {i : Z ⟶ X} {j : Y ⟶ X} {a : W ⟶ Z} {b : W ⟶ Y} (h : a ≫ i = b ≫ j)
    {E : DerivedCategory X.Modules} {p : ℕ}
    (hrank : ∃ M : Z.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        b.toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            j.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hrank
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := hM.1
  have hsq : b.toLRSHom.toShHom ≫ j.toLRSHom.toShHom =
      a.toLRSHom.toShHom ≫ i.toLRSHom.toShHom :=
    congrArg (fun f => f.toLRSHom.toShHom) h.symm
  exact ⟨(Scheme.Modules.pullback a).obj M, hM.pullback a,
    ⟨(Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        b.toLRSHom.toShHom j.toLRSHom.toShHom).app E ≪≫
      (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        a.toLRSHom.toShHom i.toLRSHom.toShHom).app E).symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom).mapIso e ≪≫
      derivedPullbackSingleIsoOfIsFiniteLocallyFree a M⟩⟩

/-- **From `X₁` to `X₁ ∩ X₂`.** If `E|_{X₁}` is isomorphic to a finite locally free module of rank
`< p` placed in degree `0`, so is `(E|_{X₂})|_{X₁ ×_X X₂}`: this is the hypothesis of Stacks 0F9H
on `E₂ = E|_{X₂}`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd {X X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) {E : DerivedCategory X.Modules} {p : ℕ}
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq pullback.condition hrank

/-- **Direct sums.** If `E|_W` and `F|_W` are isomorphic to finite locally free modules of ranks
`< p` and `< q` placed in degree `0`, then `(E ⊕ F)|_W` is isomorphic to one of rank `< p + q`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod {W Y : Scheme.{u}} (z : W ⟶ Y)
    {E F : DerivedCategory Y.Modules} {p q : ℕ}
    (hE : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hF : ∃ N : W.Modules, IsFiniteLocallyFreeOfRankLT N q ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj F ≅ (DerivedCategory.singleFunctor _ 0).obj N)) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M (p + q) ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj (E ⊞ F : DerivedCategory Y.Modules) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hE
  obtain ⟨N, hN, ⟨e'⟩⟩ := hF
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.singleFunctor W.Modules 0)
  exact ⟨M ⊞ N, hM.biprod hN, ⟨derivedPullbackBiprodIso z E F ≪≫ biprod.mapIso e e' ≪≫
    ((DerivedCategory.singleFunctor W.Modules 0).mapBiprod M N).symm⟩⟩

end Derived
/-! ### Transport of degrees -/

section Transport

variable {C : ChowSituation.{u}}

/-- Two transports along equalities of degrees compose to one. -/
theorem bivariantClassDegreeCongr_bivariantClassDegreeCongr {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX}
    {a b c : ℤ} (h : a = b) (h' : b = c) (x : BivariantClass C G sX sY f hf a) :
    bivariantClassDegreeCongr C G sX sY f hf h' (bivariantClassDegreeCongr C G sX sY f hf h x) =
      bivariantClassDegreeCongr C G sX sY f hf (h.trans h') x := by
  subst h h'
  rfl

/-- The product of Chow cohomology classes commutes with transport along equalities of degrees. -/
theorem BivariantClass.mulId_bivariantClassDegreeCongr {Y : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {a a' b b' : ℤ} (ha : a = a') (hb : b = b')
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sY a)
    (y : chowCohomologyComponent C (gysinSystemOfInvertible C) sY b) :
    (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) ha x).mulId C sY
        (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) hb y) =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by rw [ha, hb])
        (x.mulId C sY y) := by
  subst ha hb
  rfl

/-- The pushforward of Stacks 0EPK commutes with transport along equalities of degrees. -/
theorem properPushforwardChowCohomology_bivariantClassDegreeCongr {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : Y ⟶ X} [IsProper f] [LocallyOfFiniteType f] {hf : f ≫ sX = sY} {a b : ℤ} (h : a = b)
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sX f hf a) :
    properPushforwardChowCohomology C sX sY f hf
        (bivariantClassDegreeCongr C _ sY sX f hf h c) =
      bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) h
        (properPushforwardChowCohomology C sX sY f hf c) := by
  subst h
  rfl

/-- The restriction of Chow cohomology classes commutes with transport along equalities of
degrees. -/
theorem chowCohomologyRestriction_bivariantClassDegreeCongr {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType f] {a b : ℤ}
    (h : a = b) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX a) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f b
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantClassDegreeCongr C _ sX sX (𝟙 X) (Category.id_comp sX) h c) =
      bivariantClassDegreeCongr C _ (f ≫ sX) (f ≫ sX) (𝟙 Y) (Category.id_comp _) h
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f a
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) := by
  subst h
  rfl

end Transport

/-! ### Total classes read in integer degrees -/

section IntComponent

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The component of degree `n ∈ ℤ` of a total class** `c ∈ ∏_{p ≥ 0} A^p(Y)`: the component
`c_n` for `n ≥ 0`, and `0` for `n < 0`. -/
def TotalChowClass.intComponent (c : TotalChowClass C sY) (n : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sY n :=
  if h : 0 ≤ n then
    bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (Int.toNat_of_nonneg h)
      (c n.toNat)
  else 0

variable {C sY}

/-- In a degree `k ≥ 0` the integer-degree component is the component. -/
theorem TotalChowClass.intComponent_natCast (c : TotalChowClass C sY) (k : ℕ) :
    c.intComponent C sY k = c k := by
  rw [TotalChowClass.intComponent, dite_eq_left (Int.natCast_nonneg k)]
  rfl

/-- In a negative degree the integer-degree component vanishes. -/
theorem TotalChowClass.intComponent_of_neg (c : TotalChowClass C sY) {n : ℤ} (hn : n < 0) :
    c.intComponent C sY n = 0 :=
  dite_eq_right (not_le.mpr hn)

/-- **The components of a product of total classes, in integer degrees**:
`(c d)_n = ∑_{0 ≤ i ≤ n} c_i d_{n - i}`. -/
theorem TotalChowClass.intComponent_mul (c d : TotalChowClass C sY) (n : ℤ) :
    (c * d).intComponent C sY n = ∑ i ∈ Finset.Icc 0 n,
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by omega)
        ((c.intComponent C sY i).mulId C sY (d.intComponent C sY (n - i))) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [TotalChowClass.intComponent_of_neg _ hn, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have key : ∀ (a a' b b' : ℕ) (ha : a = a') (hb : b = b') {N : ℤ} (h : (a : ℤ) + b = N)
      (h' : (a' : ℤ) + b' = N),
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) h
          ((c a).mulId C sY (d b)) =
        bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) h'
          ((c a').mulId C sY (d b')) := by
    intro a a' b b' ha hb N h h'
    subst ha hb
    rfl
  rw [TotalChowClass.intComponent_natCast, TotalChowClass.mul_apply]
  refine Finset.sum_nbij' (fun j => (m : ℤ) - j) (fun i => (m - i).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [TotalChowClass.mulTerm, dite_eq_left hj', TotalChowClass.intComponent,
      dite_eq_left (by omega), TotalChowClass.intComponent, dite_eq_left (by omega),
      BivariantClass.mulId_bivariantClassDegreeCongr,
      bivariantClassDegreeCongr_bivariantClassDegreeCongr]
    exact key _ _ _ _ (by omega) (by omega) _ _

/-- The restriction of a component of a total class is the component of the restriction. -/
theorem TotalChowClass.chowCohomologyRestriction_intComponent {Y' : Scheme.{u}} (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] (c : TotalChowClass C sY) (n : ℤ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (c.intComponent C sY n) =
      (TotalChowClass.res h rfl c).intComponent C (h ≫ sY) n := by
  rw [TotalChowClass.intComponent, TotalChowClass.intComponent]
  split_ifs with hn
  · rw [chowCohomologyRestriction_bivariantClassDegreeCongr, TotalChowClass.res_rfl_apply]
  · exact map_zero _

end IntComponent
/-! ### The first and second multiplications of Stacks 0FA0 on extensions -/

section Extension

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] {p q : ℤ}

/-- **The first multiplication of Stacks 0FA0 on extensions, through the characterization.** If
`c ∈ A^p(X₂ ⟶ X)` extends `a ∈ A^p(X₂)`, with `a` vanishing over `X₁ ×_X X₂`, then for
`d ∈ A^q(X)` the composition `c ∘ d` extends `a d|_{X₂}`. -/
theorem IsClosedCoverExtension.supportedRightComp
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    {c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl a c)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      (a.mulId C (i₂ ≫ sX) (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ q
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d))
      (Stacks.Chow.supportedRightComp C (i₂ ≫ sX) sX i₂ rfl c d) := by
  rw [hc.eq_closedCoverExtension hcover ha, supportedRightComp_closedCoverExtension]
  exact isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

/-- **The second multiplication of Stacks 0FA0 on extensions, through the characterization.**
For `d ∈ A^p(X)`, if `c ∈ A^q(X₂ ⟶ X)` extends `b ∈ A^q(X₂)`, with `b` vanishing over
`X₁ ×_X X₂`, then `res(d) ∘ c` extends `d|_{X₂} b`. -/
theorem IsClosedCoverExtension.ambientSupportedMul
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) q}
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂))
    {c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl q}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl b c) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      ((chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d).mulId C (i₂ ≫ sX) b)
      (Stacks.Chow.ambientSupportedMul C (i₂ ≫ sX) sX i₂ rfl d c) := by
  rw [hc.eq_closedCoverExtension hcover hb, ambientSupportedMul_closedCoverExtension]
  exact isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

end Extension

/-! ### The class `c^{(p)}(E)` and Stacks 0FAL -/

section Whitney

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)

/-- **The class `c^{(p)}(E) ∈ A^{(p)}(X₂ ⟶ X)`.** Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed
immersions whose images cover `X`, and let `E ∈ D(𝒪_X)` have defined Chern classes, with
`(E|_{X₂})|_{X₁ ∩ X₂}` isomorphic to a finite locally free module of rank `< p` placed in degree
`0`. Then

  `c^{(p)}(E) = 1 + c_1(E) + … + c_{p-1}(E) + c'_p(E|_{X₂}) + c'_{p+1}(E|_{X₂}) + …`:

its component in a degree `0 ≤ i < p` is `c_i(E) ∈ A^i(X)`, in a negative degree it is `0`, and
in a degree `i ≥ p` it is the class `c'_i(E|_{X₂}) ∈ A^i(X₂ ⟶ X)` of Stacks 0F9H
(`Stacks.Chow.closedCoverChernClass`), which is defined since a rank `< p` is a rank `< i`. -/
@[stacks 0FAL "the class c^(p)(E) in A^(p)(X₂ → X)"]
def closedCoverTotalChernClass {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
    (p : ℕ)
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p :=
  (fun i => (perfectChernClass C sX hE).intComponent C sX i.1,
    fun i => bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl
      (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg p) i.2))
      (closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl (hE.derivedPullback i₂) i.1.toNat hcover
        (hrank.imp fun _ hM => ⟨hM.1.mono (by have := i.2; omega), hM.2⟩)))

variable {C sX i₁ i₂ hcover}

variable {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) {p : ℕ}

/-- The components of `c^{(p)}(E)` below the cutoff are the Chern classes of `E`. -/
theorem closedCoverTotalChernClass_fst
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (i : {i : ℤ // i < (p : ℤ)}) :
    (closedCoverTotalChernClass C sX i₁ i₂ hcover hE p hrank).1 i =
      (perfectChernClass C sX hE).intComponent C sX i.1 :=
  rfl

/-- In a degree `i ≥ p`, the Chern class `c_i(E|_{X₂})` vanishes over `X₁ ×_X X₂` when
`(E|_{X₂})|_{X₁ ×_X X₂}` has rank `< p`. -/
theorem vanishesOver_intComponent_perfectChernClass
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    {i : ℤ} (hi : (p : ℤ) ≤ i) :
    BivariantClass.VanishesOver
      ((perfectChernClass C (i₂ ≫ sX) (hE.derivedPullback i₂)).intComponent C (i₂ ≫ sX) i)
      (pullback.snd i₁ i₂) := by
  rw [TotalChowClass.intComponent, dite_eq_left (by omega)]
  exact BivariantClass.VanishesOver.bivariantClassDegreeCongr C _
    (vanishesOver_perfectChernClass_of_rankLT C (i₂ ≫ sX) (pullback.snd i₁ i₂)
      (hE.derivedPullback i₂) i.toNat
      (hrank.imp fun _ hM => ⟨hM.1.mono (by omega), hM.2⟩))

/-- **The components of `c^{(p)}(E)` from the cutoff on are extensions**: in a degree `i ≥ p` the
component `c'_i(E|_{X₂})` extends `c_i(E|_{X₂})` (Stacks 0F9H). -/
theorem isClosedCoverExtension_closedCoverTotalChernClass_snd
    (hrank : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            i₂.toLRSHom.toShHom).obj E) ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (i : {i : ℤ // (p : ℤ) ≤ i}) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      ((perfectChernClass C (i₂ ≫ sX) (hE.derivedPullback i₂)).intComponent C (i₂ ≫ sX) i.1)
      ((closedCoverTotalChernClass C sX i₁ i₂ hcover hE p hrank).2 i) := by
  rw [TotalChowClass.intComponent, dite_eq_left (le_trans (Int.natCast_nonneg p) i.2)]
  exact IsClosedCoverExtension.bivariantClassDegreeCongr C sX i₁ i₂ _
    (isClosedCoverExtension_closedCoverChernClass C sX i₁ i₂ (i₂ ≫ sX) rfl _ _ hcover _)

/-- **The pushed components of `c^{(p)}(E)` are the Chern classes of `E`** (Stacks 0F9I), when
`E|_{X₁}` is isomorphic to a finite locally free module of rank `< p` placed in degree `0`. -/
theorem localizedGradingPush_closedCoverTotalChernClass
    (hrank : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) (i : ℤ) :
    localizedGradingPush C (i₂ ≫ sX) sX i₂ rfl
        (closedCoverTotalChernClass C sX i₁ i₂ hcover hE p
          (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂ hrank)) i =
      (perfectChernClass C sX hE).intComponent C sX i := by
  rcases lt_or_ge i (p : ℤ) with h | h
  · rw [localizedGradingPush_of_lt _ h]
    rfl
  · rw [localizedGradingPush_of_le _ h]
    change properPushforwardChowCohomology C sX (i₂ ≫ sX) i₂ rfl
      (bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl _ _) = _
    rw [properPushforwardChowCohomology_bivariantClassDegreeCongr,
      properPushforwardChowCohomology_closedCoverChernClass C sX i₁ i₂ hE i.toNat hcover
        (hrank.imp fun _ hM => ⟨hM.1.mono (by omega), hM.2⟩),
      TotalChowClass.intComponent, dite_eq_left (by omega)]

variable {F : DerivedCategory X.Modules} (hF : HasDefinedChernClasses F) {q : ℕ}

/-- Let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set-theoretically,
and let `E, F ∈ D(𝒪_X)` have defined Chern classes, with `E|_{X₁}` and `F|_{X₁}` isomorphic to
finite locally free `𝒪_{X₁}`-modules of rank `< p` and `< q` placed in degree `0`. Then

  `c^{(p+q)}(E ⊕ F) = c^{(p)}(E) c^{(q)}(F)`   in `A^{(p+q)}(X₂ ⟶ X)`,

with the multiplication of Stacks 0FA0 (`Stacks.Chow.localizedGradingMul`). The hypotheses of
Stacks 0F9H on `E|_{X₂}`, `F|_{X₂}` and `(E ⊕ F)|_{X₂}`, under which the classes `c^{(·)}` are
defined, follow from these
(`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd`,
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod`), and so does the
definedness of the Chern classes of `E ⊕ F` (`Stacks.Chow.hasDefinedChernClasses_biprod`).

**The correction.** The source assumes in (2) that the restrictions `E|_{X₁ ∩ X₂}` and
`F|_{X₁ ∩ X₂}` are finite locally free of rank `< p`, `< q` (calling them `𝒪_{X₁}`-modules). As
written, on `X₁ ∩ X₂`, the statement is false: let `X = X₁ ⊔ X₂` be a disjoint union of
`X₁ = ℙ¹_k` over a field and a point `X₂`, so that (2) is vacuous; take `E = 𝒪(1)^{⊕ 2}` on `X₁`
and `0` on `X₂`, `F = 0` and `p = q = 1`. In degree `1 < p + q` the component of
`c^{(2)}(E ⊕ F)` is `c_1(E) ≠ 0`, while that of `c^{(1)}(E) c^{(1)}(F)` is
`(i_{2,*} c'_1(E|_{X₂})) · 1 + 1 · (i_{2,*} c'_1(0)) = 0`. The hypothesis on `X₁`, to which the
phrase "`𝒪_{X₁}`-modules" points, is the one Stacks 0F9I needs to compare the pushed classes
`i_{2,*} c'_i(E|_{X₂})` with `c_i(E)`, and with it the statement holds. Perfectness of `E`, `F`
is not used, only that their Chern classes are defined. -/
@[stacks 0FAL "CORRECTED: hypothesis (2) is imposed on E|_{X₁}, F|_{X₁} (as written, on \
X₁ ∩ X₂, it is false: X = ℙ¹ ⊔ pt, E = 𝒪(1)² on ℙ¹ and 0 on pt, F = 0, p = q = 1, where the \
degree-1 components are c₁(E) ≠ 0 and 0)"]
theorem closedCoverTotalChernClass_biprod
    (hrankE : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (hrankF : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M q ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        i₁.toLRSHom.toShHom).obj F ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    closedCoverTotalChernClass C sX i₁ i₂ hcover (hasDefinedChernClasses_biprod hE hF) (p + q)
        (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂
          (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_biprod i₁ hrankE hrankF)) =
      localizedGradingMul C (i₂ ≫ sX) sX i₂ rfl
        (closedCoverTotalChernClass C sX i₁ i₂ hcover hE p
          (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂ hrankE))
        (closedCoverTotalChernClass C sX i₁ i₂ hcover hF q
          (exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂ hrankF)) := by
  have hEF := hasDefinedChernClasses_biprod hE hF
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · rw [localizedGradingMul_fst, closedCoverTotalChernClass_fst,
      perfectChernClass_biprod C sX hE hF, TotalChowClass.intComponent_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [localizedGradingPush_closedCoverTotalChernClass hE hrankE,
      localizedGradingPush_closedCoverTotalChernClass hF hrankF]
  · set cE := perfectChernClass C (i₂ ≫ sX) (hE.derivedPullback i₂)
    set cF := perfectChernClass C (i₂ ≫ sX) (hF.derivedPullback i₂)
    have hW : perfectChernClass C (i₂ ≫ sX) (hEF.derivedPullback i₂) = cE * cF := by
      rw [← res_perfectChernClass_derivedPullback_of_comp_eq C sX hEF i₂ rfl,
        perfectChernClass_biprod C sX hE hF hEF, map_mul,
        res_perfectChernClass_derivedPullback_of_comp_eq C sX hE i₂ rfl,
        res_perfectChernClass_derivedPullback_of_comp_eq C sX hF i₂ rfl]
    have hres : ∀ {G : DerivedCategory X.Modules} (hG : HasDefinedChernClasses G) (i : ℤ),
        chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ i
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          ((perfectChernClass C sX hG).intComponent C sX i) =
        (perfectChernClass C (i₂ ≫ sX) (hG.derivedPullback i₂)).intComponent C (i₂ ≫ sX) i :=
      fun hG i => by
        rw [TotalChowClass.chowCohomologyRestriction_intComponent,
          res_perfectChernClass_derivedPullback_of_comp_eq C sX hG i₂ rfl]
    have hn := n.2
    push_cast at hn
    have hE₂ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂ hrankE
    have hF₂ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_pullbackSnd i₁ i₂ hrankF
    refine IsClosedCoverExtension.eq hcover
      (isClosedCoverExtension_closedCoverTotalChernClass_snd hEF _ n) ?_
    rw [hW, TotalChowClass.intComponent_mul, localizedGradingMul_snd]
    refine IsClosedCoverExtension.sum C sX i₁ i₂ _ fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    refine IsClosedCoverExtension.bivariantClassDegreeCongr C sX i₁ i₂ _ ?_
    by_cases hpi : (p : ℤ) ≤ i
    · by_cases hqi : (q : ℤ) ≤ n.1 - i
      · rw [localizedGradingHighTerm_of_le_of_le _ _ _ hpi hqi]
        exact IsClosedCoverExtension.supportedMul C sX i₁ i₂ hcover
          (vanishesOver_intComponent_perfectChernClass hE hE₂ hpi)
          (vanishesOver_intComponent_perfectChernClass hF hF₂ hqi)
          (isClosedCoverExtension_closedCoverTotalChernClass_snd hE _ ⟨i, hpi⟩)
          (isClosedCoverExtension_closedCoverTotalChernClass_snd hF _ ⟨n.1 - i, hqi⟩)
      · rw [localizedGradingHighTerm_of_le_of_lt _ _ _ hpi (not_le.mp hqi), ← hres hF]
        exact IsClosedCoverExtension.supportedRightComp C sX i₁ i₂ hcover
          (vanishesOver_intComponent_perfectChernClass hE hE₂ hpi)
          (isClosedCoverExtension_closedCoverTotalChernClass_snd hE _ ⟨i, hpi⟩) _
    · have hqi : (q : ℤ) ≤ n.1 - i := by omega
      rw [localizedGradingHighTerm_of_lt _ _ _ (not_le.mp hpi) hqi, ← hres hE]
      exact IsClosedCoverExtension.ambientSupportedMul C sX i₁ i₂ hcover _
        (vanishesOver_intComponent_perfectChernClass hF hF₂ hqi)
        (isClosedCoverExtension_closedCoverTotalChernClass_snd hF _ ⟨n.1 - i, hqi⟩)

end Whitney

end Stacks.Chow

end
