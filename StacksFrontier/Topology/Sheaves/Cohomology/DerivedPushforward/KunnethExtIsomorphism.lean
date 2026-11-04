module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the Künneth morphism for Ext

In the situation of the Künneth formula for Ext — morphisms of ringed spaces `a : X ⟶ S`,
`b : Y ⟶ S`, `p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ a = f = q ≫ b`, the exterior product
`K ⊠ M = Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M`, and the canonical morphism

`Ra_*R SheafHom(K, K') ⊗^𝐋_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`

of Stacks 0FXY — Stacks 0FXZ asserts that this morphism is an isomorphism when `a` and `b` are
quasi-compact and quasi-separated, `X` and `Y` are Tor independent over `S`, `K` and `M` are
perfect and `K'`, `M'` have quasi-coherent cohomology.

This file carries out the *shape* of the source's proof.  By construction the morphism of
Stacks 0FXY is the relative Künneth morphism of Stacks 0FLP at the pair of derived internal
homs, followed by the direct image of the comparison

`Lp^*R SheafHom(K, K') ⊗^𝐋_{𝒪_W} Lq^*R SheafHom(M, M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`,

so it is invertible as soon as both factors are.  The first factor is Stacks 0FLQ, the
invertibility of the relative Künneth morphism; the second is the source's identification
`R SheafHom(K, K') = K' ⊗^𝐋 K^∨` for perfect `K` (Cohomology, Stacks 08DQ) together with the
compatibility the source declines to check.  Neither is available here in usable form — 0FLQ is
carried, but only conditionally on four inputs of its own, and of 08DQ only the perfectness of
the dual is proved — so both are carried as explicit hypotheses; see the implementation notes.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.isIso_tensorMap`: a derived tensor product of two
  invertible morphisms is invertible.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_boxSheafHomMap`: the comparison of a tensor
  product of pulled-back derived internal homs with the derived internal hom of the exterior
  products is invertible as soon as the two pullback comparisons of Stacks 08I3 and the
  comparison of Stacks 0FXP on `W` are.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap`: the Künneth morphism for Ext is
  invertible as soon as the relative Künneth morphism of Stacks 0FLP at the two derived
  internal homs and the comparison above are.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_of_isIso_sheafHomComparisons`: the
  same with the comparison above replaced by its three constituents.
* `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_cartesian`: **Stacks 0FXZ** at a
  cartesian square of schemes, on the source's own hypotheses together with the two carried
  inputs.

## Implementation notes

*What is proved and what is assumed.*  The source's proof of Stacks 0FXZ has exactly two
steps, and this file proves neither of them; what it proves is that they suffice, which in the
source is the word "hence".  The two steps are carried as hypotheses:

* `hkunneth`, the invertibility of `Stacks.Cohomology.DerivedKunneth.kunnethMap` at the pair
  `(R SheafHom(K, K'), R SheafHom(M, M'))`.  This is Stacks 0FLQ, which the repository carries
  for this same `kunnethMap`, as
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_of_projectionFormulas_of_baseChange`,
  but itself only conditionally: that carrier takes as hypotheses the projection formula of
  Stacks 08EU for `a` and for `p` — of which only the case `K = 𝒪_Y[0]` is proved
  (`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`) — the
  Tor-independent base-change comparison of Stacks 08IB for the square, and the Stacks
  079U/0D5S monoidality coherence.  `hkunneth` is exactly that carrier's conclusion, so it is
  obtainable from it as soon as those four are supplied, and is taken here as a single
  hypothesis rather than as four.  Note that perfectness of `K` and of `M` does not help to
  discharge them: 0FLQ is applied to `R SheafHom(K, K')` and `R SheafHom(M, M')`, which for
  `K'` and `M'` merely in `D_QCoh` are quasi-coherent and not perfect, so the dévissage from
  finite locally free modules that proves the projection formula has nothing to run on.
* `hbox`, the invertibility of `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`.  This is
  where perfectness of `K` and of `M` is used in the source, through the identification
  `R SheafHom(K, K') = K' ⊗^𝐋 K^∨` of Cohomology, Stacks 08DQ; of that tag the repository
  carries only the half saying that the dual of a perfect object is perfect
  (`Stacks.SheafOfModules.isPerfect_derivedDual`), and the identification itself — invertibility
  of `Stacks.SheafOfModules.derivedTensorDualToSheafHom`, the canonical map of Stacks 08I1 — is
  not available.  The parenthesis "we omit the verification that with these identifications we
  obtain the same map" is also inside this hypothesis: `hbox` is about the canonical comparison
  `boxSheafHomMap`, so assuming it assumes both the identification and its compatibility with
  the Künneth morphism.

Because of this the geometric hypotheses of the source — quasi-compactness and
quasi-separatedness of `a` and `b`, Tor independence of `X` and `Y` over `S`, perfectness of
`K` and `M`, quasi-coherence of the cohomology of `K'` and `M'` — appear in
`isIso_kunnethExtMap_cartesian` but are not consumed by its proof.  They are the hypotheses
under which the two carried inputs are theorems, and they are kept in the statement so that it
is the statement of the source's lemma and not a different one.  The ringed-space results above
it drop them, and are correspondingly more general.

*Invertibility is transported along the definition, not reproved.*  Each proof below rewrites
the morphism into the composite it is by definition
(`Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap_eq` and the definitional unfoldings of
`boxSheafHomMap` and `tensorMap`) and then lets instance search assemble invertibility of a
composite of invertible morphisms, of the image of an invertible morphism under a functor, and
of the component of an invertible natural transformation.

## References

* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedQCoh
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

/-! ### Derived tensor products of invertible morphisms -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived tensor product `x ⊗^𝐋 y` of two invertible morphisms of `D(𝒪_Z)` is invertible.
The derived tensor product is a bifunctor, so `x ⊗^𝐋 y` is the composite of a component of the
natural transformation `- ⊗^𝐋 B` applied to `x` with the image of `y` under `A' ⊗^𝐋 -`, and both
are invertible. -/
theorem isIso_tensorMap {A A' B B' : DerivedCategory (Mod Z.sheaf)} (x : A ⟶ A') (y : B ⟶ B')
    (hx : IsIso x) (hy : IsIso y) : IsIso (tensorMap Z x y) := by
  have := hx
  have := hy
  unfold tensorMap
  infer_instance

end OneSpace

/-! ### Invertibility of the Künneth morphism for Ext -/

section Kunneth

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison
`Lp^*R SheafHom(K, K') ⊗^𝐋_{𝒪_W} Lq^*R SheafHom(M, M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`
is invertible as soon as its three constituents are: the two pullback comparisons

`Lp^*R SheafHom(K, K') ⟶ R SheafHom(Lp^*K, Lp^*K')`,
`Lq^*R SheafHom(M, M') ⟶ R SheafHom(Lq^*M, Lq^*M')`

of Stacks 08I3, and the comparison

`R SheafHom(Lp^*K, Lp^*K') ⊗^𝐋_{𝒪_W} R SheafHom(Lq^*M, Lq^*M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`

of Stacks 0FXP on `W`.  The comparison is by definition the derived tensor product of the first
two followed by the third. -/
theorem isIso_boxSheafHomMap (K K' : DerivedCategory (Mod X.sheaf))
    (M M' : DerivedCategory (Mod Y.sheaf))
    (hpull : IsIso (pullbackSheafHomMap p K K'))
    (hpull' : IsIso (pullbackSheafHomMap q M M'))
    (htensor : IsIso (sheafHomTensorMap W ((derivedPullbackFunctor p).obj K)
      ((derivedPullbackFunctor p).obj K') ((derivedPullbackFunctor q).obj M)
      ((derivedPullbackFunctor q).obj M'))) :
    IsIso (boxSheafHomMap p q K K' M M') := by
  have := htensor
  have := isIso_tensorMap W (pullbackSheafHomMap p K K') (pullbackSheafHomMap q M M')
    hpull hpull'
  unfold boxSheafHomMap
  infer_instance

/-- **The two steps of the proof of Stacks 0FXZ suffice.**  The Künneth morphism for Ext

`Ra_*R SheafHom(K, K') ⊗^𝐋_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`

is invertible as soon as the relative Künneth morphism of Stacks 0FLP is invertible at the pair
`(R SheafHom(K, K'), R SheafHom(M, M'))` and the comparison
`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap` is invertible; by
`Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap_eq` the Künneth morphism for Ext is the first
followed by the direct image of the second. -/
theorem isIso_kunnethExtMap (K K' : DerivedCategory (Mod X.sheaf))
    (M M' : DerivedCategory (Mod Y.sheaf))
    (hkunneth : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
      (sheafHomObj X K K') (sheafHomObj Y M M')))
    (hbox : IsIso (boxSheafHomMap p q K K' M M')) :
    IsIso (kunnethExtMap a b p q f hp hq K K' M M') := by
  have hpush : IsIso ((derivedPushforwardFunctor f).map (boxSheafHomMap p q K K' M M')) := by
    have := hbox
    infer_instance
  rw [kunnethExtMap_eq]
  exact (@asIso _ _ _ _ (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
        (sheafHomObj X K K') (sheafHomObj Y M M')) hkunneth ≪≫
      @asIso _ _ _ _ ((derivedPushforwardFunctor f).map (boxSheafHomMap p q K K' M M'))
        hpush).isIso_hom

/-- The Künneth morphism for Ext is invertible as soon as the relative Künneth morphism of
Stacks 0FLP is invertible at the two derived internal homs and the three comparisons of
Stacks 08I3 and Stacks 0FXP entering
`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap` are invertible. -/
theorem isIso_kunnethExtMap_of_isIso_sheafHomComparisons
    (K K' : DerivedCategory (Mod X.sheaf)) (M M' : DerivedCategory (Mod Y.sheaf))
    (hkunneth : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
      (sheafHomObj X K K') (sheafHomObj Y M M')))
    (hpull : IsIso (pullbackSheafHomMap p K K'))
    (hpull' : IsIso (pullbackSheafHomMap q M M'))
    (htensor : IsIso (sheafHomTensorMap W ((derivedPullbackFunctor p).obj K)
      ((derivedPullbackFunctor p).obj K') ((derivedPullbackFunctor q).obj M)
      ((derivedPullbackFunctor q).obj M'))) :
    IsIso (kunnethExtMap a b p q f hp hq K K' M M') :=
  isIso_kunnethExtMap a b p q f hp hq K K' M M' hkunneth
    (isIso_boxSheafHomMap p q K K' M M' hpull hpull' htensor)

end Kunneth

/-! ### Stacks 0FXZ at a cartesian square of schemes -/

section Schemes

variable {S X Y W : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)

/-- A commuting square of schemes is an instance of the data the Künneth morphism takes: read on
the underlying ringed spaces, `CategoryTheory.IsPullback.w` says that the second projection
followed by `b` is the structure morphism `p ≫ a`. -/
theorem toShHom_isPullback_w (hW : IsPullback p q a b) :
    q.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = (p ≫ a).toLRSHom.toShHom :=
  congrArg (fun g : W ⟶ S => g.toLRSHom.toShHom) hW.w.symm

/-- **Stacks 0FXZ.**  Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes which are
quasi-compact and quasi-separated, let `X` and `Y` be Tor independent over `S`, and let
`W = X ×_S Y` with its two projections `p` and `q`.  If `K ∈ D(𝒪_X)` is perfect,
`K' ∈ D_{QCoh}(𝒪_X)`, `M ∈ D(𝒪_Y)` is perfect and `M' ∈ D_{QCoh}(𝒪_Y)`, then the Künneth
morphism for Ext of Stacks 0FXY,

`Ra_*R SheafHom(K, K') ⊗^𝐋_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`,

is an isomorphism.

The two steps of the source's proof are carried as the hypotheses `hkunneth` and `hbox`, and
the geometric hypotheses are therefore not consumed; the implementation notes of this file say
what each of the two steps is, why neither is available in the library, and where the
verification the source omits sits.  `hkunneth` is Stacks 0FLQ at the pair of derived internal
homs and `hbox` is the identification of Cohomology, Stacks 08DQ together with that
verification. -/
@[stacks 0FXZ "for a and b quasi-compact and quasi-separated, X and Y Tor independent over S, \
K and M perfect and K', M' in D_QCoh, the Künneth morphism for Ext of Tag 0FXY at a cartesian \
square of schemes is invertible.  Both steps of the source's two-step proof are carried as \
explicit hypotheses and the source's geometric hypotheses are consequently not consumed: \
hkunneth is the invertibility of the relative Künneth morphism of Tag 0FLP at the pair \
(RSheafHom(K,K'), RSheafHom(M,M')), which is Tag 0FLQ.  That tag is carried, for this same \
kunnethMap, by isIso_kunnethMap_of_projectionFormulas_of_baseChange, but itself only \
conditionally, on four named inputs: the projection formula of Tag 08EU for a and for p, the \
Tor-independent base-change comparison of Tag 08IB for the square, and the Tag 079U/0D5S \
monoidality coherence.  So hkunneth is exactly that carrier's conclusion and is obtainable \
from it once those four are supplied; it is carried here as one hypothesis rather than four.  \
Perfectness of K and M does not discharge them, because 0FLQ is applied to RSheafHom(K,K') \
and RSheafHom(M,M'), which for K' and M' merely in D_QCoh are quasi-coherent and not \
perfect.  And hbox is the invertibility of the \
canonical comparison Lp^*RSheafHom(K,K') (x)^L Lq^*RSheafHom(M,M') -> RSheafHom(K [x] M, K' \
[x] M'), which is where the source uses perfectness, through the identification \
RSheafHom(K,K') = K' (x)^L K^dual of Cohomology Tag 08DQ, of which the repository carries only \
the statement that the dual of a perfect object is perfect, and which also absorbs the \
parenthetical verification the source omits that the identifications give the same map.  What \
is proved here is that the two steps suffice, which in the source is the word `hence`"]
theorem isIso_kunnethExtMap_cartesian (hW : IsPullback p q a b)
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (_htor : AlgebraicGeometry.TorIndependent a b)
    (K K' : DerivedCategory X.Modules) (M M' : DerivedCategory Y.Modules)
    (_hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (_hK' : IsDQCoh (R := X.ringCatSheaf) K')
    (_hM : RingedSpace.IsPerfect (X := Y.toRingedSpace) M)
    (_hM' : IsDQCoh (R := Y.ringCatSheaf) M')
    (hkunneth : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a.toLRSHom.toShHom
      b.toLRSHom.toShHom p.toLRSHom.toShHom q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl
      (toShHom_isPullback_w a b p q hW)
      (sheafHomObj X.toRingedSpace K K') (sheafHomObj Y.toRingedSpace M M')))
    (hbox : IsIso (boxSheafHomMap p.toLRSHom.toShHom q.toLRSHom.toShHom K K' M M')) :
    IsIso (kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom p.toLRSHom.toShHom
      q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl (toShHom_isPullback_w a b p q hW)
      K K' M M') :=
  isIso_kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom p.toLRSHom.toShHom
    q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl (toShHom_isPullback_w a b p q hW)
    K K' M M' hkunneth hbox

end Schemes

end Stacks.Cohomology.DerivedKunnethExt

end
