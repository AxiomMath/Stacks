module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethDischarged
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
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

This file proves the reduction step of the source's proof.  By construction the morphism of
Stacks 0FXY is the relative Künneth morphism of Stacks 0FLP at the pair of derived internal
homs, followed by the direct image of the comparison

`Lp^*R SheafHom(K, K') ⊗^𝐋_{𝒪_W} Lq^*R SheafHom(M, M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`,

so it is invertible as soon as both factors are.  The first factor is Stacks 0FLQ, the
invertibility of the relative Künneth morphism; the second is the source's identification
`R SheafHom(K, K') = K' ⊗^𝐋 K^∨` for perfect `K` (Cohomology, Stacks 08DQ) together with the
compatibility the source declines to check.  Both factors are proved invertible at every
cartesian square of schemes, which gives Stacks 0FXZ as
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_cartesian`; its specialization to the
chosen fibre product `X ×_S Y` is
`Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_fibreProduct`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethExtFibreProduct`.

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
* `Stacks.Cohomology.DerivedKunnethExt.isIso_kunnethExtMap_cartesian`: **Stacks 0FXZ** at an
  arbitrary cartesian square of schemes, under the hypotheses of the source.

## Implementation notes

*The two factors.*  In `isIso_kunnethExtMap_cartesian` they are proved as follows.

* The invertibility of `Stacks.Cohomology.DerivedKunneth.kunnethMap` at the pair
  `(R SheafHom(K, K'), R SheafHom(M, M'))` is Stacks 0FLQ at the given cartesian square,
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme_of_isPullback`, applied to the two
  derived internal homs, which lie in `D_QCoh` by
  `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect`.
* The invertibility of `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`, which is where
  perfectness of `K` and of `M` is used, follows from
  `Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect`
  and `Stacks.Cohomology.DerivedKunnethExt.isIso_sheafHomTensorMap_of_isPerfect_space`; it holds
  at any commuting square.

The ringed-space results drop the geometric hypotheses of the source and are correspondingly
more general.

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

-- `KunnethDischarged` makes the abelian and Grothendieck structures of
-- `Stacks.Cohomology.SiteModules` on module sheaves visible; the derived categories of this file
-- are those of `SheafOfModules.instAbelian`, as in the modules it builds on.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

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

/-- Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes,
and let `X` and `Y` be Tor independent over `S`.  Let `p : W ⟶ X` and `q : W ⟶ Y` make `W` a
fibre product of `a` and `b`, and let `f = p ≫ a`.  If `K ∈ D(𝒪_X)` is perfect,
`K' ∈ D_QCoh(𝒪_X)`, `M ∈ D(𝒪_Y)` is perfect and `M' ∈ D_QCoh(𝒪_Y)`, then the Künneth morphism
for Ext of Stacks 0FXY

`Ra_*R SheafHom(K, K') ⊗^𝐋_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`

is an isomorphism. -/
@[stacks 0FXZ "at an arbitrary cartesian square of schemes"]
theorem isIso_kunnethExtMap_cartesian (hW : IsPullback p q a b)
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (htor : AlgebraicGeometry.TorIndependent a b)
    (K K' : DerivedCategory X.Modules) (M M' : DerivedCategory Y.Modules)
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (hK' : IsDQCoh (R := X.ringCatSheaf) K')
    (hM : RingedSpace.IsPerfect (X := Y.toRingedSpace) M)
    (hM' : IsDQCoh (R := Y.ringCatSheaf) M') :
    IsIso (kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom p.toLRSHom.toShHom
      q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl (toShHom_isPullback_w a b p q hW)
      K K' M M') :=
  isIso_kunnethExtMap a.toLRSHom.toShHom b.toLRSHom.toShHom p.toLRSHom.toShHom
    q.toLRSHom.toShHom (p ≫ a).toLRSHom.toShHom rfl (toShHom_isPullback_w a b p q hW)
    K K' M M'
    (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme_of_isPullback a b p q hW htor
      (sheafHomObj X.toRingedSpace K K') (sheafHomObj Y.toRingedSpace M M')
      (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect X K K' hK hK')
      (AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect Y M M' hM hM'))
    (isIso_boxSheafHomMap p.toLRSHom.toShHom q.toLRSHom.toShHom K K' M M'
      (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
        p.toLRSHom.toShHom K hK K')
      (Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_isPerfect
        q.toLRSHom.toShHom M hM M')
      (isIso_sheafHomTensorMap_of_isPerfect_space W.toRingedSpace
        ((derivedPullbackFunctor p.toLRSHom.toShHom).obj K)
        ((derivedPullbackFunctor p.toLRSHom.toShHom).obj K')
        ((derivedPullbackFunctor q.toLRSHom.toShHom).obj M)
        ((derivedPullbackFunctor q.toLRSHom.toShHom).obj M')
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
          p.toLRSHom.toShHom K hK)
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
          q.toLRSHom.toShHom M hM)))

end Schemes

end Stacks.Cohomology.DerivedKunnethExt

end
