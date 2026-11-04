module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGeneration
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.Group.TensorConstraints
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.TensorFiniteness.RingedSpace

/-!
# Untwisting finite type and coherence along an invertible module

An invertible `𝒪_X`-module `ℒ` has a tensor inverse, so `ω ⊗ ℒ` determines `ω` back again:
`(ω ⊗ ℒ) ⊗ ℒ^{⊗ -1} ≅ ω`. Since tensoring preserves finite type ([Stacks, Tag 01CE]) and
`ℒ^{⊗ -1}` is itself of finite type, finite type of `ω ⊗ ℒ` gives finite type of `ω`.

This is the step that turns the single carried input `hFft` of [Stacks, Tag 0B5H] — finite type
of `ω_X ⊗ ℒ` — into coherence of `ω_X` itself, which is what the Euler-characteristic and
kernel arguments of that tag's proof consume.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isFiniteType_of_isFiniteType_tensorSheaf_of_isInvertible`: finite type descends from
  `ω ⊗ ℒ` to `ω` along an invertible `ℒ`.
* `CohenMacaulayCurveSituation.isFiniteType_tensorPowerModule_neg_one`: the inverse of an
  invertible module on the curve of Situation [Stacks, Tag 0B5D] is of finite type.
* `CohenMacaulayCurveSituation.isCoherent_of_isFiniteType_tensorSheaf`: the pair of coherence
  statements, for `ω` and for `ω ⊗ ℒ`, that finite type of `ω ⊗ ℒ` yields on that curve.
* `CohenMacaulayCurveSituation.isFiniteType_tensorSheaf_dualizingSheafOverField_iff_isCoherent`:
  the two directions together — finite type of `ω_X ⊗ ℒ` **is** coherence of `ω_X`.
* `CohenMacaulayCurveSituation`
  `.isFiniteType_tensorSheaf_dualizingSheafOverField_of_isDualizingComplex`: finite type of
  `ω_X ⊗ ℒ` from the dualizing-complex property of `ω_X^• = f^×(𝒪_{Spec k})`.

## What the last two results are for, and why they carry no tag

The input `hFft` of [Stacks, Tag 0B5H] in
`Curves/VanishingResults/DualizingTwistGenerationAlgClosed.lean` is finite type of `ω_X ⊗ ℒ`.
`isFiniteType_tensorSheaf_dualizingSheafOverField_iff_isCoherent` says in Lean what the note on
that tag says in prose: `hFft` is equivalent to coherence of `ω_X`, which is the coherence
assertion of clause (2) of [Stacks, Tag 0BS2]. It is an equivalence between two statements this
development has not proved, so it asserts no tag.

`isFiniteType_tensorSheaf_dualizingSheafOverField_of_isDualizingComplex` then reduces `hFft` to
the single statement that the canonical complex `ω_X^• = f^×(𝒪_{Spec k})` is a dualizing complex
in the sense of [Stacks, Tag 0A87] — `Stacks.Duality.IsDualizingComplex` of
`Stacks.Duality.dualizingComplexOverField` — by way of
`Stacks.Duality.isCoherent_homology_of_isDualizingComplex`. That hypothesis is **not available
here**, and it is the hypothesis, not the conclusion, that is the content: the source gets it
from Example [Stacks, Tag 0AWI], `ω_X^• = f^!ω_S^•` with `f^!` the exceptional inverse image,
which is a dualizing complex by [Stacks, Tag 0AA3]. The library's [Stacks, Tag 0AA3] is
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`, which carries the affine-chart
description of `f^!` — [Stacks, Tag 0AA1] with clause (b) of [Stacks, Tag 0BV2] — as the explicit
hypothesis `h0AA1`, and is moreover about `f^!` on `FTS S` rather than the `f^×` used here. So
attaching this result to [Stacks, Tag 0B5H] would replace one assumption by another, and it is
left untagged; what it buys is that whoever supplies [Stacks, Tag 0AA1] discharges `hFft` in one
line.

## Implementation notes

The cancelling isomorphism is assembled from the coherence constraints of the tensor product
sheaf rather than from the monoidal structure: `Stacks.SheafOfModules.tensorSheafAssociator`
regroups `(ω ⊗ ℒ) ⊗ ℒ^{⊗ -1}` as `ω ⊗ (ℒ ⊗ ℒ^{⊗ -1})`,
`Stacks.SheafOfModules.Invertible.mulNegOneIso` contracts the second factor to `𝒪_X`, and
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` removes it. Working at the monoidal spelling
would need the comparison of `ω ⊗ ℒ` with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` at every step, which is what the tag's
statement is written at.

Finite type of `ℒ^{⊗ -1}` is not available on an arbitrary scheme at this spelling, so the
general statement takes it as a hypothesis; on a proper scheme over a field it is discharged by
coherence of a finite locally free module.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPowerModule)

universe u

namespace AlgebraicGeometry

/-- **`(ω ⊗ ℒ) ⊗ ℒ^{⊗ -1} ≅ ω`** for an invertible `𝒪_X`-module `ℒ`: regroup, contract
`ℒ ⊗ ℒ^{⊗ -1}` to `𝒪_X`, and remove the trivial factor. -/
public def tensorSheafMulNegOneIso {X : Scheme.{u}} (ω L : X.Modules)
    [IsInvertible X.presheaf X.ringCatSheaf.property L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
              (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (ω)).obj
          (L))))).obj ((tensorPowerModule L (-1)))) ≅ ω :=
  Stacks.SheafOfModules.tensorSheafAssociator X.presheaf X.ringCatSheaf.property ω L
      (tensorPowerModule L (-1)) ≪≫
    Stacks.SheafOfModules.tensorSheafMapIso X.presheaf X.ringCatSheaf.property (Iso.refl ω)
      (Stacks.SheafOfModules.Invertible.mulNegOneIso X.presheaf X.ringCatSheaf.property L) ≪≫
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso X.presheaf X.ringCatSheaf.property ω

/-- **Finite type descends along an invertible twist.** If `ω ⊗ ℒ` and `ℒ^{⊗ -1}` are of finite
type and `ℒ` is invertible, then `ω` is of finite type, being isomorphic to
`(ω ⊗ ℒ) ⊗ ℒ^{⊗ -1}`. -/
public theorem isFiniteType_of_isFiniteType_tensorSheaf_of_isInvertible {X : Scheme.{u}}
    (ω L : X.Modules) [IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hN : (tensorPowerModule L (-1)).IsFiniteType)
    (hF : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (ω)).obj
        (L))).IsFiniteType) :
    ω.IsFiniteType :=
  have := hF
  have := hN
  have h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
        (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
      (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
            (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj (ω)).obj
        (L))))).obj ((tensorPowerModule L (-1))))).IsFiniteType :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType X.toRingedSpace _ _ hF hN
  isFiniteType_of_iso (tensorSheafMulNegOneIso ω L) h

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- An invertible module on the curve of Situation [Stacks, Tag 0B5D] is of finite type. -/
private theorem isFiniteType_of_isInvertible_aux (L : S.X.Modules)
    [hL : IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] : L.IsFiniteType :=
  have hfree : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible S.X _ hL
  have : L.IsCoherent :=
    @Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      S.k _ S.X S.f _ _ 1 hfree
  SheafOfModules.IsCoherent.isFiniteType

/-- **The inverse of an invertible module on the curve of Situation [Stacks, Tag 0B5D] is of
finite type.** It is invertible ([Stacks, Tag 01CU]), hence finite locally free of rank one
([Stacks, Tag 0B8M]), hence coherent on a proper scheme over a field, hence of finite type. -/
public theorem isFiniteType_tensorPowerModule_neg_one (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] :
    (tensorPowerModule L (-1)).IsFiniteType :=
  have : IsInvertible S.X.presheaf S.X.ringCatSheaf.property (tensorPowerModule L (-1)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry S.X.presheaf
        S.X.ringCatSheaf.property (tensorPowerModule L (-1))).1
      (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible S.X.presheaf
        S.X.ringCatSheaf.property L (-1))
  S.isFiniteType_of_isInvertible_aux (tensorPowerModule L (-1))

/-- **An invertible module on the curve of Situation [Stacks, Tag 0B5D] is quasi-coherent**, an
invertible module on a scheme being locally free of rank one. -/
public theorem isQuasicoherent_of_isInvertible (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] : L.IsQuasicoherent :=
  have : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.X.presheaf
        S.X.ringCatSheaf.property).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry S.X.presheaf
      S.X.ringCatSheaf.property L).2 inferInstance
  Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible S.X L

/-- **`ω_X ⊗ ℒ` is quasi-coherent**, by [Stacks, Tag 01CE] from quasi-coherence of the dualizing
sheaf and of the invertible `ℒ`. -/
public theorem isQuasicoherent_tensorSheaf_dualizingSheafOverField (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent S.X.toRingedSpace _ _
    (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f)
    (S.isQuasicoherent_of_isInvertible L)

/-- **Finite type of `ω_X ⊗ ℒ` makes `ω_X ⊗ ℒ` coherent.** The curve of Situation
[Stacks, Tag 0B5D] is locally Noetherian, being of finite type over a field, and a quasi-coherent
module of finite type on a locally Noetherian scheme is coherent. -/
public theorem isCoherent_tensorSheaf_dualizingSheafOverField_of_isFiniteType (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsFiniteType) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsCoherent :=
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    S.X _ _ (S.isQuasicoherent_tensorSheaf_dualizingSheafOverField L) hFft

/-- **Finite type of `ω_X ⊗ ℒ` makes `ω_X` itself coherent.** Untwisting by `ℒ^{⊗ -1}` turns
finite type of `ω_X ⊗ ℒ` into finite type of `ω_X`, which together with the quasi-coherence of
the dualizing sheaf gives coherence on the locally Noetherian curve.

This is what carries the single remaining input `hFft` of [Stacks, Tag 0B5H] to the coherence of
`ω_X` that clause (2) of [Stacks, Tag 0BS2] asserts and that the proof of that tag consumes. -/
public theorem isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (hFft : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsFiniteType) :
    (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent :=
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    S.X _ _ (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f)
    (isFiniteType_of_isFiniteType_tensorSheaf_of_isInvertible
      (Stacks.Duality.dualizingSheafOverField S.f) L (S.isFiniteType_tensorPowerModule_neg_one L)
      hFft)

/-! ### The converse: what finite type of `ω_X ⊗ ℒ` is equivalent to -/

/-- **An invertible module on the curve of Situation [Stacks, Tag 0B5D] is of finite type.** It is
finite locally free of rank one ([Stacks, Tag 0B8M]), hence coherent on a proper scheme over a
field, hence of finite type. This is
`AlgebraicGeometry.CohenMacaulayCurveSituation.isFiniteType_tensorPowerModule_neg_one` at the
module itself rather than at its inverse. -/
public theorem isFiniteType_of_isInvertible (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] : L.IsFiniteType :=
  S.isFiniteType_of_isInvertible_aux L

/-- **Coherence of `ω_X` makes `ω_X ⊗ ℒ` of finite type.** This is [Stacks, Tag 01CE] clause (2)
applied to the coherent `ω_X` and the invertible `ℒ`, and it is the converse of
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf`. -/
public theorem isFiniteType_tensorSheaf_dualizingSheafOverField_of_isCoherent (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (hω : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsFiniteType :=
  have hft : (Stacks.Duality.dualizingSheafOverField S.f).IsFiniteType :=
    have := hω
    SheafOfModules.IsCoherent.isFiniteType
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType S.X.toRingedSpace _ _ hft
    (S.isFiniteType_of_isInvertible L)

/-- **Finite type of `ω_X ⊗ ℒ` is exactly coherence of `ω_X`.** The two implications are
`AlgebraicGeometry.CohenMacaulayCurveSituation`
`.isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf`, which untwists by `ℒ^{⊗ -1}`,
and `AlgebraicGeometry.CohenMacaulayCurveSituation`
`.isFiniteType_tensorSheaf_dualizingSheafOverField_of_isCoherent`, which twists back.

So the input `hFft` carried by [Stacks, Tag 0B5H] in
`Curves/VanishingResults/DualizingTwistGenerationAlgClosed.lean` is neither more nor less than
the coherence assertion of clause (2) of [Stacks, Tag 0BS2], for *every* invertible `ℒ` at
once. -/
public theorem isFiniteType_tensorSheaf_dualizingSheafOverField_iff_isCoherent (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsFiniteType ↔
      (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent :=
  ⟨S.isCoherent_dualizingSheafOverField_of_isFiniteType_tensorSheaf L,
    S.isFiniteType_tensorSheaf_dualizingSheafOverField_of_isCoherent L⟩

/-- **The dualizing-complex property discharges `hFft`.** If the canonical complex
`ω_X^• = f^×(𝒪_{Spec k})` is a dualizing complex on `X` in the sense of [Stacks, Tag 0A87], then
its degree `-1` cohomology sheaf `ω_X` is coherent, and so `ω_X ⊗ ℒ` is of finite type for every
invertible `ℒ`.

This is the one-line discharge of the input `hFft` of [Stacks, Tag 0B5H]; see the module
documentation for why the hypothesis below cannot be supplied in this development, and why
nothing here is tagged. -/
public theorem isFiniteType_tensorSheaf_dualizingSheafOverField_of_isDualizingComplex
    (L : S.X.Modules) [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (hω : letI : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
      Stacks.Duality.IsDualizingComplex (Stacks.Duality.dualizingComplexOverField S.f).obj) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨S.X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf)
          (forget₂ CommRingCat RingCat) (S.X.ringCatSheaf.property)⟩).obj
        ((Stacks.Duality.dualizingSheafOverField S.f))).obj (L))).IsFiniteType :=
  let : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  S.isFiniteType_tensorSheaf_dualizingSheafOverField_of_isCoherent L
    (Stacks.Duality.isCoherent_homology_of_isDualizingComplex hω (-1))

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
