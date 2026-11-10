module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCommutesCompletionToposGlobal
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FullRingedToposHom

/-!
# `Rf_*` commutes with derived completion at a morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S`, and give both the ringed
topoi of their associated sites, for a topology `τ` coarser than the fppf one, with the structure
sheaves of **Stacks 06TV** (`AlgebraicGeometry.Stack.fullRingedTopos` of **Stacks 0H0C**, sections
in the universe of the site). Let `ℐ ⊂ 𝒪_𝒴` be a sheaf of ideals of finite type and let
`ℐ' = f^{-1}ℐ · 𝒪_𝒳`. This file proves that the canonical comparison map

`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`

is invertible for every object `K` of `D(𝒪_𝒳)` — in particular for every complex of quasi-coherent
`𝒪_𝒳`-modules. This is the analogue of Equation 52.7.0.1 of **Stacks 0A0I** for morphisms of
algebraic stacks that the last sentence of **Stacks 0AKL** (Remark 52.7.4) attributes to
[HL-P, Theorem 6.5].

## Main results

* `AlgebraicGeometry.Stack.isIso_derivedCompletionPushforwardComparison_fullRingedToposHom`: the
  statement for a 1-morphism of categories fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.isIso_derivedCompletionPushforwardComparison_of_isAlgebraicStack`:
  **the analogue of [Stacks, Tag 0A0I] for morphisms of algebraic stacks**, the content of the
  last sentence of [Stacks, Tag 0AKL].

## Implementation notes

A 1-morphism of categories fibred in groupoids induces a morphism of ringed topoi,
`AlgebraicGeometry.Stack.fullRingedToposHom` (Stacks 06TW), and [Stacks, Tag 0A0G] is proved for
an arbitrary morphism of ringed topoi, by the theorem
`isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType` in the
namespace `AlgebraicGeometry.RingedToposHom`.
The ideal sheaf `ℐ'` is the one that statement builds out of `ℐ`,
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf`, which is `f^{-1}ℐ · 𝒪_𝒳` by
construction. Nothing about algebraicity is used: the statement holds for every 1-morphism of
categories fibred in groupoids over the big fppf site of `S`, and is proved in that generality
first.

The derived completion functors of this library are defined on ringed topoi whose three universes
— morphisms of the site, objects of the site, sections of the structure sheaf — agree. The
structure sheaf of **Stacks 06TV** has its sections in the universe `u` of the schemes, while a
category fibred in groupoids over the big fppf site has its objects in `Type (u + 1)`; so the
statements below use the structure sheaf with its sections lifted to `u + 1`,
`AlgebraicGeometry.Stack.liftedStructureSheaf`, which is the universe in which the direct images of
modules on stacks live in this library anyway, and they take the stacks with objects and
morphisms in `Type (u + 1)`. `AlgebraicGeometry.Stack.IsAlgebraicStack` is stated for an arbitrary
object and morphism universe of the total category, so that seating is an instance of it.

## References

* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0A0I](https://stacks.math.columbia.edu/tag/0A0I)
* [Stacks Project, Tag 0AKL](https://stacks.math.columbia.edu/tag/0AKL)
* [HL-P] D. Halpern-Leistner, A. Preygel, *Mapping stacks and categorical notions of
  properness*, Theorem 6.5.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **[Stacks, Tag 099F] on the ringed topos of a category fibred in groupoids.** For a sheaf of
ideals `ℐ' ⊆ 𝒪_𝒳` of finite type the derived completion functor along `ℐ'` exists. This is
`AlgebraicGeometry.RingedToposHom.isRightAdjoint_ι_isDerivedComplete_toRingedSite` at
`AlgebraicGeometry.Stack.fullRingedTopos`, restated because instance search does not find it at a
ringed topos of this shape. -/
instance isRightAdjoint_ι_isDerivedComplete_fullRingedTopos
    {𝒳 : Type (u + 1)} [Category.{u + 1} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (I' : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (fullRingedTopos.{u, u + 1, u + 1} B S hS p τ
          (liftedStructureSheaf.{u, u + 1, u + 1} B S hS p τ hp hτ)).toRingedSite.O)))
    [I'.toSheafOfModules.IsFiniteType] :
    (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u + 1, u + 1, u + 1, u + 1}
      (fullRingedTopos.{u, u + 1, u + 1} B S hS p τ
          (liftedStructureSheaf.{u, u + 1, u + 1} B S hS p τ hp hτ)).toRingedSite
        I')).IsRightAdjoint :=
  RingedToposHom.isRightAdjoint_ι_isDerivedComplete_toRingedSite
    (X := fullRingedTopos.{u, u + 1, u + 1} B S hS p τ
        (liftedStructureSheaf.{u, u + 1, u + 1} B S hS p τ hp hτ)) I'

/-- **`f^{-1}ℐ · 𝒪_𝒳` is of finite type when `ℐ` is**, at the morphism of ringed topoi
`AlgebraicGeometry.Stack.fullRingedToposHom` of a 1-morphism. This is
`AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf` at that morphism,
restated because instance search does not find it at ringed topoi of this shape. -/
instance isFiniteType_inverseImageIdealSheaf_fullRingedToposHom
    {𝒳 : Type (u + 1)} [Category.{u + 1} 𝒳] {𝒴 : Type (u + 1)} [Category.{u + 1} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F)
    (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (fullRingedTopos.{u, u + 1, u + 1} B S hS q τ
        (liftedStructureSheaf.{u, u + 1, u + 1} B S hS q τ hq hτ)).toRingedSite.O)))
    [I.toSheafOfModules.IsFiniteType] :
    (RingedToposHom.inverseImageIdealSheaf.{u + 1}
      (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I).toSheafOfModules.IsFiniteType :=
  RingedToposHom.isFiniteType_inverseImageIdealSheaf
    (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I inferInstance

/-- **`Rf_*` commutes with derived completion at a 1-morphism of categories fibred in groupoids.**
Let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`,
let `f` be the morphism of ringed topoi `(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh(𝒴_τ), 𝒪_𝒴)` it induces
(`AlgebraicGeometry.Stack.fullRingedToposHom`), let `ℐ ⊂ 𝒪_𝒴` be a sheaf of ideals of finite type
and let `ℐ' = f^{-1}ℐ · 𝒪_𝒳` be the sheaf of ideals generated by `f^♯(f^{-1}ℐ)`. Then the
canonical comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible for every object `K` of
`D(𝒪_𝒳)`.

It is [Stacks, Tag 0A0G] for a morphism of ringed topoi, the theorem
`isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType` in the
namespace `AlgebraicGeometry.RingedToposHom`, at the morphism of ringed topoi of
[Stacks, Tag 06TW]. -/
theorem isIso_derivedCompletionPushforwardComparison_fullRingedToposHom
    {𝒳 : Type (u + 1)} [Category.{u + 1} 𝒳] {𝒴 : Type (u + 1)} [Category.{u + 1} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hF : p.IsFibredOneMorphism q F)
    (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (fullRingedTopos.{u, u + 1, u + 1} B S hS q τ
        (liftedStructureSheaf.{u, u + 1, u + 1} B S hS q τ hq hτ)).toRingedSite.O)))
    [I.toSheafOfModules.IsFiniteType]
    (K : letI := HasDerivedCategory.standard; DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (fullRingedTopos.{u, u + 1, u + 1} B S hS p τ
          (liftedStructureSheaf.{u, u + 1, u + 1} B S hS p τ hp hτ)).toRingedSite.O))) :
    IsIso ((RingedToposHom.derivedCompletionPushforwardComparison
      (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I
      (RingedToposHom.inverseImageIdealSheaf.{u + 1}
        (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I)
      (RingedToposHom.idealCompatible_inverseImageIdealSheaf.{u + 1}
        (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I)).app K) :=
  RingedToposHom.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType
    (fullRingedToposHom B S hS p q F hp hq τ hτ hF) I K

/-- **The analogue of [Stacks, Tag 0A0I] for morphisms of algebraic stacks, [HL-P, Theorem 6.5],
which is the content of the last sentence of [Stacks, Tag 0AKL].** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, let `τ` be a topology coarser than the fppf one (any of
the Zariski, étale, smooth, syntomic and fppf topologies), and consider the morphism of ringed
topoi `(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh(𝒴_τ), 𝒪_𝒴)` that `f` induces (Stacks 06TW). Let `ℐ ⊂ 𝒪_𝒴` be a sheaf
of ideals of finite type and let `ℐ' = f^{-1}ℐ · 𝒪_𝒳`. Then the canonical comparison map

`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`

is invertible for every object `K` of `D(𝒪_𝒳)`, the completion on `𝒴` being taken along `ℐ` and
the one on `𝒳` along `ℐ'`. In particular `Rf_*(ℱ^∧) = (Rf_*ℱ)^∧` for every complex of
quasi-coherent `𝒪_𝒳`-modules `ℱ`, which is the form in which the remark states it, and every
quasi-coherent sheaf of ideals of finite type is an admissible `ℐ`.

The ideal `ℐ'` is `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf`, the sheaf of ideals
generated by `f^♯(f^{-1}ℐ)`; the relation between `ℐ` and `ℐ'` that the comparison map needs, and
finite type of `ℐ'`, are theorems about that construction. The two algebraic stacks are taken
with objects and morphisms in `Type (u + 1)` and the structure sheaves with sections in
`Type (u + 1)`; see the module documentation for why.

It is `AlgebraicGeometry.Stack.isIso_derivedCompletionPushforwardComparison_fullRingedToposHom`,
which needs only that `𝒳` and `𝒴` are fibred in groupoids — the first clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`. -/
@[stacks 0AKL "the mathematical content of Remark 52.7.4, which is its fifth and last sentence: \
the analogue of Equation 52.7.0.1 of [Stacks, Tag 0A0I] for complexes of quasi-coherent \
modules, [HL-P, Theorem 6.5], here for a 1-morphism `f : 𝒳 ⟶ 𝒴` of **algebraic stacks** over \
`S`. For the morphism of ringed topoi `(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh(𝒴_τ), 𝒪_𝒴)` that `f` induces, at \
any topology `τ` coarser than the fppf one, a sheaf of ideals `ℐ ⊂ 𝒪_𝒴` of finite type and \
`ℐ' = f^{-1}ℐ · 𝒪_𝒳`, the canonical comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible for \
**every** object `K` of `D(𝒪_𝒳)`, so in particular for every complex of quasi-coherent \
modules, and every quasi-coherent sheaf of ideals of finite type is an admissible `ℐ`. The \
proof is [Stacks, Tag 0A0G] for an arbitrary morphism of ringed topoi, \
`AlgebraicGeometry.RingedToposHom.isIso_derivedCompletionPushforwardComparison_\
inverseImageIdealSheaf_of_isFiniteType`, \
at the morphism of ringed topoi of [Stacks, Tag 06TW], \
`AlgebraicGeometry.Stack.fullRingedToposHom`; it holds for every 1-morphism of categories \
fibred in groupoids over the big fppf site, \
`AlgebraicGeometry.Stack.isIso_derivedCompletionPushforwardComparison_fullRingedToposHom`. The \
stacks have objects and morphisms in `Type (u + 1)` and the structure sheaves sections in \
`Type (u + 1)`, the seating at which the library's derived completion on a ringed topos is \
defined. The remark's first four sentences are bibliography — pointers to [lurie-thesis, \
Theorem 6.3.1] for a derived formal functions theorem for proper maps, to [dag12, Chapter 4] \
with the cross-reference to More on Algebra, Section 091N for the affine story, and to [G-R, \
Section 2.9] for proper base change and derived completion via (ind) coherent modules — and \
carry no formalizable statement. [HL-P, Theorem 6.5] is also stated for morphisms of \
**derived** algebraic stacks; derived algebraic stacks are not defined in this library, so \
that part of the reference's setting is outside it"]
theorem isIso_derivedCompletionPushforwardComparison_of_isAlgebraicStack
    {𝒳 𝒴 : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴)
    (f : 𝒳 ⥤ᵇ 𝒴)
    (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (fullRingedTopos.{u, u + 1, u + 1} B S hS 𝒴.p τ
        (liftedStructureSheaf.{u, u + 1, u + 1} B S hS 𝒴.p τ h𝒴.fst hτ)).toRingedSite.O)))
    [I.toSheafOfModules.IsFiniteType]
    (K : letI := HasDerivedCategory.standard; DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (fullRingedTopos.{u, u + 1, u + 1} B S hS 𝒳.p τ
          (liftedStructureSheaf.{u, u + 1, u + 1} B S hS 𝒳.p τ h𝒳.fst hτ)).toRingedSite.O))) :
    IsIso ((RingedToposHom.derivedCompletionPushforwardComparison
      (fullRingedToposHom B S hS 𝒳.p 𝒴.p f.toFunctor h𝒳.fst h𝒴.fst τ hτ
        (.of_isFiberedInGroupoids h𝒴.fst f.w)) I
      (RingedToposHom.inverseImageIdealSheaf.{u + 1}
        (fullRingedToposHom B S hS 𝒳.p 𝒴.p f.toFunctor h𝒳.fst h𝒴.fst τ hτ
          (.of_isFiberedInGroupoids h𝒴.fst f.w)) I)
      (RingedToposHom.idealCompatible_inverseImageIdealSheaf.{u + 1}
        (fullRingedToposHom B S hS 𝒳.p 𝒴.p f.toFunctor h𝒳.fst h𝒴.fst τ hτ
          (.of_isFiberedInGroupoids h𝒴.fst f.w)) I)).app K) :=
  isIso_derivedCompletionPushforwardComparison_fullRingedToposHom B S hS τ hτ 𝒳.p 𝒴.p f.toFunctor
    h𝒳.fst h𝒴.fst (.of_isFiberedInGroupoids h𝒴.fst f.w) I K

end AlgebraicGeometry.Stack

end
