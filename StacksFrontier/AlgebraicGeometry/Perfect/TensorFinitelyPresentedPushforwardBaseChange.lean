module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The hypothesis of Stacks 0A1H on a finitely presented complex

Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let `E` be an object of
`D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`,
whose support is proper over `S`. [Stacks, Tag 0A1H] asserts two things about
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` when `E` is perfect: that `K` is a perfect object of `D(𝒪_S)`, and
that its formation commutes with arbitrary base change. This file records the hypothesis on
`𝒢^•` and the consequences of it that [Stacks, Tag 0A1D] asks for; the tag itself is
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`.

## Main definitions

* `AlgebraicGeometry.FlatProperSupportFinitelyPresented` is the hypothesis of
  [Stacks, Tag 0A1H] on `𝒢^•`: bounded, finitely presented in each degree, flat over `S` in
  each degree, and with all degrees supported on one closed subset proper over `S`. It is the
  finite-presentation analogue of
  `Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex`, the hypothesis of
  [Stacks, Tag 0DJQ], which asks for coherence instead and so needs a Noetherian base.

## Main results

* `AlgebraicGeometry.FlatProperSupportFinitelyPresented.minus`,
  `AlgebraicGeometry.FlatProperSupportFinitelyPresented.isQuasicoherent` and
  `AlgebraicGeometry.FlatProperSupportFinitelyPresented.isQuasicoherent_pullbackComplex`:
  boundedness above of `𝒢^•` and quasi-coherence of the terms of `𝒢^•` and of `(g')^*𝒢^•`
  ([Stacks, Tags 01BW, 01BG]).

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback

-- The terms of the complex live in `X.Modules`, indexed by
-- `X.ringCatSheaf = (sheafCompose _ (forget₂ _ _)).obj X.sheaf`, while Tag 01BG is stated at
-- `structureSheafRing X.toRingedSpace`, whose reduct stops at an explicit-constructor
-- projection.  Instance search has to cross between the two — a quasi-coherence hypothesis is
-- read at one index and consumed at the other — so these two Mathlib definitions must unfold
-- during it.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The hypothesis of Stacks 0A1H on the complex -/

/-- **The hypothesis of [Stacks, Tag 0A1H] on `𝒢^•`.** A bounded complex of finitely presented
`𝒪_X`-modules, flat over `S`, whose support is proper over `S`.

The support condition is the one [Stacks, Tag 0CYS] makes sense of: a single closed subset `Z`
of `X` proper over `S` in the sense of `AlgebraicGeometry.IsProperOver`, containing the support
of every term. Since the complex is bounded, this is the proper-support condition for the
complex.

This is `Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex`, the hypothesis of
[Stacks, Tag 0DJQ], with coherence of the terms replaced by finite presentation and with the
category of `𝒪_X`-modules spelled `AlgebraicGeometry.Scheme.Modules`, which is the spelling the
base-change map of [Stacks, Tag 08HY] is written at. Over a Noetherian scheme the two
conditions on the terms agree ([Stacks, Tag 01XZ]); [Stacks, Tag 0A1H] asks for the weaker one
over an arbitrary base. -/
public structure FlatProperSupportFinitelyPresented {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (G : CochainComplex X.Modules ℤ) : Prop where
  /-- `𝒢^•` is a bounded complex. -/
  bounded : ∃ a b : ℤ, G.IsStrictlyGE a ∧ G.IsStrictlyLE b
  /-- Every term of `𝒢^•` is a finitely presented `𝒪_X`-module. -/
  isFinitePresentation : ∀ i : ℤ, (G.X i).IsFinitePresentation
  /-- Every term of `𝒢^•` is flat over `S`. -/
  isFlatOver : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i)
  /-- The support of `𝒢^•` is contained in a closed subset of `X` proper over `S`. -/
  properSupport : ∃ Z : Closeds X, IsProperOver f Z ∧
    ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)

namespace FlatProperSupportFinitelyPresented

variable {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFinitePresentation f]
  {G : CochainComplex X.Modules ℤ}

/-- **The terms of `𝒢^•` are quasi-coherent.** This is [Stacks, Tag 01BW]: a finitely presented
module is quasi-coherent. -/
public theorem isQuasicoherent (hG : FlatProperSupportFinitelyPresented f G) (i : ℤ) :
    (G.X i).IsQuasicoherent :=
  have := hG.isFinitePresentation i
  isQuasicoherent_of_isFinitePresentation (G.X i)

/-- **`𝒢^•` is bounded above.** `CochainComplex.minus` is boundedness above alone, which the
two-sided boundedness of [Stacks, Tag 0A1H] gives; it is the form [Stacks, Tag 0A1D] asks
for. -/
public theorem minus (hG : FlatProperSupportFinitelyPresented f G) :
    CochainComplex.minus X.Modules G :=
  let ⟨_, b, _, hb⟩ := hG.bounded
  ⟨b, hb⟩

/-- **The terms of the ordinary pullback `(g')^*𝒢^•` are quasi-coherent.** The terms of `𝒢^•`
are quasi-coherent by [Stacks, Tag 01BW] and pullback preserves quasi-coherence by
[Stacks, Tag 01BG]. -/
public theorem isQuasicoherent_pullbackComplex {X' : Scheme.{u}} (g' : X' ⟶ X)
    (hG : FlatProperSupportFinitelyPresented f G) (i : ℤ) :
    (((pullbackComplex g'.toLRSHom.toShHom).obj G).X i).IsQuasicoherent :=
  have := hG.isQuasicoherent i
  SheafOfModules.modulePullback_isQuasicoherent g'.toLRSHom.toShHom (G.X i)

end FlatProperSupportFinitelyPresented

end AlgebraicGeometry

end
