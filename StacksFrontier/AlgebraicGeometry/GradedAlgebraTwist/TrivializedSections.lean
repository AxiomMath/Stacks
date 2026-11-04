module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule

/-!
# The sections of a twisted graded algebra over an open trivializing the twisting sheaf

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra and `ℒ` an invertible
`𝒪_S`-module, and let `ℬ = 𝒜 ⊗ ℒ` be the twist of Tag 02NB, whose degree-`d` piece is
`𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`
(`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`). Over an open `W` of `S` on which `ℒ` is
trivialized, every tensor power `ℒ^{⊗ d}` is trivialized as well, so the degree-`d` sections of
the twist over `W` are the degree-`d` sections of `𝒜` over `W`.

This file records that comparison, degree by degree. It is the section-level form of the first
step of the proof of [Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC), whose own
argument is: *"This is the identity map when `ℒ ≅ 𝒪_S`. In general choose an open covering of
`S` such that `ℒ` is trivialized over the pieces and glue the corresponding maps."*

## Main definitions

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twistPieceSectionsEquiv`: **over an open
  trivializing `ℒ`, the degree-`d` sections of the twist are the degree-`d` sections of `𝒜`**, by
  a `Γ(S, W)`-linear isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twistPieceSectionsEquiv_apply`: the comparison is
  `x ↦ x ⊗ ℓ^{⊗ d}`, the local section determined by `x` and the generator of `ℒ^{⊗ d}` that the
  trivialization of `ℒ` induces.

## Implementation notes

The trivialization of the tensor powers is `Stacks.SheafOfModules.TensorPower`
`.overTensorPowerUnitIso`, which holds for every integer exponent and is stated on the slice site
over `W`; the comparison of sections of a tensor product one factor of which is trivialized is
`Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv`. Both apply to a scheme's site of
opens with no further hypothesis: the slice-site sheafification instances that
`overTensorPowerUnitIso` needs are available there, so neither affineness of `W` nor
quasi-coherence of the pieces enters, and the composite needs no transport between the two
spellings `(TensorSheafification.structureSheaf O hO).over W` and
`SliceRestriction.sliceStructureSheaf O hO W` of the restricted structure sheaf.

Nothing here chooses the trivialization: it is a hypothesis, and the comparison depends on it.

## What is not done here

**The comparison is not known to be multiplicative, so it does not yet assemble into an
isomorphism of the graded section rings, and the relative form of Tag 02NC does not follow from
it.** The multiplication of the twist on a pair of pure local sections is
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulSection_pure`: it multiplies the two sections of
`𝒜` by the multiplication of `𝒜` and the two sections of the tensor powers of `ℒ` by the
coherent multiplication `Stacks.SheafOfModules.TensorPower.coherentMulIso` of Tag 01CU. So
multiplicativity of this comparison is exactly the assertion that the generators it uses
multiply additively in the degree,

`coherentMulIso i j (gen_i ⊗ gen_j) = gen_{i + j}`,

for `gen_d` the generator `Stacks.SheafOfModules.TensorGenerator.generator` of `ℒ^{⊗ d}` induced
by the trivialization of `ℒ`. That is a coherence property of `overTensorPowerUnitIso`, which is
built as the composite of three comparisons:
`Stacks.SheafOfModules.TensorPower.overTensorPowerIso`, `tensorPowerCongr` and
`unitTensorPowerIso`.

**The first of the three is now multiplicative**, as
`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_overTensorPowerIso` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorAssociativity.lean`: all six
normalisations that `map_coherentMulIso_tensorPowerComparison` requires are available for the
restriction tensorator, the last of them being
`Stacks.SheafOfModules.TensorPower.isAssociative_whiskerTensorator`.

**The other two are not.** Neither `tensorPowerCongr` along a trivialization nor
`unitTensorPowerIso` is known to be compatible with `coherentMulIso`, and both are built by
`Stacks.Equivalence.powIntertwineObj` and `powObjIsoSelf` — recursion on an iterate of an abstract
autoequivalence — so neither compatibility is formal. Only
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr_zero`, `tensorPowerCongr_one`,
`unitTensorPowerIso_zero` and `unitTensorPowerIso_one` are available. Reaching them by the route
the first factor took would need the five laws of
`Stacks.SheafOfModules.TensorPower.TensorPowerCoherence` for the transported multiplication, hence
the compatibility of `tensorPowerCongr` and of `unitTensorPowerIso` with the unitors, the
associator and the braiding of Tag 01CA; `coherentMulIso_eq` would then identify the transport
with `coherentMulIso`. An alternative avoiding both is to define the family `gen_d` itself by
recursion through `coherentMulIso`, the multiplicativity then holding by construction in degree
`(d, 1)` and in every other pair of degrees by `coherentMulIso_assoc`.

Consequently the chain from here to the relative Tag 02NC — the graded ring isomorphism over a
trivializing open, `Proj` of it, independence of the chosen trivialization (for which the engine
`Stacks.GradedRing.Proj_map_eq_of_target_degreeScale` does exist), and the glueing over a
trivializing affine cover of `S` — is not begun.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.AlgebraicGeometry.GradedAlgebraTwist

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- **Over an open trivializing `ℒ`, the degree-`d` sections of the twist `𝒜 ⊗ ℒ` are the
degree-`d` sections of `𝒜`.**

The trivialization `e` of `ℒ` over `W` trivializes every tensor power `ℒ^{⊗ d}`, and tensoring
with a trivialized factor does not change the sections. This is the section-level form of the
first step of the proof of Tag 02NC, that the comparison is the identity where `ℒ ≅ 𝒪_S`.

No affineness of `W` and no quasi-coherence of the pieces is used. The comparison depends on the
trivialization `e`. -/
public def twistPieceSectionsEquiv (W : S.Opens)
    (e : L.over W ≅ SheafOfModules.unit
      ((structureSheaf S.sheaf.obj S.ringCatSheaf.property).over W))
    (d : ℤ) :
    Γ(𝒜.piece d, W) ≃ₗ[Γ(S, W)] Γ((twist 𝒜 L).piece d, W) :=
  Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv
    S.sheaf.obj S.ringCatSheaf.property W (𝒜.piece d)
    (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L d)
    (Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso
      S.sheaf.obj S.ringCatSheaf.property L W e d)

/-- **The comparison is `x ↦ x ⊗ ℓ^{⊗ d}`**: it sends a degree-`d` section of `𝒜` over `W` to the
local section of `𝒜_d ⊗ ℒ^{⊗ d}` determined by it and by the generator of `ℒ^{⊗ d}` that the
trivialization of `ℒ` induces. -/
public theorem twistPieceSectionsEquiv_apply (W : S.Opens)
    (e : L.over W ≅ SheafOfModules.unit
      ((structureSheaf S.sheaf.obj S.ringCatSheaf.property).over W))
    (d : ℤ) (x : Γ(𝒜.piece d, W)) :
    twistPieceSectionsEquiv 𝒜 L W e d x =
      tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (Opposite.op W) (𝒜.piece d)
        (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L d) x
        (Stacks.SheafOfModules.TensorGenerator.generator
          S.sheaf.obj S.ringCatSheaf.property W
          (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L d)
          (Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso
            S.sheaf.obj S.ringCatSheaf.property L W e d)) :=
  Stacks.SheafOfModules.TensorGenerator.tensorSectionsEquiv_apply
    S.sheaf.obj S.ringCatSheaf.property W (𝒜.piece d)
    (TensorPower.tensorPower S.sheaf.obj S.ringCatSheaf.property L d) _ x

end Stacks.AlgebraicGeometry.GradedAlgebraTwist

end
