module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Projective
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistTensor.TensorPowCongrIntBidegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation

/-!
# The arithmetic of the twisting sheaves of a blowup

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, and let `X'` be the blowup
of `X` in `ℐ`, the relative `Proj` of the Rees algebra `⨁_{d ≥ 0} ℐ^d`. This file proves the
two arithmetic laws of its twisting sheaves:

`𝒪_{X'}(n) ⊗ 𝒪_{X'}(m) ≅ 𝒪_{X'}(n + m)` and `𝒪_{X'}(-n) ≅ 𝒪_{X'}(n)^∨`,

in all integer degrees and with no hypothesis on `X` or on `ℐ`.

## Main results

* `Stacks.Blowup.isIso_mulSheaf_reesTwist`: the multiplication maps of the twists are
  isomorphisms.
* `Stacks.Blowup.reesTwistAddIso`: **the addition law** `𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)`.
* `Stacks.Blowup.reesTwistZeroIsoUnit`: `𝒪(0) ≅ 𝒪_{X'}`.
* `Stacks.Blowup.reesTwistNegTensorIsoUnit`: `𝒪(n) ⊗ 𝒪(-n) ≅ 𝒪_{X'}`.
* `Stacks.Blowup.reesTwistNegIsoDual`: **the inversion law** `𝒪(-n) ≅ 𝒪(n)^∨`.

## The route

The Rees algebra of a quasi-coherent sheaf of ideals is generated in degree one over every
affine open of the base, `AlgebraicGeometry.isGeneratedInDegreeOne_reesSheafGradedAlgebra`, which
is exactly the hypothesis of the multiplication clause of [Stacks, Tag 01O4],
`Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_mulSheaf_twistDataOfGradedAlgebra`. So the
addition law is that clause instantiated at the Rees algebra, and the remaining three statements
are monoidal consequences: an invertible module `L` with `L ⊗ L ≅ L` is the unit, which gives
`𝒪(0) ≅ 𝒪_{X'}`; the addition law at `(n, -n)` then exhibits `𝒪(-n)` as a tensor inverse of
`𝒪(n)`, and a tensor inverse of an invertible module is its dual, [Stacks, Tag 0B8N] (c).

## Which twisting sheaf

The twists here are `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist` of the Rees algebra on
the `SheafGradedAlgebra` substrate — the homogeneous pieces of the glued graded algebra of
[Stacks, Tag 01NR] — on the scheme
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj (Stacks.Blowup.reesSheafGradedAlgebra ℐ)`,
which is the blowup: `Stacks.Blowup.reesProjBlowUpIso` identifies it with
`AlgebraicGeometry.blowUp ℐ` over the base and compatibly with the charts
(`Stacks.Blowup.chart_reesProjBlowUpIso_hom`).

The repository carries the graded twists of a relative `Proj` twice over, and the laws above are
**not** transported to the second copy `AlgebraicGeometry.blowUpTwist`, which is glued from the
chart twists along `Stacks.RelativeProj.Situation.twistTransition`. Transporting them needs a
degreewise comparison of the two glueings, and that comparison does not exist: the chart
comparison of the datum here is `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap` while the
one of `twistTransition` is `Stacks.ProjTwistComparison.twistMap`, and nothing in the library
identifies those two maps — a gap recorded in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeTwist.lean`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.Ample
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.TwistMapsInvertible

universe u

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The `n`-th twisting sheaf of the blowup of `X` in `ℐ`, read on the relative `Proj` of the
Rees algebra on the `SheafGradedAlgebra` substrate. -/
public abbrev reesTwist (n : ℤ) :
    (relativeProj (reesSheafGradedAlgebra I)).scheme.Modules :=
  relativeTwist (reesSheafGradedAlgebra I) n

/-- **The twisting sheaves of a blowup are invertible**, in every degree and with no hypothesis
on the centre. -/
public instance isInvertibleModule_reesTwist (n : ℤ) :
    IsInvertibleModule (relativeProj (reesSheafGradedAlgebra I)).scheme (reesTwist I n) :=
  twistDataOfGradedAlgebra_isInvertible
    (AlgebraicGeometry.isGeneratedInDegreeOne_reesSheafGradedAlgebra I) n

/-- **The multiplication maps of the twisting sheaves of a blowup are isomorphisms.** This is the
multiplication clause of [Stacks, Tag 01O4] at the Rees algebra, which is generated in degree one
over every affine open of the base. -/
public theorem isIso_mulSheaf_reesTwist (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf
      (twistDataOfGradedAlgebra (reesSheafGradedAlgebra I)).algebra n m) :=
  isIso_mulSheaf_twistDataOfGradedAlgebra
    (AlgebraicGeometry.isGeneratedInDegreeOne_reesSheafGradedAlgebra I) n m

/-- **The addition law for the twisting sheaves of a blowup**: `𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)`, in all
integer degrees, for an arbitrary scheme and an arbitrary quasi-coherent sheaf of ideals. The
isomorphism is the multiplication map of the glued graded algebra of [Stacks, Tag 01NR]. -/
public def reesTwistAddIso (n m : ℤ) :
    reesTwist I n ⊗ reesTwist I m ≅ reesTwist I (n + m) :=
  @asIso _ _ _ _ _ (isIso_mulSheaf_reesTwist I n m)

/-- The addition law is the multiplication map of the glued graded algebra of [Stacks, Tag 01NR],
not an abstract isomorphism: it is `asIso` of that map. -/
public theorem reesTwistAddIso_hom (n m : ℤ) :
    (reesTwistAddIso I n m).hom =
      SheafOfModules.GradedAlgebra.mulSheaf
        (twistDataOfGradedAlgebra (reesSheafGradedAlgebra I)).algebra n m :=
  rfl

/-- Reindexing of `𝒪(n)` along an equality of degrees. -/
public def reesTwistCongr {n m : ℤ} (h : n = m) : reesTwist I n ≅ reesTwist I m :=
  eqToIso (congrArg (fun k : ℤ => reesTwist I k) h)

/-- **`𝒪(0) ≅ 𝒪_{X'}`.** The degree-zero twist is invertible and idempotent for the tensor
product — the addition law at `(0, 0)` — and an invertible module isomorphic to its own square is
the unit: tensoring `𝒪(0) ⊗ 𝒪(0) ≅ 𝒪(0)` with a tensor inverse of `𝒪(0)` on the right collapses
the left side to `𝒪(0)` and the right side to `𝒪_{X'}`. -/
public def reesTwistZeroIsoUnit :
    reesTwist I 0 ≅ 𝟙_ (relativeProj (reesSheafGradedAlgebra I)).scheme.Modules :=
  let Y := (relativeProj (reesSheafGradedAlgebra I)).scheme
  let L := reesTwist I 0
  let N := tensorPowModule Y L (-1)
  let eN : L ⊗ N ≅ 𝟙_ Y.Modules :=
    whiskerRightIso (tensorPowModuleOneIso Y L).symm N ≪≫
      Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleInvIsoRight Y L 1
  let h : L ⊗ L ≅ L := reesTwistAddIso I 0 0 ≪≫ reesTwistCongr I (by ring)
  (ρ_ L).symm ≪≫ whiskerLeftIso L eN.symm ≪≫ (α_ L L N).symm ≪≫
    whiskerRightIso h N ≪≫ eN

/-- **`𝒪(n) ⊗ 𝒪(-n) ≅ 𝒪_{X'}`**: the twists in opposite degrees are tensor inverses. -/
public def reesTwistNegTensorIsoUnit (n : ℤ) :
    reesTwist I n ⊗ reesTwist I (-n) ≅
      𝟙_ (relativeProj (reesSheafGradedAlgebra I)).scheme.Modules :=
  reesTwistAddIso I n (-n) ≪≫ reesTwistCongr I (by ring) ≪≫ reesTwistZeroIsoUnit I

/-- **The inversion law for the twisting sheaves of a blowup**: `𝒪(-n) ≅ 𝒪(n)^∨`, in all integer
degrees, for an arbitrary scheme and an arbitrary quasi-coherent sheaf of ideals.

`𝒪(-n)` is a tensor inverse of `𝒪(n)` by `Stacks.Blowup.reesTwistNegTensorIsoUnit`, and a tensor
inverse of an invertible sheaf of modules is its dual, [Stacks, Tag 0B8N] (c). -/
public def reesTwistNegIsoDual (n : ℤ) :
    reesTwist I (-n) ≅
      Stacks.SheafOfModules.dualSheaf
        (relativeProj (reesSheafGradedAlgebra I)).scheme.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
          (relativeProj (reesSheafGradedAlgebra I)).scheme)
        (reesTwist I n) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf _ _ (reesTwist I n) (reesTwist I (-n))
    (reesTwistNegTensorIsoUnit I n)

end Stacks.Blowup

end
