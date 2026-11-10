module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Quotient

/-!
# A graded ideal from a multiplicative degreewise map out of a graded algebra

Work in Situation 01NN: a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. This file
constructs a graded ideal of `𝒜` with quasi-coherent pieces out of a degreewise family of
morphisms `φ_n : 𝒜_n ⟶ 𝒯_n` into quasi-coherent modules, carrying a multiplication of the targets
that the family respects. The ideal is the degreewise kernel.

This is the shape in which Stacks Tag 0801 produces its ideal: there `𝒯_d` is
`p_*(i_*(i^*𝒪_{Proj_S(𝒜)}(d)))` for a closed subscheme `i : Z ⟶ Proj_S(𝒜)` and `φ_d` is the
homogeneous-section map of Tag 01NR followed by the unit of the pullback-pushforward adjunction.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.MulCompatibleMaps`: the datum — a
  quasi-coherent target in each degree, a morphism out of each homogeneous piece of `𝒜`, a
  multiplication of the targets, and the compatibility of the morphisms with the two
  multiplications.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.kerPiece`: the degreewise kernel, as a
  submodule of the homogeneous piece.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.kerGradedIdeal` and `kerQcohGradedIdeal`:
  **the degreewise kernel as a graded ideal**, respectively as one with quasi-coherent pieces, so
  that it can be fed to `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_kerPiece_iff`: a local section lies in the
  ideal exactly when the degreewise morphism kills it.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.map_mul_eq_zero`: **the kernels absorb
  multiplication.** This is the `mul_mem` field, and it is a two-line consequence of the
  compatibility: the product is carried to the product of the images, and the first factor is
  zero.

## Implementation notes

The datum asks for strictly less than a homomorphism of graded algebras: no unit, no
associativity, no commutativity, and no vanishing in negative degrees. That matters for the
intended application, where the target is a family of twists `p_*(𝒪(d))` which does **not** vanish
in negative degrees, so it cannot be presented as a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` and the degreewise map cannot be
presented as a `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom`. Only the
multiplication of the targets and the compatibility are used, and only those are asked for.

Quasi-coherence of the kernel is `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`
transported along `Stacks.Algebraization.kernelSubmoduleIso`, which identifies the sectionwise
kernel submodule with the categorical kernel — the same route
`AlgebraicGeometry.isQuasicoherent_imageSubmodule` of
`StacksFrontier/AlgebraicGeometry/Modules/SubmoduleOpen.lean` takes.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Not done here

No Stacks tag is claimed, and **Tag 0801 is not proved.** What this file does is remove the
`mul_mem` field of `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedIdeal` from the list of
things Tag 0801 still owes, by reducing it to the multiplicativity of the degreewise maps. No
instance of `MulCompatibleMaps` is constructed here.

The instance Tag 0801 needs **is** constructed, in the sibling file
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistRestriction.lean`, as
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistMulCompatibleMaps`, and with it the graded
ideal `twistKerGradedIdeal`. For
`𝒯_d = p_*(i_*(i^*𝒪(d)))` the `targetMul` and `map_mul` fields amount to a graded-algebra
structure on the pullback of the twists along `i` and to the compatibility of the unit of the
pullback-pushforward adjunction with it, and both inputs are in the library: the graded structure is
`Stacks.Conormal.gradedPullback`
(`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/GradedPullback.lean`), the pullback of a sheaf of
graded algebras along a morphism of schemes, and the compatibility is its
`gradedPullback_mul_pullbackSection` read through `pullbackSection_self`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)

/-- A degreewise family of morphisms out of the homogeneous pieces of `𝒜`, into quasi-coherent
modules carrying a multiplication that the family respects.

Less is asked for than a homomorphism of graded algebras: the targets need no unit, no
associativity and no vanishing in negative degrees, which is what makes the family of twists
`p_*(𝒪(d))` of a relative Proj an admissible target. -/
structure MulCompatibleMaps (𝒜 : SheafGradedAlgebra S) where
  /-- The target in each degree. -/
  target (n : ℤ) : S.Modules
  /-- Every target is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (target n).IsQuasicoherent
  /-- The morphism out of the degree-`n` homogeneous piece of `𝒜`. -/
  map (n : ℤ) : 𝒜.piece n ⟶ target n
  /-- The multiplication of the targets. -/
  targetMul (i j : ℤ) : SheafBilinearMap (target i) (target j) (target (i + j))
  /-- The morphisms carry the multiplication of `𝒜` to the multiplication of the targets. -/
  map_mul (i j : ℤ) (U : S.Opens) (a : Γ(𝒜.piece i, U)) (b : Γ(𝒜.piece j, U)) :
    (map (i + j)).val.app (op U) ((𝒜.mul i j).app U a b) =
      (targetMul i j).app U ((map i).val.app (op U) a) ((map j).val.app (op U) b)

attribute [instance] MulCompatibleMaps.isQuasicoherent

variable (D : MulCompatibleMaps 𝒜)

/-- **The degree-`n` piece of the kernel ideal**: the sectionwise kernel of `φ_n : 𝒜_n ⟶ 𝒯_n`. -/
def kerPiece (n : ℤ) : (𝒜.piece n).Submodule :=
  Stacks.Algebraization.kernelSubmodule (D.map n)

/-- A homogeneous local section lies in the kernel ideal exactly when the degreewise morphism
kills it. -/
theorem mem_kerPiece_iff (n : ℤ) (U : S.Opens) (s : Γ(𝒜.piece n, U)) :
    s ∈ (kerPiece 𝒜 D n).toSubmodule.obj (op U) ↔ (D.map n).val.app (op U) s = 0 :=
  AlgebraicGeometry.mem_kernelSubmodule_iff (D.map n) U s

/-- **The kernels absorb multiplication.** If a homogeneous local section of degree `i` is killed
by `φ_i`, its product with an arbitrary homogeneous local section of degree `j` is killed by
`φ_{i + j}`: the product goes to the product of the images, whose first factor is zero, and the
multiplication of the targets is additive in each variable. -/
theorem map_mul_eq_zero (i j : ℤ) (U : S.Opens) {x : Γ(𝒜.piece i, U)}
    (hx : (D.map i).val.app (op U) x = 0) (b : Γ(𝒜.piece j, U)) :
    (D.map (i + j)).val.app (op U) ((𝒜.mul i j).app U x b) = 0 :=
  have h1 : (D.targetMul i j).app U ((D.map i).val.app (op U) x) = 0 :=
    (congrArg ((D.targetMul i j).app U) hx).trans (map_zero _)
  (D.map_mul i j U x b).trans
    ((DFunLike.congr_fun h1 ((D.map j).val.app (op U) b)).trans (AddMonoidHom.zero_apply _))

/-- **The degreewise kernel of a multiplicative degreewise family is a graded ideal of `𝒜`.** -/
def kerGradedIdeal : GradedIdeal 𝒜 where
  piece n := kerPiece 𝒜 D n
  mul_mem := by
    intro i j U x hx b
    exact (mem_kerPiece_iff 𝒜 D (i + j) U _).2
      (map_mul_eq_zero 𝒜 D i j U ((mem_kerPiece_iff 𝒜 D i U x).1 hx) b)

/-- The pieces of the kernel ideal are quasi-coherent: the sectionwise kernel submodule is the
categorical kernel, and a kernel of a morphism of quasi-coherent modules is quasi-coherent. -/
instance isQuasicoherent_kerPiece (n : ℤ) :
    (kerPiece 𝒜 D n).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (Stacks.Algebraization.kernelSubmoduleIso (D.map n)).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (D.map n))

/-- **The degreewise kernel, as a graded ideal with quasi-coherent pieces**, which is what
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra` consumes. -/
def kerQcohGradedIdeal : QcohGradedIdeal 𝒜 where
  __ := kerGradedIdeal 𝒜 D
  isQuasicoherent n := isQuasicoherent_kerPiece 𝒜 D n

/-- The degree-`n` piece of `kerQcohGradedIdeal` is the degreewise kernel `kerPiece`. -/
@[simp]
theorem kerQcohGradedIdeal_piece (n : ℤ) :
    (kerQcohGradedIdeal 𝒜 D).piece n = kerPiece 𝒜 D n := rfl

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
