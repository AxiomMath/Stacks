module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem

/-!
# Extension problems for pairs of a ringed topos and a module

Fix an extension problem `S` for a ringed topos `X` over a first order thickening of a base (the
ring part, `Deformation.ToposThickening.RingedToposExtensionProblem`), an `O_X`-module `L`, a
second `O_X`-module `GL`, the prescribed kernel for a thickening of `L`, and an `O_X`-bilinear
pairing `μ : G ⊗ L ⟶ GL`, where `G` is the prescribed kernel of the ring part. A solution is a
solution `O'` of the ring part together with an `O'`-module `L'`, a locally surjective map
`L' ⟶ L` whose kernel is identified with `GL`, such that a section `g` of the kernel `G` of
`O' ⟶ O_X` acts on a section `l'` of `L'` by `μ(g ⊗ l̄')`, where `l̄'` is the image of `l'`
in `L`.

## Main definitions

* `Deformation.PairDeformation.sectionTensor`: the sectionwise tensor product of two
  `O_X`-modules, a presheaf of modules.
* `Deformation.PairDeformation.PairExtensionProblem`: the ring part, the module `L`, its
  prescribed kernel `GL`, and the pairing `μ`.
* `Deformation.PairDeformation.PairExtensionProblem.pairing`: the pairing on local sections.
* `Deformation.PairDeformation.PairExtensionProblem.Solution`: a solution of a pair extension
  problem.

## Implementation notes

The pairing is a map of presheaves of modules out of the sectionwise tensor product
`PresheafOfModules.tensorObj`, the presheaf that `Stacks.SheafOfModules.Tensor.sheafTensor`
sheafifies. A map out of the sheafified tensor product into the sheaf `GL` is the same thing, and
the sectionwise form needs no sheafification and evaluates directly on local pure tensors; maps
out of it are built from bilinear maps on sections by `PresheafOfModules.tensorMk`.

As in `Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening`,
the module `L` and the kernel `GL` are made modules over the thickened structure sheaf by
restriction of scalars along the reduction, the map `L' ⟶ L` is only required to be locally
surjective, and its kernel is identified with `GL` section by section.

The prescribed kernel `GL` is the field `moduleKernel`: `GL` is a token of Mathlib (the
general linear group notation) and cannot be a field name.

## References

* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry (RingedTopos)
open Deformation.ToposThickening (RingedToposExtensionProblem)

universe v u w v' u' w'

namespace Deformation.PairDeformation

/-- The sectionwise tensor product of two modules over the structure sheaf of a ringed topos,
as a presheaf of modules: its sections over `U` are `M(U) ⊗_{O(U)} N(U)`. -/
public noncomputable abbrev sectionTensor {X : RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (M N : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)) :
    PresheafOfModules.{w} (X.O.val ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  PresheafOfModules.tensorObj (O := X.O.val) M.val N.val

/-- The fixed data of an extension problem for a pair: the ring part `S`, an `O_X`-module `L`,
the prescribed kernel `GL` of a thickening of `L`, and an `O_X`-bilinear pairing
`μ : G ⊗ L ⟶ GL`, where `G` is the prescribed kernel of the ring part. -/
public structure PairExtensionProblem
    (X : RingedTopos.{v, u, w})
    (B : RingedTopos.{v', u', w'})
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [B.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})] where
  /-- The ring part of the problem. -/
  S : RingedToposExtensionProblem X B
  /-- The module to be thickened. -/
  L : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)
  /-- The prescribed kernel of a thickening of `L`. -/
  moduleKernel :
    SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)
  /-- The pairing `G ⊗ L ⟶ GL` through which the kernel of the ring part acts. -/
  μ : sectionTensor S.G L ⟶
    (moduleKernel.val : PresheafOfModules.{w} (X.O.val ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

namespace PairExtensionProblem

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The pairing of a pair extension problem on local sections: `μ(g ⊗ l)`. -/
public noncomputable def pairing (P : PairExtensionProblem X B) (U : X.Cᵒᵖ)
    (g : P.S.G.val.obj U) (l : P.L.val.obj U) : P.moduleKernel.val.obj U :=
  P.μ.app U (g ⊗ₜ[X.O.val.obj U] l)

/-- The restriction of scalars of an `O_X`-module along the reduction `O' ⟶ O_X` of a solution
of the ring part. -/
public noncomputable abbrev restrictToExtension {P : PairExtensionProblem X B}
    (Q : P.S.CompatibleFirstOrderThickening)
    (M : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)) :
    SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj Q.extension) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map Q.reduction)).obj M

/-- A solution of a pair extension problem: a solution `O'` of the ring part, an `O'`-module
`L'`, a locally surjective `O'`-linear map `L' ⟶ L` whose kernel is identified with `GL`, such
that a section `g` of the kernel `G` of `O' ⟶ O_X` acts on a section `l'` of `L'` by
`μ(g ⊗ l̄')`. -/
public structure Solution (P : PairExtensionProblem X B) where
  /-- The solution of the ring part. -/
  ring : P.S.CompatibleFirstOrderThickening
  /-- The thickened module. -/
  module : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj ring.extension)
  /-- The reduction of the thickened module to `L`. -/
  reduction : module ⟶ restrictToExtension ring P.L
  /-- The reduction is locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective X.J
    ((PresheafOfModules.toPresheaf _).map reduction.val)
  /-- The identification of `GL` with the kernel of the reduction. -/
  kernelInclusion : restrictToExtension ring P.moduleKernel ⟶ module
  /-- The chosen inclusion lands in the kernel. -/
  kernelZero : ∀ (U : X.Cᵒᵖ) (a : P.moduleKernel.val.obj U),
    reduction.val.app U (kernelInclusion.val.app U a) = 0
  /-- The chosen inclusion identifies `GL` with the entire kernel. -/
  kernelUniversal : ∀ (U : X.Cᵒᵖ) (l : module.val.obj U),
    reduction.val.app U l = 0 → ∃! a : P.moduleKernel.val.obj U, kernelInclusion.val.app U a = l
  /-- A section `g` of the kernel of `O' ⟶ O_X` acts on `l'` by `μ(g ⊗ l̄')`. -/
  smul_eq : ∀ (U : X.Cᵒᵖ) (g : P.S.G.val.obj U) (l : module.val.obj U),
    (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ring.extension).val.obj U from ring.kernelInclusion.val.app U g) • l =
      kernelInclusion.val.app U (P.pairing U g (reduction.val.app U l))

end PairExtensionProblem

end Deformation.PairDeformation

end
