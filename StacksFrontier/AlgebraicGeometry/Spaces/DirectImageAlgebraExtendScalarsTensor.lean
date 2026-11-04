module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommExtendScalarsMixedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictScalarsSheafification

/-!
# Extension of scalars along `f♯ : 𝒪_X ⟶ f_*𝒪_Y` preserves quasi-coherence

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `𝒜 = f_*𝒪_Y` be the direct-image algebra of Stacks 03G8.  Extension of scalars
along `f♯ : 𝒪_X ⟶ 𝒜`, read back as a functor to `𝒪_X`-modules, is the tensor product `𝒜 ⊗_{𝒪_X} -`
on the small étale site of `X`; for an affine `f` the algebra `𝒜` is quasi-coherent as an
`𝒪_X`-module, so that functor preserves quasi-coherence by the tensor-product clause of
Stacks 03M1.

That is `AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`, to which the hypothesis
`hL` of `AlgebraicGeometry.Space.isEquivalence_quasicoherentDirectImage` reduces; with it `hL`
holds for every affine morphism.

## Main results

* `AlgebraicGeometry.Space.mul_comm_structureRingSheafDirectImage`: the sections of `𝒜` over an
  étale chart of `X` commute.
* `AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`: **extension of scalars
  along `f♯`, read back as a functor to `𝒪_X`-modules, is the tensor product by `𝒜`**, that is,
  `𝒜 ⊗_{𝒪_X} ℱ` in the shape `AlgebraicGeometry.Space.tensorModule` in which the
  tensor-product clause of Stacks 03M1 is proved.
* `AlgebraicGeometry.Space.extendScalarsPreservesQuasicoherence`:
  **`AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence` for an affine morphism.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`: **`hL` for an
  affine morphism, with no hypothesis beyond affineness** — the quasi-inverse of Stacks 08AI
  carries quasi-coherent `𝒜`-modules to quasi-coherent `𝒪_Y`-modules.

## The argument

Write `E` for extension of scalars along `f♯` and `Rs` for restriction of scalars along it.
`E` is the objectwise extension of scalars sheafified, and `AlgebraicGeometry.Space.tensorModule`
is the objectwise tensor product, its sections raised by a universe they already lie in,
sheafified.  The comparison of the two therefore splits into three steps, none of which computes
a sheafification:

* restriction of scalars commutes with sheafification of presheaves of modules, by
  `AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso` — the two sheaves of
  modules have one and the same underlying abelian sheaf and only the two scalar actions have to
  be compared;
* before sheafifying, the objectwise extension of scalars read back over `𝒪_X` *is* the
  objectwise tensor product with `𝒜`, by
  `Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend`.  This is where
  commutativity of the sections of `𝒜` is used: the tensor product of
  `PresheafOfModules.MixedTensor.tensorObj` is taken over the commutative structure ring and
  uses `𝒜` as a module over it, which agrees with the relative tensor product of
  `Stacks.NoncommChangeOfRings.BaseChange` exactly when the sections of `𝒜` commute;
* raising the universe of the sections of the objectwise tensor product changes nothing, by
  `PresheafOfModules.uliftSectionsSelfIso`.

Commutativity of the sections of `𝒜` is not an extra input.  `𝒜` is the inverse image of the
structure sheaf of `Y` along the direct image of sheaves of sets, and the inverse image of a
sheaf of *commutative* rings has commutative sections:
`Stacks.Sheaves.RingedToposModules.inverseImageSectionsCommRing`, whose own hypothesis is
discharged by `Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm`.

Given the comparison, `Rs (E ℱ)` is quasi-coherent whenever `ℱ` is: it is `𝒜 ⊗_{𝒪_X} ℱ`, both
factors are quasi-coherent — `𝒜` by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage`,
which is where affineness of `f` enters — and the tensor product of two quasi-coherent
`𝒪_X`-modules is quasi-coherent by clause (5) of Stacks 03M1.

## Implementation notes

The three isomorphisms compose on the nose: the target of the chain is syntactically
`AlgebraicGeometry.Space.tensorModule`, so no transport is needed to feed it to clause (5).

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

noncomputable section

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- **The sections of the direct-image algebra `𝒜 = f_*𝒪_Y` over an étale chart of `X`
commute.**  `𝒜` is the inverse image of the structure sheaf of `Y` along the direct image of
sheaves of sets, and the inverse image of a sheaf of commutative rings has commutative
sections. -/
theorem mul_comm_structureRingSheafDirectImage (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (structureRingSheafDirectImage B S hS f).obj.obj V) : a * b = b * a :=
  (inverseImageSectionsCommRing (SmallEtale.topology B S hS X.1)
    (smallEtaleDirectImage B S hS f)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
    (commRingSheaf_mul_comm (structureSheaf B S hS Y.1 Y.2)) V).mul_comm a b

/-- **Extension of scalars along `f♯ : 𝒪_X ⟶ 𝒜`, read back as a functor to `𝒪_X`-modules, is the
tensor product by `𝒜`.**

The target is `AlgebraicGeometry.Space.tensorModule`, the shape of the tensor product in which
clause (5) of Stacks 03M1 is proved on the small étale site, with `𝒜` read as an `𝒪_X`-module by
restriction of scalars along `f♯`.

Three steps carry the comparison, and none of them computes a sheafification: restriction of
scalars commutes with sheafification; the objectwise extension of scalars read back over `𝒪_X`
is the objectwise tensor product with `𝒜`; and raising the universe of the sections of that
tensor product by a universe they already lie in changes nothing. -/
def restrictScalarsExtendScalarsIsoTensorModule (F : Modules.{u, u} B S hS X.1 X.2) :
    (directImageAlgebraRestrictScalars B S hS f).obj
        ((directImageAlgebraExtendScalars B S hS f).obj F) ≅
      tensorModule B S hS X.1 X.2
        ((directImageAlgebraRestrictScalars B S hS f).obj
          (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))) F :=
  AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso.{u, u, u, u + 1}
      (structureSharp B S hS f) _ ≪≫
    (PresheafOfModules.sheafification.{u}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).mapIso
      ((Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend
          (structureSharp B S hS f).hom
          (mul_comm_structureRingSheafDirectImage B S hS f) F.val).symm ≪≫
        (PresheafOfModules.uliftSectionsSelfIso _).symm)

/-- **Extension of scalars along `f♯ : 𝒪_X ⟶ 𝒜`, read back as a functor to `𝒪_X`-modules,
preserves quasi-coherence**, for an affine morphism of algebraic spaces.  This is
`AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`.

It is the tensor product by `𝒜` by
`AlgebraicGeometry.Space.restrictScalarsExtendScalarsIsoTensorModule`; `𝒜` is quasi-coherent as
an `𝒪_X`-module for an affine `f` by the first assertion of Stacks 07U8, and the tensor product
of two quasi-coherent `𝒪_X`-modules is quasi-coherent by clause (5) of Stacks 03M1. -/
theorem extendScalarsPreservesQuasicoherence (hf : IsAffineHom B S hS f.hom) :
    ExtendScalarsPreservesQuasicoherence B S hS f := fun F hF =>
  (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (restrictScalarsExtendScalarsIsoTensorModule B S hS f F).symm
    (isQuasicoherentOnSite_tensorModule_schemeUniverse B S hS X.1 X.2 _ F
      (isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage B S hS f hf) hF)

/-- **The quasi-inverse of Stacks 08AI preserves quasi-coherence**, for an affine morphism of
algebraic spaces and with no further hypothesis: it carries quasi-coherent `𝒜`-modules to
quasi-coherent `𝒪_Y`-modules.

This is the hypothesis `hL` of
`AlgebraicGeometry.Space.isEquivalence_quasicoherentDirectImage`, discharged.  The reduction to
extension of scalars is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars`, and
the statement it takes is
`AlgebraicGeometry.Space.extendScalarsPreservesQuasicoherence`. -/
theorem isQuasicoherentOnSite_directImageAlgebraPullback (hf : IsAffineHom B S hS f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) :
    ((directImageAlgebraPullback B S hS f).obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars B S hS f hf
    (extendScalarsPreservesQuasicoherence B S hS f hf) G hG

end AlgebraicGeometry.Space

end

end
