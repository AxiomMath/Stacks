module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# `D_QCoh` is closed under the derived tensor product, at an arbitrary model

[Stacks, Tag 08DX] part (1) says that for a scheme `X` and complexes `K`, `L` of `𝒪_X`-modules
with quasi-coherent cohomology sheaves, every cohomology sheaf of `K ⊗^𝐋_{𝒪_X} L` is
quasi-coherent.  `Stacks.Duality.isQuasicoherent_homology_derivedTensor` proves it at the
locally small model of `D(𝒪_X)`, the only model at which its affine input was available when it
was written.  This file carries it to every model.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_tensorComplex`: the statement with no derived category
  in it — for a complex `C` and a *K-flat* complex `P` of `𝒪_X`-modules, both with
  quasi-coherent cohomology, every cohomology sheaf of the total tensor complex
  `Tot(C ⊗_{𝒪_X} P)` of [Stacks, Tag 06YM] is quasi-coherent.
* `Stacks.Duality.isQuasicoherent_homology_derivedTensor_anyModel`: **[Stacks, Tag 08DX] part (1)
  at an arbitrary model of `D(𝒪_X)`.**

## Implementation notes

The derived tensor product is computed by the total tensor complex as soon as one factor is
K-flat — that is the `comparisonRight` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, which asks K-flatness of the *right*
factor only — and the total tensor complex is a complex, an object of no derived category.  So
the quasi-coherence of its cohomology is a model-free statement, and
`isQuasicoherent_homology_tensorComplex` proves it once, at the locally small model, by reading
[Stacks, Tag 08DX] part (1) through that comparison.  Any other model then reads it
back through the same comparison, which is `isQuasicoherent_homology_derivedTensor_anyModel`.

This is the device `Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel` uses for
[Stacks, Tag 08DW] part (1), with the K-flat computation of the derived pullback replaced by the
K-flat computation of the derived tensor product.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite

universe w u

namespace Stacks.Duality

/-! ### The cohomology of a total tensor complex -/

/-- **The cohomology sheaves of a total tensor complex `Tot(C ⊗_{𝒪_X} P)` are quasi-coherent**
when those of `C` and of `P` are and `P` is K-flat.

No derived category appears in the statement.  The proof reads [Stacks, Tag 08DX] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedTensor`, through the K-flat comparison of
[Stacks, Tag 06YU] at the locally small model, which identifies `C ⊗^𝐋_{𝒪_X} P` with the class
of `Tot(C ⊗_{𝒪_X} P)` because `P` is K-flat. -/
theorem isQuasicoherent_homology_tensorComplex (X : Scheme.{u})
    (C P : CochainComplex (Modules X.toRingedSpace.sheaf) ℤ)
    (hP : Stacks.SheafOfModules.KFlat.KFlat X.toRingedSpace.sheaf P)
    (hC : ∀ j : ℤ, (C.homology j).IsQuasicoherent)
    (hPq : ∀ j : ℤ, (P.homology j).IsQuasicoherent) (i : ℤ) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj C).obj
      P).homology i).IsQuasicoherent := by
  have hCQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      (DerivedCategory.Q.obj C)).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) j).app C).symm
      (hC j)
  have hPQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      (DerivedCategory.Q.obj P)).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) j).app P).symm
      (hPq j)
  have h08 := isQuasicoherent_homology_derivedTensor X
    ⟨DerivedCategory.Q.obj C, hCQ⟩ ⟨DerivedCategory.Q.obj P, hPQ⟩ i
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) i).app
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj C).obj P)) ?_
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonRight C P hP)) h08

/-! ### [Stacks, Tag 08DX] part (1) at an arbitrary model -/

/-- **[Stacks, Tag 08DX] part (1) at an arbitrary model of `D(𝒪_X)`: `D_QCoh(𝒪_X)` is closed
under the derived tensor product.**  For a scheme `X` and objects `E`, `A` of `D(𝒪_X)` all of
whose cohomology sheaves are quasi-coherent, every cohomology sheaf of `E ⊗^𝐋_{𝒪_X} A` is
quasi-coherent.

The model of the derived category is a free `[HasDerivedCategory.{w}]` binder, so this serves the
locally small model of `Stacks.Duality.isQuasicoherent_homology_derivedTensor` and
`CategoryTheory.HasDerivedCategory.standard` alike.  `A` is the class of a K-flat complex `P` by
[Stacks, Tag 06YS], `E` is the class of some complex `C`, the K-flat comparison of
[Stacks, Tag 06YU] identifies `E ⊗^𝐋_{𝒪_X} A` with the class of `Tot(C ⊗_{𝒪_X} P)`, and the
cohomology of that complex is quasi-coherent by `isQuasicoherent_homology_tensorComplex`. -/
@[stacks 08DX "part (1) at an arbitrary model of the derived category"]
theorem isQuasicoherent_homology_derivedTensor_anyModel (X : Scheme.{u})
    [HasDerivedCategory.{w} (Modules X.toRingedSpace.sheaf)]
    (E A : DerivedCategory (Modules X.toRingedSpace.sheaf))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules X.toRingedSpace.sheaf) j).obj E).IsQuasicoherent)
    (hA : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (Modules X.toRingedSpace.sheaf) j).obj A).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules X.toRingedSpace.sheaf) i).obj
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E).obj A)).IsQuasicoherent := by
  obtain ⟨P, f, hP, hf⟩ := exists_kFlat_quasiIso X.toRingedSpace.sheaf
    (DerivedCategory.Q.objPreimage A)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := Modules X.toRingedSpace.sheaf) f).2 hf
  have eA : (DerivedCategory.Q.obj P : DerivedCategory (Modules X.toRingedSpace.sheaf)) ≅ A :=
    @asIso _ _ _ _ (DerivedCategory.Q.map f) hiso ≪≫ DerivedCategory.Q.objObjPreimageIso A
  set C := DerivedCategory.Q.objPreimage E with hCdef
  have eE : (DerivedCategory.Q.obj C : DerivedCategory (Modules X.toRingedSpace.sheaf)) ≅ E :=
    DerivedCategory.Q.objObjPreimageIso E
  have hCh : ∀ j : ℤ, (C.homology j).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) j).app C)
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor (Modules X.toRingedSpace.sheaf) j).mapIso eE).symm
        (hE j))
  have hPh : ∀ j : ℤ, (P.homology j).IsQuasicoherent := fun j =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) j).app P)
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor (Modules X.toRingedSpace.sheaf) j).mapIso eA).symm
        (hA j))
  have e : (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E).obj A) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSpace.sheaf).obj C).obj P) :=
    (((derivedTensorProductFunctor X.toRingedSpace.sheaf).mapIso eE).app A).symm ≪≫
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        (DerivedCategory.Q.obj C)).mapIso eA).symm ≪≫
      (canonicalDerivedTensorProduct X.toRingedSpace.sheaf).comparisonRight C P hP
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Modules X.toRingedSpace.sheaf) i).mapIso e).symm ?_
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors (Modules X.toRingedSpace.sheaf) i).app _).symm
    (isQuasicoherent_homology_tensorComplex X C P hP hCh hPh i)

end Stacks.Duality

end
