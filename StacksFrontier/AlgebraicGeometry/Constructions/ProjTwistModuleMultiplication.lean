module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic

/-!
# Multiplication of a twisted module sheaf by a twist of the structure sheaf

Let `S` be a nonnegatively graded ring, `X = Proj S`, and let `ℱ` be a sheaf of
`𝒪_X`-modules. For integers `n` and `m` there is a canonical multiplication morphism

`𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`,

where `ℱ(k) = ℱ ⊗ 𝒪_X(k)` is the `k`-th twist of `ℱ`. It is built out of the
symmetric-monoidal constraints of the sheaf tensor product and the multiplication
`𝒪_X(n) ⊗ 𝒪_X(m) ⟶ 𝒪_X(n + m)` of the twisting sheaves.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap`: the canonical
  morphism `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`.

## References

* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] CategoryTheory.sheafCompose TopCat.Sheaf
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.SheafOfModules.Invertible

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The canonical multiplication map `𝒪_X(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`** on `X = Proj S`, for a
sheaf of `𝒪_X`-modules `ℱ`: reassociate, braid `𝒪(n)` past `ℱ`, reassociate again, and
multiply the two twists of the structure sheaf together. -/
@[stacks 03GJ]
public noncomputable def twistSheafMultiplicationMap
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj ((twistingSheaf 𝒮 n))).obj
        ((twistSheafOfModules 𝒮 F m))) ⟶
      twistSheafOfModules 𝒮 F (n + m) := by
  let O := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
  let J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)
  let hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O) :=
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property
  let L (k : ℤ) := twistingSheaf 𝒮 k
  let f₁ :=
    (tensorProductAssociator O hO (L n) F (L m)).inv
  let f₂ :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
      (((tensorProductBraiding O hO (L n) F).hom, (𝟙 (L m))) : (_, _) ⟶ (_, _)))
  let f₃ :=
    (tensorProductAssociator O hO F (L n) (L m)).hom
  let f₄ :=
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
      (((𝟙 F), (twistMultiplicationMap 𝒮 n m)) : (_, _) ⟶ (_, _)))
  exact f₁ ≫ f₂ ≫ f₃ ≫ f₄

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
