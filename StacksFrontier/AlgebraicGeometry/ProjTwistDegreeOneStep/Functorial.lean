module

public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneStep.Twist

/-!
# The graded action on twisted global sections is natural in the sheaf

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮` and `φ : ℱ ⟶ 𝒢` a morphism of
`𝒪_X`-modules. Twisting `φ` gives maps `ℱ(d) ⟶ 𝒢(d)` in every degree, and on global sections
these commute with multiplication by a homogeneous scalar, so `φ` induces a map of the graded
`S`-modules `⨁_d Γ(X, ℱ(d)) ⟶ ⨁_d Γ(X, 𝒢(d))` of [Stacks, Tag 03GK] — the functoriality of that
tag in the sheaf.

## Main results

* `twistFunctor_map_eq`: the twist functor acts on a morphism by tensoring it with the identity of
  the twisting sheaf.
* `twistSheafScalarMap_comp_twistFunctor_map`: multiplication by a homogeneous scalar commutes
  with the twist of `φ`, as morphisms of sheaves.
* `globalSections_map_homogeneousScalar`: the same on global sections.

## References

* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor (projRingSheaf twistFunctor)
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The twist `ℱ(d) ⟶ 𝒢(d)` of a morphism `φ : ℱ ⟶ 𝒢` is the tensor product of `φ` with the
identity of the twisting sheaf `𝒪(d)`. -/
theorem twistFunctor_map_eq (d : ℤ) {F G : SheafOfModules.{u} (projRingSheaf 𝒮)} (φ : F ⟶ G) :
    (twistFunctor 𝒮 d).map φ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
          (X := (F, twistingSheaf 𝒮 d)) (Y := (G, twistingSheaf 𝒮 d))
          (φ, 𝟙 (twistingSheaf 𝒮 d)) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
    (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮)
    φ (𝟙 (twistingSheaf 𝒮 d))).symm

/-- For `φ : ℱ ⟶ 𝒢` and a homogeneous `a` of degree `i`, multiplication by `a` from `ℱ(d)` to
`ℱ(k)`, where `i + d = k`, commutes with the tensor products of `φ` with the identities of the
twisting sheaves: `a · (φ ⊗ 𝟙) = (φ ⊗ 𝟙) · a` as morphisms `ℱ(d) ⟶ 𝒢(k)`. -/
theorem twistSheafScalarMap_comp_twistFunctor_map
    {F G : SheafOfModules.{u} (projRingSheaf 𝒮)} (φ : F ⟶ G)
    (i : ℕ) (d k : ℤ) (hk : (i : ℤ) + d = k) (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 F i d k hk a ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
            (X := (F, twistingSheaf 𝒮 k)) (Y := (G, twistingSheaf 𝒮 k))
            (φ, 𝟙 (twistingSheaf 𝒮 k)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
          (X := (F, twistingSheaf 𝒮 d)) (Y := (G, twistingSheaf 𝒮 d))
          (φ, 𝟙 (twistingSheaf 𝒮 d)) ≫ twistSheafScalarMap 𝒮 G i d k hk a := by
  refine ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map_comp
      (X := (F, twistingSheaf 𝒮 d)) (Y := (F, twistingSheaf 𝒮 k))
      (Z := (G, twistingSheaf 𝒮 k))
      (𝟙 F, twistScalarSheafMap 𝒮 i d k hk a) (φ, 𝟙 (twistingSheaf 𝒮 k))).symm.trans ?_
  refine Eq.trans ?_
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (_root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map_comp
        (X := (F, twistingSheaf 𝒮 d)) (Y := (G, twistingSheaf 𝒮 d))
        (Z := (G, twistingSheaf 𝒮 k))
        (φ, 𝟙 (twistingSheaf 𝒮 d)) (𝟙 G, twistScalarSheafMap 𝒮 i d k hk a))
  exact congrArg _ (Prod.ext ((Category.id_comp φ).trans (Category.comp_id φ).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The degreewise maps of twisted global sections `Γ(X, ℱ(d)) ⟶ Γ(X, 𝒢(d))` induced by
`φ : ℱ ⟶ 𝒢` commute with multiplication by a homogeneous scalar `a` of degree `i`. -/
theorem globalSections_map_homogeneousScalar
    {F G : SheafOfModules.{u} (projRingSheaf 𝒮)} (φ : F ⟶ G) (i : ℕ) (d : ℤ) (a : 𝒮 i)
    (z : twistedSectionsComponent 𝒮 F d) :
    ((((twistFunctor 𝒮 ((i : ℤ) + d)).map φ).val.app (op ⊤)).hom
        (homogeneousScalarTwistedSections 𝒮 F i d a z)) =
      homogeneousScalarTwistedSections 𝒮 G i d a
        ((((twistFunctor 𝒮 d).map φ).val.app (op ⊤)).hom z) := by
  have naturality := twistSheafScalarMap_comp_twistFunctor_map 𝒮 φ i d ((i : ℤ) + d) rfl a
  rw [← twistFunctor_map_eq, ← twistFunctor_map_eq] at naturality
  exact congrArg (fun morphism => (morphism.val.app (op ⊤)).hom z) naturality

end Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep

end
