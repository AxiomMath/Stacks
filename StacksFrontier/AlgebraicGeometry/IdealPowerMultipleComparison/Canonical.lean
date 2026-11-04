module

public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Restriction

/-!
# The canonical map of [Stacks, Tag 01YB] for morphisms

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals given by its affine-local ideal data,
`U = X \ V(I)` the open complement of its support, and `G`, `F` sheaves of modules on `X` with
`G` quasi-coherent. This file constructs the canonical map

`colim_n Hom(I ^ n • G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

of [Stacks, Tag 01YB] and proves the equation that characterises it: on the class of a morphism
`φ : I ^ n • G ⟶ F` its value is the morphism `G|_U ⟶ F|_U` whose composite with the restriction
of the inclusion `I ^ n • G ⟶ G` is the restriction of `φ`.

That equation is the assertion [Stacks, Tag 01YB] labels *canonical restriction property for
morphisms*, with its `homsOverOpen` replaced by the map built here — and with three hypotheses
dropped: `X` is not assumed Noetherian, `G` is assumed only quasi-coherent rather than coherent,
and `F` carries no hypothesis at all.

**What remains for that tag is exactly the bijectivity of this map.** That is where the Noetherian
hypothesis and the substance of the source's proof (Artin–Rees, the ascending chain condition, and
the affine case) enter. Once it is proved, `homsOverOpen` is `Equiv.ofBijective` of this map and
the characterisation below *is* the labelled assertion. No tag is attached here: both labelled
assertions are about an equivalence, and this is a map not yet known to be one.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerComparison.restrictLeg`: the restriction to `U` of a
  morphism out of `I ^ n • G`, read as a morphism `G|_U ⟶ F|_U`.
* `Stacks.AlgebraicGeometry.IdealPowerComparison.restrictCocone`: these legs as a cocone on
  `n ↦ Hom(I ^ n • G, F)`.
* `Stacks.AlgebraicGeometry.IdealPowerComparison.canonicalHomsOverOpen`: the induced map out of
  the colimit.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerComparison.idealPowerSystem_map_succ` and
  `idealPowerHom_map_succ`: the successor transitions of the two systems, identified with the
  filtration inclusion and with precomposition by it.
* `Stacks.AlgebraicGeometry.IdealPowerComparison.canonicalHomsOverOpen_restrict`: the
  characterising equation.

## Implementation notes

Both naturality obligations are discharged at successor steps only, through
`CategoryTheory.NatTrans.ofSequence`. That matters: `CategoryTheory.Functor.OfSequence.map` on a
general `m ⟶ n` of `ℕ` is defined by recursion on the gap and is *not* definitionally the
composite, so `CategoryTheory.Functor.OfSequence.map_le_succ` is a lemma proved by induction
rather than a `rfl`; routing through `ofSequence` avoids needing that induction at all.

The cocone leg at `n` composes `(restrictFunctor U.ι).map φ` after the inverse of
`(restrictFunctor U.ι).map (I ^ n • G).ι`, which exists because that restricted inclusion is an
isomorphism (`isIso_restrictFunctor_map_ι`). The naturality square then collapses by
`idealPowerSystem_map_succ_comp_ι` and the cancellation of the two inverses.

At this pin a morphism of `Type u` is a structure wrapping a function rather than a function, so
the legs are wrapped with `TypeCat.ofHom` and the two equalities of morphisms go through
`CategoryTheory.ConcreteCategory.hom_ext` and `CategoryTheory.ConcreteCategory.congr_hom`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerHomColimit
open Stacks.LocalCohomology

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerComparison

variable {X : Scheme.{u}}

/-! ### The successor transitions of the two systems -/

/-- The successor transition of the inverse system `n ↦ I ^ n • M` is the inclusion of the
filtration. -/
theorem idealPowerSystem_map_succ (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (idealPowerSystem I M).map (homOfLE (n.le_add_right 1)).op =
      idealPowerMultipleMap I M (Nat.le_succ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The successor transition of `n ↦ I ^ n • M`, followed by the inclusion of `I ^ n • M` into
`M`, is the inclusion of `I ^ (n + 1) • M` into `M`. -/
theorem idealPowerSystem_map_succ_comp_ι (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (idealPowerSystem I M).map (homOfLE (n.le_add_right 1)).op ≫
        (idealPowerMultiple I n M).ι =
      (idealPowerMultiple I (n + 1) M).ι :=
  (congrArg (· ≫ (idealPowerMultiple I n M).ι)
    (idealPowerSystem_map_succ I M n)).trans (idealPowerMultipleMap_comp_ι I M (Nat.le_succ n))

/-- The successor transition of the direct system `n ↦ Hom(I ^ n • G, F)` is precomposition with
the inclusion of the filtration. -/
theorem idealPowerHom_map_succ (I : X.IdealSheafData) (G F : X.Modules) (n : ℕ) :
    (idealPowerHom I G F).map (homOfLE (n.le_add_right 1)) =
      TypeCat.ofHom (fun φ : (idealPowerSystem I G).obj (op n) ⟶ F ↦
        (idealPowerSystem I G).map (homOfLE (Nat.le_succ n)).op ≫ φ) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-! ### The cancellation, in an abstract category -/

/-- **The cancellation the cocone's naturality square needs, with no sheaf theory in it.** If a
functor `R` sends two morphisms `ι₁`, `ι₂` into `A` to isomorphisms and `t ≫ ι₁ = ι₂`, then
reading a morphism out of the source of `ι₂` through `inv (R.map ι₂)` agrees with reading its
factorisation through `t` out of the source of `ι₁`.

This is stated abstractly on purpose. `AlgebraicGeometry.Scheme.Modules` is a `def`, so a `rw`
with `CategoryTheory.Functor.map_comp` or with `CategoryTheory.IsIso.eq_comp_inv` on a goal in it
fails with "did not find an occurrence of the pattern" on a pattern that is present — the
reported cause being that the target is not type-correct at `implicit` transparency. Here there
is no such instance to unfold and every rewrite goes through. -/
theorem inv_map_comp_eq {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {P Q A E : C} (ι₁ : P ⟶ A) (ι₂ : Q ⟶ A) (t : Q ⟶ P) (ψ : P ⟶ E)
    [IsIso (R.map ι₁)] [IsIso (R.map ι₂)] (h : t ≫ ι₁ = ι₂) :
    inv (R.map ι₂) ≫ R.map (t ≫ ψ) = inv (R.map ι₁) ≫ R.map ψ := by
  have h2 : R.map t ≫ R.map ι₁ = R.map ι₂ := by rw [← R.map_comp, h]
  rw [R.map_comp, IsIso.inv_comp_eq, ← h2, Category.assoc, IsIso.hom_inv_id_assoc]

/-! ### The canonical map -/

variable (I : X.IdealSheafData) (G F : X.Modules) [G.IsQuasicoherent]

/-- The restriction to `U = X \ V(I)` of a morphism `φ : I ^ n • G ⟶ F`, read as a morphism
`G|_U ⟶ F|_U` through the inverse of the restricted inclusion `I ^ n • G ⟶ G`. -/
def restrictLeg (n : ℕ) (φ : (idealPowerMultiple I n G).toSheafOfModules ⟶ F) :
    G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι :=
  inv ((Scheme.Modules.restrictFunctor (idealComplement I).ι).map
      (idealPowerMultiple I n G).ι) ≫
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ

/-- The leg at `n` is characterised by restriction. -/
theorem restrictFunctor_map_ι_comp_restrictLeg (n : ℕ)
    (φ : (idealPowerMultiple I n G).toSheafOfModules ⟶ F) :
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
          (idealPowerMultiple I n G).ι ≫
        restrictLeg I G F n φ =
      (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ := by
  rw [restrictLeg, IsIso.hom_inv_id_assoc]

/-- The legs are compatible with the transition of the direct system. -/
theorem restrictLeg_succ (n : ℕ)
    (φ : (idealPowerMultiple I n G).toSheafOfModules ⟶ F) :
    restrictLeg I G F (n + 1)
        ((idealPowerSystem I G).map (homOfLE (n.le_add_right 1)).op ≫ φ) =
      restrictLeg I G F n φ :=
  inv_map_comp_eq (Scheme.Modules.restrictFunctor (idealComplement I).ι)
    (idealPowerMultiple I n G).ι (idealPowerMultiple I (n + 1) G).ι
    ((idealPowerSystem I G).map (homOfLE (n.le_add_right 1)).op) φ
    (idealPowerSystem_map_succ_comp_ι I G n)

/-- The cocone on `n ↦ Hom(I ^ n • G, F)` with vertex `Hom_{𝒪_U}(G|_U, F|_U)`. -/
def restrictCocone : Cocone (idealPowerHom I G F) where
  pt := G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι
  ι := NatTrans.ofSequence (fun n ↦ TypeCat.ofHom (restrictLeg I G F n))
    (fun n ↦ ConcreteCategory.hom_ext _ _ fun φ ↦ by
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, idealPowerHom_map_succ]
      exact restrictLeg_succ I G F n φ)

/-- **The canonical map `colim_n Hom(I ^ n • G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)` of
[Stacks, Tag 01YB].** -/
def canonicalHomsOverOpen :
    colimit (idealPowerHom I G F) ⟶
      (G.restrict (idealComplement I).ι ⟶ F.restrict (idealComplement I).ι) :=
  colimit.desc _ (restrictCocone I G F)

/-- The value of the canonical map on the class of a representative is that representative's
leg. -/
theorem canonicalHomsOverOpen_colimit_ι (n : ℕ)
    (φ : (idealPowerMultiple I n G).toSheafOfModules ⟶ F) :
    canonicalHomsOverOpen I G F (colimit.ι (idealPowerHom I G F) n φ) =
      restrictLeg I G F n φ :=
  (CategoryTheory.comp_apply (C := Type u) (colimit.ι (idealPowerHom I G F) n)
        (colimit.desc (idealPowerHom I G F) (restrictCocone I G F)) φ).symm.trans
    (ConcreteCategory.congr_hom (colimit.ι_desc (restrictCocone I G F) n) φ)

/-- **The canonical map is characterised by restriction.** Precomposing its value on the class of
`φ : I ^ n • G ⟶ F` with the restriction of the inclusion `I ^ n • G ⟶ G` gives the restriction
of `φ`. This is the equation [Stacks, Tag 01YB] states about its `homsOverOpen`, here for the map
constructed above and with neither the Noetherian nor the coherence hypothesis. -/
theorem canonicalHomsOverOpen_restrict (n : ℕ)
    (φ : (idealPowerMultiple I n G).toSheafOfModules ⟶ F) :
    (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
          (idealPowerMultiple I n G).ι ≫
        canonicalHomsOverOpen I G F (colimit.ι (idealPowerHom I G F) n φ) =
      (Scheme.Modules.restrictFunctor (idealComplement I).ι).map φ :=
  (congrArg (fun m ↦ (Scheme.Modules.restrictFunctor (idealComplement I).ι).map
        (idealPowerMultiple I n G).ι ≫ m)
      (canonicalHomsOverOpen_colimit_ι I G F n φ)).trans
    (restrictFunctor_map_ι_comp_restrictLeg I G F n φ)

end Stacks.AlgebraicGeometry.IdealPowerComparison

end
