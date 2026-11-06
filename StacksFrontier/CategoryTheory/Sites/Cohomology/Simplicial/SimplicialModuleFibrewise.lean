module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreInclusion
import StacksCore.Tactic.StacksAttribute

/-!
# A sheaf of `π^{-1}O`-modules on `Δ × C` is a simplicial sheaf of `O`-modules

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it, let `π : Δ × C ⥤ C` be the
projection of Stacks 09D0 and let `Δ × C` carry the topology inherited from `(C, J)` along `π`.
Stacks 09D1 reads a simplicial module over the constant simplicial sheaf of rings `O` as a sheaf
of modules over `π^{-1}O` on `Δ × C`. This file proves that reading, in the direction the
computation of `Lπ_!` needs: the functor

`fibrewiseMod : Mod(π^{-1}O) ⥤ Δᵒᵖ ⥤ Mod(O)`

that restricts a sheaf of `π^{-1}O`-modules to the fibres `{n} × C`, and the identification of
the module lower shriek `π_!` with the colimit over `Δᵒᵖ` of that simplicial module.

This is the module-coefficient sibling of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSheafEquivalence.lean`, whose
`Stacks.SimplicialModules.fibrewise` is defined for coefficients of the form `Sheaf J A` and
therefore does not apply to sheaves of modules.

## Why no base change appears

Restriction along the fibre inclusion `i_n : C ⥤ Δ × C` carries a `π^{-1}O`-module to an
honest `O`-module with no extension or restriction of scalars, because `i_n ⋙ π = 𝟭 C`
(`Stacks.SimplicialModules.fibreInclusion_comp_projection`) and so

`i_n^{-1}(π^{-1}O) = O`

*on the nose* — `Stacks.SimplicialModules.fibreRingMap` is the identity. Each level of
`fibrewiseMod` is therefore Mathlib's `SheafOfModules.pushforward` along `i_n` for the identity
morphism of sheaves of rings, and the simplicial structure maps are Mathlib's
`SheafOfModules.pushforwardNatTrans` applied to the natural transformations
`i_n ⟶ i_m` of `CategoryTheory.Functor.prodSectionSndFunctor`.

## Main definitions

* `CategoryTheory.Functor.prodSectionSndFunctor`: the coordinate sections `U ↦ (d, U)` of the
  second projection of a product category, assembled into a functor `D ⥤ (C ⥤ D × C)`.
* `Stacks.SimplicialModules.fibreRestrictionMod`: restriction of sheaves of modules along the
  fibre inclusion `i_n`, that is **evaluation in degree `n`**.
* `Stacks.SimplicialModules.fibrewiseMod`: a sheaf of `π^{-1}O`-modules read as a simplicial
  sheaf of `O`-modules.

## Main results

* `Stacks.SimplicialModules.fibrewiseMod_comp_evaluation`: the degree `n` of the simplicial
  module is restriction along `i_n`, on the nose.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₃ u₃ v₄ u₄

variable {D : Type u₃} [Category.{v₃} D] {C : Type u₄} [Category.{v₄} C]

/-- The coordinate sections `U ↦ (d, U)` of the second projection of a product category,
assembled into a functor `D ⥤ (C ⥤ D × C)`: a morphism `f : d ⟶ d'` goes to the natural
transformation with components `(f, 𝟙 U)`. -/
@[simps]
def Functor.prodSectionSndFunctor : D ⥤ (C ⥤ D × C) where
  obj d := Functor.prodSectionSnd d
  map f :=
    { app := fun U => (f, 𝟙 U)
      naturality := fun _ _ g => Prod.ext
        ((Category.id_comp f).trans (Category.comp_id f).symm)
        ((Category.comp_id g).trans (Category.id_comp g).symm) }
  map_id _ := NatTrans.ext (funext fun _ => rfl)
  map_comp _ _ := NatTrans.ext (funext fun U => Prod.ext rfl (Category.comp_id (𝟙 U)).symm)

end CategoryTheory

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})

/-- The natural transformation of fibre inclusions `i_n ⟶ i_m`, with components `(α, 𝟙 U)`,
attached to a morphism `α : n ⟶ m` of `Δ`. -/
abbrev fibreInclusionMap {m n : SimplexCategory} (α : n ⟶ m) :
    fibreInclusion C n ⟶ fibreInclusion C m :=
  (Functor.prodSectionSndFunctor (D := SimplexCategory) (C := C)).map α

/-- **`i_n^{-1}(π^{-1}O) = O`, and the identity is the identification.** The fibre inclusion
followed by the projection is the identity functor, so restricting `π^{-1}O` along `i_n` gives
back `O` with no base change at all; this records the identity morphism of sheaves of rings in
the shape that `SheafOfModules.pushforward` asks for. -/
abbrev fibreRingMap (n : SimplexCategory) :
    O ⟶ ((fibreInclusion C n).sheafPushforwardContinuous RingCat.{w} J
      (projectionTopology C J)).obj (projectionRing C J O) :=
  𝟙 O

/-- **Evaluation in degree `n`.** Restriction of sheaves of modules along the fibre inclusion
`i_n : C ⥤ Δ × C`: a sheaf of `π^{-1}O`-modules on `Δ × C` restricted to the fibre `{n} × C`,
where it is a sheaf of `O`-modules by `Stacks.SimplicialModules.fibreRingMap`. -/
abbrev fibreRestrictionMod (n : SimplexCategory) :
    SheafOfModules.{w} (projectionRing C J O) ⥤ SheafOfModules.{w} O :=
  SheafOfModules.pushforward.{w} (F := fibreInclusion C n) (fibreRingMap C J O n)

/-- The identification `i_n^{-1}(π^{-1}O) = O` is compatible with the natural transformations
`i_n ⟶ i_m` coming from `Δ`: the comparison is restriction of `π^{-1}O` along `(α, 𝟙)`, which is
restriction of `O` along an identity. -/
theorem fibreRingMap_comp {m n : SimplexCategory} (α : n ⟶ m) :
    fibreRingMap C J O m ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (fibreInclusionMap C α) RingCat.{w} J
          (projectionTopology C J)).app (projectionRing C J O) =
      fibreRingMap C J O n :=
  Sheaf.hom_ext (NatTrans.ext (funext fun X => O.obj.map_id X))

/-- **The structure map of the fibrewise reading** at `α : m ⟶ n` in `Δᵒᵖ`: Mathlib's
`SheafOfModules.pushforwardNatTrans` applied to the natural transformation `i_{n} ⟶ i_{m}` of
fibre inclusions, corrected by `Stacks.SimplicialModules.fibreRingMap_comp`. -/
def fibrewiseModMap {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    fibreRestrictionMod C J O m.unop ⟶ fibreRestrictionMod C J O n.unop :=
  SheafOfModules.pushforwardNatTrans (fibreRingMap C J O m.unop)
      (fibreInclusionMap C α.unop) ≫
    (SheafOfModules.pushforwardCongr (fibreRingMap_comp C J O α.unop)).hom

/-- On sections, the structure map is restriction of `M` along `(α, 𝟙)` — nothing is done to the
module structure, both sides being modules over the same ring `O(U)`. -/
theorem fibrewiseModMap_val_app {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (M : SheafOfModules.{w} (projectionRing C J O)) (U : Cᵒᵖ)
    (x : ((fibreRestrictionMod C J O m.unop).obj M).val.obj U) :
    ((fibrewiseModMap C J O α).app M).val.app U x =
      M.val.presheaf.map ((fibreInclusionMap C α.unop).app U.unop).op x :=
  rfl

/-- The restrictions of `M` along `(α, 𝟙)` compose, which is the functoriality of the fibrewise
reading in the simplex. -/
theorem fibreInclusionMap_app_op_comp {m n p : SimplexCategoryᵒᵖ} (α : m ⟶ n) (β : n ⟶ p)
    (U : Cᵒᵖ) :
    ((fibreInclusionMap C (α ≫ β).unop).app U.unop).op =
      ((fibreInclusionMap C α.unop).app U.unop).op ≫
        ((fibreInclusionMap C β.unop).app U.unop).op := by
  rw [← op_comp]
  exact congrArg Quiver.Hom.op (Prod.ext rfl (Category.comp_id (𝟙 U.unop)).symm)

/-- **The simplicial structure of the fibrewise reading**: degree `n` is restriction along the
fibre inclusion `i_n`, and the structure maps are
`Stacks.SimplicialModules.fibrewiseModMap`. -/
def fibrewiseModFunctor :
    SimplexCategoryᵒᵖ ⥤
      (SheafOfModules.{w} (projectionRing C J O) ⥤ SheafOfModules.{w} O) where
  obj n := fibreRestrictionMod C J O n.unop
  map α := fibrewiseModMap C J O α
  map_id n := by
    ext M U x
    refine (fibrewiseModMap_val_app C J O (𝟙 n) M U x).trans ?_
    rw [show ((fibreInclusionMap C (𝟙 n).unop).app U.unop).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp {m n p} α β := by
    ext M U x
    refine (fibrewiseModMap_val_app C J O (α ≫ β) M U x).trans ?_
    rw [fibreInclusionMap_app_op_comp C α β U, CategoryTheory.Functor.map_comp]
    rfl

/-- **A sheaf of `π^{-1}O`-modules on `Δ × C` read as a simplicial sheaf of `O`-modules**, by
restricting to the fibres `{n} × C`. This is the module-coefficient form of
`Stacks.SimplicialModules.fibrewise`, and is the functor in which the module-coefficient
computation of `Lπ_!` of Stacks 09D0 is stated. -/
def fibrewiseMod :
    SheafOfModules.{w} (projectionRing C J O) ⥤
      CategoryTheory.SimplicialObject (SheafOfModules.{w} O) :=
  (fibrewiseModFunctor C J O).flip

/-- Degree `n` of the simplicial module is restriction along the fibre inclusion `i_n`, on the
nose. -/
theorem fibrewiseMod_comp_evaluation (n : SimplexCategoryᵒᵖ) :
    fibrewiseMod C J O ⋙ (evaluation _ _).obj n = fibreRestrictionMod C J O n.unop :=
  rfl

end Stacks.SimplicialModules

end
