module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.RingTheory.MilnorPatching.DerivedGlueingMap

/-!
# Restricting the glueing map of Stacks 0DL7

The isomorphism step of Stacks 0DL7 (`AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso`) is
checked étale locally on the pushout `Y'`. For that the glueing map
`Rj_* M ⊕ Rf'_* K' ⟶ Rj_* Rf_* Li^* K'` (`MilnorPatching.glueingMap`) of a triple `(M, K', α)`,
restricted along an étale chart `W ⟶ Y'`, has to be the glueing map of the restricted triple, up
to the base change isomorphisms of the four direct images. This file proves that statement over
abstract categories: the restriction functors `Φ` and the base change maps `β` are arbitrary,
subject to the two conditions that make the identification work.

* The base change maps along `f` and `i` are compatible with the units (`hf`, `hi`): this is the
  defining property of a base change map as a mate, `CategoryTheory.unit_mateEquiv`.
* The base change maps along the four sides of the square are compatible with the
  identifications `c : Rf ⋙ Rj ≅ Ri ⋙ Rf'` and `c_W` of the two composite direct images (`hc`):
  the cube condition.

## Main results

* `Stacks.CategoryTheory.BaseChange.unit_comp_map`: the base change map of a square of adjunctions
  is compatible with the units through the comparison of the two composites; this is the
  hypothesis `hf` (and `hi`) below for the base change maps of
  `Stacks.CategoryTheory.BaseChange.map`, in particular for
  `AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`.
* `MilnorPatching.map_glueingMap_comp_baseChange`: `Φ` of the glueing map of `(M, K', α)`,
  followed by the base change isomorphisms, is the base change isomorphisms followed by the
  glueing map of `(Φ₁ M, Φ₂ K', α_W)`.

## What the instance at algebraic spaces consumes

For the glueing map `AlgebraicGeometry.Space.pushoutGlueingMapOfModels` and an étale chart
`h : W ⟶ Y'`, the base change maps are those of
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` for the four cartesian squares over
`h`, invertible by `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModuleBaseChangeMap`, and `hf`,
`hi` are `Stacks.CategoryTheory.BaseChange.unit_comp_map`. The cube condition `hc` is the
compatibility of the compositors of Stacks 0D6D
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) around the cube formed by the
square and its base change along `h`: it is
`AlgebraicGeometry.Space.smallEtaleDerivedPullback_cube`, through
`MilnorPatching.mate_cube`. The glueing map of `pushoutGlueingMapOfModels` is moreover read at
arbitrary models of the derived categories, through `StacksDraft.DerivedModel.modelEquiv`, so the
base change maps are transported along those equivalences:
`AlgebraicGeometry.Space.pushoutGlueingMap_restrict`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/DerivedPushoutGlueingCubeSpaces.lean`.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.BaseChange

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*} [Category* A] [Category* B]
  [Category* A'] [Category* B'] {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}

/-- **The base change map is compatible with the units.** `Lg` of the unit of `Lf ⊣ Rf`, followed
by the base change map, is the unit of `Lf' ⊣ Rf'` followed by `Rf'` of the comparison of the two
composites around the square. This is `CategoryTheory.unit_mateEquiv` for the mate defining the
base change map. -/
theorem unit_comp_map (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc) (M : A) :
    Lg.map (adjf.unit.app M) ≫ map adjf adjf' eg ef (Lf.obj M) =
      adjf'.unit.app (Lg.obj M) ≫ Rf'.map (eg.hom.app M ≫ ef.inv.app M) :=
  unit_mateEquiv adjf adjf' (pullbackComparison eg ef) M

end Stacks.CategoryTheory.BaseChange

namespace MilnorPatching

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ : Type*} [Category* 𝒟] [Category* 𝒟₁] [Category* 𝒟₂]
  [Category* 𝒟₀] [Category* 𝒲] [Category* 𝒲₁] [Category* 𝒲₂] [Category* 𝒲₀]
  [Preadditive 𝒟] [HasBinaryBiproducts 𝒟] [Preadditive 𝒲] [HasBinaryBiproducts 𝒲]
  {Rj : 𝒟₁ ⥤ 𝒟} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀} {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀}
  {Ri : 𝒟₀ ⥤ 𝒟₂}
  {RjW : 𝒲₁ ⥤ 𝒲} {Rf'W : 𝒲₂ ⥤ 𝒲} {LfW : 𝒲₁ ⥤ 𝒲₀} {RfW : 𝒲₀ ⥤ 𝒲₁} {LiW : 𝒲₂ ⥤ 𝒲₀}
  {RiW : 𝒲₀ ⥤ 𝒲₂}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀} [Φ.Additive]

/-- **The glueing map of Stacks 0DL7 commutes with restriction.** Let `Φ, Φ₁, Φ₂, Φ₀` be functors
from the four corners of the square to the four corners of a second one, `βj, βf', βf, βi` base
change maps for the four direct images, `δf : Φ₁ ⋙ LfW ⟶ Lf ⋙ Φ₀` and `γi : Li ⋙ Φ₀ ≅ Φ₂ ⋙ LiW`
comparisons of the inverse images such that `βf` and `βi` are their mates (`hf`, `hi`), and let
the base change maps be compatible with `c` and `c_W` (`hc`). Then `Φ` of the glueing map of
`(M, K', α)`, followed by `βj` and `RjW` of `βf` and of `γi`, is, on each of the two summands,
`βj` respectively `βf'` followed by the glueing map of `(Φ₁ M, Φ₂ K', δf ≫ Φ₀ α ≫ γi)`. -/
theorem map_glueingMap_comp_baseChange (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
    (c : Rf ⋙ Rj ≅ Ri ⋙ Rf') (adjFW : LfW ⊣ RfW) (adjIW : LiW ⊣ RiW)
    (cW : RfW ⋙ RjW ≅ RiW ⋙ Rf'W)
    (βj : Rj ⋙ Φ ⟶ Φ₁ ⋙ RjW) (βf' : Rf' ⋙ Φ ⟶ Φ₂ ⋙ Rf'W) (βf : Rf ⋙ Φ₁ ⟶ Φ₀ ⋙ RfW)
    (βi : Ri ⋙ Φ₂ ⟶ Φ₀ ⋙ RiW) (δf : Φ₁ ⋙ LfW ⟶ Lf ⋙ Φ₀) (γi : Li ⋙ Φ₀ ≅ Φ₂ ⋙ LiW)
    (hf : ∀ M, Φ₁.map (adjF.unit.app M) ≫ βf.app (Lf.obj M) =
      adjFW.unit.app (Φ₁.obj M) ≫ RfW.map (δf.app M))
    (hi : ∀ K, Φ₂.map (adjI.unit.app K) ≫ βi.app (Li.obj K) =
      adjIW.unit.app (Φ₂.obj K) ≫ RiW.map (γi.inv.app K))
    (hc : ∀ N, Φ.map (c.inv.app N) ≫ βj.app (Rf.obj N) ≫ RjW.map (βf.app N) =
      βf'.app (Ri.obj N) ≫ Rf'W.map (βi.app N) ≫ cW.inv.app (Φ₀.obj N))
    (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    (Φ.map biprod.inl ≫ Φ.map (glueingMap adjF adjI c M K' α) ≫ βj.app (Rf.obj (Li.obj K')) ≫
        RjW.map (βf.app (Li.obj K')) ≫ RjW.map (RfW.map (γi.hom.app K')) =
      βj.app M ≫ biprod.inl ≫ glueingMap adjFW adjIW cW (Φ₁.obj M) (Φ₂.obj K')
          (δf.app M ≫ Φ₀.map α ≫ γi.hom.app K')) ∧
    (Φ.map biprod.inr ≫ Φ.map (glueingMap adjF adjI c M K' α) ≫ βj.app (Rf.obj (Li.obj K')) ≫
        RjW.map (βf.app (Li.obj K')) ≫ RjW.map (RfW.map (γi.hom.app K')) =
      βf'.app K' ≫ biprod.inr ≫ glueingMap adjFW adjIW cW (Φ₁.obj M) (Φ₂.obj K')
          (δf.app M ≫ Φ₀.map α ≫ γi.hom.app K')) := by
  constructor
  · have h1 := βj.naturality (adjF.homEquiv M (Li.obj K') α)
    have h2 := βf.naturality α
    simp only [Functor.comp_map, Functor.comp_obj] at h1 h2
    rw [inl_glueingMap adjFW adjIW cW, ← Φ.map_comp_assoc, inl_glueingMap adjF adjI c,
      reassoc_of% h1, ← RjW.map_comp, ← RjW.map_comp, Adjunction.homEquiv_unit,
      Adjunction.homEquiv_unit, Φ₁.map_comp, Category.assoc, reassoc_of% h2, reassoc_of% hf,
      RfW.map_comp, RfW.map_comp]
  · have h1 := βf'.naturality (adjI.unit.app K')
    have h3 := cW.inv.naturality (γi.inv.app K')
    simp only [Functor.comp_map, Functor.comp_obj] at h1 h3
    rw [inr_glueingMap adjFW adjIW cW, ← Φ.map_comp_assoc, inr_glueingMap adjF adjI c,
      Φ.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_inj, Φ.map_comp, Category.assoc,
      reassoc_of% hc, reassoc_of% h1, ← Rf'W.map_comp_assoc, hi, Rf'W.map_comp, Category.assoc,
      reassoc_of% h3, ← RjW.map_comp, ← RfW.map_comp, Iso.inv_hom_id_app]
    simp

end MilnorPatching

end
