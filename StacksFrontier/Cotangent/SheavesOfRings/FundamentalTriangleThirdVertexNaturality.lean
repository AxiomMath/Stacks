module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleNaturality

/-!
# Naturality in the base ring of the third-vertex identification of the fundamental triangle

Let `k : A₁ ⟶ A₂`, `g : A₂ ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings
on a site, with every `B(U) → D(U)` injective. The identification `coker ≅ L_{D/B}` of the third
vertex of the fundamental triangle of Tag 08SZ, `CategoryTheory.Sheaf.towerThirdVertexIso`, passes
through the comparison of Remark 08SE with the complexes `Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`, where
`R̄_•(U) = R_•(U) ⊗_{S_•(U)} B(U)` is built from the standard resolutions of `D(U)` and of `B(U)`
over `B(U)`. This file proves that the identification is compatible with change of base along
`k`: `CategoryTheory.Sheaf.TowerThirdVertexNatural`.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseRelativeBaseChangeBaseMap`: the map
  `R̄(A₁ ⟶ B ⟶ D) ⟶ R̄(A₂ ⟶ B ⟶ D)` of complexes `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` induced by `k`.
  The pushout `R̄_•(U)` only involves `B(U) → D(U)`, so this map is the identity in every degree
  and over every object.

## Main results

* `CategoryTheory.Sheaf.sectionwiseRelativeBaseChangeLeg_comp_baseMap` and
  `CategoryTheory.Sheaf.sectionwiseFundamentalCokernelMap_comp_baseMap`: the map of `R̄`-complexes
  commutes with the two comparison arrows `L_{D/B} ⟶ R̄ ⟵ coker` of Remark 08SE.
* `CategoryTheory.Sheaf.towerThirdVertexNatural`: **the third-vertex identification is natural in
  the base ring**, i.e. `TowerThirdVertexNatural J k g h hinj` holds.

## Implementation notes

The objects attached to the towers `A₁ ⟶ B ⟶ D` and `A₂ ⟶ B ⟶ D` are definitionally equal in
every component, but the definitional check at the level of whole complexes or whole maps of
complexes is expensive. So the map of `R̄`-complexes is built componentwise from identities, and
every compatibility is stated between morphisms with the same source and target. Universe
parameters are spelled out where `w` would otherwise be inferred only from `max u v w`.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory.Sheaf

universe t u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ B D : Sheaf J CommRingCat.{max u v w}} (k : A₁ ⟶ A₂) (g : A₂ ⟶ B) (h : B ⟶ D)

/-- **The map `R̄(A₁ ⟶ B ⟶ D) ⟶ R̄(A₂ ⟶ B ⟶ D)` of the complexes
`U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of Remark 08SE induced by `k`.** The pushout
`R̄_•(U) = R_•(U) ⊗_{S_•(U)} B(U)` only involves `B(U) → D(U)`, so the map is the identity over
every object and in every degree. -/
def sectionwiseRelativeBaseChangeBaseMap : sectionwiseRelativeBaseChangeComplex J (k ≫ g) h ⟶
    sectionwiseRelativeBaseChangeComplex J g h where
  f j :=
    { app U := 𝟙 ((relativeBaseChangeCotangentComplex J g h U).X j)
      naturality _ := rfl }
  comm' _ _ _ := rfl

/-- The comparison `L_{D/B} ⟶ R̄` of Remark 08SE of `A₁ ⟶ B ⟶ D`, followed by the map of
`R̄`-complexes induced by `k`, is the comparison of `A₂ ⟶ B ⟶ D`. -/
theorem sectionwiseRelativeBaseChangeLeg_comp_baseMap :
    sectionwiseRelativeBaseChangeLeg J (k ≫ g) h ≫ sectionwiseRelativeBaseChangeBaseMap J k g h =
      sectionwiseRelativeBaseChangeLeg J g h := by
  refine HomologicalComplex.hom_ext _ _ fun j => PresheafOfModules.Hom.ext (funext fun U => ?_)
  exact Category.comp_id _

/-- Over every object, the square of the change of base along `k` followed by the square of the
change of base ring along `A₂(U) → B(U)` is the square of the change of base ring along
`A₁(U) → B(U)`. -/
theorem sectionsBaseSquare_comp_baseRingSquareTop (U : Cᵒᵖ) :
    (sectionsBaseSquare J k g h U).comp
        (CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h U)) =
      CommAlgCat.baseRingSquareTop (sectionsTowerHom J (k ≫ g) h U) := by
  unfold sectionsBaseSquare CommAlgCat.baseRingSquareTop CommAlgCat.AlgebraSquare.comp
  rfl

/-- **Change of base along `k` commutes with the sectionwise second maps**: the map
`L^{sw}_{D/A₁} ⟶ L^{sw}_{D/A₂}` followed by `L^{sw}_{D/A₂} ⟶ L^{sw}_{D/B}` is
`L^{sw}_{D/A₁} ⟶ L^{sw}_{D/B}`. -/
theorem sectionwiseTowerBaseMap_comp_sectionwiseTowerChangeOfBaseMap :
    sectionwiseTowerBaseMap J k g h ≫ sectionwiseTowerChangeOfBaseMap J g h =
      sectionwiseTowerChangeOfBaseMap J (k ≫ g) h := by
  refine HomologicalComplex.hom_ext _ _ fun j => PresheafOfModules.Hom.ext (funext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact (CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _
    (sectionsBaseSquare_comp_baseRingSquareTop J k g h U).symm j x).symm

variable {k g h} in
/-- **The cokernel comparison of Remark 08SE commutes with change of base**: for any morphism `τ`
of the sectionwise short exact sequences whose middle map commutes with the sectionwise second
maps, the cokernel map of `A₁ ⟶ B ⟶ D` followed by the map of `R̄`-complexes is `τ₃` followed by
the cokernel map of `A₂ ⟶ B ⟶ D`. -/
theorem sectionwiseFundamentalCokernelMap_comp_baseMap
    (τ : sectionwiseFundamentalShortComplex.{u, v, w} J (k ≫ g) h ⟶
      sectionwiseFundamentalShortComplex.{u, v, w} J g h)
    (hτ : τ.τ₂ ≫ sectionwiseTowerChangeOfBaseMap.{u, v, w} J g h =
      sectionwiseTowerChangeOfBaseMap.{u, v, w} J (k ≫ g) h) :
    sectionwiseFundamentalCokernelMap.{u, v, w} J (k ≫ g) h ≫
        sectionwiseRelativeBaseChangeBaseMap.{u, v, w} J k g h =
      τ.τ₃ ≫ sectionwiseFundamentalCokernelMap.{u, v, w} J g h := by
  refine coequalizer.hom_ext ?_
  have e₁ := sectionwiseFundamentalShortComplex_g_comp_cokernelMap.{u, v, w} J (k ≫ g) h
  have e₃ := sectionwiseFundamentalShortComplex_g_comp_cokernelMap.{u, v, w} J g h
  have hl := sectionwiseRelativeBaseChangeLeg_comp_baseMap.{u, v, w} J k g h
  change (sectionwiseFundamentalShortComplex.{u, v, w} J (k ≫ g) h).g ≫ _ =
    (sectionwiseFundamentalShortComplex.{u, v, w} J (k ≫ g) h).g ≫ _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ sectionwiseRelativeBaseChangeBaseMap.{u, v, w} J k g h) e₁).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (sectionwiseTowerChangeOfBaseMap.{u, v, w} J (k ≫ g) h ≫ ·) hl).trans ?_
  refine (congrArg (· ≫ sectionwiseRelativeBaseChangeLeg.{u, v, w} J g h) hτ.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (τ.τ₂ ≫ ·) e₃.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ sectionwiseFundamentalCokernelMap.{u, v, w} J g h) τ.comm₂₃).trans ?_
  exact Category.assoc _ _ _

/-- An identification `X₁ ≅ R₁ ≅ L ≅ M` built from isomorphisms `c₁ : X₁ ⟶ R₁`, `l₁ : L ⟶ R₁` and
`e`, and the analogous `X₂ ≅ M`, are compatible with `t : X₁ ⟶ X₂` as soon as some
`φ : R₁ ⟶ R₂` commutes with the `cᵢ` and the `lᵢ`. -/
theorem asIso_trans_symm_trans_inv_comp {𝒟 : Type*} [Category 𝒟] {X₁ X₂ R₁ R₂ L M : 𝒟}
    (c₁ : X₁ ⟶ R₁) (c₂ : X₂ ⟶ R₂) (l₁ : L ⟶ R₁) (l₂ : L ⟶ R₂) [IsIso c₁] [IsIso c₂] [IsIso l₁]
    [IsIso l₂] (e : L ≅ M) (t : X₁ ⟶ X₂) (φ : R₁ ⟶ R₂) (hl : l₁ ≫ φ = l₂)
    (hc : c₁ ≫ φ = t ≫ c₂) :
    (asIso c₁ ≪≫ (asIso l₁).symm ≪≫ e).inv ≫ t = (asIso c₂ ≪≫ (asIso l₂).symm ≪≫ e).inv := by
  have ht : inv c₁ ≫ t = φ ≫ inv c₂ := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv, Category.assoc, ht]
  rw [← Category.assoc l₁, hl]

section Injective

variable (hinj : ∀ U, Function.Injective (h.hom.app U).hom)
  [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]

/-- **The identification of the third vertex of the fundamental triangle is natural in the base
ring**: `towerThirdVertexIso` of `A₁ ⟶ B ⟶ D` is that of `A₂ ⟶ B ⟶ D` composed with the sheafified
map of cokernels induced by `k`. -/
theorem towerThirdVertexNatural : TowerThirdVertexNatural.{t, u, v, w} J k g h hinj := by
  have := quasiIso_sheafify_sectionwiseFundamentalCokernelMap.{u, v, w} J (k ≫ g) h hinj
  have := quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg.{u, v, w} J (k ≫ g) h hinj
  have := quasiIso_sheafify_sectionwiseFundamentalCokernelMap.{u, v, w} J g h hinj
  have := quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg.{u, v, w} J g h hinj
  have hl := congrArg (fun φ => DerivedCategory.Q.map ((sheafifyTowerComplex J D).map φ))
    (sectionwiseRelativeBaseChangeLeg_comp_baseMap.{u, v, w} J k g h)
  have hc := congrArg (fun φ => DerivedCategory.Q.map ((sheafifyTowerComplex J D).map φ))
    (sectionwiseFundamentalCokernelMap_comp_baseMap.{u, v, w} J
      (sectionwiseFundamentalShortComplexBaseMap J k g h)
      (sectionwiseTowerBaseMap_comp_sectionwiseTowerChangeOfBaseMap.{u, v, w} J k g h))
  simp only [Functor.map_comp] at hl hc
  exact asIso_trans_symm_trans_inv_comp _ _ _ _ _ _ _ hl hc

end Injective

end CategoryTheory.Sheaf
