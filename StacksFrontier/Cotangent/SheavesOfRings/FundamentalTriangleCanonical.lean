module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral

/-!
# The connecting morphism of the fundamental triangle, as a definition

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. The distinguished
triangle of Tag 08SZ,

`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`,

is recorded in `StacksFrontier/Cotangent/SheavesOfRings/FundamentalTriangleGeneral.lean` as an
existence statement, `CategoryTheory.Sheaf.exists_distTriang_towerCotangent`: its connecting
morphism is produced inside a proof. A connecting morphism obtained by choice from that statement
can be compared with nothing, so it cannot be shown to depend naturally on the tower. This file
names the connecting morphism the proof constructs, and proves the triangle on it distinguished.

## Main definitions

* `CategoryTheory.Sheaf.towerConnectingOfInjective`: when every `B(U) → D(U)` is injective, the
  connecting morphism of the sheafified sectionwise short exact sequence of Tag 08SD, read through
  the identifications of Tag 08SE and Tag 08SX.
* `CategoryTheory.Sheaf.towerConnecting`: in general, the image of the connecting morphism of the
  tower `A ⟶ B ⟶ B × D` under the second summand functor `Mod(B × D) ⥤ Mod(D)`.

## Main results

* `CategoryTheory.Sheaf.towerConnectingOfInjective_distinguished` and
  `CategoryTheory.Sheaf.towerConnecting_distinguished`: **Tag 08SZ** with the named connecting
  morphism.

## Implementation notes

The constructions are those of the proofs of `exists_distTriang_towerCotangent_of_injective` and
`exists_distTriang_towerCotangent`, which are reproduced here with the connecting morphism held in
a definition. As there, the triangle of the tower `A ⟶ B ⟶ B × D` is formed in the standard model
of the derived category of `B × D`-modules (`HasDerivedCategory.standard`), an auxiliary category
that does not appear in the statements.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Sheaf

universe t u v w

/-- **A triangle with vertices identified with those of a distinguished triangle.** If `T` is
distinguished and `dᵢ : T.objᵢ ≅ Xᵢ` carry `T.mor₁`, `T.mor₂` to `α`, `β`, then `α`, `β` and
`d₃⁻¹ ≫ T.mor₃ ≫ d₁⟦1⟧` form a distinguished triangle. -/
theorem distinguished_mk_of_isoVertices {𝒯 : Type*} [Category 𝒯] [Preadditive 𝒯] [HasZeroObject 𝒯]
    [HasShift 𝒯 ℤ] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
    {X Y Z : 𝒯} (T : Triangle 𝒯) (hT : T ∈ distTriang 𝒯)
    (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) (α : X ⟶ Y) (β : Y ⟶ Z)
    (hα : T.mor₁ = d₁.hom ≫ α ≫ d₂.inv) (hβ : T.mor₂ = d₂.hom ≫ β ≫ d₃.inv) :
    Triangle.mk α β (d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧') ∈ distTriang 𝒯 :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ d₁.symm d₂.symm d₃.symm (by simp [hα]) (by simp [hβ]) (by simp))

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-! ### Towers whose second map is injective on sections -/

section Injective

variable (hinj : ∀ U, Function.Injective (h.hom.app U).hom)
  [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]

/-- The identification of the cokernel of the sheafified sectionwise first map with `L_{D/B}`:
the cokernel map and the comparison of Tag 08SE are quasi-isomorphisms, and Tag 08SX identifies
the sheafified sectionwise cotangent complex with `L_{D/B}`. -/
def towerThirdVertexIso :
    DerivedCategory.Q.obj ((sheafifyTowerComplex J D).obj
        (sectionwiseFundamentalShortComplex J g h).X₃) ≅
      DerivedCategory.Q.obj (cotangentComplex J h) :=
  haveI := quasiIso_sheafify_sectionwiseFundamentalCokernelMap J g h hinj
  haveI := quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg J g h hinj
  asIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalCokernelMap J g h))) ≪≫
    (asIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseRelativeBaseChangeLeg J g h)))).symm ≪≫
    DerivedCategory.Q.mapIso (sheafifiedSectionwiseCotangentModuleComplexIso J h)

/-- **The connecting morphism of the fundamental triangle of a tower `A ⟶ B ⟶ D` with every
`B(U) → D(U)` injective**: the connecting morphism of the sheafified sectionwise short exact
sequence `0 → L_{B/A} ⊗ D → L_{D/A} → Q → 0` of Tag 08SD, with `Q` identified with `L_{D/B}`
by `towerThirdVertexIso` and the first term with `L_{B/A} ⊗_B D` by Tag 08SX. -/
def towerConnectingOfInjective :
    cotangentComplexDerived.{u, v, w, t} J h ⟶
      (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))⟦(1 : ℤ)⟧ :=
  (towerThirdVertexIso J g h hinj).inv ≫
    (DerivedCategory.triangleOfSES
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj)).mor₃ ≫
    (DerivedCategory.Q.mapIso
      (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h)).hom⟦(1 : ℤ)⟧'

/-- **Tag 08SZ for a tower whose second map is injective on sections, on the named connecting
morphism `towerConnectingOfInjective`.** -/
theorem towerConnectingOfInjective_distinguished :
    Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h))
        (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h))
        (towerConnectingOfInjective J g h hinj) ∈
      distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
  have h₁ := sheafification_map_sectionwiseTowerBaseChangeComplexMap J g h
  have h₂ := sheafification_map_sectionwiseTowerChangeOfBaseMap J g h
  have := quasiIso_sheafify_sectionwiseFundamentalCokernelMap J g h hinj
  have := quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg J g h hinj
  refine distinguished_mk_of_isoVertices _ (DerivedCategory.triangleOfSES_distinguished
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj))
    (DerivedCategory.Q.mapIso (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h))
    (DerivedCategory.Q.mapIso (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)))
    (towerThirdVertexIso J g h hinj) _ _ ?_ ?_
  · change DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseTowerBaseChangeComplexMap J g h)) = _
    rw [h₁, Functor.map_comp, Functor.map_comp]
    rfl
  · change DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalShortComplex J g h).g) = _
    have hπ : (sheafifyTowerComplex J D).map (sectionwiseFundamentalShortComplex J g h).g ≫
          (sheafifyTowerComplex J D).map (sectionwiseFundamentalCokernelMap J g h) =
        (sheafifyTowerComplex J D).map (sectionwiseTowerChangeOfBaseMap J g h) ≫
          (sheafifyTowerComplex J D).map (sectionwiseRelativeBaseChangeLeg J g h) :=
      ((sheafifyTowerComplex J D).map_comp _ _).symm.trans
        ((congrArg (sheafifyTowerComplex J D).map
          (sectionwiseFundamentalShortComplex_g_comp_cokernelMap J g h)).trans
            ((sheafifyTowerComplex J D).map_comp _ _))
    have : IsIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalCokernelMap J g h))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (quasiIso_sheafify_sectionwiseFundamentalCokernelMap J g h hinj)
    have : Mono (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalCokernelMap J g h))) := IsIso.mono_of_iso _
    refine (cancel_mono (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalCokernelMap J g h)))).1 ?_
    refine ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map hπ).trans
      ((DerivedCategory.Q.map_comp _ _).trans (congrArg (fun z => DerivedCategory.Q.map z ≫
        DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
          (sectionwiseRelativeBaseChangeLeg J g h))) h₂)))).trans ?_
    have key : (towerThirdVertexIso J g h hinj).inv ≫ DerivedCategory.Q.map
        ((sheafifyTowerComplex J D).map (sectionwiseFundamentalCokernelMap J g h)) =
        DerivedCategory.Q.map (sheafifiedSectionwiseCotangentModuleComplexIso J h).inv ≫
          DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
            (sectionwiseRelativeBaseChangeLeg J g h)) := by
      simp only [towerThirdVertexIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv,
        Functor.mapIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (congrArg (fun z => z ≫ DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseRelativeBaseChangeLeg J g h)))
      ((DerivedCategory.Q.map_comp _ _).trans (congrArg (fun z => DerivedCategory.Q.map
        (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom ≫ z)
          (DerivedCategory.Q.map_comp _ _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun z => DerivedCategory.Q.map
        (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom ≫ z)
          ((Category.assoc _ _ _).trans ((congrArg (fun z =>
            DerivedCategory.Q.map (towerCotangentChangeOfBase J g h) ≫ z) key.symm).trans
              (Category.assoc _ _ _).symm))).trans (Category.assoc _ _ _).symm))

end Injective

/-! ### Arbitrary towers -/

section General

variable [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]

/-- The identification of the second summand of the first vertex of the triangle of
`A ⟶ B ⟶ B × D` with `L_{B/A} ⊗_B D`, in the standard model of `D(B × D)`. -/
def towerProdFirstVertexIso :
    letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g (prodGraph J h))) ≅
      DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h) :=
  letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategoryFactors.app
      (baseChangedCotangentComplex.{u, v, w} J g (prodGraph J h)) ≪≫
    DerivedCategory.Q.mapIso (prodGraphBaseChangedIso J g h)

/-- The identification of the second summand of the second vertex of the triangle of
`A ⟶ B ⟶ B × D` with `L_{D/A}`, by the second component of Tag 08SY. -/
def towerProdSecondVertexIso :
    letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J (g ≫ prodGraph J h))) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J (g ≫ h)) :=
  letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  haveI := quasiIso_prodSndCotangentComparison J (g ≫ prodGraph J h) g (g ≫ h)
    (prod.hom_ext (by rw [Category.assoc, prodRingHom_fst, prodRingHom_fst, Category.comp_id])
      (by rw [Category.assoc, prodRingHom_snd, prodRingHom_snd])) (prodGraph_square_base J g h)
  (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategoryFactors.app
      (cotangentComplex.{u, v, w} J (g ≫ prodGraph J h)) ≪≫
    asIso (DerivedCategory.Q.map (prodSndCotangentComparison.{u, v, w} J (g ≫ prodGraph J h)
      (g ≫ h) (prodGraph_square_base J g h)))

/-- The identification of the second summand of the third vertex of the triangle of
`A ⟶ B ⟶ B × D` with `L_{D/B}`, by the second component of Tag 08SY. -/
def towerProdThirdVertexIso :
    letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
    (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J (prodGraph J h))) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J h) :=
  letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  haveI := quasiIso_prodSndCotangentComparison J (prodGraph J h) (𝟙 B) h rfl
    (prodGraph_square_top J h)
  (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategoryFactors.app
      (cotangentComplex.{u, v, w} J (prodGraph J h)) ≪≫
    asIso (DerivedCategory.Q.map (prodSndCotangentComparison.{u, v, w} J (prodGraph J h) h
      (prodGraph_square_top J h)))

/-- **The connecting morphism of the fundamental triangle of Tag 08SZ**,
`L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`, for an arbitrary tower `A ⟶ B ⟶ D`: the connecting morphism
`towerConnectingOfInjective` of the tower `A ⟶ B ⟶ B × D`, whose second map `b ↦ (b, h b)` is
injective on sections, carried to `D(D)` by the exact second summand functor and read through
`towerProdFirstVertexIso` and `towerProdThirdVertexIso`. -/
def towerConnecting :
    cotangentComplexDerived.{u, v, w, t} J h ⟶
      (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))⟦(1 : ℤ)⟧ :=
  letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  (towerProdThirdVertexIso J h).inv ≫
    ((prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory.mapTriangle.obj
      (Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
          (prodGraph J h))) (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
            (prodGraph J h)))
        (towerConnectingOfInjective J g (prodGraph J h) (injective_prodGraph J h)))).mor₃ ≫
    (towerProdFirstVertexIso J g h).hom⟦(1 : ℤ)⟧'

/-- **Tag 08SZ on the named connecting morphism**: the triangle
`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]` with the canonical first two arrows and
third arrow `towerConnecting` is distinguished in `D(D)`. -/
theorem towerConnecting_distinguished :
    Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h))
        (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h))
        (towerConnecting J g h) ∈
      distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
  let := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  let E := prodSndSummand.{u, v, w} J (B := B) (D := D)
  let Φ := E.mapDerivedCategory
  let T' := Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
    (prodGraph J h))) (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
      (prodGraph J h))) (towerConnectingOfInjective J g (prodGraph J h) (injective_prodGraph J h))
  have hΦ := Φ.map_distinguished _
    (towerConnectingOfInjective_distinguished J g (prodGraph J h) (injective_prodGraph J h))
  let i₁ := towerProdFirstVertexIso J g h
  let i₂ := towerProdSecondVertexIso J g h
  let i₃ := towerProdThirdVertexIso J h
  have c₁ : Φ.map (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
        (prodGraph J h))) ≫ i₂.hom =
      i₁.hom ≫ DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h) := by
    dsimp only [i₁, i₂, towerProdFirstVertexIso, towerProdSecondVertexIso, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, asIso_hom]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp,
      prodSndCotangentComparison_baseChange, Functor.map_comp, Category.assoc]
  have c₂ : Φ.map (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
        (prodGraph J h))) ≫ i₃.hom =
      i₂.hom ≫ DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h) := by
    dsimp only [i₂, i₃, towerProdSecondVertexIso, towerProdThirdVertexIso, Iso.trans_hom,
      Iso.app_hom, asIso_hom]
    rw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp,
      prodSndCotangentComparison_changeOfBase, Functor.map_comp, Category.assoc]
  refine isomorphic_distinguished _ hΦ _ (Triangle.isoMk _ _ i₁.symm i₂.symm i₃.symm ?_ ?_ ?_)
  · change DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h) ≫ i₂.inv =
      i₁.inv ≫ Φ.map (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g
        (prodGraph J h)))
    rw [← cancel_epi i₁.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← c₁, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · change DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h) ≫ i₃.inv =
      i₂.inv ≫ Φ.map (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g
        (prodGraph J h)))
    rw [← cancel_epi i₂.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← c₂, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · change (i₃.inv ≫ (Φ.mapTriangle.obj T').mor₃ ≫ i₁.hom⟦(1 : ℤ)⟧') ≫ i₁.inv⟦(1 : ℤ)⟧' =
      i₃.inv ≫ (Φ.mapTriangle.obj T').mor₃
    refine (Category.assoc _ _ _).trans (congrArg (fun k => i₃.inv ≫ k) ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => (Φ.mapTriangle.obj T').mor₃ ≫ k)
      ((shiftFunctor _ (1 : ℤ)).map_comp i₁.hom i₁.inv).symm).trans ?_
    rw [Iso.hom_inv_id, Functor.map_id]
    exact Category.comp_id _

end General

end CategoryTheory.Sheaf

end
