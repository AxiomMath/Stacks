module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleCanonical

/-!
# Naturality of the connecting morphism of the fundamental triangle in the base ring

Let `k : A₁ ⟶ A₂`, `g : A₂ ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings
on a site, and compare the towers `A₁ ⟶ B ⟶ D` (first map `k ≫ g`) and `A₂ ⟶ B ⟶ D`. Change of
base along `k` maps the sectionwise short exact sequence
`0 → L^{sw}_{B/A} ⊗ D → L^{sw}_{D/A} → coker → 0` of the first tower to that of the second, and the
connecting morphism `CategoryTheory.Sheaf.towerConnecting` of Tag 08SZ is built from that
sequence. This file proves that the connecting morphisms are compatible with the induced map of
first vertices `L_{B/A₁} ⊗_B D ⟶ L_{B/A₂} ⊗_B D`.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseFundamentalShortComplexBaseMap`: the morphism of sectionwise
  short exact sequences induced by `k`.
* `CategoryTheory.Sheaf.baseChangedCotangentBaseMap`: the map
  `L_{B/A₁} ⊗_B D ⟶ L_{B/A₂} ⊗_B D` of first vertices, read through Tag 08SX.

## Main results

* `CategoryTheory.Sheaf.towerConnectingOfInjective_naturality`: for a tower whose second map is
  injective on sections, the connecting morphisms are compatible with the map of first vertices,
  given the compatibility of the identifications of the third vertices
  (`CategoryTheory.Sheaf.TowerThirdVertexNatural`).
* `CategoryTheory.Sheaf.towerConnecting_naturality`: the same for an arbitrary tower, given in
  addition the compatibility of the first-vertex identifications of the product-graph reduction
  (`CategoryTheory.Sheaf.TowerProdFirstVertexNatural`).

## Implementation notes

The two compatibilities that are arguments of the main results are statements about the
identifications of Tag 08SE and of the reduction to an injective second map, and are stated as
named propositions so that they can be proved separately. Nothing about the cotangent complex is
assumed: they are equalities between explicit morphisms of the derived category.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Sheaf

universe t u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ B D : Sheaf J CommRingCat.{max u v w}} (k : A₁ ⟶ A₂) (g : A₂ ⟶ B) (h : B ⟶ D)

/-! ### The sectionwise short exact sequences -/

/-- The change of base `L^{sw}_{B/A₁} ⊗ D ⟶ L^{sw}_{B/A₂} ⊗ D` along `k`, on the sectionwise first
vertices. -/
abbrev sectionwiseBaseChangedBaseMap :
    sectionwiseBaseChangedCotangentComplex J (k ≫ g) h ⟶
      sectionwiseBaseChangedCotangentComplex J g h :=
  ((towerChangeOfRings J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (sectionwiseTowerChangeOfBaseMap J k g)

/-- The square `(A₁(U) → D(U)) ⟶ (A₂(U) → D(U))` of the change of base along `k`: base `k_U`,
the identity of `D(U)` on top. -/
def sectionsBaseSquare (U : Cᵒᵖ) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w} (A₁.obj.obj U) (A₂.obj.obj U)
      (sectionsAlgebra J ((k ≫ g) ≫ h) U) (sectionsAlgebra J (g ≫ h) U) where
  base := (k.hom.app U).hom
  map := RingHom.id (D.obj.obj U)
  map_algebraMap _ := rfl

/-- The square of the change of base along `k` restricts along `U ⟶ V` in two ways, and the two
composite squares agree. -/
theorem sectionsBaseSquare_comp {U V : Cᵒᵖ} (r : U ⟶ V) :
    (sectionsBaseSquare J k g h U).comp (sectionsRestrictionSquare J (g ≫ h) r) =
      (sectionsRestrictionSquare J ((k ≫ g) ≫ h) r).comp (sectionsBaseSquare J k g h V) := by
  have hbase : (A₂.obj.map r).hom.comp (k.hom.app U).hom =
      (k.hom.app V).hom.comp (A₁.obj.map r).hom :=
    congrArg CommRingCat.Hom.hom (k.hom.naturality r).symm
  unfold sectionsBaseSquare sectionsRestrictionSquare CommAlgCat.AlgebraSquare.comp
  congr 1

/-- The change of base `L^{sw}_{D/A₁} ⟶ L^{sw}_{D/A₂}` along `k`, on the sectionwise second
vertices. -/
def sectionwiseTowerBaseMap :
    sectionwiseCotangentModuleComplex J ((k ≫ g) ≫ h) ⟶
      sectionwiseCotangentModuleComplex J (g ≫ h) where
  f j :=
    { app U := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (sectionsBaseSquare J k g h U)).f j
      naturality {U V} r := by
        ext x
        exact (((CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _
          (sectionsBaseSquare_comp J k g h r).symm j x).symm).trans
          (CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _ rfl j x)).symm }
  comm' i j _ := by
    refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact ConcreteCategory.congr_hom
      ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (sectionsBaseSquare J k g h U)).comm i j) x

/-- The two composite squares of the change of base along `k` and of the first map of the tower
agree, over every object. -/
theorem baseRingSquareTop_comp_idSquare_sectionsTowerHom (U : Cᵒᵖ) :
    (CommAlgCat.baseRingSquareTop (sectionsTowerHom J k g U)).comp
        (CommAlgCat.idSquare (sectionsTowerHom J g h U)) =
      (CommAlgCat.idSquare (sectionsTowerHom J (k ≫ g) h U)).comp
        (sectionsBaseSquare J k g h U) := by
  unfold CommAlgCat.idSquare CommAlgCat.baseRingSquareTop sectionsBaseSquare
    CommAlgCat.AlgebraSquare.comp
  congr 1

/-- Change of base along `k` commutes with the sectionwise first maps, before transposing along
the change of rings, in every degree. -/
theorem sectionwiseTowerChangeOfBaseMap_comp_sectionwiseTowerBaseChangeMap_f (j : ℤ) :
    (sectionwiseTowerChangeOfBaseMap J k g).f j ≫ (sectionwiseTowerBaseChangeMap J g h).f j =
      (sectionwiseTowerBaseChangeMap J (k ≫ g) h).f j ≫
        (PresheafOfModules.restrictScalars (towerRingMap J h)).map
          ((sectionwiseTowerBaseMap J k g h).f j) := by
  refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  let x' : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A₁.obj.obj U)
      (sectionsAlgebra J (k ≫ g) U)).X j := x
  have e₁ := CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp
    (CommAlgCat.baseRingSquareTop (sectionsTowerHom J k g U))
    (CommAlgCat.idSquare (sectionsTowerHom J g h U)) rfl j x'
  have e₂ := CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp
    (CommAlgCat.idSquare (sectionsTowerHom J (k ≫ g) h U))
    (sectionsBaseSquare J k g h U) (baseRingSquareTop_comp_idSquare_sectionsTowerHom J k g h U) j x'
  exact e₁.symm.trans e₂

/-- **Change of base along `k` commutes with the sectionwise first maps** of the two towers. -/
theorem sectionwiseTowerBaseChangeComplexMap_naturality :
    sectionwiseTowerBaseChangeComplexMap J (k ≫ g) h ≫ sectionwiseTowerBaseMap J k g h =
      sectionwiseBaseChangedBaseMap J k g h ≫ sectionwiseTowerBaseChangeComplexMap J g h := by
  ext j : 1
  have h₁ := (towerChangeOfRingsAdjunction J h).homEquiv_naturality_right_symm
    ((sectionwiseTowerBaseChangeMap J (k ≫ g) h).f j) ((sectionwiseTowerBaseMap J k g h).f j)
  have h₂ := (towerChangeOfRingsAdjunction J h).homEquiv_naturality_left_symm
    ((sectionwiseTowerChangeOfBaseMap J k g).f j) ((sectionwiseTowerBaseChangeMap J g h).f j)
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  exact congrArg ((towerChangeOfRingsAdjunction J h).homEquiv _ _).symm
    (sectionwiseTowerChangeOfBaseMap_comp_sectionwiseTowerBaseChangeMap_f J k g h j).symm

/-- **The morphism of sectionwise short exact sequences induced by change of base along `k`.** -/
def sectionwiseFundamentalShortComplexBaseMap :
    sectionwiseFundamentalShortComplex J (k ≫ g) h ⟶ sectionwiseFundamentalShortComplex J g h where
  τ₁ := sectionwiseBaseChangedBaseMap J k g h
  τ₂ := sectionwiseTowerBaseMap J k g h
  τ₃ := cokernel.map _ _ (sectionwiseBaseChangedBaseMap J k g h)
    (sectionwiseTowerBaseMap J k g h) (sectionwiseTowerBaseChangeComplexMap_naturality J k g h)
  comm₁₂ := (sectionwiseTowerBaseChangeComplexMap_naturality J k g h).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-! ### The map of first vertices -/

/-- **The map of first vertices `L_{B/A₁} ⊗_B D ⟶ L_{B/A₂} ⊗_B D`**: the sheafification of the
sectionwise change of base along `k`, read through the identifications of Tag 08SX. -/
def baseChangedCotangentBaseMap :
    baseChangedCotangentComplex.{u, v, w} J (k ≫ g) h ⟶
      baseChangedCotangentComplex.{u, v, w} J g h :=
  (sheafifiedSectionwiseBaseChangedCotangentComplexIso J (k ≫ g) h).inv ≫
    (sheafifyTowerComplex J D).map (sectionwiseBaseChangedBaseMap J k g h) ≫
    (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom

/-! ### Towers whose second map is injective on sections -/

section Injective

variable (hinj : ∀ U, Function.Injective (h.hom.app U).hom)
  [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]

/-- **The identifications of the third vertices are compatible with change of base**: the
identification `coker ≅ L_{D/B}` of the tower `A₁ ⟶ B ⟶ D`, `towerThirdVertexIso`, is that of
`A₂ ⟶ B ⟶ D` composed with the sheafified map of cokernels. This is the input of Remark 08SE
that the naturality of the connecting morphism needs. -/
def TowerThirdVertexNatural : Prop :=
  (towerThirdVertexIso J (k ≫ g) h hinj).inv ≫
      DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalShortComplexBaseMap J k g h).τ₃) =
    (towerThirdVertexIso J g h hinj).inv

/-- **Naturality of `towerConnectingOfInjective` in the base ring**: change of base along `k`
carries the connecting morphism of `A₁ ⟶ B ⟶ D` to that of `A₂ ⟶ B ⟶ D`, given the compatibility
of the third-vertex identifications. -/
theorem towerConnectingOfInjective_naturality (h₃ : TowerThirdVertexNatural J k g h hinj) :
    towerConnectingOfInjective J (k ≫ g) h hinj ≫
        (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h))⟦(1 : ℤ)⟧' =
      towerConnectingOfInjective J g h hinj := by
  have hn := DerivedCategory.triangleOfSESδ_naturality
    (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J (k ≫ g) h hinj)
    (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj)
    ((sheafifyTowerComplex J D).mapShortComplex.map
      (sectionwiseFundamentalShortComplexBaseMap J k g h))
  have hd : DerivedCategory.Q.map (sheafifiedSectionwiseBaseChangedCotangentComplexIso J
        (k ≫ g) h).hom ≫ DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h) =
      DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseBaseChangedBaseMap J k g h)) ≫
        DerivedCategory.Q.map (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, baseChangedCotangentBaseMap,
      Iso.hom_inv_id_assoc]
  have hn' : DerivedCategory.triangleOfSESδ
        (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J (k ≫ g) h hinj) ≫
        (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
          (sectionwiseBaseChangedBaseMap J k g h)))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalShortComplexBaseMap J k g h).τ₃) ≫
        DerivedCategory.triangleOfSESδ
          (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj) := hn
  unfold towerConnectingOfInjective
  show ((towerThirdVertexIso J (k ≫ g) h hinj).inv ≫
      DerivedCategory.triangleOfSESδ
        (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J (k ≫ g) h hinj) ≫
        (DerivedCategory.Q.map (sheafifiedSectionwiseBaseChangedCotangentComplexIso J
          (k ≫ g) h).hom)⟦(1 : ℤ)⟧') ≫
      (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h))⟦(1 : ℤ)⟧' =
    (towerThirdVertexIso J g h hinj).inv ≫ DerivedCategory.triangleOfSESδ
        (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj) ≫
      (DerivedCategory.Q.map
        (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom)⟦(1 : ℤ)⟧'
  rw [Category.assoc, Category.assoc, ← Functor.map_comp]
  refine (congrArg (fun φ => (towerThirdVertexIso J (k ≫ g) h hinj).inv ≫
    DerivedCategory.triangleOfSESδ
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J (k ≫ g) h hinj) ≫
    (shiftFunctor _ (1 : ℤ)).map φ) hd).trans ?_
  have hmc := (shiftFunctor (DerivedCategory (targetModules.{u, v, w} J D)) (1 : ℤ)).map_comp
    (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map (sectionwiseBaseChangedBaseMap J k g h)))
    (DerivedCategory.Q.map (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom)
  refine (congrArg (fun φ => (towerThirdVertexIso J (k ≫ g) h hinj).inv ≫ φ)
    ((congrArg (fun ψ => DerivedCategory.triangleOfSESδ
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J (k ≫ g) h hinj) ≫ ψ)
        hmc).trans (Category.assoc _ _ _).symm)).trans ?_
  refine (congrArg (fun φ => (towerThirdVertexIso J (k ≫ g) h hinj).inv ≫ φ ≫
    (DerivedCategory.Q.map
      (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom)⟦(1 : ℤ)⟧')
      hn').trans ?_
  refine ((congrArg (fun φ => (towerThirdVertexIso J (k ≫ g) h hinj).inv ≫ φ)
    (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans ?_
  exact congrArg (fun φ => φ ≫ DerivedCategory.triangleOfSESδ
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj) ≫
    (DerivedCategory.Q.map
      (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom)⟦(1 : ℤ)⟧')
      h₃

end Injective

/-! ### Arbitrary towers -/

section General

variable [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]

/-- **The first-vertex identifications of the product-graph reduction are compatible with change
of base**: `towerProdFirstVertexIso` carries the map of first vertices of the towers
`A ⟶ B ⟶ B × D` to that of the towers `A ⟶ B ⟶ D`. -/
def TowerProdFirstVertexNatural : Prop :=
  letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory.map
      (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g (prodGraph J h))) ≫
      (towerProdFirstVertexIso J g h).hom =
    (towerProdFirstVertexIso J (k ≫ g) h).hom ≫
      DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h)

/-- **Naturality of `towerConnecting` in the base ring**: change of base along `k` carries the
connecting morphism of the fundamental triangle of `A₁ ⟶ B ⟶ D` to that of `A₂ ⟶ B ⟶ D`, given
the compatibility of the third-vertex identifications of the towers `Aᵢ ⟶ B ⟶ B × D` and of the
first-vertex identifications of the product-graph reduction. -/
theorem towerConnecting_naturality
    (h₃ : letI := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
      TowerThirdVertexNatural J k g (prodGraph J h) (injective_prodGraph J h))
    (h₁ : TowerProdFirstVertexNatural.{t} J k g h) :
    towerConnecting J (k ≫ g) h ≫
        (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h))⟦(1 : ℤ)⟧' =
      towerConnecting J g h := by
  let := HasDerivedCategory.standard (targetModules.{u, v, w} J (prodObj J B D))
  let Φ := (prodSndSummand.{u, v, w} J (B := B) (D := D)).mapDerivedCategory
  have hinj := towerConnectingOfInjective_naturality J k g (prodGraph J h)
    (injective_prodGraph J h) h₃
  have hc := ((Φ.commShiftIso (1 : ℤ)).hom.naturality
    (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g (prodGraph J h))))
  have h₁' : Φ.map (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g (prodGraph J h))) ≫
      (towerProdFirstVertexIso J g h).hom =
      (towerProdFirstVertexIso J (k ≫ g) h).hom ≫
        DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h) := h₁
  unfold towerConnecting
  show ((towerProdThirdVertexIso J h).inv ≫
      (Φ.map (towerConnectingOfInjective J (k ≫ g) (prodGraph J h) (injective_prodGraph J h)) ≫
        (Φ.commShiftIso (1 : ℤ)).hom.app _) ≫
      (towerProdFirstVertexIso J (k ≫ g) h).hom⟦(1 : ℤ)⟧') ≫
      (DerivedCategory.Q.map (baseChangedCotangentBaseMap J k g h))⟦(1 : ℤ)⟧' =
    (towerProdThirdVertexIso J h).inv ≫
      (Φ.map (towerConnectingOfInjective J g (prodGraph J h) (injective_prodGraph J h)) ≫
        (Φ.commShiftIso (1 : ℤ)).hom.app _) ≫
      (towerProdFirstVertexIso J g h).hom⟦(1 : ℤ)⟧'
  have hc' : (Φ.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J (k ≫ g) (prodGraph J h))) ≫
      (Φ.map (DerivedCategory.Q.map
        (baseChangedCotangentBaseMap J k g (prodGraph J h))))⟦(1 : ℤ)⟧' =
      Φ.map ((DerivedCategory.Q.map
        (baseChangedCotangentBaseMap J k g (prodGraph J h)))⟦(1 : ℤ)⟧') ≫
        (Φ.commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g (prodGraph J h))) :=
    hc.symm
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← h₁', Functor.map_comp, ← Category.assoc
    ((Φ.commShiftIso (1 : ℤ)).hom.app _), hc', Category.assoc, ← Category.assoc (Φ.map _),
    ← Φ.map_comp, hinj]

end General

end CategoryTheory.Sheaf

end
