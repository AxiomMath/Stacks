module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonSquareNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseTower

/-!
# Sheafifying the sectionwise maps of the fundamental triangle

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. Over every object `U`
the two displayed maps of the fundamental triangle of the ring maps `A(U) → B(U) → D(U)` form
maps of complexes of presheaves of `D`-modules

`U ↦ (L_{B(U)/A(U)} ⊗_{B(U)} D(U) ⟶ L_{D(U)/A(U)})` and `U ↦ (L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)})`.

This file shows that their sheafifications are the two displayed arrows
`CategoryTheory.Sheaf.towerCotangentBaseChange` and
`CategoryTheory.Sheaf.towerCotangentChangeOfBase` of the triangle of Tag 08SZ, once the sheafified
sources and targets are identified with the vertices `L_{B/A} ⊗_B D`, `L_{D/A}` and `L_{D/B}`.

## Main definitions

* `CategoryTheory.Sheaf.towerSheafifyChangeOfRingsIso`: change of rings along `h : B ⟶ D`
  followed by sheafification is sheafification followed by extension of scalars.
* `CategoryTheory.Sheaf.sheafifiedSectionwiseBaseChangedCotangentComplexIso`: the
  sheafification of `U ↦ L_{B(U)/A(U)} ⊗_{B(U)} D(U)` is `L_{B/A} ⊗_B D`.

## Main results

* `CategoryTheory.Sheaf.sheafification_map_sectionwiseTowerBaseChangeComplexMap`: the
  sectionwise first map sheafifies to the first arrow of the triangle.
* `CategoryTheory.Sheaf.sheafification_map_sectionwiseTowerChangeOfBaseMap`: the sectionwise
  second map sheafifies to the second arrow of the triangle.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- Extension of scalars along `h` is additive. -/
noncomputable instance : (towerExtendScalars.{u, v, w} J h).Additive :=
  (towerExtendRestrictAdjunction.{u, v, w} J h).left_adjoint_additive

/-- **Change of rings along `h` commutes with sheafification**: sheafifying the change of rings
`D ⊗_{p,B} P` of a presheaf of `B`-modules is extending the scalars of the sheafification of
`P`, through the change of rings of the sheafification unit of `P`. -/
noncomputable def towerSheafifyChangeOfRingsIso :
    towerChangeOfRings J h ⋙ PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj) ≅
      PresheafOfModules.sheafification.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj) ⋙
        towerExtendScalars.{u, v, w} J h :=
  NatIso.ofComponents
    (fun P => Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso h.hom
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property P)
    (fun {P Q} f => by
      let RB := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B
      let RD := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D
      let aD := PresheafOfModules.sheafification.{max u v w} (𝟙 RD.obj)
      let aB := PresheafOfModules.sheafification.{max u v w} (𝟙 RB.obj)
      let η := (PresheafOfModules.sheafificationAdjunction.{max u v w} (𝟙 RB.obj)).unit
      let F := towerChangeOfRings J h
      have hη : f ≫ η.app Q = η.app P ≫ (aB.map f).val := η.naturality f
      have hF : F.map f ≫ F.map (η.app Q) = F.map (η.app P) ≫ F.map (aB.map f).val :=
        (F.map_comp _ _).symm.trans ((congrArg F.map hη).trans (F.map_comp _ _))
      exact (aD.map_comp _ _).symm.trans ((congrArg aD.map hF).trans (aD.map_comp _ _)))

/-- **The first vertex is the sheafification of `U ↦ L_{B(U)/A(U)} ⊗_{B(U)} D(U)`**: the
sheafification of the degreewise change of rings along `h` of the sectionwise cotangent complex
of `A ⟶ B` is the degreewise base change `L_{B/A} ⊗_B D`, as complexes of sheaves of
`D`-modules. -/
noncomputable def sheafifiedSectionwiseBaseChangedCotangentComplexIso :
    ((PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (sectionwiseBaseChangedCotangentComplex J g h) ≅
      baseChangedCotangentComplex.{u, v, w} J g h :=
  (Functor.mapHomologicalComplexCompIso (towerSheafifyChangeOfRingsIso J h)
      (ComplexShape.up ℤ)).app (sectionwiseCotangentModuleComplex J g) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm.app
      (sectionwiseCotangentModuleComplex J g) ≪≫
    ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (sheafifiedSectionwiseCotangentModuleComplexIso J g) ≪≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
      ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
        (cotangentSimplicialModule.{u, v, w} J g).object)
      (ComplexShape.embeddingUpIntLE 0)).symm ≪≫
    ((ComplexShape.embeddingUpIntLE 0).extendFunctor (targetModules.{u, v, w} J D)).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
        (towerExtendScalars.{u, v, w} J h)).app (cotangentSimplicialModule.{u, v, w} J g).object)

/-! ## The two squares on sections -/

/-- The square `(id, h_U)` of the tower on sections over `U` is the square on sections of the
square `(𝟙 A, h)` of sheaves of rings. -/
theorem idSquare_sectionsTowerHom (hsq : g ≫ h = 𝟙 A ≫ (g ≫ h)) (U : Cᵒᵖ) :
    CommAlgCat.idSquare (sectionsTowerHom J g h U) = sectionsSquare J (𝟙 A) h hsq U :=
  rfl

/-- The square `(A(U) → B(U), id)` of the change of base ring on sections over `U` is the square
on sections of the square `(g, 𝟙 D)` of sheaves of rings. -/
theorem baseRingSquareTop_sectionsTowerHom (hsq : (g ≫ h) ≫ 𝟙 D = g ≫ h) (U : Cᵒᵖ) :
    CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h U) = sectionsSquare J g (𝟙 D) hsq U :=
  rfl

/-! ## The naturality squares of the comparison maps -/

/-- The sectionwise first map of the triangle is intertwined by the comparison maps of Tag 08SX
with the map of cotangent complexes of sheaves induced by the square `(𝟙 A, h)`. -/
theorem sectionwiseTowerBaseChangeMap_comp_comparison (j : ℤ) :
    (sectionwiseTowerBaseChangeMap J g h).f j ≫
        (PresheafOfModules.restrictScalars (towerRingMap J h)).map
          ((sectionwiseCotangentModuleComplexComparison J (g ≫ h)).f j) =
      (sectionwiseCotangentModuleComplexComparison J g).f j ≫
        (SheafOfModules.forget _).map
          ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j) := by
  refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  have e := sectionsCotangentComplexComparison_square J (f := g) (f' := g ≫ h) (𝟙 A) h
    (Category.id_comp _).symm U j x
  rw [← idSquare_sectionsTowerHom J g h] at e
  exact e.symm

/-- The sectionwise second map of the triangle is intertwined by the comparison maps of Tag 08SX
with the map of cotangent complexes of sheaves induced by the square `(g, 𝟙 D)`. -/
theorem sectionwiseTowerChangeOfBaseMap_comp_comparison (j : ℤ) :
    (sectionwiseTowerChangeOfBaseMap J g h).f j ≫
        (sectionwiseCotangentModuleComplexComparison J h).f j =
      (sectionwiseCotangentModuleComplexComparison J (g ≫ h)).f j ≫
        (SheafOfModules.forget _).map ((towerCotangentChangeOfBase.{u, v, w} J g h).f j) := by
  refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  have e := sectionsCotangentComplexComparison_square J (f := g ≫ h) (f' := h) g (𝟙 D)
    (Category.comp_id _) U j x
  rw [← baseRingSquareTop_sectionsTowerHom J g h] at e
  exact e.symm
/-! ## The first arrow through extension of scalars -/

/-- A transpose along `CategoryTheory.Sheaf.towerExtendRestrictAdjunction`, read on underlying
presheaves of modules, is the transpose along the composite of the change-of-rings adjunction
with the sheafification adjunction. -/
theorem towerExtendRestrictAdjunction_homEquiv_val {L : targetModules.{u, v, w} J B}
    {M : targetModules.{u, v, w} J D} (Φ : (towerExtendScalars.{u, v, w} J h).obj L ⟶ M) :
    ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv L M Φ).val =
      ((towerChangeOfRingsAdjunction J h).comp
        (PresheafOfModules.sheafificationAdjunction.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj))).homEquiv
            L.val M Φ := by
  have h₁ := Stacks.Sheaves.RingedToposModules.forget_map_extendRestrictScalarsAdjunction_unit_app
    J h.hom (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property L
  have h₂ := Adjunction.comp_unit_app (towerChangeOfRingsAdjunction J h)
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)) L.val
  refine (congrArg SheafOfModules.Hom.val
    ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv_unit L M Φ)).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit ((towerChangeOfRingsAdjunction J h).comp
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj))) L.val M Φ).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) h₂.symm)
  exact congrArg (· ≫ ((squareRestrict.{u, v, w} J h).map Φ).val) h₁

/-- Read through the comparison of extension of scalars with the extension of complexes and the
alternating-face-map complex, the first arrow of the triangle is, in every degree, the transpose
along the extension–restriction adjunction of the map of cotangent complexes induced by the
square `(𝟙 A, h)`. -/
theorem towerCotangentBaseChange_f_eq_homEquiv_symm (j : ℤ) :
    (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
        ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
          (cotangentSimplicialModule.{u, v, w} J g).object)
        (ComplexShape.embeddingUpIntLE 0)).inv.f j ≫
      (HomologicalComplex.extendMap ((alternatingFaceMapComplexCompMapHomologicalComplexIso
          (towerExtendScalars.{u, v, w} J h)).hom.app
            (cotangentSimplicialModule.{u, v, w} J g).object)
        (ComplexShape.embeddingUpIntLE 0)).f j ≫
      (towerCotangentBaseChange.{u, v, w} J g h).f j =
    ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
      ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j) := by
  by_cases hpos : 0 < j
  · exact (cotangentComplex_isZero_pos.{u, v, w} J (g ≫ h) j hpos).eq_of_tgt _ _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
    have key :
        (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
            ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
              (cotangentSimplicialModule.{u, v, w} J g).object)
            (ComplexShape.embeddingUpIntLE 0)).inv.f (-(n : ℤ)) ≫
          (HomologicalComplex.extendMap ((alternatingFaceMapComplexCompMapHomologicalComplexIso
              (towerExtendScalars.{u, v, w} J h)).hom.app
                (cotangentSimplicialModule.{u, v, w} J g).object)
            (ComplexShape.embeddingUpIntLE 0)).f (-(n : ℤ)) ≫
          (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).hom =
        (towerExtendScalars.{u, v, w} J h).map
          (cotangentComplex_degreeIso.{u, v, w} J g n).hom := by
      refine (Iso.inv_comp_eq ((HomologicalComplex.eval _ _ (-(n : ℤ))).mapIso
        (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
          ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
            (cotangentSimplicialModule.{u, v, w} J g).object)
          (ComplexShape.embeddingUpIntLE 0)))).mpr ?_
      change _ = (HomologicalComplex.mapHomologicalComplexExtendIso _ _ _).hom.f _ ≫ _
      rw [HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ hn,
        HomologicalComplex.extendMap_f _ _ hn]
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine congrArg (fun k => _ ≫ k) ?_
      refine (Category.assoc _ _ _).trans ?_
      refine ((Category.id_comp _).trans (HomologicalComplex.extendXIso _ _ hn).inv_hom_id).trans ?_
      exact ((Functor.map_id _ _).symm.trans
        (congrArg (towerExtendScalars.{u, v, w} J h).map
          (HomologicalComplex.extendXIso _ _ hn).inv_hom_id).symm).trans (Functor.map_comp _ _ _)
    rw [towerCotangentBaseChange_f, squareCotangentComplexMap_f,
      Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
      baseChangeSimplicialMap_app]
    refine Eq.trans ?_ (congrArg (· ≫ _) key)
    exact (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
/-! ## Transposes -/

variable {J} in
/-- The transpose along the sheafification adjunction of the degree-`j` component of the
identification of the sheafification of `U ↦ L_{B(U)/A(U)}` with `L_{B/A}` is the canonical map
of Tag 08SX. -/
theorem sheafificationAdjunction_homEquiv_sheafifiedSectionwiseCotangentModuleComplexIso_f
    {A' B' : Sheaf J CommRingCat.{max u v w}} (f : A' ⟶ B') (j : ℤ) :
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B').obj)).homEquiv _ _
        ((sheafifiedSectionwiseCotangentModuleComplexIso J f).hom.f j) =
      (sectionwiseCotangentModuleComplexComparison J f).f j :=
  (congrArg (fun E => E ((sheafifiedSectionwiseCotangentModuleComplexIso J f).hom.f j))
    (Equiv.ext fun k => PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ k)).trans
    (Equiv.apply_symm_apply _ _)

/-- The transpose along the sheafification adjunction of a sheafified map into the degree-`j`
sectionwise cotangent module, followed by the identification with `L`, is the precomposition of
the canonical map of Tag 08SX. -/
private theorem sheafificationAdjunction_homEquiv_map_comp_iso_f
    {A' B' : Sheaf J CommRingCat.{max u v w}} (f : A' ⟶ B') (j : ℤ) {X'}
    (φ : X' ⟶ (sectionwiseCotangentModuleComplex J f).X j) :
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B').obj)).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B').obj)).map φ ≫
          (sheafifiedSectionwiseCotangentModuleComplexIso J f).hom.f j) =
      φ ≫ (sectionwiseCotangentModuleComplexComparison J f).f j := by
  rw [Adjunction.homEquiv_naturality_left,
    sheafificationAdjunction_homEquiv_sheafifiedSectionwiseCotangentModuleComplexIso_f]
  rfl

/-- The transpose along the change-of-rings adjunction of the sectionwise first map
`L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)}` is the `B`-linear map `L_{B(U)/A(U)} ⟶ L_{D(U)/A(U)}`. -/
theorem towerChangeOfRingsAdjunction_homEquiv_sectionwiseTowerBaseChangeComplexMap_f (j : ℤ) :
    (towerChangeOfRingsAdjunction J h).homEquiv ((sectionwiseCotangentModuleComplex J g).X j)
        ((sectionwiseCotangentModuleComplex J (g ≫ h)).X j)
        ((sectionwiseTowerBaseChangeComplexMap J g h).f j) =
      (sectionwiseTowerBaseChangeMap J g h).f j :=
  Equiv.apply_symm_apply ((towerChangeOfRingsAdjunction J h).homEquiv _ _) _

/-- The transpose of the sheafified sectionwise first map, read in `L_{D/A}`, along the composite
of the change-of-rings and sheafification adjunctions. -/
theorem sheafifiedSectionwiseTowerBaseChange_transpose (j : ℤ) :
    ((towerChangeOfRingsAdjunction J h).comp (PresheafOfModules.sheafificationAdjunction.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj))).homEquiv _ _
        ((PresheafOfModules.sheafification.{max u v w}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).map
            ((sectionwiseTowerBaseChangeComplexMap J g h).f j) ≫
          (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom.f j) =
      (sectionwiseTowerBaseChangeMap J g h).f j ≫
        (PresheafOfModules.restrictScalars (towerRingMap J h)).map
          ((sectionwiseCotangentModuleComplexComparison J (g ≫ h)).f j) := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  have e₂ := (towerChangeOfRingsAdjunction J h).homEquiv_naturality_right
      (X := (sectionwiseCotangentModuleComplex J g).X j)
      (Y := (sectionwiseCotangentModuleComplex J (g ≫ h)).X j)
      (Y' := (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).obj
          ((cotangentComplex J (g ≫ h)).X j))
      ((sectionwiseTowerBaseChangeComplexMap J g h).f j)
      ((sectionwiseCotangentModuleComplexComparison J (g ≫ h)).f j)
  exact (congrArg _ (sheafificationAdjunction_homEquiv_map_comp_iso_f J (g ≫ h) j _)).trans <|
    e₂.trans (congrArg (· ≫ _)
    (towerChangeOfRingsAdjunction_homEquiv_sectionwiseTowerBaseChangeComplexMap_f J g h j))

/-- The sheafification unit followed by the degree-`j` component of the identification of the
sheafification of `U ↦ L_{B(U)/A(U)}` with `L_{B/A}` is the canonical map of Tag 08SX. -/
theorem sheafificationAdjunction_unit_comp_sheafifiedSectionwiseCotangentModuleComplexIso_f
    (j : ℤ) :
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).unit.app
          ((sectionwiseCotangentModuleComplex J g).X j) ≫
        ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j).val =
      (sectionwiseCotangentModuleComplexComparison J g).f j :=
  ((PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).homEquiv_unit _ _
      ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j)).symm.trans
    (sheafificationAdjunction_homEquiv_sheafifiedSectionwiseCotangentModuleComplexIso_f g j)

/-- The transpose of the first arrow, read on the sheafification of `U ↦ L_{B(U)/A(U)}`, along
the composite of the change-of-rings and sheafification adjunctions. -/
theorem towerCotangentBaseChange_transpose (j : ℤ) :
    ((towerChangeOfRingsAdjunction J h).comp (PresheafOfModules.sheafificationAdjunction.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj))).homEquiv _ _
        ((towerSheafifyChangeOfRingsIso J h).hom.app ((sectionwiseCotangentModuleComplex J g).X j) ≫
          (towerExtendScalars.{u, v, w} J h).map
            ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j) ≫
          ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
            ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j)) =
      (sectionwiseCotangentModuleComplexComparison J g).f j ≫
        (SheafOfModules.forget _).map
          ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j) := by
  have e₁ := Adjunction.homEquiv_naturality_left ((towerChangeOfRingsAdjunction J h).comp
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)))
    ((PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).unit.app
        ((sectionwiseCotangentModuleComplex J g).X j))
    ((towerExtendScalars.{u, v, w} J h).map
        ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j) ≫
      ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j))
  have e₂ := Adjunction.homEquiv_naturality_left ((towerChangeOfRingsAdjunction J h).comp
    (PresheafOfModules.sheafificationAdjunction.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)))
    ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j).val
    (((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j))
  have e₃ := (towerExtendRestrictAdjunction_homEquiv_val J h
      (((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j))).symm.trans
      (congrArg SheafOfModules.Hom.val (Equiv.apply_symm_apply _ _))
  refine e₁.trans ((congrArg (_ ≫ ·) (e₂.trans (congrArg (_ ≫ ·) e₃))).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (sheafificationAdjunction_unit_comp_sheafifiedSectionwiseCotangentModuleComplexIso_f J g j))

/-- **The first arrow, sheafified, in one degree.** Sheafifying the sectionwise map
`L_{B(U)/A(U)} ⊗_{B(U)} D(U) ⟶ L_{D(U)/A(U)}` in degree `j` and identifying the target with
`L_{D/A}` gives the transpose of the map of cotangent complexes induced by `(𝟙 A, h)`, read on
the base change of `L_{B/A}`. -/
theorem sheafification_map_sectionwiseTowerBaseChangeComplexMap_f (j : ℤ) :
    (PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).map
        ((sectionwiseTowerBaseChangeComplexMap J g h).f j) ≫
      (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom.f j =
    (towerSheafifyChangeOfRingsIso J h).hom.app ((sectionwiseCotangentModuleComplex J g).X j) ≫
      (towerExtendScalars.{u, v, w} J h).map
        ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j) ≫
      ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        ((squareCotangentComplexMap (towerBaseChangeSquare.{u, v, w} J g h)).f j) :=
  (((towerChangeOfRingsAdjunction J h).comp (PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj))).homEquiv
      ((sectionwiseCotangentModuleComplex J g).X j) ((cotangentComplex J (g ≫ h)).X j)).injective
    ((sheafifiedSectionwiseTowerBaseChange_transpose J g h j).trans
      ((sectionwiseTowerBaseChangeMap_comp_comparison J g h j).trans
        (towerCotangentBaseChange_transpose J g h j).symm))

/-- **The second arrow, sheafified, in one degree.** Sheafifying the sectionwise map
`L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)}` in degree `j` and identifying source and target with `L_{D/A}`
and `L_{D/B}` gives the second arrow of the triangle. -/
theorem sheafification_map_sectionwiseTowerChangeOfBaseMap_f (j : ℤ) :
    (PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).map
        ((sectionwiseTowerChangeOfBaseMap J g h).f j) ≫
      (sheafifiedSectionwiseCotangentModuleComplexIso J h).hom.f j =
    (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom.f j ≫
      (towerCotangentChangeOfBase.{u, v, w} J g h).f j := by
  refine ((PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).homEquiv
      ((sectionwiseCotangentModuleComplex J (g ≫ h)).X j) ((cotangentComplex J h).X j)).injective ?_
  have e₂ := (PresheafOfModules.sheafificationAdjunction.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).homEquiv_naturality_right
      (X := (sectionwiseCotangentModuleComplex J (g ≫ h)).X j)
      (Y := (cotangentComplex J (g ≫ h)).X j) (Y' := (cotangentComplex J h).X j)
      ((sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom.f j)
      ((towerCotangentChangeOfBase.{u, v, w} J g h).f j)
  rw [sheafificationAdjunction_homEquiv_map_comp_iso_f, e₂,
    sheafificationAdjunction_homEquiv_sheafifiedSectionwiseCotangentModuleComplexIso_f]
  exact sectionwiseTowerChangeOfBaseMap_comp_comparison J g h j

/-- **The sectionwise first map of the triangle sheafifies to the first arrow.** Sheafifying
`U ↦ (L_{B(U)/A(U)} ⊗_{B(U)} D(U) ⟶ L_{D(U)/A(U)})` gives
`CategoryTheory.Sheaf.towerCotangentBaseChange`, once its source and target are identified with
`L_{B/A} ⊗_B D` and `L_{D/A}`. -/
theorem sheafification_map_sectionwiseTowerBaseChangeComplexMap :
    ((PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (sectionwiseTowerBaseChangeComplexMap J g h) =
      (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom ≫
        towerCotangentBaseChange.{u, v, w} J g h ≫
          (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  have eT : (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h).hom.f j =
      (towerSheafifyChangeOfRingsIso J h).hom.app ((sectionwiseCotangentModuleComplex J g).X j) ≫
        (towerExtendScalars.{u, v, w} J h).map
          ((sheafifiedSectionwiseCotangentModuleComplexIso J g).hom.f j) ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (towerExtendScalars.{u, v, w} J h)
            ((alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
              (cotangentSimplicialModule.{u, v, w} J g).object)
            (ComplexShape.embeddingUpIntLE 0)).inv.f j ≫
          (HomologicalComplex.extendMap ((alternatingFaceMapComplexCompMapHomologicalComplexIso
              (towerExtendScalars.{u, v, w} J h)).hom.app
                (cotangentSimplicialModule.{u, v, w} J g).object)
            (ComplexShape.embeddingUpIntLE 0)).f j :=
    congrArg (_ ≫ ·) (Category.id_comp _)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, eT]
  refine (sheafification_map_sectionwiseTowerBaseChangeComplexMap_f J g h j).trans ?_
  rw [← towerCotangentBaseChange_f_eq_homEquiv_symm]
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).symm

/-- **The sectionwise second map of the triangle sheafifies to the second arrow.** Sheafifying
`U ↦ (L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)})` gives `CategoryTheory.Sheaf.towerCotangentChangeOfBase`,
once its source and target are identified with `L_{D/A}` and `L_{D/B}`. -/
theorem sheafification_map_sectionwiseTowerChangeOfBaseMap :
    ((PresheafOfModules.sheafification.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (sectionwiseTowerChangeOfBaseMap J g h) =
      (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom ≫
        towerCotangentChangeOfBase.{u, v, w} J g h ≫
          (sheafifiedSectionwiseCotangentModuleComplexIso J h).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact HomologicalComplex.hom_ext _ _ (sheafification_map_sectionwiseTowerChangeOfBaseMap_f J g h)

end CategoryTheory.Sheaf

end
