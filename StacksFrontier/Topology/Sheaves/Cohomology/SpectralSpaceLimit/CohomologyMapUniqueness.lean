module

public import StacksFrontier.CategoryTheory.Abelian.InjectiveResolution.DescHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit

/-!
# Uniqueness of the maps on cohomology prescribed by Tag 0A37

`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` specifies the canonical map on sheaf
cohomology attached to a map of abelian sheaves over a continuous map: a lift to injective
resolutions, conjugated by identifications of cohomology with right-derived evaluation.

This file proves that this specification determines the map, using the homotopy uniqueness of a
lift of an injective resolution into an arbitrary complex of injective objects
(`StacksFrontier.CategoryTheory.Abelian.InjectiveResolution.DescHomotopy`), and draws the
consequences: a canonical map, its identity and composition laws, the resulting diagram
`Kᵒᵖ ⥤ AddCommGrpCat`, and a `CohomologyCocone` built from it.

## Main definitions

* `IsDerivedCohomologyMap` is the specification of `IsCohomologyMap` stripped of the two
  identifications with right-derived evaluation; it is what the uniqueness argument sees.
* `derivedCohomologyMap` and `cohomologyMap` are the canonical maps so specified.
* `spaceCohomologyMap` is `cohomologyMap` for a morphism of abelian sheafed spaces.
* `cohomologyDiagram` is the diagram `Kᵒᵖ ⥤ AddCommGrpCat` of the stage cohomology groups with
  the canonical maps as its arrows, and `cohomologyDiagramIota` is its comparison cocone.
* `cohomologyCocone` assembles these into a `CohomologyCocone` of Tag 0A37.

## Main results

* `IsDerivedCohomologyMap.eq` and `IsCohomologyMap.eq`: the prescribed map is unique.
* `isCohomologyMap_iff`: `IsCohomologyMap` holds exactly of the conjugate of
  `derivedCohomologyMap`, so the specification has a unique solution and
  `IsCohomologyMap.eq_cohomologyMap` identifies it.
* `derivedCohomologyMap_id` and `derivedCohomologyMap_comp`, and their sheafed-space forms
  `spaceCohomologyMap_id` and `spaceCohomologyMap_comp`: the canonical maps are functorial.
* `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_comp_homologyMap` and
  `homologyMap_comp_isoRightDerivedObj_inv`: changing the chosen injective resolution along a
  map over the identity does not change the identification with the right-derived object.

## Implementation notes

Uniqueness is proved by comparing two witnesses `(I₁, J₁, ψ₁)` and `(I₂, J₂, ψ₂)` in two steps.
First the target resolution of the first witness is moved onto `J₂` along a descent
`J₁.cocomplex ⟶ J₂.cocomplex` of the identity; this is a change of the identification with the
right-derived object, and costs nothing.  Then the two resulting lifts out of `I₁` into the
*same* complex `f_* J₂.cocomplex` agree on `I₁.ι`, so they are homotopic, because the
pushforward of an injective resolution consists of injective objects even though it resolves
nothing; hence they induce the same map on homology.

The composition law uses that the pushforward along a composite is *definitionally* the
composite of the pushforwards, so the composite of two lifts is a lift of the composite, and
that the two conjugating identifications at the middle stage cancel.

Many of the small steps are written in term mode.  The identifications with right-derived
evaluation have `(HomologicalComplex.homologyFunctor _ _ p).obj K` as an endpoint where
`HomologicalComplex.homologyMap` has `K.homology p`; the two are definitionally equal but not
syntactically so, and `rw`/`simp only [Category.assoc]` cannot reassociate across the junction.
`Eq.trans` and `congrArg` check their arguments up to full definitional equality and so do not
care.  The same applies to `((CochainComplex.single₀ C).obj G).X 0` versus `G` in the
degree-zero commutation relations.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v' u₂ v₂ u₃ v₃ u₄ v₄

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] {Z : C}

/-- The identification of a right-derived object with the homology of a chosen injective
resolution is compatible with any map of resolutions over the identity. -/
theorem isoRightDerivedObj_hom_comp_homologyMap (I I' : InjectiveResolution Z)
    (α : I.cocomplex ⟶ I'.cocomplex) (hα : I.ι.f 0 ≫ α.f 0 = I'.ι.f 0)
    (Φ : C ⥤ D) [Φ.Additive] (n : ℕ) :
    (I.isoRightDerivedObj Φ n).hom ≫
        HomologicalComplex.homologyMap ((Φ.mapHomologicalComplex _).map α) n =
      (I'.isoRightDerivedObj Φ n).hom := by
  have h0 := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 Z) I I' α
    (hα.trans (Category.id_comp _).symm) Φ n
  simp only [Functor.map_id, Category.id_comp, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] at h0
  exact h0.symm

/-- The inverse form of `isoRightDerivedObj_hom_comp_homologyMap`. -/
theorem homologyMap_comp_isoRightDerivedObj_inv (I I' : InjectiveResolution Z)
    (α : I.cocomplex ⟶ I'.cocomplex) (hα : I.ι.f 0 ≫ α.f 0 = I'.ι.f 0)
    (Φ : C ⥤ D) [Φ.Additive] (n : ℕ) :
    HomologicalComplex.homologyMap ((Φ.mapHomologicalComplex _).map α) n ≫
        (I'.isoRightDerivedObj Φ n).inv =
      (I.isoRightDerivedObj Φ n).inv := by
  have h0 := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 Z) I I' α
    (hα.trans (Category.id_comp _).symm) Φ n
  simp only [Functor.map_id, Category.comp_id, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] at h0
  exact h0.symm

end CategoryTheory.InjectiveResolution

namespace Stacks.Cohomology.SpectralLimit

/-- Associativity in the shape in which the specification of a map on cohomology compares a
conjugated composite with the conjugate of a composite. -/
theorem conj_assoc {C : Type u₂} [Category.{v₂} C] {A₀ A₁ A₂ A₃ A₄ A₅ : C}
    (e : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (d : A₄ ⟶ A₅) :
    e ≫ a ≫ b ≫ c ≫ d = e ≫ (a ≫ b ≫ c) ≫ d := by
  simp

/-- The conjugate of an identity map by an isomorphism is the identity. -/
theorem conj_id {C : Type u₂} [Category.{v₂} C] {A B : C} (e : A ≅ B) :
    e.hom ≫ 𝟙 B ≫ e.inv = 𝟙 A := by
  simp

/-- Conjugates by identifications compose to the conjugate of the composite. -/
theorem conj_comp {C : Type u₂} [Category.{v₂} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃) (a : B₁ ⟶ B₂) (b : B₂ ⟶ B₃) :
    (e₁.hom ≫ a ≫ e₂.inv) ≫ (e₂.hom ≫ b ≫ e₃.inv) = e₁.hom ≫ (a ≫ b) ≫ e₃.inv := by
  simp

/-- The commutation relation satisfied by the composite of two lifts of sheaf maps. -/
theorem comm_comp {C₁ : Type u₂} [Category.{v₂} C₁] {C₂ : Type u₃} [Category.{v₃} C₂]
    {C₃ : Type u₄} [Category.{v₄} C₃] (P₁ : C₁ ⥤ C₂) (P₂ : C₂ ⥤ C₃)
    {A₁ B₁ : C₁} {A₂ B₂ : C₂} {A₃ B₃ : C₃}
    (φ₁ : A₂ ⟶ P₁.obj A₁) (φ₂ : A₃ ⟶ P₂.obj A₂)
    (i₁ : A₁ ⟶ B₁) (i₂ : A₂ ⟶ B₂) (i₃ : A₃ ⟶ B₃)
    (t₂ : B₃ ⟶ P₂.obj B₂) (t₁ : B₂ ⟶ P₁.obj B₁)
    (H₂ : i₃ ≫ t₂ = φ₂ ≫ P₂.map i₂) (H₁ : i₂ ≫ t₁ = φ₁ ≫ P₁.map i₁) :
    i₃ ≫ t₂ ≫ P₂.map t₁ = (φ₂ ≫ P₂.map φ₁) ≫ P₂.map (P₁.map i₁) := by
  rw [← Category.assoc, H₂, Category.assoc, ← Functor.map_comp, H₁, Functor.map_comp,
    ← Category.assoc]

section Derived

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}

/-- The specification of the map on *right-derived evaluation* induced by a map of abelian
sheaves over a continuous map: it is computed from some lift to injective resolutions. -/
def IsDerivedCohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (m : ((sections.{u, u} Y V).rightDerived p).obj G ⟶
      ((sections.{u, u} X U).rightDerived p).obj F) : Prop :=
  ∃ (I : InjectiveResolution G)
    (J : InjectiveResolution F)
    (ψ : I.cocomplex ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J.cocomplex),
    (I.ι.f 0 ≫ ψ.f 0 = φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)) ∧
    m = (I.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
      HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) p ≫
      (J.isoRightDerivedObj (sections.{u, u} X U) p).inv

/-- Postcomposing a lift with the image of a map of target complexes postcomposes the induced
map of section complexes with the image of that map. -/
theorem sectionsComplexMap_comp
    {I : CochainComplex (Y.Sheaf AddCommGrpCat.{u}) ℕ}
    {J J' : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ}
    (ψ : I ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J)
    (β : J ⟶ J') (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    sectionsComplexMap.{u, u} f
        (ψ ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map β)
        V U h =
      sectionsComplexMap.{u, u} f ψ V U h ≫
        ((sections.{u, u} X U).mapHomologicalComplex _).map β := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have hnat : (sections.{u, u} Y V).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (β.f n)) ≫
        (restrictSections.{u, u} f V U h).app (J'.X n) =
      (restrictSections.{u, u} f V U h).app (J.X n) ≫ (sections.{u, u} X U).map (β.f n) :=
    (restrictSections.{u, u} f V U h).naturality (β.f n)
  simp only [sectionsComplexMap, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  rw [Functor.map_comp, Category.assoc, hnat, Category.assoc]

/-- The induced map of section complexes, split into the functorial image of the lift followed
by the restriction to the smaller open. -/
theorem sectionsComplexMap_eq_comp
    {I : CochainComplex (Y.Sheaf AddCommGrpCat.{u}) ℕ}
    {J : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ}
    (ψ : I ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    sectionsComplexMap.{u, u} f ψ V U h =
      ((sections.{u, u} Y V).mapHomologicalComplex _).map ψ ≫
        ((restrictSections.{u, u} f V U h).mapHomologicalComplex _).app J :=
  rfl

/-- Precomposing a lift with a map of source complexes precomposes the induced map of section
complexes with the image of that map. -/
theorem sectionsComplexMap_comp_left
    {I I' : CochainComplex (Y.Sheaf AddCommGrpCat.{u}) ℕ}
    {J : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℕ} (α : I ⟶ I')
    (ψ : I' ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    sectionsComplexMap.{u, u} f (α ≫ ψ) V U h =
      ((sections.{u, u} Y V).mapHomologicalComplex _).map α ≫
        sectionsComplexMap.{u, u} f ψ V U h := by
  rw [sectionsComplexMap_eq_comp, sectionsComplexMap_eq_comp, Functor.map_comp, Category.assoc]

/-- The pushforward of an injective resolution consists of injective objects. -/
private theorem injective_pushforward_cocomplex_X {F : X.Sheaf AddCommGrpCat.{u}}
    (J : InjectiveResolution F) :
    ∀ n, Injective ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex).X n) := fun n =>
  Functor.injective_obj_of_injective (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (J.injective n)

/-- Two injective resolutions of the same object admit a map of cocomplexes compatible with
the augmentations. -/
private theorem exists_hom_of_ι_eq_ι {Z : Y.Sheaf AddCommGrpCat.{u}} (I J : InjectiveResolution Z) :
    ∃ α : I.cocomplex ⟶ J.cocomplex, I.ι.f 0 ≫ α.f 0 = J.ι.f 0 :=
  ⟨InjectiveResolution.desc (𝟙 Z) J I, by
    rw [InjectiveResolution.desc_commutes_zero]; exact Category.id_comp _⟩

/-- The map on right-derived evaluation prescribed by `IsDerivedCohomologyMap` is unique: it
does not depend on the chosen injective resolutions nor on the chosen lift.  This is the
homotopy uniqueness of a lift of an injective resolution into a complex of injective objects,
applied to the pushforward of an injective resolution of the source sheaf. -/
theorem IsDerivedCohomologyMap.eq
    {φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F}
    {V : Opens Y} {U : Opens X} {h : U ≤ (Opens.map f).obj V} {p : ℕ}
    {m₁ m₂ : ((sections.{u, u} Y V).rightDerived p).obj G ⟶
      ((sections.{u, u} X U).rightDerived p).obj F}
    (h₁ : IsDerivedCohomologyMap f φ V U h p m₁)
    (h₂ : IsDerivedCohomologyMap f φ V U h p m₂) : m₁ = m₂ := by
  obtain ⟨I₁, J₁, ψ₁, hψ₁, hm₁⟩ := h₁
  obtain ⟨I₂, J₂, ψ₂, hψ₂, hm₂⟩ := h₂
  have hpi := preservesInjectiveObjects_sheafPushforward f
  have hT := injective_pushforward_cocomplex_X f J₂
  obtain ⟨β, hβ⟩ := exists_hom_of_ι_eq_ι J₁ J₂
  obtain ⟨α, hα⟩ := exists_hom_of_ι_eq_ι I₁ I₂
  have hβ' : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J₁.ι.f 0) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (β.f 0) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J₂.ι.f 0) :=
    (Functor.map_comp _ (J₁.ι.f 0) (β.f 0)).symm.trans
      (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map hβ)
  have hψ₁' : I₁.ι.f 0 ≫
      (ψ₁ ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map β).f 0 =
      φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J₂.ι.f 0) :=
    (Category.assoc (I₁.ι.f 0) (ψ₁.f 0)
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (β.f 0))).symm.trans
      ((congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (β.f 0))
          hψ₁).trans
        ((Category.assoc φ _ _).trans (congrArg (fun t => φ ≫ t) hβ')))
  have hw : I₁.ι ≫ (α ≫ ψ₂) =
      I₁.ι ≫ (ψ₁ ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map
        β) :=
    InjectiveResolution.ι_comp_ext (I := I₁) _ _
      (((Category.assoc (I₁.ι.f 0) (α.f 0) (ψ₂.f 0)).symm.trans
        ((congrArg (fun t => t ≫ ψ₂.f 0) hα).trans hψ₂)).trans hψ₁'.symm)
  have e2 := CategoryTheory.InjectiveResolution.homologyMap_mapHomologicalComplex_map_eq
    (I := I₁) (sections.{u, u} Y V) _ _ hw p
  have e3 : HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f (α ≫ ψ₂) V U h) p =
      HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f
        (ψ₁ ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map β)
        V U h) p := by
    rw [sectionsComplexMap_eq_comp, sectionsComplexMap_eq_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, e2]
  have e4 : HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f (α ≫ ψ₂) V U h) p =
      HomologicalComplex.homologyMap
          (((sections.{u, u} Y V).mapHomologicalComplex (ComplexShape.up ℕ)).map α) p ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p := by
    rw [sectionsComplexMap_comp_left, HomologicalComplex.homologyMap_comp]
  have e5 : HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₁ V U h) p ≫
        HomologicalComplex.homologyMap
          (((sections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℕ)).map β) p =
      HomologicalComplex.homologyMap
          (((sections.{u, u} Y V).mapHomologicalComplex (ComplexShape.up ℕ)).map α) p ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← sectionsComplexMap_comp, ← sectionsComplexMap_comp_left, e3]
  have s1 : (J₁.isoRightDerivedObj (sections.{u, u} X U) p).inv =
      HomologicalComplex.homologyMap
          (((sections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℕ)).map β) p ≫
        (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv :=
    (CategoryTheory.InjectiveResolution.homologyMap_comp_isoRightDerivedObj_inv
      J₁ J₂ β hβ (sections.{u, u} X U) p).symm
  have inner : HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₁ V U h) p ≫
        (J₁.isoRightDerivedObj (sections.{u, u} X U) p).inv =
      HomologicalComplex.homologyMap
          (((sections.{u, u} Y V).mapHomologicalComplex (ComplexShape.up ℕ)).map α) p ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p ≫
        (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv :=
    (congrArg (fun t =>
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₁ V U h) p ≫ t) s1).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv)
          e5)).trans (Category.assoc _ _ _))
  rw [hm₁, hm₂]
  calc (I₁.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₁ V U h) p ≫
        (J₁.isoRightDerivedObj (sections.{u, u} X U) p).inv
      = (I₁.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
        (HomologicalComplex.homologyMap
            (((sections.{u, u} Y V).mapHomologicalComplex (ComplexShape.up ℕ)).map α) p ≫
          HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p ≫
          (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv) :=
        congrArg (fun t => (I₁.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫ t) inner
    _ = ((I₁.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
          HomologicalComplex.homologyMap
            (((sections.{u, u} Y V).mapHomologicalComplex (ComplexShape.up ℕ)).map α) p) ≫
        (HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p ≫
          (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv) := (Category.assoc _ _ _).symm
    _ = (I₂.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ₂ V U h) p ≫
        (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv :=
      congrArg (fun t => t ≫ (HomologicalComplex.homologyMap
            (sectionsComplexMap.{u, u} f ψ₂ V U h) p ≫
          (J₂.isoRightDerivedObj (sections.{u, u} X U) p).inv))
        (CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_comp_homologyMap
          I₁ I₂ α hα (sections.{u, u} Y V) p)

/-- For any choice of injective resolutions of source and target, the map `φ` lifts to a map of
complexes into the pushforward of the target resolution. -/
theorem exists_lift
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (I : InjectiveResolution G) (J : InjectiveResolution F) :
    ∃ ψ : I.cocomplex ⟶
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J.cocomplex,
      I.ι.f 0 ≫ ψ.f 0 = φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0) := by
  have := preservesInjectiveObjects_sheafPushforward f
  have hT := injective_pushforward_cocomplex_X f J
  have hz : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.cocomplex.d 0 1) = 0 := by
    rw [← Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero]
  have hg : (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)) ≫
      ((Functor.mapHomologicalComplex (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
        (ComplexShape.up ℕ)).obj J.cocomplex).d 0 1 = 0 :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => φ ≫ t) hz).trans Limits.comp_zero)
  exact ⟨descToComplex I _ hT _ hg, ι_comp_descToComplex I _ hT _ hg⟩

/-- The specification `IsDerivedCohomologyMap` is satisfiable. -/
theorem exists_isDerivedCohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ) :
    ∃ m, IsDerivedCohomologyMap f φ V U h p m := by
  obtain ⟨ψ, hψ⟩ := exists_lift f φ (InjectiveResolution.of G) (InjectiveResolution.of F)
  exact ⟨_, _, _, ψ, hψ, rfl⟩

/-- The canonical map on right-derived evaluation induced by a map of abelian sheaves over a
continuous map together with a compatible pair of opens. -/
def derivedCohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ) :
    ((sections.{u, u} Y V).rightDerived p).obj G ⟶
      ((sections.{u, u} X U).rightDerived p).obj F :=
  Classical.choose (exists_isDerivedCohomologyMap f φ V U h p)

/-- `derivedCohomologyMap` satisfies its own specification. -/
theorem isDerivedCohomologyMap_derivedCohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ) :
    IsDerivedCohomologyMap f φ V U h p (derivedCohomologyMap f φ V U h p) :=
  Classical.choose_spec (exists_isDerivedCohomologyMap f φ V U h p)

/-- Every map satisfying the specification is `derivedCohomologyMap`. -/
theorem IsDerivedCohomologyMap.eq_derivedCohomologyMap
    {φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F}
    {V : Opens Y} {U : Opens X} {h : U ≤ (Opens.map f).obj V} {p : ℕ}
    {m : ((sections.{u, u} Y V).rightDerived p).obj G ⟶
      ((sections.{u, u} X U).rightDerived p).obj F}
    (hm : IsDerivedCohomologyMap f φ V U h p m) : m = derivedCohomologyMap f φ V U h p :=
  IsDerivedCohomologyMap.eq f hm (isDerivedCohomologyMap_derivedCohomologyMap f φ V U h p)

/-- `IsCohomologyMap` pins its argument down: it holds exactly of the conjugate of
`derivedCohomologyMap` by the given identifications with right-derived evaluation. -/
theorem isCohomologyMap_iff
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G)
    (eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F)
    (m : Sheaf.H'.{u, u, u} G p V ⟶ Sheaf.H'.{u, u, u} F p U) :
    IsCohomologyMap f φ V U h p eG eF m ↔
      m = eG.hom ≫ derivedCohomologyMap f φ V U h p ≫ eF.inv := by
  constructor
  · rintro ⟨I, J, ψ, hψ, hm⟩
    have hd : derivedCohomologyMap f φ V U h p =
        (I.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
          HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) p ≫
          (J.isoRightDerivedObj (sections.{u, u} X U) p).inv :=
      (IsDerivedCohomologyMap.eq_derivedCohomologyMap f ⟨I, J, ψ, hψ, rfl⟩).symm
    rw [hm, hd]
    exact conj_assoc _ _ _ _ _
  · intro hm
    obtain ⟨I, J, ψ, hψ, hd⟩ := isDerivedCohomologyMap_derivedCohomologyMap f φ V U h p
    refine ⟨I, J, ψ, hψ, ?_⟩
    rw [hm, hd]
    exact (conj_assoc _ _ _ _ _).symm

/-- The map on native sheaf cohomology prescribed by `IsCohomologyMap` is unique. -/
theorem IsCohomologyMap.eq
    {φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F}
    {V : Opens Y} {U : Opens X} {h : U ≤ (Opens.map f).obj V} {p : ℕ}
    {eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G}
    {eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F}
    {m₁ m₂ : Sheaf.H'.{u, u, u} G p V ⟶ Sheaf.H'.{u, u, u} F p U}
    (h₁ : IsCohomologyMap f φ V U h p eG eF m₁)
    (h₂ : IsCohomologyMap f φ V U h p eG eF m₂) : m₁ = m₂ :=
  ((isCohomologyMap_iff f φ V U h p eG eF m₁).1 h₁).trans
    ((isCohomologyMap_iff f φ V U h p eG eF m₂).1 h₂).symm

/-- The canonical map on native sheaf cohomology. -/
def cohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G)
    (eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F) :
    Sheaf.H'.{u, u, u} G p V ⟶ Sheaf.H'.{u, u, u} F p U :=
  eG.hom ≫ derivedCohomologyMap f φ V U h p ≫ eF.inv

/-- `cohomologyMap` satisfies `IsCohomologyMap`. -/
theorem isCohomologyMap_cohomologyMap
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G)
    (eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F) :
    IsCohomologyMap f φ V U h p eG eF (cohomologyMap f φ V U h p eG eF) :=
  (isCohomologyMap_iff f φ V U h p eG eF _).2 rfl

/-- Every map satisfying `IsCohomologyMap` is `cohomologyMap`. -/
theorem IsCohomologyMap.eq_cohomologyMap
    {φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F}
    {V : Opens Y} {U : Opens X} {h : U ≤ (Opens.map f).obj V} {p : ℕ}
    {eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G}
    {eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F}
    {m : Sheaf.H'.{u, u, u} G p V ⟶ Sheaf.H'.{u, u, u} F p U}
    (hm : IsCohomologyMap f φ V U h p eG eF m) : m = cohomologyMap f φ V U h p eG eF :=
  (isCohomologyMap_iff f φ V U h p eG eF m).1 hm

/-! ### Functoriality of the canonical map -/

/-- Along the identity map of a space, with the identity map of sheaves, the canonical map on
right-derived evaluation is the identity. -/
theorem isDerivedCohomologyMap_id (U : Opens X) (h : U ≤ (Opens.map (𝟙 X)).obj U) (p : ℕ) :
    IsDerivedCohomologyMap (𝟙 X)
      (𝟙 F : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X)).obj F) U U h p (𝟙 _) := by
  have hR : ((restrictSections.{u, u} (𝟙 X) U U h).mapHomologicalComplex
        (ComplexShape.up ℕ)).app (InjectiveResolution.of F).cocomplex = 𝟙 _ :=
    HomologicalComplex.hom_ext _ _ fun n =>
      CategoryTheory.Functor.map_id ((InjectiveResolution.of F).cocomplex.X n).obj (op U)
  refine ⟨InjectiveResolution.of F, InjectiveResolution.of F,
    𝟙 (InjectiveResolution.of F).cocomplex, (Category.comp_id _).trans
      (Category.id_comp _).symm, ?_⟩
  have hsc : sectionsComplexMap.{u, u} (𝟙 X)
      (𝟙 (InjectiveResolution.of F).cocomplex :
        (InjectiveResolution.of F).cocomplex ⟶
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X)).mapHomologicalComplex _).obj
            (InjectiveResolution.of F).cocomplex) U U h = 𝟙 _ :=
    (sectionsComplexMap_eq_comp (𝟙 X) _ U U h).trans
      ((congrArg (fun t => t ≫ ((restrictSections.{u, u} (𝟙 X) U U h).mapHomologicalComplex
              (ComplexShape.up ℕ)).app (InjectiveResolution.of F).cocomplex)
          (CategoryTheory.Functor.map_id
            ((sections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℕ))
            (InjectiveResolution.of F).cocomplex)).trans
        ((Category.id_comp _).trans hR))
  rw [hsc, HomologicalComplex.homologyMap_id]
  exact (conj_id _).symm

/-- Along the identity map of a space, with the identity map of sheaves, the canonical map on
right-derived evaluation is the identity. -/
theorem derivedCohomologyMap_id (U : Opens X) (h : U ≤ (Opens.map (𝟙 X)).obj U) (p : ℕ) :
    derivedCohomologyMap (𝟙 X)
        (𝟙 F : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (𝟙 X)).obj F) U U h p = 𝟙 _ :=
  (IsDerivedCohomologyMap.eq_derivedCohomologyMap (𝟙 X)
    (isDerivedCohomologyMap_id U h p)).symm

end Derived

section Comp

variable {X₁ X₂ X₃ : TopCat.{u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
  {F₁ : X₁.Sheaf AddCommGrpCat.{u}} {F₂ : X₂.Sheaf AddCommGrpCat.{u}}
  {F₃ : X₃.Sheaf AddCommGrpCat.{u}}

/-- Restriction to an open along a composite factors through restriction along each factor. -/
theorem restrictSections_app_comp
    (U₃ : Opens X₃) (U₂ : Opens X₂) (U₁ : Opens X₁)
    (h₂ : U₂ ≤ (Opens.map f₂).obj U₃) (h₁ : U₁ ≤ (Opens.map f₁).obj U₂)
    (h₃ : U₁ ≤ (Opens.map (f₁ ≫ f₂)).obj U₃) (W : X₁.Sheaf AddCommGrpCat.{u}) :
    (restrictSections.{u, u} f₂ U₃ U₂ h₂).app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₁).obj W) ≫
        (restrictSections.{u, u} f₁ U₂ U₁ h₁).app W =
      (restrictSections.{u, u} (f₁ ≫ f₂) U₃ U₁ h₃).app W := by
  have hopens : (homOfLE h₁ : U₁ ⟶ (Opens.map f₁).obj U₂) ≫
      (Opens.map f₁).map (homOfLE h₂) = homOfLE h₃ := Subsingleton.elim _ _
  show W.obj.map ((Opens.map f₁).map (homOfLE h₂)).op ≫ W.obj.map (homOfLE h₁).op =
    W.obj.map (homOfLE h₃).op
  rw [← Functor.map_comp, ← op_comp, hopens]
  exact rfl

/-- The map of section complexes induced by the composite of two lifts. -/
theorem sectionsComplexMap_comp_comp
    {K₃ : CochainComplex (X₃.Sheaf AddCommGrpCat.{u}) ℕ}
    {K₂ : CochainComplex (X₂.Sheaf AddCommGrpCat.{u}) ℕ}
    {K₁ : CochainComplex (X₁.Sheaf AddCommGrpCat.{u}) ℕ}
    (ψ₂ : K₃ ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).mapHomologicalComplex _).obj K₂)
    (ψ₁ : K₂ ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₁).mapHomologicalComplex _).obj K₁)
    (ψ₃ : K₃ ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f₁ ≫ f₂)).mapHomologicalComplex _).obj K₁)
    (hψ₃ : ∀ n, ψ₃.f n =
      ψ₂.f n ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).map (ψ₁.f n))
    (U₃ : Opens X₃) (U₂ : Opens X₂) (U₁ : Opens X₁)
    (h₂ : U₂ ≤ (Opens.map f₂).obj U₃) (h₁ : U₁ ≤ (Opens.map f₁).obj U₂)
    (h₃ : U₁ ≤ (Opens.map (f₁ ≫ f₂)).obj U₃) :
    sectionsComplexMap.{u, u} (f₁ ≫ f₂) ψ₃ U₃ U₁ h₃ =
      sectionsComplexMap.{u, u} f₂ ψ₂ U₃ U₂ h₂ ≫ sectionsComplexMap.{u, u} f₁ ψ₁ U₂ U₁ h₁ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have hnat : (sections.{u, u} X₃ U₃).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).map (ψ₁.f n)) ≫
      (restrictSections.{u, u} f₂ U₃ U₂ h₂).app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₁).obj (K₁.X n)) ≫
        (restrictSections.{u, u} f₁ U₂ U₁ h₁).app (K₁.X n) =
      (restrictSections.{u, u} f₂ U₃ U₂ h₂).app (K₂.X n) ≫
        (sections.{u, u} X₂ U₂).map (ψ₁.f n) ≫
          (restrictSections.{u, u} f₁ U₂ U₁ h₁).app (K₁.X n) :=
    (restrictSections.{u, u} f₂ U₃ U₂ h₂).naturality_assoc (ψ₁.f n)
      ((restrictSections.{u, u} f₁ U₂ U₁ h₁).app (K₁.X n))
  have step1 : (sections.{u, u} X₃ U₃).map (ψ₃.f n) =
      (sections.{u, u} X₃ U₃).map (ψ₂.f n) ≫
        (sections.{u, u} X₃ U₃).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).map (ψ₁.f n)) :=
    (congrArg (sections.{u, u} X₃ U₃).map (hψ₃ n)).trans
      (CategoryTheory.Functor.map_comp _ _ _)
  simp only [sectionsComplexMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
  rw [step1, ← restrictSections_app_comp f₁ f₂ U₃ U₂ U₁ h₂ h₁ h₃]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t => (sections.{u, u} X₃ U₃).map (ψ₂.f n) ≫ t) hnat)

/-- The canonical map on right-derived evaluation is compatible with composition. -/
theorem derivedCohomologyMap_comp
    (φ₁ : F₂ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₁).obj F₁)
    (φ₂ : F₃ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).obj F₂)
    (U₃ : Opens X₃) (U₂ : Opens X₂) (U₁ : Opens X₁)
    (h₂ : U₂ ≤ (Opens.map f₂).obj U₃) (h₁ : U₁ ≤ (Opens.map f₁).obj U₂)
    (h₃ : U₁ ≤ (Opens.map (f₁ ≫ f₂)).obj U₃) (p : ℕ) :
    derivedCohomologyMap (f₁ ≫ f₂)
        (show F₃ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f₁ ≫ f₂)).obj F₁ from
          φ₂ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).map φ₁) U₃ U₁ h₃ p =
      derivedCohomologyMap f₂ φ₂ U₃ U₂ h₂ p ≫ derivedCohomologyMap f₁ φ₁ U₂ U₁ h₁ p := by
  obtain ⟨ψ₂, hψ₂⟩ := exists_lift f₂ φ₂ (InjectiveResolution.of F₃) (InjectiveResolution.of F₂)
  obtain ⟨ψ₁, hψ₁⟩ := exists_lift f₁ φ₁ (InjectiveResolution.of F₂) (InjectiveResolution.of F₁)
  obtain ⟨ψ₃, hψ₃, hscm⟩ : ∃ ψ₃ : (InjectiveResolution.of F₃).cocomplex ⟶
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f₁ ≫ f₂)).mapHomologicalComplex _).obj
          (InjectiveResolution.of F₁).cocomplex,
      ((InjectiveResolution.of F₃).ι.f 0 ≫ ψ₃.f 0 =
          (show F₃ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f₁ ≫ f₂)).obj F₁ from
            φ₂ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).map φ₁) ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f₁ ≫ f₂)).map
              ((InjectiveResolution.of F₁).ι.f 0)) ∧
        sectionsComplexMap.{u, u} (f₁ ≫ f₂) ψ₃ U₃ U₁ h₃ =
          sectionsComplexMap.{u, u} f₂ ψ₂ U₃ U₂ h₂ ≫
            sectionsComplexMap.{u, u} f₁ ψ₁ U₂ U₁ h₁ :=
    ⟨ψ₂ ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂).mapHomologicalComplex _).map ψ₁,
      comm_comp (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₁)
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f₂) φ₁ φ₂
        ((InjectiveResolution.of F₁).ι.f 0) ((InjectiveResolution.of F₂).ι.f 0)
        ((InjectiveResolution.of F₃).ι.f 0) (ψ₂.f 0) (ψ₁.f 0) hψ₂ hψ₁,
      sectionsComplexMap_comp_comp f₁ f₂ ψ₂ ψ₁ _ (fun _ => rfl) U₃ U₂ U₁ h₂ h₁ h₃⟩
  have hT : HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} (f₁ ≫ f₂) ψ₃ U₃ U₁ h₃) p =
      HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f₂ ψ₂ U₃ U₂ h₂) p ≫
        HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f₁ ψ₁ U₂ U₁ h₁) p := by
    rw [hscm, HomologicalComplex.homologyMap_comp]
  rw [IsDerivedCohomologyMap.eq_derivedCohomologyMap (f₁ ≫ f₂)
      (⟨InjectiveResolution.of F₃, InjectiveResolution.of F₁, ψ₃, hψ₃, rfl⟩ :
        IsDerivedCohomologyMap (f₁ ≫ f₂) _ U₃ U₁ h₃ p _) |>.symm,
    IsDerivedCohomologyMap.eq_derivedCohomologyMap f₂
      (⟨InjectiveResolution.of F₃, InjectiveResolution.of F₂, ψ₂, hψ₂, rfl⟩ :
        IsDerivedCohomologyMap f₂ φ₂ U₃ U₂ h₂ p _) |>.symm,
    IsDerivedCohomologyMap.eq_derivedCohomologyMap f₁
      (⟨InjectiveResolution.of F₂, InjectiveResolution.of F₁, ψ₁, hψ₁, rfl⟩ :
        IsDerivedCohomologyMap f₁ φ₁ U₂ U₁ h₁ p _) |>.symm]
  exact (congrArg (fun t =>
      ((InjectiveResolution.of F₃).isoRightDerivedObj (sections.{u, u} X₃ U₃) p).hom ≫ t ≫
        ((InjectiveResolution.of F₁).isoRightDerivedObj (sections.{u, u} X₁ U₁) p).inv)
    hT).trans (conj_comp _ _ _ _ _).symm

end Comp

/-! ### The canonical map for a morphism of abelian sheafed spaces -/

section Spaces

/-- Conjugation by identity isomorphisms. -/
theorem refl_conj {C : Type u₂} [Category.{v₂} C] {A B : C} (x : A ⟶ B) :
    (Iso.refl A).inv ≫ x ≫ (Iso.refl B).hom = x := by
  simp

/-- Precomposition with the inverse of an identity isomorphism. -/
theorem refl_comp {C : Type u₂} [Category.{v₂} C] {A B : C} (x : A ⟶ B) :
    (Iso.refl A).inv ≫ x = x := by
  simp

/-- The canonical map on native sheaf cohomology induced by a morphism of abelian sheafed
spaces, a compatible pair of opens, and identifications with right-derived evaluation. -/
def spaceCohomologyMap {W Z : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (g : W ⟶ Z)
    (V : Opens Z) (U : Opens W) (h : U ≤ (Opens.map g.hom.base).obj V) (p : ℕ)
    (eZ : Sheaf.H'.{u, u, u} Z.sheaf p V ≅
      ((sections.{u, u} Z V).rightDerived p).obj Z.sheaf)
    (eW : Sheaf.H'.{u, u, u} W.sheaf p U ≅
      ((sections.{u, u} W U).rightDerived p).obj W.sheaf) :
    Sheaf.H'.{u, u, u} Z.sheaf p V ⟶ Sheaf.H'.{u, u, u} W.sheaf p U :=
  cohomologyMap g.hom.base (sheafMap g) V U h p eZ eW

/-- `spaceCohomologyMap` satisfies the specification `IsCohomologyMap` of Tag 0A37. -/
theorem isCohomologyMap_spaceCohomologyMap
    {W Z : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (g : W ⟶ Z)
    (V : Opens Z) (U : Opens W) (h : U ≤ (Opens.map g.hom.base).obj V) (p : ℕ)
    (eZ : Sheaf.H'.{u, u, u} Z.sheaf p V ≅
      ((sections.{u, u} Z V).rightDerived p).obj Z.sheaf)
    (eW : Sheaf.H'.{u, u, u} W.sheaf p U ≅
      ((sections.{u, u} W U).rightDerived p).obj W.sheaf) :
    IsCohomologyMap g.hom.base (sheafMap g) V U h p eZ eW
      (spaceCohomologyMap g V U h p eZ eW) :=
  isCohomologyMap_cohomologyMap g.hom.base (sheafMap g) V U h p eZ eW

/-- The canonical map depends on the morphism of sheafed spaces only through its value, so
equal morphisms induce the same map. -/
theorem spaceCohomologyMap_congr {W Z : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {g g' : W ⟶ Z}
    (hg : g = g') (V : Opens Z) (U : Opens W)
    (h : U ≤ (Opens.map g.hom.base).obj V) (h' : U ≤ (Opens.map g'.hom.base).obj V) (p : ℕ)
    (eZ : Sheaf.H'.{u, u, u} Z.sheaf p V ≅
      ((sections.{u, u} Z V).rightDerived p).obj Z.sheaf)
    (eW : Sheaf.H'.{u, u, u} W.sheaf p U ≅
      ((sections.{u, u} W U).rightDerived p).obj W.sheaf) :
    spaceCohomologyMap g V U h p eZ eW = spaceCohomologyMap g' V U h' p eZ eW := by
  subst hg
  rfl

/-- The canonical map along an identity morphism of sheafed spaces is the identity. -/
theorem spaceCohomologyMap_id {W : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (V : Opens W)
    (h : V ≤ (Opens.map (𝟙 W : W ⟶ W).hom.base).obj V) (p : ℕ)
    (e : Sheaf.H'.{u, u, u} W.sheaf p V ≅
      ((sections.{u, u} W V).rightDerived p).obj W.sheaf) :
    spaceCohomologyMap (𝟙 W) V V h p e e = 𝟙 _ :=
  (congrArg (fun t => e.hom ≫ t ≫ e.inv) (derivedCohomologyMap_id V h p)).trans (conj_id e)

/-- The canonical map is compatible with composition of morphisms of sheafed spaces. -/
theorem spaceCohomologyMap_comp {W₁ W₂ W₃ : SheafedSpace.{_, _, u} AddCommGrpCat.{u}}
    (g₁ : W₁ ⟶ W₂) (g₂ : W₂ ⟶ W₃)
    (U₃ : Opens W₃) (U₂ : Opens W₂) (U₁ : Opens W₁)
    (h₂ : U₂ ≤ (Opens.map g₂.hom.base).obj U₃) (h₁ : U₁ ≤ (Opens.map g₁.hom.base).obj U₂)
    (h₃ : U₁ ≤ (Opens.map (g₁ ≫ g₂).hom.base).obj U₃) (p : ℕ)
    (e₃ : Sheaf.H'.{u, u, u} W₃.sheaf p U₃ ≅
      ((sections.{u, u} W₃ U₃).rightDerived p).obj W₃.sheaf)
    (e₂ : Sheaf.H'.{u, u, u} W₂.sheaf p U₂ ≅
      ((sections.{u, u} W₂ U₂).rightDerived p).obj W₂.sheaf)
    (e₁ : Sheaf.H'.{u, u, u} W₁.sheaf p U₁ ≅
      ((sections.{u, u} W₁ U₁).rightDerived p).obj W₁.sheaf) :
    spaceCohomologyMap (g₁ ≫ g₂) U₃ U₁ h₃ p e₃ e₁ =
      spaceCohomologyMap g₂ U₃ U₂ h₂ p e₃ e₂ ≫ spaceCohomologyMap g₁ U₂ U₁ h₁ p e₂ e₁ :=
  (congrArg (fun t => e₃.hom ≫ t ≫ e₁.inv)
    (derivedCohomologyMap_comp g₁.hom.base g₂.hom.base (sheafMap g₁) (sheafMap g₂)
      U₃ U₂ U₁ h₂ h₁ h₃ p)).trans (conj_comp e₃ e₂ e₁ _ _).symm

end Spaces

/-! ### The cohomology diagram and the comparison cocone -/

section Cocone

variable {K : Type v} [Category.{v'} K] (E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u})
  (c : Cone E) (O : OpenCone E c) (p : ℕ)
  (e : ∀ k : K, Sheaf.H'.{u, u, u} (E.obj k).sheaf p (O.obj k) ≅
    ((sections.{u, u} (E.obj k) (O.obj k)).rightDerived p).obj (E.obj k).sheaf)

/-- The diagram of sheaf cohomology groups of a compatible system of opens, with the canonical
maps of Tag 0A37 as its arrows.  Functoriality is exactly the uniqueness of those maps. -/
def cohomologyDiagram : Kᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj A := Sheaf.H'.{u, u, u} (E.obj A.unop).sheaf p (O.obj A.unop)
  map {A B} a := spaceCohomologyMap (E.map a.unop) (O.obj A.unop) (O.obj B.unop)
    (O.map_le a.unop) p (e A.unop) (e B.unop)
  map_id A :=
    (spaceCohomologyMap_congr (E.map_id A.unop) (O.obj A.unop) (O.obj A.unop)
        (O.map_le (𝟙 A.unop)) (le_refl _) p (e A.unop) (e A.unop)).trans
      (spaceCohomologyMap_id (O.obj A.unop) (le_refl _) p (e A.unop))
  map_comp {A B C} a b := by
    have h₃ : O.obj C.unop ≤
        (Opens.map (E.map b.unop ≫ E.map a.unop).hom.base).obj (O.obj A.unop) := by
      rw [← E.map_comp]
      exact O.map_le (b.unop ≫ a.unop)
    exact (spaceCohomologyMap_congr (E.map_comp b.unop a.unop) (O.obj A.unop) (O.obj C.unop)
        (O.map_le (b.unop ≫ a.unop)) h₃ p (e A.unop) (e C.unop)).trans
      (spaceCohomologyMap_comp (E.map b.unop) (E.map a.unop) (O.obj A.unop) (O.obj B.unop)
        (O.obj C.unop) (O.map_le a.unop) (O.map_le b.unop) h₃ p (e A.unop) (e B.unop)
        (e C.unop))

/-- The comparison cocone on `cohomologyDiagram`, with legs the canonical maps attached to the
projections of the cone. -/
def cohomologyDiagramIota
    (e' : Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt ≅
      ((sections.{u, u} c.pt O.pt).rightDerived p).obj c.pt.sheaf) :
    cohomologyDiagram E c O p e ⟶
      (Functor.const Kᵒᵖ).obj (Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt) where
  app A := spaceCohomologyMap (c.π.app A.unop) (O.obj A.unop) O.pt (O.leg_le A.unop) p
    (e A.unop) e'
  naturality {A B} a := by
    have h₃ : O.pt ≤
        (Opens.map (c.π.app B.unop ≫ E.map a.unop).hom.base).obj (O.obj A.unop) := by
      rw [c.w a.unop]
      exact O.leg_le A.unop
    exact ((spaceCohomologyMap_comp (c.π.app B.unop) (E.map a.unop) (O.obj A.unop)
          (O.obj B.unop) O.pt (O.map_le a.unop) (O.leg_le B.unop) h₃ p (e A.unop) (e B.unop)
          e').symm.trans
        (spaceCohomologyMap_congr (c.w a.unop) (O.obj A.unop) O.pt h₃ (O.leg_le A.unop) p
          (e A.unop) e')).trans (Category.comp_id _).symm

/-- Given identifications of the stage and vertex sheaf cohomology with right-derived
evaluation, the arrows prescribed by Tag 0A37 assemble into a `CohomologyCocone`; the identity
and composition laws come from the uniqueness of the prescribed maps. -/
def cohomologyCocone
    (e' : Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt ≅
      ((sections.{u, u} c.pt O.pt).rightDerived p).obj c.pt.sheaf) :
    CohomologyCocone E c O p where
  diagram := cohomologyDiagram E c O p e
  objIso _ := Iso.refl _
  objDerivedIso := e
  vertexDerivedIso := e'
  map_eq _ := (isCohomologyMap_iff _ _ _ _ _ _ _ _ _).2 (refl_conj _)
  ι := cohomologyDiagramIota E c O p e e'
  ι_eq _ := (isCohomologyMap_iff _ _ _ _ _ _ _ _ _).2 (refl_comp _)

end Cocone

end Stacks.Cohomology.SpectralLimit

end
