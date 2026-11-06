module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.ElementSiteExtensionByZero

/-!
# Restriction of modules along an étale morphism of algebraic spaces preserves injectives

Let `i : X' ⟶ X` be an étale morphism of algebraic spaces. The small étale site of `X'` is
equivalent to the site of elements of the presheaf of sets on the small étale site of `X`
represented by `i`, and under this equivalence restriction of `𝒪_X`-modules along `i` is
restriction along the projection of the site of elements. Hence it carries injective
`𝒪_X`-modules to injective `𝒪_{X'}`-modules.

## Main definitions

* `AlgebraicGeometry.Space.etaleChartPresheaf`: the presheaf of sets on the small étale site of
  `X` represented by `i : X' ⟶ X`.
* `AlgebraicGeometry.Space.smallEtaleToElements`: the comparison functor from the small étale
  site of `X'` to the site of elements of `etaleChartPresheaf`.
* `AlgebraicGeometry.Space.smallEtaleElementsEquivalence`: the comparison functor as an
  equivalence of categories.
* `AlgebraicGeometry.Space.elementsRestriction`: restriction of `𝒪_X`-modules to the site of
  elements.
* `AlgebraicGeometry.Space.elementsModuleEquivalence`: the modules on the site of elements are
  the `𝒪_{X'}`-modules.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_elementsRestriction`: restriction of
  `𝒪_X`-modules to the site of elements preserves injective objects.
* `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`: pullback of
  `𝒪_X`-modules along an étale morphism of algebraic spaces preserves injective objects.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03DH](https://stacks.math.columbia.edu/tag/03DH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (i : X' ⟶ X)

/-- The sections over an étale chart `W` of `X` of the presheaf of sets represented by
`i : X' ⟶ X`: the `W`-points of `X'` lying over the structure morphism of `W`. -/
abbrev EtaleChartSections (W : (SmallEtale B S hS X.1)ᵒᵖ) : Type u :=
  {s : X'.1.obj (op ((SmallEtale.toOver B S hS X.1).obj W.unop)) //
    i.hom.app _ s = yonedaEquiv W.unop.1.hom}

/-- Restriction of a point of `X'` over `X` along a morphism of étale charts of `X`. -/
def etaleChartPointRestrict {W W' : (SmallEtale B S hS X.1)ᵒᵖ} (f : W ⟶ W')
    (s : EtaleChartSections B S hS i W) : EtaleChartSections B S hS i W' :=
  ⟨X'.1.map ((SmallEtale.toOver B S hS X.1).map f.unop).op s.1, by
    rw [NatTrans.naturality_apply, s.2, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv (CostructuredArrow.w f.unop.hom)⟩

/-- The presheaf of sets on the small étale site of `X` represented by a morphism
`i : X' ⟶ X`. -/
def etaleChartPresheaf : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u where
  obj W := EtaleChartSections B S hS i W
  map f := ↾(etaleChartPointRestrict B S hS i f)
  map_id W := by
    ext s
    simp [etaleChartPointRestrict]
  map_comp f g := by
    ext s
    simp [etaleChartPointRestrict]

/-- The sections of `etaleChartPresheaf` restrict by restricting the underlying point. -/
@[simp]
theorem etaleChartPresheaf_map_coe {W W' : (SmallEtale B S hS X.1)ᵒᵖ} (f : W ⟶ W')
    (s : EtaleChartSections B S hS i W) :
    (((etaleChartPresheaf B S hS i).map f) s).1 =
      X'.1.map ((SmallEtale.toOver B S hS X.1).map f.unop).op s.1 := rfl

/-- The comparison functor from the small étale site of `X'` to the site of elements of the
presheaf of sets represented by `i : X' ⟶ X`: an étale chart `U ⟶ X'` is sent to the étale
chart `U ⟶ X` of `X` together with the point of `X'` that it is. -/
def smallEtaleToElements (hi : IsEtale B S hS i.hom) :
    SmallEtale B S hS X'.1 ⥤ ((etaleChartPresheaf B S hS i).Elements)ᵒᵖ where
  obj A := op ((etaleChartPresheaf B S hS i).elementsMk (op ((smallEtalePostcomp B S hS i hi).obj A))
    ⟨yonedaEquiv A.1.hom, rfl⟩)
  map {A A'} g := Quiver.Hom.op (Functor.Elements.homMk
    ((smallEtalePostcomp B S hS i hi).map g).op
    (Subtype.ext (by
      rw [etaleChartPresheaf_map_coe]
      change X'.1.map ((SmallEtale.toOver B S hS X'.1).map g).op (yonedaEquiv A'.1.hom) =
        yonedaEquiv A.1.hom
      rw [yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (CostructuredArrow.w g.hom))))
  map_id A := by
    refine Quiver.Hom.unop_inj (Functor.Elements.hom_ext ?_)
    exact congrArg Quiver.Hom.op ((smallEtalePostcomp B S hS i hi).map_id A)
  map_comp {A A' A''} g g' := by
    refine Quiver.Hom.unop_inj (Functor.Elements.hom_ext ?_)
    exact congrArg Quiver.Hom.op ((smallEtalePostcomp B S hS i hi).map_comp g g')

/-- The comparison functor followed by the projection of the site of elements is
postcomposition with `i`. -/
theorem smallEtaleToElements_comp_proj (hi : IsEtale B S hS i.hom) :
    smallEtaleToElements B S hS i hi ⋙
        Stacks.Sites.ExtensionByZero.OverElements.proj (etaleChartPresheaf B S hS i) =
      smallEtalePostcomp B S hS i hi := rfl

/-- The comparison functor to the site of elements is faithful. -/
instance smallEtaleToElements_faithful (hi : IsEtale B S hS i.hom) :
    (smallEtaleToElements B S hS i hi).Faithful := by
  have h : (smallEtaleToElements B S hS i hi ⋙
      (Stacks.Sites.ExtensionByZero.OverElements.proj (etaleChartPresheaf B S hS i) ⋙
        SmallEtale.toOver B S hS X.1)).Faithful := by
    change (SmallEtale.toOver B S hS X'.1).Faithful
    infer_instance
  exact Functor.Faithful.of_comp (smallEtaleToElements B S hS i hi)
    (Stacks.Sites.ExtensionByZero.OverElements.proj (etaleChartPresheaf B S hS i) ⋙
      SmallEtale.toOver B S hS X.1)

/-- The comparison functor to the site of elements is full. -/
instance smallEtaleToElements_full (hi : IsEtale B S hS i.hom) :
    (smallEtaleToElements B S hS i hi).Full where
  map_surjective {A A'} φ := by
    obtain ⟨⟨f, hf⟩⟩ := φ
    have hcompat : yoneda.map ((SmallEtale.toOver B S hS X.1).map f.unop) ≫ A'.1.hom =
        A.1.hom :=
      yonedaEquiv.injective
        ((yonedaEquiv_naturality _ _).symm.trans (congrArg Subtype.val hf))
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk
      ((SmallEtale.toOver B S hS X.1).map f.unop) hcompat),
      Quiver.Hom.unop_inj (Functor.Elements.hom_ext ?_)⟩
    exact congrArg Quiver.Hom.op ((SmallEtale.toOver B S hS X.1).map_injective rfl)

/-- Every object of the site of elements of `etaleChartPresheaf` is isomorphic to the image of
an étale chart of `X'` under the comparison functor: a point `s` of `X'` over an étale chart
`W` of `X` is an étale chart `W ⟶ X'` of `X'`. -/
theorem exists_iso_smallEtaleToElements (hi : IsEtale B S hS i.hom)
    (W : SmallEtale B S hS X.1) (s : EtaleChartSections B S hS i (op W)) :
    ∃ A : SmallEtale B S hS X'.1,
      Nonempty ((smallEtaleToElements B S hS i hi).obj A ≅
        op ((etaleChartPresheaf B S hS i).elementsMk (op W) s)) := by
  have ht : yonedaEquiv.symm s.1 ≫ i.hom = W.1.hom :=
    yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply]; exact s.2)
  have hA : IsEtaleChart B S hS X'.1 (CostructuredArrow.mk (yonedaEquiv.symm s.1)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_of_isEtale_over B S hS
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj W)) X'.2 X.2
        _ W.1.hom i.hom ((isEtale_iff_presheaf_of_yoneda B S hS W.1.hom).2 W.2) hi ht)
  refine ⟨⟨CostructuredArrow.mk (yonedaEquiv.symm s.1), hA⟩, ⟨Iso.op ?_⟩⟩
  refine
    { hom := Functor.Elements.homMk
        (Quiver.Hom.op (ObjectProperty.homMk (CostructuredArrow.homMk
          (𝟙 ((SmallEtale.toOver B S hS X.1).obj W))
          (by
            show yoneda.map (𝟙 _) ≫ W.1.hom = yonedaEquiv.symm s.1 ≫ i.hom
            rw [ht]
            simp))))
        (Subtype.ext rfl)
      inv := Functor.Elements.homMk
        (Quiver.Hom.op (ObjectProperty.homMk (CostructuredArrow.homMk
          (𝟙 ((SmallEtale.toOver B S hS X.1).obj W))
          (by
            show yoneda.map (𝟙 _) ≫ (yonedaEquiv.symm s.1 ≫ i.hom) = W.1.hom
            rw [ht]
            simp))))
        (Subtype.ext (by
          show X'.1.map (𝟙 ((SmallEtale.toOver B S hS X.1).obj W)).op
            (yonedaEquiv (yonedaEquiv.symm s.1)) = s.1
          rw [Equiv.apply_symm_apply]
          simp))
      hom_inv_id := Functor.Elements.hom_ext (congrArg Quiver.Hom.op
        ((SmallEtale.toOver B S hS X.1).map_injective (Category.id_comp _)))
      inv_hom_id := Functor.Elements.hom_ext (congrArg Quiver.Hom.op
        ((SmallEtale.toOver B S hS X.1).map_injective (Category.id_comp _))) }

/-- The comparison functor to the site of elements is essentially surjective. -/
instance smallEtaleToElements_essSurj (hi : IsEtale B S hS i.hom) :
    (smallEtaleToElements B S hS i hi).EssSurj where
  mem_essImage Z := by
    obtain ⟨@⟨⟨W⟩, s⟩⟩ := Z
    exact exists_iso_smallEtaleToElements B S hS i hi W s

/-- The comparison functor to the site of elements is an equivalence of categories. -/
instance smallEtaleToElements_isEquivalence (hi : IsEtale B S hS i.hom) :
    (smallEtaleToElements B S hS i hi).IsEquivalence where

section Injectives

open Stacks.Sites.ExtensionByZero.OverElements

/-- The small étale site of `X'` is equivalent to the site of elements of the presheaf of sets
represented by an étale `i : X' ⟶ X`. -/
noncomputable def smallEtaleElementsEquivalence (hi : IsEtale B S hS i.hom) :
    SmallEtale B S hS X'.1 ≌ ((etaleChartPresheaf B S hS i).Elements)ᵒᵖ :=
  (smallEtaleToElements B S hS i hi).asEquivalence

/-- The topology on the site of elements transported from the small étale topology of `X'`. -/
noncomputable abbrev etaleChartElementsTopology (hi : IsEtale B S hS i.hom) :
    GrothendieckTopology ((etaleChartPresheaf B S hS i).Elements)ᵒᵖ :=
  (smallEtaleElementsEquivalence B S hS i hi).inverse.inducedTopology
    (SmallEtale.topology B S hS X'.1)

/-- The site of elements of `etaleChartPresheaf` is essentially small. -/
theorem etaleChartElements_essentiallySmall (hi : IsEtale B S hS i.hom) :
    EssentiallySmall.{u} (((etaleChartPresheaf B S hS i).Elements)ᵒᵖ) :=
  (essentiallySmall_congr (smallEtaleElementsEquivalence B S hS i hi)).1 inferInstance

/-- The projection of the site of elements to the small étale site of `X` is continuous. -/
instance proj_isContinuous (hi : IsEtale B S hS i.hom) :
    (proj (etaleChartPresheaf B S hS i)).IsContinuous
      (etaleChartElementsTopology B S hS i hi) (SmallEtale.topology B S hS X.1) := by
  have hpost : ((smallEtaleElementsEquivalence B S hS i hi).functor ⋙
      proj (etaleChartPresheaf B S hS i)).IsContinuous
      (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1) := by
    change (smallEtalePostcomp B S hS i hi).IsContinuous _ _
    infer_instance
  have h : ((smallEtaleElementsEquivalence B S hS i hi).inverse ⋙
      ((smallEtaleElementsEquivalence B S hS i hi).functor ⋙
        proj (etaleChartPresheaf B S hS i))).IsContinuous
      (etaleChartElementsTopology B S hS i hi) (SmallEtale.topology B S hS X.1) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS X'.1) _
  exact Functor.isContinuous_of_iso
    ((Functor.associator (smallEtaleElementsEquivalence B S hS i hi).inverse
          (smallEtaleElementsEquivalence B S hS i hi).functor
          (proj (etaleChartPresheaf B S hS i))).symm ≪≫
      Functor.isoWhiskerRight (smallEtaleElementsEquivalence B S hS i hi).counitIso
        (proj (etaleChartPresheaf B S hS i)) ≪≫
      (proj (etaleChartPresheaf B S hS i)).leftUnitor) _ _

/-- The projection of the site of elements to the small étale site of `X` is continuous, for
the topology of `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance smallEtaleRingedSite_isContinuous_proj (hi : IsEtale B S hS i.hom) :
    (proj (etaleChartPresheaf B S hS i)).IsContinuous
      (etaleChartElementsTopology B S hS i hi)
      (smallEtaleRingedSite B S hS X.1 X.2).J := by
  change (proj (etaleChartPresheaf B S hS i)).IsContinuous _ (SmallEtale.topology B S hS X.1)
  infer_instance

/-- The comparison functor to the site of elements is continuous, for the topology of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance smallEtaleRingedSite_isContinuous_elementsFunctor (hi : IsEtale B S hS i.hom) :
    (smallEtaleElementsEquivalence B S hS i hi).functor.IsContinuous
      (smallEtaleRingedSite B S hS X'.1 X'.2).J
      (etaleChartElementsTopology B S hS i hi) := by
  change (smallEtaleElementsEquivalence B S hS i hi).functor.IsContinuous
    (SmallEtale.topology B S hS X'.1) _
  infer_instance

/-- The inverse of the comparison functor to the site of elements is continuous, for the
topology of `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance smallEtaleRingedSite_isContinuous_elementsInverse (hi : IsEtale B S hS i.hom) :
    (smallEtaleElementsEquivalence B S hS i hi).inverse.IsContinuous
      (etaleChartElementsTopology B S hS i hi)
      (smallEtaleRingedSite B S hS X'.1 X'.2).J := by
  change (smallEtaleElementsEquivalence B S hS i hi).inverse.IsContinuous
    _ (SmallEtale.topology B S hS X'.1)
  infer_instance

/-- The structure sheaf of the site of elements: the restriction of `𝒪_X` along the projection
of the site of elements. -/
noncomputable abbrev elementsRingSheaf (hi : IsEtale B S hS i.hom) :
    Sheaf (etaleChartElementsTopology B S hS i hi) RingCat.{u} :=
  restrictedRingSheaf (etaleChartPresheaf B S hS i) (SmallEtale.topology B S hS X.1)
    (etaleChartElementsTopology B S hS i hi)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- Restriction of `𝒪_X`-modules to the site of elements of the presheaf of sets represented by
`i`: the functor `j_K^{-1}` for `K = etaleChartPresheaf`. -/
noncomputable abbrev elementsRestriction (hi : IsEtale B S hS i.hom) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (elementsRingSheaf B S hS i hi) :=
  SheafOfModules.pushforward.{u} (F := proj (etaleChartPresheaf B S hS i))
    (𝟙 (elementsRingSheaf B S hS i hi) :
      elementsRingSheaf B S hS i hi ⟶ elementsRingSheaf B S hS i hi)

/-- Restriction of `𝒪_X`-modules to the site of elements of the presheaf of sets represented by
`i` preserves injective objects. -/
theorem preservesInjectiveObjects_elementsRestriction (hi : IsEtale B S hS i.hom) :
    (elementsRestriction B S hS i hi).PreservesInjectiveObjects :=
  have := etaleChartElements_essentiallySmall B S hS i hi
  preservesInjectiveObjects_pushforward_proj (etaleChartPresheaf B S hS i)
    (SmallEtale.topology B S hS X.1) (etaleChartElementsTopology B S hS i hi)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- The `𝒪_X`-modules on the site of elements are the `𝒪_{X'}`-modules on the small étale site
of `X'`, by reindexing along the equivalence of sites. -/
noncomputable def elementsModuleEquivalence (hi : IsEtale B S hS i.hom) :
    SheafOfModules.{u} (elementsRingSheaf B S hS i hi) ≌ Modules.{u, u} B S hS X'.1 X'.2 :=
  Stacks.SheafOfModules.reindexEquivalence (smallEtaleElementsEquivalence B S hS i hi)
    (elementsRingSheaf B S hS i hi)

/-- Pullback of `𝒪_X`-modules along an étale morphism `i : X' ⟶ X` of algebraic spaces carries
injective `𝒪_X`-modules to injective `𝒪_{X'}`-modules. -/
theorem preservesInjectiveObjects_etaleModulePullback (hi : IsEtale B S hS i.hom) :
    (etaleModulePullback.{u, u} B S hS i hi).PreservesInjectiveObjects := by
  have hproj := preservesInjectiveObjects_elementsRestriction B S hS i hi
  have heq := (elementsModuleEquivalence B S hS i hi).isEquivalence_functor
  constructor
  intro M hM
  have hM' : Injective ((elementsRestriction B S hS i hi).obj M) :=
    Functor.injective_obj_of_injective _ hM
  exact Functor.injective_obj (elementsModuleEquivalence B S hS i hi).functor
    ((elementsRestriction B S hS i hi).obj M)

end Injectives

end AlgebraicGeometry.Space

end
