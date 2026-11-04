module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Presentable.Comma
public import StacksFrontier.CategoryTheory.KanExtension.ExtendTensor
public import StacksFrontier.CategoryTheory.KanExtension.ArrowGenerators
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered

/-! # Exactness of the extension of a functor from compact generators

Let `P` be a property of objects of `C` cutting out a locally small full subcategory of
categorically compact objects (Stacks 0FWX) such that every object of `C` is a filtered colimit
of `P`-objects, and let `F : C ⥤ D` be a functor commuting with filtered colimits whose
restriction to the `P`-objects is identified with a functor `F'`. This file proves the
paragraphs of the proof of Stacks 0GRJ which say that the extension inherits exactness
properties from `F'`:

* if `F'` preserves zero morphisms, so does `F`;
* if `P` is closed under binary coproducts and `F'` preserves them, so does `F`, hence `F` is
  additive when `F'` is;
* if `P` is closed under cokernels and `F'` preserves them, so does `F` (the right exactness
  paragraph), hence `F` preserves finite colimits;
* `F` then commutes with all colimits ("a right exact functor which commutes with all coproducts
  commutes with all colimits", Stacks 002P).

## Main results

* `CategoryTheory.ObjectProperty.isIso_of_preservesFilteredColimits`: a natural transformation
  between functors commuting with filtered colimits is an isomorphism as soon as its components
  at `P`-objects are.
* `CategoryTheory.Limits.cokerAdjunction`: the cokernel functor on arrows is a left adjoint, so it
  commutes with colimits.
* `CategoryTheory.ObjectProperty.preservesZeroMorphisms_of_preservesFilteredColimits` and
  `CategoryTheory.ObjectProperty.preservesCokernels_of_preservesFilteredColimits`: the extension
  preserves zero morphisms and cokernels when `F'` does; the second runs the uniqueness argument
  in the arrow category, whose compact generators are the arrows between `P`-objects
  (`StacksFrontier.CategoryTheory.KanExtension.ArrowGenerators`).
* `ObjectProperty.additive_preservesFiniteColimits_preservesColimits_of_preservesFilteredColimits`:
  the extension is additive, right exact and commutes with all colimits.
* `CategoryTheory.ObjectProperty.existsUnique_tensorExtension`: the abstract form of Stacks 0GRJ:
  a right exact tensor functor on the compact generators extends uniquely to a right exact tensor
  functor commuting with all colimits.
-/

@[expose] public section

open CategoryTheory Category Limits ObjectProperty MonoidalCategory

universe w v v' u u'

namespace CategoryTheory

namespace Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C] [HasCokernels C]

open ZeroObject

/-- The functor sending an object `Z` to the arrow `0 ⟶ Z` out of the zero object. -/
@[simps]
noncomputable def zeroArrowFunctor : C ⥤ Arrow C where
  obj Z := Arrow.mk (0 : (0 : C) ⟶ Z)
  map g := Arrow.homMk (0 : (0 : C) ⟶ 0) g (by simp)

/-- Morphisms out of the cokernel of `f` are morphisms of arrows from `f` to `0 ⟶ Z`. -/
@[simps]
noncomputable def cokerHomEquiv (f : Arrow C) (Z : C) :
    (cokernel f.hom ⟶ Z) ≃ (f ⟶ zeroArrowFunctor.obj Z) where
  toFun g := Arrow.homMk 0 (cokernel.π f.hom ≫ g)
    (zero_comp.trans ((cokernel.condition_assoc f.hom g).trans zero_comp).symm)
  invFun u := cokernel.desc f.hom u.right ((Arrow.w u).symm.trans comp_zero)
  left_inv _ := coequalizer.hom_ext (cokernel.π_desc _ _ _)
  right_inv _ := Comma.hom_ext _ _ ((isZero_zero C).eq_of_tgt _ _) (cokernel.π_desc _ _ _)

/-- **The cokernel functor on arrows is left adjoint** to `Z ↦ (0 ⟶ Z)`. -/
noncomputable def cokerAdjunction : coker C ⊣ zeroArrowFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cokerHomEquiv
      homEquiv_naturality_left_symm := fun {f f' Z} u g ↦ by
        apply coequalizer.hom_ext
        have h₁ : cokernel.π f.hom ≫ (coker C).map u = u.right ≫ cokernel.π f'.hom :=
          cokernel.π_desc _ _ _
        exact (cokernel.π_desc _ _ _).trans (Eq.symm ((assoc _ _ _).symm.trans
          ((congr_arg (· ≫ (cokerHomEquiv f' Z).symm g) h₁).trans ((assoc _ _ _).trans
            (congr_arg (u.right ≫ ·) (cokernel.π_desc _ _ _))))))
      homEquiv_naturality_right := fun {f Z Z'} g h ↦
        Comma.hom_ext _ _ ((isZero_zero C).eq_of_tgt _ _) (assoc _ _ _).symm }

/-- The cokernel functor on arrows preserves all colimits. -/
instance : PreservesColimitsOfSize.{w, w} (coker C) :=
  cokerAdjunction.leftAdjoint_preservesColimits

end Limits

namespace ObjectProperty

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (P : ObjectProperty C)
  [LocallySmall.{w} P.FullSubcategory]
  (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)

include hP hgen

/-- A natural transformation between functors commuting with filtered colimits is an
isomorphism as soon as its components at the `P`-objects are isomorphisms. -/
theorem isIso_of_preservesFilteredColimits {G₁ G₂ : C ⥤ D}
    [PreservesFilteredColimitsOfSize.{w, w} G₁] [PreservesFilteredColimitsOfSize.{w, w} G₂]
    (α : G₁ ⟶ G₂) (h : ∀ X : P.FullSubcategory, IsIso (α.app X.obj)) : IsIso α := by
  have : IsIso (Functor.whiskerLeft P.ι α) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X ↦ h X
  have hφ : (natIsoOfPreservesFilteredColimits P hP hgen G₁ G₂
      (asIso (Functor.whiskerLeft P.ι α))).hom = α :=
    natTrans_ext_of_preservesFilteredColimits P hP hgen fun X ↦ by
      rw [natIsoOfPreservesFilteredColimits_hom_app]
      rfl
  rw [← hφ]
  infer_instance

omit [LocallySmall.{w} P.FullSubcategory] hP hgen in
/-- If `F'` is identified with the restriction of `F` to the `P`-objects, then `F` carries a
colimit cocone of a diagram of `P`-objects whose apex is a `P`-object to a colimit cocone, as
soon as `F'` preserves the colimit of that diagram. -/
noncomputable def isColimitMapCoconeOfMem {F : C ⥤ D} {F' : P.FullSubcategory ⥤ D}
    (e : P.ι ⋙ F ≅ F') {J : Type*} [Category J] (K : J ⥤ P.FullSubcategory)
    [PreservesColimit K F'] {c : Cocone (K ⋙ P.ι)} (hc : IsColimit c) (hcP : P c.pt) :
    IsColimit (F.mapCocone c) := by
  let c' : Cocone K :=
    { pt := ⟨c.pt, hcP⟩
      ι := { app := fun j ↦ ObjectProperty.homMk (c.ι.app j)
             naturality := fun {j j'} f ↦ by
               ext
               simpa using c.w f } }
  have hc' : IsColimit c' := isColimitOfReflects P.ι hc
  exact IsColimit.mapCoconeEquiv e.symm (isColimitOfPreserves F' hc')

section Zero

variable [Preadditive C] [Preadditive D]

/-- **The extension preserves zero morphisms** when `F'` does. -/
theorem preservesZeroMorphisms_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F] {F' : P.FullSubcategory ⥤ D}
    (e : P.ι ⋙ F ≅ F') [F'.PreservesZeroMorphisms] : F.PreservesZeroMorphisms := by
  have h₁ : ∀ X Y : P.FullSubcategory, F.map (0 : X.obj ⟶ Y.obj) = 0 := by
    intro X Y
    have h : F.map (0 : X.obj ⟶ Y.obj) ≫ e.hom.app Y = e.hom.app X ≫ F'.map 0 :=
      e.hom.naturality (0 : X ⟶ Y)
    rw [F'.map_zero, comp_zero] at h
    rw [← cancel_mono (e.hom.app Y), h, zero_comp]
  have h₂ : ∀ (X : C) (Y : P.FullSubcategory), F.map (0 : X ⟶ Y.obj) = 0 := by
    intro X Y
    refine app_eq_of_preservesFilteredColimits P hP hgen F ((Functor.const C).obj (F.obj Y.obj))
      (fun X ↦ F.map (0 : X ⟶ Y.obj)) (fun _ ↦ 0) (fun f ↦ ?_) (fun f ↦ by simp)
      (fun X ↦ h₁ X Y) X
    rw [← F.map_comp, comp_zero]
    simp
  refine ⟨fun X Y ↦ ?_⟩
  obtain ⟨J, _, _, pres, hpres⟩ := hgen X
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  rw [← comp_zero (f := (0 : X ⟶ pres.diag.obj j)), F.map_comp,
    h₂ X ⟨pres.diag.obj j, hpres j⟩, zero_comp]

end Zero

section Cokernels

variable [Preadditive C] [Preadditive D] [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D]
  [HasFiniteColimits C] [HasFiniteColimits D] [HasZeroObject C] [HasZeroObject D]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]

omit hP hgen [LocallySmall.{w} P.FullSubcategory] [Preadditive C] [Preadditive D]
  [HasFiniteColimits C] [HasFiniteColimits D] [HasZeroObject C] [HasZeroObject D]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})] in
/-- `F.mapArrow` commutes with filtered colimits when `F` does. -/
theorem preservesFilteredColimitsOfSize_mapArrow (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    PreservesFilteredColimitsOfSize.{w, w} F.mapArrow where
  preserves_filtered_colimits J _ _ := ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨by
    have h₁ : IsColimit (Arrow.leftFunc.mapCocone c) := isColimitOfPreserves _ hc
    have h₂ : IsColimit (Arrow.rightFunc.mapCocone c) := isColimitOfPreserves _ hc
    exact Comma.fstSndJointlyReflectColimit (isColimitOfPreserves F h₁)
      (isColimitOfPreserves F h₂)⟩⟩⟩

/-- The cokernel comparison maps `coker (F f) ⟶ F (coker f)`, as a natural transformation of
functors on arrows. -/
@[simps]
noncomputable def cokernelComparisonNatTrans (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.mapArrow ⋙ coker D ⟶ coker C ⋙ F where
  app f := cokernelComparison f.hom F
  naturality {f g} u := by
    apply coequalizer.hom_ext
    change cokernel.π (F.map f.hom) ≫ cokernel.desc _ (F.map u.right ≫ cokernel.π _)
        (by rw [← F.map_comp_assoc, ← Arrow.w u, F.map_comp_assoc, cokernel.condition,
          comp_zero]) ≫ cokernelComparison g.hom F =
      cokernel.π (F.map f.hom) ≫ cokernelComparison f.hom F ≫
        F.map (cokernel.desc _ (u.right ≫ cokernel.π _) _)
    rw [cokernel.π_desc_assoc, assoc, π_comp_cokernelComparison, ← F.map_comp,
      π_comp_cokernelComparison_assoc, ← F.map_comp, cokernel.π_desc]

include hP hgen

/-- **The extension preserves cokernels** when `F'` does. -/
theorem preservesCokernels_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F] {F' : P.FullSubcategory ⥤ D}
    (e : P.ι ⋙ F ≅ F') [F'.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F'] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F := by
  have := preservesZeroMorphisms_of_preservesFilteredColimits P hP hgen F e
  have := ArrowGenerators.locallySmall_arrow.{w} P
  have := preservesFilteredColimitsOfSize_mapArrow F
  have hiso : IsIso (cokernelComparisonNatTrans F) := by
    refine isIso_of_preservesFilteredColimits P.arrow (arrow_le_isFinitelyPresentable P hP)
      (arrow_ind P hP hgen) _ fun g ↦ ?_
    have hK : ∀ j, P ((parallelPair g.obj.hom 0).obj j) := by
      rintro (_ | _)
      exacts [g.property.1, g.property.2]
    have hc := isColimitMapCoconeOfMem P e (P.lift (parallelPair g.obj.hom 0) hK)
      (c := (CokernelCofork.ofπ (cokernel.π g.obj.hom) (cokernel.condition g.obj.hom) :
        Cocone (parallelPair g.obj.hom 0)))
      (cokernelIsCokernel g.obj.hom)
      (ArrowGenerators.prop_cokernel _ g.property.1 g.property.2)
    have : PreservesColimit (parallelPair g.obj.hom 0) F :=
      preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel g.obj.hom) hc
    change IsIso (cokernelComparison g.obj.hom F)
    infer_instance
  have : IsIso (cokernelComparison f F) :=
    (NatIso.isIso_app_of_isIso (cokernelComparisonNatTrans F) (Arrow.mk f) : _)
  exact PreservesCokernel.of_iso_comparison F f

end Cokernels

section Assembly

variable [Preadditive C] [Preadditive D] [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D]
  [HasFiniteColimits C] [HasFiniteColimits D] [HasZeroObject C] [HasZeroObject D]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]

include hP hgen

/-- **The extension of a right exact functor is right exact and commutes with all colimits.**
If `F : C ⥤ D` commutes with filtered colimits and its restriction to the `P`-objects is
identified with an additive functor `F'` preserving finite colimits, then `F` is additive,
preserves finite colimits, and preserves all `w`-small colimits. -/
theorem additive_preservesFiniteColimits_preservesColimits_of_preservesFilteredColimits
    (F : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} F] {F' : P.FullSubcategory ⥤ D}
    (e : P.ι ⋙ F ≅ F') [F'.Additive] [PreservesFiniteColimits F'] :
    F.Additive ∧ PreservesFiniteColimits F ∧ PreservesColimitsOfSize.{w, w} F := by
  have := preservesZeroMorphisms_of_preservesFilteredColimits P hP hgen F e
  have : ∀ {X Y : C} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F :=
    fun f ↦ preservesCokernels_of_preservesFilteredColimits P hP hgen F e f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have hfin : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesCokernels F
  have := Functor.preservesBinaryCoproducts_of_preservesCokernels F
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  refine ⟨Functor.additive_of_preservesBinaryBiproducts F, hfin, ?_⟩
  have : PreservesFiniteCoproducts F := inferInstance
  have : ∀ J : Type w, PreservesColimitsOfShape (Discrete J) F := fun J ↦
    Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete F
  exact preservesColimits_of_preservesCoequalizers_and_coproducts F

end Assembly

section Main

variable [MonoidalCategory C] [MonoidalCategory D] [P.IsMonoidal]
  [Preadditive C] [Preadditive D] [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D]
  [HasFiniteColimits C] [HasFiniteColimits D] [HasZeroObject C] [HasZeroObject D]
  [P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)]
  [P.IsClosedUnderColimitsOfShape WalkingParallelPair]
  [P.IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : C, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ X : D, PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

include hP hgen

/-- **A right exact tensor functor out of compact generators extends uniquely to a right exact
tensor functor commuting with all colimits.**

Let `C` and `D` be preadditive monoidal categories with `w`-small colimits, in which tensoring on
either side commutes with filtered colimits, and let `P` be a monoidal property of objects of `C`
closed under finite coproducts and cokernels, cutting out a locally `w`-small full subcategory of
categorically compact objects, such that every object of `C` is a `w`-filtered colimit of
`P`-objects. Let `F'` be a functor from the `P`-objects to `D` which is additive, preserves
finite colimits, and is a functor of monoidal categories (Stacks 0FFL). Then there are a functor
`F : C ⥤ D`, an identification `e` of its restriction to the `P`-objects with `F'`, and a
structure of functor of monoidal categories on `F` compatible with that of `F'` along `e`, such
that `F` is additive, preserves finite colimits and preserves all `w`-small colimits; and for any
other functor `G` commuting with filtered colimits together with an identification `e'` of its
restriction with `F'`, there is a unique isomorphism `F ≅ G` inducing `e' ⁻¹ ∘ e` on the
`P`-objects, which is compatible with the tensor structures whenever `G` is a functor of monoidal
categories and `e'` is compatible with the tensor structures. -/
theorem existsUnique_tensorExtension (F' : P.FullSubcategory ⥤ D) [F'.Additive]
    [PreservesFiniteColimits F'] (hF' : F'.TensorStructure) :
    ∃ (F : C ⥤ D) (e : P.ι ⋙ F ≅ F') (hF : F.TensorStructure),
      (F.Additive ∧ PreservesFiniteColimits F ∧ PreservesColimitsOfSize.{w, w} F ∧
        (hF.restrict P).IsCompatible hF' e) ∧
      ∀ (G : C ⥤ D), PreservesFilteredColimitsOfSize.{w, w} G → ∀ (e' : P.ι ⋙ G ≅ F'),
        ∃! φ : F ≅ G, Functor.whiskerLeft P.ι φ.hom = (e ≪≫ e'.symm).hom ∧
          ∀ hG : G.TensorStructure, (hG.restrict P).IsCompatible hF' e' →
            hF.IsCompatible hG φ := by
  obtain ⟨F, hFfilt, ⟨e⟩⟩ := exists_extension_of_locallySmall P hP hgen F'
  obtain ⟨h₁, h₂, h₃⟩ :=
    additive_preservesFiniteColimits_preservesColimits_of_preservesFilteredColimits P hP hgen F e
  refine ⟨F, e, tensorStructureExtension P hP hgen F e hF',
    ⟨h₁, h₂, h₃, isCompatible_tensorStructureExtension P hP hgen F e hF'⟩, fun G hG e' ↦ ?_⟩
  let φ := natIsoOfPreservesFilteredColimits P hP hgen F G (e ≪≫ e'.symm)
  have hφ' (X : P.FullSubcategory) : φ.hom.app X.obj = e.hom.app X ≫ e'.inv.app X :=
    natIsoOfPreservesFilteredColimits_hom_app P hP hgen F G _ X
  have hφ : Functor.whiskerLeft P.ι φ.hom = (e ≪≫ e'.symm).hom := by
    ext X
    exact hφ' X
  refine ⟨φ, ⟨hφ, fun hG' he' ↦ ?_⟩, fun ψ hψ ↦ ?_⟩
  · refine isCompatible_of_preservesFilteredColimits P hP hgen _ hG' φ fun X Y ↦ ?_
    have hXY : φ.hom.app (X.obj ⊗ Y.obj) = e.hom.app (X ⊗ Y) ≫ e'.inv.app (X ⊗ Y) :=
      hφ' (X ⊗ Y)
    have h₁ := isCompatible_tensorStructureExtension P hP hgen F e hF' X Y
    have h₂ := he' X Y
    change (tensorExtensionμIso P hP hgen F e hF' X.obj Y.obj).hom ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ (hF'.μIso X Y).hom at h₁
    change (hG'.μIso X.obj Y.obj).hom ≫ e'.hom.app (X ⊗ Y) =
      (e'.hom.app X ⊗ₘ e'.hom.app Y) ≫ (hF'.μIso X Y).hom at h₂
    change (tensorExtensionμIso P hP hgen F e hF' X.obj Y.obj).hom ≫
      φ.hom.app (X.obj ⊗ Y.obj) = (φ.hom.app X.obj ⊗ₘ φ.hom.app Y.obj) ≫
        (hG'.μIso X.obj Y.obj).hom
    have h₂' : (hG'.μIso X.obj Y.obj).hom = (e'.hom.app X ⊗ₘ e'.hom.app Y) ≫
        (hF'.μIso X Y).hom ≫ e'.inv.app (X ⊗ Y) := by
      rw [← reassoc_of% h₂, Iso.hom_inv_id_app]
      exact (comp_id _).symm
    rw [hφ' X, hφ' Y, hXY, h₂', ← assoc, h₁, tensorHom_comp_tensorHom_assoc]
    simp
  · refine Iso.ext (natTrans_ext_of_preservesFilteredColimits P hP hgen fun X ↦ ?_)
    exact congr_arg (·.app X) (hψ.1.trans hφ.symm)

end Main

end ObjectProperty

end CategoryTheory
