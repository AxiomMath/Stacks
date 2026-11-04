module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatCover
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.AlgebraicGeometry.RecoveryAux.DerivedFunctorCoproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction

/-!
# Compactness of extension by zero of the structure sheaf

Let `U` be an open subset of a ringed space `X`. If cohomology of modules over `U` has finite
cohomological dimension and commutes with direct sums in every degree, then the extension by
zero of the structure sheaf of `U` is compact in the unbounded derived category of modules on
`X`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Cohomology.CompactObjects.isCompactObject_jShriek_structureSheaf` gives the
  compactness criterion.

## Implementation notes

The extension by zero is the left adjoint to restriction on sheaves of modules, applied to the
unit module over the restricted structure sheaf. Cohomology in nonnegative degree is the right
derived functor of evaluation on `U`; negative sheaf cohomology vanishes automatically. Commutation
with direct sums is stated as preservation of discrete colimits, which includes the canonical
comparison and its naturality. The integer bound is retained, with nonnegative cohomological
degrees embedded into the integers.

The reduction to a K-injective resolution uses the resolution functor of Tag 079P
(`Stacks.Injectives.kInjectiveResolutionFunctor`) and the fact that `Q` preserves coproducts of
Tag 07D9 (`Stacks.Injectives.derivedCategoryQ_preservesCoproducts`); the passage from the
individual derived functors to the unbounded one is
`Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension`.
Additivity of evaluation is the existing instance
`Stacks.Cohomology.ModuleComparison.moduleEvaluation_additive`.

## References

* [Stacks Project, Tag 0F5Z](https://stacks.math.columbia.edu/tag/0F5Z)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DerivedFunctor.Coproducts

attribute [local instance] HasDerivedCategory.standard

universe u u' v v' w z u₁ v₁ u₂ v₂

namespace Stacks.Cohomology.CompactObjects

private noncomputable def sectionsEvalEquiv
    {C : Type*} [Category C] {F : C ⥤ Type u}
    (t : C) (ht : IsInitial t) : F.sections ≃ F.obj t where
  toFun s := s.val t
  invFun x := ⟨fun Y => F.map (ht.to Y) x, by
    intro Y Z f
    change ((F.map (ht.to Y)) ≫ F.map f) x = (F.map (ht.to Z)) x
    rw [← F.map_comp, ht.hom_ext (ht.to Y ≫ f) (ht.to Z)]⟩
  left_inv s := Subtype.ext <| funext fun Y => Functor.sections_property s (ht.to Y)
  right_inv x := by
    change F.map (ht.to t) x = x
    rw [show ht.to t = 𝟙 t from ht.hom_ext _ _]
    simp

private noncomputable def unitHomEvalAddEquiv
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (t : C) (ht : IsTerminal t)
    (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃+ M.val.obj (op t) := by
  let e : (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op t) :=
    M.unitHomEquiv.trans (sectionsEvalEquiv (op t) (ht.op))
  let f : (SheafOfModules.unit R ⟶ M) →+ M.val.obj (op t) :=
    AddMonoidHom.mk' (fun g => e g) (by
      intro g h
      change (M.unitHomEquiv (g + h)).val (op t) =
        (M.unitHomEquiv g).val (op t) + (M.unitHomEquiv h).val (op t)
      rw [SheafOfModules.unitHomEquiv_apply_coe,
        SheafOfModules.unitHomEquiv_apply_coe,
        SheafOfModules.unitHomEquiv_apply_coe]
      let one : (SheafOfModules.unit R).val.obj (op t) := by
        change R.obj.obj (op t)
        exact 1
      change ((g.val.app (op t)).hom + (h.val.app (op t)).hom)
          one = _
      rw [LinearMap.add_apply]
      rfl)
  exact AddEquiv.ofBijective f e.bijective

private lemma unitHomEvalAddEquiv_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (t : C) (ht : IsTerminal t)
    {M N : SheafOfModules.{u} R} (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    unitHomEvalAddEquiv R t ht N (f ≫ g) =
      (SheafOfModules.evaluation R (op t)).map g (unitHomEvalAddEquiv R t ht M f) := by
  show (N.unitHomEquiv (f ≫ g)).val (op t) = _
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  rfl

private noncomputable def unitHomEvalNatIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (t : C) (ht : IsTerminal t)
    [(SheafOfModules.evaluation R (op t)).Additive] :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      (SheafOfModules.evaluation R (op t) ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op t))) AddCommGrpCat.{u}) := by
  refine NatIso.ofComponents (fun M => (unitHomEvalAddEquiv R t ht M).toAddCommGrpIso) ?_
  intro M N f
  ext g
  exact unitHomEvalAddEquiv_naturality t ht g f

private noncomputable def homComplexSingleCoyonedaIso
    {C : Type u'} [Category.{v'} C] [Preadditive C] [HasZeroObject C]
    (X : C) (K : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj X).HomComplex K ≅
      ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := X) (K := K) (p := 0) (q := j) (n := j) (by ring)).toAddCommGrpIso)
    (by
      intro i j hij
      ext (α : CochainComplex.HomComplex.Cochain _ _ _)
      obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
        α i (by ring)
      simp only [AddCommGrpCat.hom_comp, Functor.mapHomologicalComplex_obj_d]
      have hLHS : (AddCommGrpCat.Hom.hom ((preadditiveCoyoneda.obj (op X)).map (K.d i j)))
            ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0:ℤ)+i=i))
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)))
          = f ≫ K.d i j := by
        rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
        rfl
      have h1 : (AddCommGrpCat.Hom.hom ((((CochainComplex.singleFunctor C 0).obj X).HomComplex
          K).d i j)) (CochainComplex.HomComplex.Cochain.fromSingleMk f
            (by ring : (0:ℤ)+i=i)) =
          CochainComplex.HomComplex.δ i j
            (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)) :=
        CochainComplex.HomComplex_d_hom_apply _ _ i j _
      have hRHS : (CochainComplex.HomComplex.Cochain.fromSingleEquiv
            (by ring : (0:ℤ)+j=j))
            ((AddCommGrpCat.Hom.hom
              ((((CochainComplex.singleFunctor C 0).obj X).HomComplex K).d i j))
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0:ℤ)+i=i)))
          = f ≫ K.d i j := by
        rw [h1, CochainComplex.HomComplex.Cochain.δ_fromSingleMk f
            (show (0:ℤ)+i=i by ring) j j (by ring),
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      exact hLHS.trans hRHS.symm)

private noncomputable def zeroHomClassEquiv
    {C : Type u'} [Category.{v'} C] [Preadditive C] (K I : CochainComplex C ℤ) :
    CochainComplex.HomComplex.CohomologyClass K I 0 ≃+
      ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj I) :=
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
      ((HomotopyCategory.quotient C _).mapIso
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app I))).toAddEquiv

private lemma zeroHomClassEquiv_postcomp
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    (K : CochainComplex C ℤ) {I I' : CochainComplex C ℤ} (f : I ⟶ I')
    (a : CochainComplex.HomComplex.CohomologyClass K I 0) :
    zeroHomClassEquiv K I' (cohomologyClassPostcomp K f 0 a) =
      zeroHomClassEquiv K I a ≫ (HomotopyCategory.quotient C _).map f := by
  show (𝟙 _ ≫ CochainComplex.HomComplex.CohomologyClass.toHom
      (cohomologyClassPostcomp K f 0 a)) ≫
      (HomotopyCategory.quotient C _).map ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I') =
    ((𝟙 _ ≫ CochainComplex.HomComplex.CohomologyClass.toHom a) ≫
      (HomotopyCategory.quotient C _).map ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I)) ≫ _
  rw [toHom_cohomologyClassPostcomp]
  simp only [Category.id_comp, Category.assoc, ← Functor.map_comp]
  rw [(shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.naturality]
  rfl

private noncomputable def homComplexPostcomp
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ} (f : L ⟶ L') :
    K.HomComplex L ⟶ K.HomComplex L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun x => x.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' x y := by simp }
  comm' i j hij := by
    ext x
    change CochainComplex.HomComplex.δ i j
        (x.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero i)) =
      (CochainComplex.HomComplex.δ i j x).comp
        (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero j)
    exact CochainComplex.HomComplex.δ_comp_ofHom x f j

private lemma homologyClass_postcomp
    {C : Type u'} [Category.{v'} C] [Preadditive C]
    (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ} (f : L ⟶ L') (n : ℤ)
    (x : (K.HomComplex L).homology n) :
    CochainComplex.HomComplex.homologyAddEquiv K L' n
        (HomologicalComplex.homologyMap (homComplexPostcomp K f) n x) =
      cohomologyClassPostcomp K f n
        (CochainComplex.HomComplex.homologyAddEquiv K L n x) := by
  let H := K.HomComplex L
  let H' := K.HomComplex L'
  let h := CochainComplex.HomComplex.leftHomologyData K L n
  let h' := CochainComplex.HomComplex.leftHomologyData K L' n
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (H.homologyπ n)).mp inferInstance x
  let a : CochainComplex.HomComplex.Cocycle K L n := h.cyclesIso.hom z
  have ha : CochainComplex.HomComplex.homologyAddEquiv K L n (H.homologyπ n z) =
      CochainComplex.HomComplex.CohomologyClass.mk a :=
    ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (H.sc n) h) z
  have hmap : h'.cyclesIso.hom
      (HomologicalComplex.cyclesMap (homComplexPostcomp K f) n z) = a.postcomp f := by
    apply Subtype.ext
    have h1 := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i
      (HomologicalComplex.cyclesMap (homComplexPostcomp K f) n z)
    have h2 := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (homComplexPostcomp K f) n) z
    have h3 := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i z
    simp only [ConcreteCategory.comp_apply] at h1 h2 h3
    exact h1.trans (h2.trans (congrArg
      (fun x => x.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)) h3))
  have hb : CochainComplex.HomComplex.homologyAddEquiv K L' n
      (H'.homologyπ n (HomologicalComplex.cyclesMap (homComplexPostcomp K f) n z)) =
        CochainComplex.HomComplex.CohomologyClass.mk (a.postcomp f) := by
    rw [← hmap]
    exact ConcreteCategory.congr_hom
      (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (H'.sc n) h') _
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (homComplexPostcomp K f) n) z
  simp only [ConcreteCategory.comp_apply] at hn
  rw [hn, hb, ha, cohomologyClassPostcomp_mk]

private lemma homComplexSingleCoyonedaIso_naturality
    {C : Type u'} [Category.{v'} C] [Preadditive C] [HasZeroObject C]
    (M : C) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homComplexPostcomp ((CochainComplex.singleFunctor C 0).obj M) f ≫
        (homComplexSingleCoyonedaIso M L).hom =
      (homComplexSingleCoyonedaIso M K).hom ≫
        ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map f := by
  ext n x
  obtain ⟨g, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective x n (by omega)
  show (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by omega : (0 : ℤ) + n = n))
      ((CochainComplex.HomComplex.Cochain.fromSingleMk g (by omega : (0 : ℤ) + n = n)).comp
        (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)) = _
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp,
    CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  show g ≫ f.f n =
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by omega : (0 : ℤ) + n = n))
      (CochainComplex.HomComplex.Cochain.fromSingleMk g (by omega : (0 : ℤ) + n = n)) ≫ f.f n
  rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]

private noncomputable def homologyCoyonedaEquiv
    {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{z} C]
    (M : C) (K : CochainComplex C ℤ) [K.IsKInjective] :
    (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ≃+
      ((DerivedCategory.singleFunctor C 0).obj M ⟶ DerivedCategory.Q.obj K) :=
  ((HomologicalComplex.homologyMapIso
    (homComplexSingleCoyonedaIso M K) 0).symm.addCommGroupIsoToAddEquiv).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K 0).trans
      ((zeroHomClassEquiv _ K).trans
        ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
          (CochainComplex.IsKInjective.Qh_map_bijective _ K)).trans
          (CategoryTheory.Linear.homCongr ℤ
            ((DerivedCategory.quotientCompQhIso C).app _ ≪≫
              ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).symm)
            ((DerivedCategory.quotientCompQhIso C).app K)).toAddEquiv)))

private lemma homologyCoyonedaEquiv_naturality
    {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{z} C]
    (M : C) {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L)
    (x : (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).obj K).homology 0) :
    homologyCoyonedaEquiv M L
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map f) 0 x) =
      homologyCoyonedaEquiv M K x ≫ DerivedCategory.Q.map f := by
  let S := (CochainComplex.singleFunctor C 0).obj M
  have he : ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map f ≫
      (homComplexSingleCoyonedaIso M L).inv =
        (homComplexSingleCoyonedaIso M K).inv ≫ homComplexPostcomp S f := by
    rw [← cancel_epi (homComplexSingleCoyonedaIso M K).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← homComplexSingleCoyonedaIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have he' := ConcreteCategory.congr_hom
    (congrArg (fun g => HomologicalComplex.homologyMap g 0) he) x
  simp only [HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] at he'
  let eS := (DerivedCategory.quotientCompQhIso C).app S ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).symm
  show (eS.inv ≫ DerivedCategory.Qh.map (zeroHomClassEquiv S L
    (CochainComplex.HomComplex.homologyAddEquiv S L 0
      (HomologicalComplex.homologyMap (homComplexSingleCoyonedaIso M L).inv 0
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ)).map f) 0 x))))) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app L =
    ((eS.inv ≫ DerivedCategory.Qh.map (zeroHomClassEquiv S K
      (CochainComplex.HomComplex.homologyAddEquiv S K 0
        (HomologicalComplex.homologyMap (homComplexSingleCoyonedaIso M K).inv 0 x)))) ≫
          (DerivedCategory.quotientCompQhIso C).hom.app K) ≫ DerivedCategory.Q.map f
  rw [he', homologyClass_postcomp, zeroHomClassEquiv_postcomp]
  simp only [Functor.map_comp, Category.assoc]
  have hnat : DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app L =
        (DerivedCategory.quotientCompQhIso C).hom.app K ≫ DerivedCategory.Q.map f :=
    (DerivedCategory.quotientCompQhIso C).hom.naturality f
  rw [hnat]

private noncomputable def jShriekHomEvalIso
    (X : SheafedSpace.{u + 1, u, u} RingCat.{u}) (U : Opens X.carrier) :
    preadditiveCoyoneda.obj (op ((jShriek00A7 X U).obj
      (SheafOfModules.unit (OUSh X U)))) ≅
      SheafOfModules.evaluation (OXSh X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u} := by
  letI : (restMod X U).IsRightAdjoint := (jShriekAdjunction X U).isRightAdjoint
  letI : (jShriek00A7 X U).IsLeftAdjoint := (jShriekAdjunction X U).isLeftAdjoint
  letI : (restMod X U).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryProducts (restMod X U)
    exact Functor.additive_of_preservesBinaryBiproducts _
  letI : (jShriek00A7 X U).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (jShriek00A7 X U)
    exact Functor.additive_of_preservesBinaryBiproducts _
  let t : Opens ((Opens.toTopCat _).obj U) := ⊤
  letI : (SheafOfModules.evaluation.{u} (OUSh X U) (op t)).Additive := by
    unfold SheafOfModules.evaluation
    infer_instance
  let V := (jFun X U).obj t
  have hV : V = U := by
    ext x
    change (∃ y : U, y ∈ (⊤ : Opens U) ∧ (y : X.carrier) = x) ↔ x ∈ U
    simp
  let e : preadditiveCoyoneda.obj (op ((jShriek00A7 X U).obj
      (SheafOfModules.unit (OUSh X U)))) ≅
      restMod X U ⋙ preadditiveCoyoneda.obj (op (SheafOfModules.unit (OUSh X U))) :=
    NatIso.ofComponents (fun M =>
      ((jShriekAdjunction X U).homAddEquiv _ M).toAddCommGrpIso)
      (by
        intro M N f
        ext g
        exact (jShriekAdjunction X U).homEquiv_naturality_right g f)
  refine e ≪≫
    Functor.isoWhiskerLeft (restMod X U) (unitHomEvalNatIso (OUSh X U) t isTerminalTop) ≪≫ ?_
  refine NatIso.ofComponents (fun M => ?_) ?_
  · exact ((SheafOfModules.forget (OXSh X) ⋙
        PresheafOfModules.toPresheaf (OXSh X).obj).obj M).mapIso
        (eqToIso (congrArg op hV))
  · intro M N f
    exact (((SheafOfModules.forget (OXSh X) ⋙
      PresheafOfModules.toPresheaf (OXSh X).obj).map f).naturality
        (eqToHom (congrArg op hV))).symm

private lemma derivedHomology_preservesCoproducts
    (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (I : Type w) (n : ℤ) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n) := by
  have := Stacks.Injectives.derivedCategoryQ_preservesCoproducts A I
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := A) (J := Discrete I) (ComplexShape.up ℤ) n
  have : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A n) :=
    preservesColimitsOfShape_of_natIso (DerivedCategory.homologyFunctorFactors A n).symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    DerivedCategory.Q (DerivedCategory.homologyFunctor A n) I

private noncomputable def mapHomologyNatIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    {D : Type*} [Category* D] [Abelian D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive] [G.PreservesHomology] (n : ℤ) :
    (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) n ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) n ⋙ G :=
  NatIso.ofComponents (fun K => (((F.mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso G)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor B (.up ℤ) n).map
        ((F.mapHomologicalComplex (.up ℤ)).map f)) G)

private noncomputable def resolutionIso
    (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{z} A] :
    DerivedCategory.Q ≅ Stacks.Injectives.kInjectiveResolutionFunctor A ⋙ DerivedCategory.Q := by
  let η : DerivedCategory.Q ⟶ Stacks.Injectives.kInjectiveResolutionFunctor A ⋙ DerivedCategory.Q :=
    { app K := DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K)
      naturality K L f := by
        dsimp
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion A).naturality f) }
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

private noncomputable def resolvedCoyonedaIso
    {A : Type u'} [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{max v' z} A] (M : A) :
    Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      (preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v'} (.up ℤ) 0 ⋙
          AddCommGrpCat.uliftFunctor.{z, v'} ≅
    (Stacks.Injectives.kInjectiveResolutionFunctor A ⋙ DerivedCategory.Q) ⋙
      preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj M)) :=
  NatIso.ofComponents (fun K =>
    (AddEquiv.ulift.trans (homologyCoyonedaEquiv M
      ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))).toAddCommGrpIso)
    (by
      intro K L f
      ext x
      exact homologyCoyonedaEquiv_naturality M
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).map f) x.down)

/-- Every complex in a Grothendieck abelian category admits a quasi-isomorphism to a K-injective
complex. -/
private lemma exists_quasiIso_isKInjective
    (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{w} A] :
    ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := fun K =>
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

private noncomputable def resolvedDerivedIso
    {A : Type u'} [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))] :
    Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ≅
    (Stacks.Injectives.kInjectiveResolutionFunctor A ⋙ DerivedCategory.Q) ⋙ RF := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let R := Stacks.Injectives.kInjectiveResolutionFunctor A
  let β := Functor.whiskerLeft (R ⋙ q) α
  have hβ (K : CochainComplex A ℤ) : IsIso (β.app K) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      _ (exists_quasiIso_isKInjective A)).2 DerivedCategory.Qh RF α (R.obj K) inferInstance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact Functor.isoWhiskerLeft R
      (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator R q _).symm ≪≫ asIso β ≪≫
    (Functor.associator (R ⋙ q) DerivedCategory.Qh RF).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator R q DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft R (DerivedCategory.quotientCompQhIso A)) RF

private lemma compact_of_preservesCoyoneda
    {D : Type u'} [Category.{max w v'} D] [Preadditive D]
    (M : D) (h : ∀ I : Type w,
      PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op M))) :
    IsCompactObject.{w} M := by
  classical
  constructor
  intro I _ E _
  let H := preadditiveCoyoneda.obj (op M)
  let c : Cofan (fun i => H.obj (E i)) := Cofan.mk
    (AddCommGrpCat.of (DirectSum I (fun i => M ⟶ E i)))
    (fun i => AddCommGrpCat.ofHom (DirectSum.of (fun i => (M ⟶ E i)) i))
  let hc : IsColimit c := Cofan.IsColimit.mk _
    (fun s => AddCommGrpCat.ofHom (DirectSum.toAddMonoid (fun i => (s.inj i).hom)))
    (by
      intro s i
      ext x
      show (DirectSum.toAddMonoid (fun j => (s.inj j).hom))
        (DirectSum.of (fun j => (M ⟶ E j)) i x) = (s.inj i).hom x
      exact DirectSum.toAddMonoid_of (fun j => (s.inj j).hom) i x)
    (by
      intro s f hf
      refine AddCommGrpCat.hom_ext (DirectSum.addHom_ext fun i y => ?_)
      show f.hom (DirectSum.of (fun j => M ⟶ E j) i y) =
        (DirectSum.toAddMonoid (fun j => (s.inj j).hom))
          (DirectSum.of (fun j => M ⟶ E j) i y)
      exact (ConcreteCategory.congr_hom (hf i) y).trans
        (DirectSum.toAddMonoid_of (fun j => (s.inj j).hom) i y).symm)
  have := h I
  let hc' := (isColimitMapCoconeCofanMkEquiv H E (Sigma.ι E)).1
    (isColimitOfPreserves H (coproductIsCoproduct E))
  exact (ConcreteCategory.isIso_iff_bijective (hc.coconePointUniqueUpToIso hc').hom).1
    inferInstance

private lemma preservesCoyoneda_of_rightDerived
    (A : Type (u + 1)) [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (B : Type (u + 1)) [Category.{u} B] [Abelian B] [IsGrothendieckAbelian.{u} B]
    (M : A) (F : A ⥤ B) [F.Additive] (G : B ⥤ AddCommGrpCat.{u})
    [G.Additive] [G.PreservesHomology]
    (e : preadditiveCoyoneda.obj (op M) ≅ F ⋙ G)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (I : Type u) [PreservesColimitsOfShape (Discrete I) RF]
    [PreservesColimitsOfShape (Discrete I) G] :
    PreservesColimitsOfShape (Discrete I)
      (preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj M))) := by
  let R := Stacks.Injectives.kInjectiveResolutionFunctor A
  let H := preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj M))
  let U := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let H₀ := HomologicalComplex.homologyFunctor B (.up ℤ) 0
  let H₀' := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0
  let HD := DerivedCategory.homologyFunctor B 0
  let T := RF ⋙ HD ⋙ G ⋙ U
  let e₁ : R ⋙ (preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ) ⋙ H₀' ⋙ U ≅
      (R ⋙ DerivedCategory.Q) ⋙ H := resolvedCoyonedaIso M
  let e₂ : R ⋙ (preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (.up ℤ) ⋙ H₀' ⋙ U ≅
      R ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ H₀ ⋙ G ⋙ U :=
    Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) (H₀' ⋙ U)) ≪≫
    Functor.isoWhiskerLeft R (Functor.isoWhiskerRight (mapHomologyNatIso F G 0) U)
  let e₃ : R ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ H₀ ⋙ G ⋙ U ≅
      (R ⋙ DerivedCategory.Q) ⋙ T :=
    Functor.isoWhiskerLeft R (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors B 0).symm (G ⋙ U))) ≪≫
    Functor.isoWhiskerRight (resolvedDerivedIso F RF α) (HD ⋙ G ⋙ U)
  let e₄ : DerivedCategory.Q ⋙ H ≅ DerivedCategory.Q ⋙ T :=
    Functor.isoWhiskerRight (resolutionIso A) H ≪≫ e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫
      Functor.isoWhiskerRight (resolutionIso A).symm T
  have := Stacks.Injectives.derivedCategoryQ_preservesCoproducts A I
  have := derivedHomology_preservesCoproducts B I 0
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q ⋙ T) := by
    dsimp [T, U]
    infer_instance
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q ⋙ H) :=
    preservesColimitsOfShape_of_natIso e₄.symm
  exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q H I

private lemma compact_single_of_finiteCohomologicalDimension
    (A : Type (u + 1)) [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (B : Type (u + 1)) [Category.{u} B] [Abelian B] [IsGrothendieckAbelian.{u} B]
    (M : A) (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (G : B ⥤ AddCommGrpCat.{u}) [G.Additive] [G.PreservesHomology]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) G]
    (e : preadditiveCoyoneda.obj (op M) ≅ F ⋙ G)
    (d : ℤ) (hvanish : ∀ (p : ℕ) (N : A), d < (p : ℤ) → IsZero ((F.rightDerived p).obj N))
    (hsums : ∀ (p : ℕ) (I : Type u), PreservesColimitsOfShape (Discrete I) (F.rightDerived p)) :
    IsCompactObject.{u} ((DerivedCategory.singleFunctor A 0).obj M) := by
  let T := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have : T.HasPointwiseRightDerivedFunctor W :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} T (exists_quasiIso_isKInjective A)).1
  let RF := T.totalRightDerived DerivedCategory.Qh W
  let α := T.totalRightDerivedUnit DerivedCategory.Qh W
  let n := d.toNat + 1
  have hn (q : ℕ) (hq : n ≤ q) (N : A) : IsZero ((F.rightDerived q).obj N) := by
    apply hvanish q N
    have : d ≤ (d.toNat : ℤ) := Int.self_le_toNat d
    dsimp [n] at hq
    omega
  apply compact_of_preservesCoyoneda.{u + 1, u + 1, u}
  intro I
  have := preservesCoproductsOfShape_of_finiteCohomologicalDimension
    A B F n hn hsums RF α I
  exact preservesCoyoneda_of_rightDerived A B M F G e RF α I

/-- Finite cohomological dimension and commutation of cohomology with direct sums make
`j_! 𝒪_U` compact in the unbounded derived category of `𝒪_X`-modules. -/
@[stacks 0F5Z]
public theorem isCompactObject_jShriek_structureSheaf
    (X : SheafedSpace.{u + 1, u, u} RingCat.{u}) (U : Opens X.carrier)
    (d : ℤ)
    (hvanish : ∀ (p : ℕ) (M : SheafOfModules.{u} (OXSh X)),
      d < (p : ℤ) →
        IsZero (((SheafOfModules.evaluation (OXSh X) (op U)).rightDerived p).obj M))
    (hsums : ∀ (p : ℕ) (I : Type u),
      PreservesColimitsOfShape (Discrete I)
        ((SheafOfModules.evaluation (OXSh X) (op U)).rightDerived p)) :
    IsCompactObject.{u}
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (OXSh X)) 0).obj
        ((jShriek00A7 X U).obj (SheafOfModules.unit (OUSh X U)))) := by
  let F := SheafOfModules.evaluation (OXSh X) (op U)
  let G := forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}
  have : PreservesFiniteLimits F := by
    unfold F SheafOfModules.evaluation
    infer_instance
  exact compact_single_of_finiteCohomologicalDimension
    (SheafOfModules.{u} (OXSh X)) (ModuleCat.{u} ((OXSh X).obj.obj (op U)))
    ((jShriek00A7 X U).obj (SheafOfModules.unit (OUSh X U))) F G
    (jShriekHomEvalIso X U) d hvanish hsums

end Stacks.Cohomology.CompactObjects
