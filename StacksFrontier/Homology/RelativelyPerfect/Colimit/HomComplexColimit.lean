module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexBaseChange
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ComplexDescent
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexBaseChange

/-!
# Filtered colimits of derived morphism groups

Homology of tensor products of Hom complexes along a filtered diagram of rings, the resulting
filtered colimit descriptions of derived morphism groups, and lifting of Tor amplitude along a
change of scalar universe.

This is part 6 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

section HomComplexHomology

universe u v w

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower
open scoped ModuleCat.Algebra ChangeOfRings
universe t

universe s

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexRHomologyEquivDerivedHom_naturality_congr
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (P' F' : CochainComplex (ModuleCat.{v} B) ℤ)
    (h : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P F 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)))
    (h' : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P' F' 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)))
    {X Y : DerivedCategory (ModuleCat.{v} A)}
    {X' Y' : DerivedCategory (ModuleCat.{v} B)}
    (α : X ≅ DerivedCategory.Q.obj P) (β : Y ≅ DerivedCategory.Q.obj F)
    (α' : X' ≅ DerivedCategory.Q.obj P') (β' : Y' ≅ DerivedCategory.Q.obj F')
    (ψ : CochainComplex.HomComplex P F ⟶ CochainComplex.HomComplex P' F')
    (T : (X ⟶ Y) → (X' ⟶ Y'))
    (hψ : ∀ g : P ⟶ F, ∃ g' : P' ⟶ F',
      ψ.f 0 (CochainComplex.HomComplex.Cochain.ofHom g) =
        CochainComplex.HomComplex.Cochain.ofHom g' ∧
      T (α.hom ≫ DerivedCategory.Q.map g ≫ β.inv) =
        α'.hom ≫ DerivedCategory.Q.map g' ≫ β'.inv)
    (x : (CochainComplex.HomComplexR A P F).homology 0) :
    Iso.homCongr α'.symm β'.symm
      (homComplexRHomologyEquivDerivedHom P' F' h'
        (homologyForgetMap (E := CochainComplex.HomComplexR A P F)
          (F := CochainComplex.HomComplexR B P' F') ψ 0 x)) =
      T (Iso.homCongr α.symm β.symm (homComplexRHomologyEquivDerivedHom P F h x)) := by
  let T' := fun g ↦ Iso.homCongr α' β' (T (Iso.homCongr α.symm β.symm g))
  have hp : ∀ g : P ⟶ F, ∃ g' : P' ⟶ F',
      ψ.f 0 (CochainComplex.HomComplex.Cochain.ofHom g) =
        CochainComplex.HomComplex.Cochain.ofHom g' ∧
      T' (DerivedCategory.Q.map g) = DerivedCategory.Q.map g' := by
    intro g
    obtain ⟨g', hg', hT⟩ := hψ g
    refine ⟨g', hg', ?_⟩
    dsimp [T', Iso.homCongr]
    rw [hT]
    simp [Category.assoc]
  have hh := homComplexRHomologyEquivDerivedHom_naturality P F P' F' h h' ψ T' hp x
  have he : homologyForgetMap (E := CochainComplex.HomComplexR A P F)
      (F := CochainComplex.HomComplexR B P' F') ψ 0 x =
      (((CochainComplex.HomComplexR B P' F').sc 0).mapHomologyIso
        (forget₂ (ModuleCat.{v} B) Ab)).hom
        (HomologicalComplex.homologyMap ψ 0
          ((((CochainComplex.HomComplexR A P F).sc 0).mapHomologyIso
            (forget₂ (ModuleCat.{v} A) Ab)).inv x)) := rfl
  rw [he]
  have hh' := congrArg (Iso.homCongr α'.symm β'.symm) hh
  simpa only [T', Iso.homCongr, Iso.symm_hom, Iso.symm_inv, Equiv.coe_fn_mk,
    ConcreteCategory.comp_apply, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh'

/-- For a K-projective source, the map `H^0(Hom(P, F)) → Hom_{D}(P, F)` is bijective. -/
private lemma qh_map_homAddEquiv_bijective {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) [P.IsKProjective] :
    Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P F 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)) :=
  (CochainComplex.IsKProjective.Qh_map_bijective P _).comp
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv.bijective

/-- Extension of scalars of a bounded-above complex of free modules is K-projective. -/
private lemma isKProjective_extendScalars_obj {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (P : CochainComplex (ModuleCat.{w} A) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Module.Free A (P.X i)] :
    CochainComplex.IsKProjective
      (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P) := by
  let := f.toAlgebra
  have (i : ℤ) : Module.Free B
      ((((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P).X i) := by
    change Module.Free B (B ⊗[A] (P.X i))
    infer_instance
  have (i : ℤ) : Projective
      ((((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    inferInstance
  exact CochainComplex.isKProjective_of_projective _ d

private def homComplexBaseChangeHomologyEquivDerivedHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)] :
    (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.HomComplexR A P F)).homology 0 ≃
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F)) := by
  let := f.toAlgebra
  let Ext := (ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)
  have := isKProjective_extendScalars_obj f P d
  have := isIso_homComplexBaseChange f P F a b
  exact (ConcreteCategory.bijective_of_isIso
      ((HomologicalComplex.homologyFunctor (ModuleCat.{max v w} B) (.up ℤ) 0).map
        (homComplexBaseChange f P F))
      |> Equiv.ofBijective _).trans
    (homComplexRHomologyEquivDerivedHom (Ext.obj P) (Ext.obj F)
      (qh_map_homAddEquiv_bijective _ _))

private def homComplexBaseChangeHomologyEquivLeftDerivedHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    (L : DerivedCategory (ModuleCat.{w} A) ⥤
      DerivedCategory (ModuleCat.{max v w} B))
    (α : DerivedCategory.Q ⋙ L ⟶
      (ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [IsIso (α.app P)] [IsIso (α.app F)] :
    (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.HomComplexR A P F)).homology 0 ≃
      (L.obj (DerivedCategory.Q.obj P) ⟶ L.obj (DerivedCategory.Q.obj F)) :=
  (homComplexBaseChangeHomologyEquivDerivedHom f P F a b d).trans
    (Iso.homCongr (asIso (α.app P)).symm (asIso (α.app F)).symm)

private def tensorComplexFunctor {R : Type u} [CommRing R]
    {ι : Type t} {shape : ComplexShape ι}
    (E : HomologicalComplex (ModuleCat.{v} R) shape) :
    CommAlgCat.{w} R ⥤ HomologicalComplex (ModuleCat.{max w v} R) shape where
  obj S :=
    { X := fun i ↦ (tensorModuleFunctor (E.X i)).obj S
      d := fun i j ↦ ModuleCat.ofHom ((E.d i j).hom.lTensor S)
      shape := by
        intro i j hij
        rw [E.shape i j hij]
        apply ModuleCat.hom_ext
        exact LinearMap.lTensor_zero S
      d_comp_d' := by
        intro i j k hij hjk
        apply ModuleCat.hom_ext
        change ((E.d j k).hom.lTensor S).comp ((E.d i j).hom.lTensor S) = 0
        rw [← LinearMap.lTensor_comp]
        have h : (E.d j k).hom.comp (E.d i j).hom = 0 :=
          congrArg ModuleCat.Hom.hom (E.d_comp_d i j k)
        rw [h, LinearMap.lTensor_zero] }
  map f :=
    { f := fun i ↦ (tensorModuleFunctor (E.X i)).map f
      comm' := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext s x
        rfl }
  map_id S := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (tensorModuleFunctor (E.X i)).map_id S
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (tensorModuleFunctor (E.X i)).map_comp f g

set_option backward.isDefEq.respectTransparency false in
private def tensorComplexForgetIso {A : Type u} [CommRing A]
    {ι : Type t} {shape : ComplexShape ι}
    (B : Under (CommRingCat.of A)) (E : HomologicalComplex (ModuleCat.{v} A) shape) :
    ((forget₂ (ModuleCat.{max u v} A) Ab).mapHomologicalComplex shape).obj
      ((tensorComplexFunctor E).obj ((commAlgCatEquivUnder (CommRingCat.of A)).inverse.obj B)) ≅
    ((forget₂ (ModuleCat.{max u v} B.right) Ab).mapHomologicalComplex shape).obj
      (((ModuleCat.extendScalars.{u, u, v} B.hom.hom).mapHomologicalComplex shape).obj E) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private def tensorComplexHomologyEquiv {A : Type u} [CommRing A]
    {ι : Type t} {shape : ComplexShape ι}
    (B : Under (CommRingCat.of A))
    (E : HomologicalComplex (ModuleCat.{v} A) shape) (i : ι) :
    ((tensorComplexFunctor E).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).inverse.obj B)).homology i ≃
    (((ModuleCat.extendScalars.{u, u, v} B.hom.hom).mapHomologicalComplex shape).obj E).homology i
      := by
  have := isIso_homologyForgetMap (tensorComplexForgetIso B E).hom i
  exact Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (homologyForgetMap (tensorComplexForgetIso B E).hom i))

private lemma tensorComplexHomologyEquiv_apply {A : Type u} [CommRing A]
    {ι : Type t} {shape : ComplexShape ι}
    (B : Under (CommRingCat.of A))
    (E : HomologicalComplex (ModuleCat.{v} A) shape) (i : ι)
    (x : ((tensorComplexFunctor E).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).inverse.obj B)).homology i) :
    tensorComplexHomologyEquiv B E i x =
      homologyForgetMap (tensorComplexForgetIso B E).hom i x := rfl

private def isColimit_types_of_equiv
    {I : Type w} [Category.{t} I] [IsFilteredOrEmpty I]
    {F : I ⥤ Type u} {G : I ⥤ Type v}
    (s : Cocone F) (c : Cocone G) (hs : IsColimit s)
    (e : ∀ i, F.obj i ≃ G.obj i) (ept : s.pt ≃ c.pt)
    (hmap : ∀ {i j} (f : i ⟶ j) (x : F.obj i), e j (F.map f x) = G.map f (e i x))
    (hleg : ∀ i (x : F.obj i), ept (s.ι.app i x) = c.ι.app i (e i x)) : IsColimit c := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective _ hs (ept.symm x)
    refine ⟨i, e i y, ?_⟩
    rw [← hleg, hy, Equiv.apply_symm_apply]
  · intro i x y hxy
    have he : s.ι.app i ((e i).symm x) = s.ι.app i ((e i).symm y) := by
      apply ept.injective
      simpa only [hleg, Equiv.apply_symm_apply] using hxy
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hs _ _).mp he
    refine ⟨j, f, ?_⟩
    simpa only [hmap, Equiv.apply_symm_apply] using congrArg (e j) hf

set_option backward.isDefEq.respectTransparency false in
private def isColimit_tensorComplex_homology {R : Type u} [CommRing R]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{u} R} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, u, u} R).mapCocone c))
    {ι : Type t} {shape : ComplexShape ι}
    (E : HomologicalComplex (ModuleCat.{v} R) shape) (i : ι) :
    IsColimit ((tensorComplexFunctor E ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) shape i ⋙
      forget _).mapCocone c) :=
  isColimit_shortComplex_homology_of_isColimit_terms
    ((tensorComplexFunctor E ⋙ HomologicalComplex.shortComplexFunctor _ shape i).mapCocone c)
    (isColimit_tensorModuleFunctor hc (E.X (shape.prev i)))
    (isColimit_tensorModuleFunctor hc (E.X i))
    (isColimit_tensorModuleFunctor hc (E.X (shape.next i)))

private def isColimit_tensorComplex_homology_of_isColimit_forget
    {R : Type u} [CommRing R]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{w} R} {c : Cocone F}
    (hc : IsColimit ((forget (CommAlgCat.{w} R)).mapCocone c))
    {ι : Type t} {shape : ComplexShape ι}
    (E : HomologicalComplex (ModuleCat.{v} R) shape) (i : ι) :
    IsColimit ((tensorComplexFunctor E ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{max w v} R) shape i ⋙
      forget _).mapCocone c) :=
  isColimit_shortComplex_homology_of_isColimit_terms
    ((tensorComplexFunctor E ⋙ HomologicalComplex.shortComplexFunctor _ shape i).mapCocone c)
    (isColimit_tensorModuleFunctor_of_isColimit_forget hc (E.X (shape.prev i)))
    (isColimit_tensorModuleFunctor_of_isColimit_forget hc (E.X i))
    (isColimit_tensorModuleFunctor_of_isColimit_forget hc (E.X (shape.next i)))

set_option backward.isDefEq.respectTransparency false in
private lemma tensorComplexFunctor_map_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (E : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    letI := f.toAlgebra
    letI := (g.comp f).toAlgebra
    let q : B →ₐ[A] C := { __ := g, commutes' := fun _ ↦ rfl }
    let Ef := (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (.up ℤ)
    ((forget₂ (ModuleCat.{max u v} A) Ab).mapHomologicalComplex (.up ℤ)).map
      ((tensorComplexFunctor E).map (CommAlgCat.ofHom q)) =
      extensionScalarsUnitComplex g (Ef.obj E) ≫
        ((forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)).map (e.inv.app E) := by
  dsimp only
  let := f.toAlgebra
  let := (g.comp f).toAlgebra
  ext n z
  change B ⊗[A] (E.X n) at z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b m =>
    show g b ⊗ₜ[A, g.comp f] m =
      (ModuleCat.extendScalarsComp.{u, max u v} f g).inv.app (E.X n)
        ((1 : C) ⊗ₜ[B, g] (b ⊗ₜ[A, f] m))
    exact (extendScalarsComp_inv_app_one_tmul_tmul f g (E.X n) b m).symm

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexBaseChange_homology_naturality
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    let Ef := (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (.up ℤ)
    let _UB := (forget₂ (ModuleCat.{max u v} B) Ab).mapHomologicalComplex (.up ℤ)
    let UC := (forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)
    let τ := extensionScalarsUnitComplex g (Ef.obj (CochainComplex.HomComplexR A P F)) ≫
      UC.map (e.inv.app (CochainComplex.HomComplexR A P F))
    let ψ := homComplexMap (ModuleCat.extendScalars.{u, u, max u v} g) (Ef.obj P) (Ef.obj F) ≫
      UC.map (Stacks.HomComplex.TensorHomMap.precomp C (Efg.obj P) (Eg.obj (Ef.obj P)) (Eg.obj
        (Ef.obj F)) (e.hom.app
        P) ≫
        Stacks.HomComplex.TensorHomMap.postcomp C (Efg.obj P) (Eg.obj (Ef.obj F)) (Efg.obj F)
          (e.inv.app F))
    (forget₂ (ModuleCat.{max u v} B) Ab).map
        (HomologicalComplex.homologyMap (homComplexBaseChange f P F) 0) ≫
      homologyForgetMap (E := CochainComplex.HomComplexR B (Ef.obj P) (Ef.obj F))
        (F := CochainComplex.HomComplexR C (Efg.obj P) (Efg.obj F)) ψ 0 =
      homologyForgetMap (E := Ef.obj (CochainComplex.HomComplexR A P F))
        (F := Efg.obj (CochainComplex.HomComplexR A P F)) τ 0 ≫
          (forget₂ (ModuleCat.{max u v} C) Ab).map
        (HomologicalComplex.homologyMap (homComplexBaseChange (g.comp f) P F) 0) := by
  dsimp only
  apply homologyForgetMap_naturality
  simpa only [Functor.map_comp, Category.assoc] using
    homComplexBaseChange_naturality_underlying f g P F

set_option maxHeartbeats 600000 in
-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
private lemma tensorComplexHomologyEquiv_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (E : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ) :
    letI := f.toAlgebra
    letI := (g.comp f).toAlgebra
    let q : B →ₐ[A] C := { __ := g, commutes' := fun _ ↦ rfl }
    let EB := (tensorComplexFunctor E).obj (CommAlgCat.of A B)
    let _EC := (tensorComplexFunctor E).obj (CommAlgCat.of A C)
    let Ef := (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (.up ℤ)
    let UC := (forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)
    let τ := extensionScalarsUnitComplex g (Ef.obj E) ≫ UC.map (e.inv.app E)
    ∀ x : EB.homology i,
      tensorComplexHomologyEquiv (Under.mk (CommRingCat.ofHom (g.comp f))) E i
          (HomologicalComplex.homologyMap ((tensorComplexFunctor E).map (CommAlgCat.ofHom q)) i x) =
        homologyForgetMap (E := Ef.obj E) (F := Efg.obj E) τ i
          (tensorComplexHomologyEquiv (Under.mk (CommRingCat.ofHom f)) E i x) := by
  let := f.toAlgebra
  let := (g.comp f).toAlgebra
  intro q EB EC Ef Eg Efg e UC τ x
  let eB := tensorComplexForgetIso (Under.mk (CommRingCat.ofHom f)) E
  let eC := tensorComplexForgetIso (Under.mk (CommRingCat.ofHom (g.comp f))) E
  let UA := (forget₂ (ModuleCat.{max u v} A) Ab).mapHomologicalComplex (.up ℤ)
  let φ : EB ⟶ EC := (tensorComplexFunctor E).map (CommAlgCat.ofHom q)
  have hs : eB.hom ≫ τ = UA.map φ ≫ eC.hom := by
    show 𝟙 _ ≫ τ = UA.map φ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact (tensorComplexFunctor_map_comp f g E).symm
  have hh := congrArg (fun η ↦ homologyForgetMap (E := EB) (F := Efg.obj E) η i) hs
  rw [homologyForgetMap_comp (E := EB) (F := Ef.obj E) (G := Efg.obj E) eB.hom τ i,
    homologyForgetMap_comp (E := EB) (F := EC) (G := Efg.obj E) (UA.map φ) eC.hom i,
    homologyForgetMap_map] at hh
  exact (ConcreteCategory.congr_hom hh x).symm

set_option backward.isDefEq.respectTransparency false in
private def tensorHomComplexHomologyEquivDerivedHom
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F)] :
    ((tensorComplexFunctor (CochainComplex.HomComplexR A P F)).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).inverse.obj
        (Under.mk (CommRingCat.ofHom f)))).homology 0 ≃
      ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj (DerivedCategory.Q.obj P) ⟶
       (totalDerivedExtensionScalars.{u, u, v} f).functor.obj (DerivedCategory.Q.obj F)) :=
  (tensorComplexHomologyEquiv (Under.mk (CommRingCat.ofHom f))
    (CochainComplex.HomComplexR A P F) 0).trans
      (homComplexBaseChangeHomologyEquivLeftDerivedHom f P F a b d
        (totalDerivedExtensionScalars.{u, u, v} f).functor
        (totalDerivedExtensionScalars.{u, u, v} f).comparison)

section RepresentativeIsomorphisms
universe u₁ u₂ u₃ v₁ v₂ v₃
private lemma homCongr_map_naturality
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (f : F.obj X ⟶ F.obj Y) :
    Iso.homCongr (α.app X') (α.app Y')
        (G.map (Iso.homCongr (F.mapIso eX) (F.mapIso eY) f)) =
      Iso.homCongr (H.mapIso eX) (H.mapIso eY)
        (Iso.homCongr (α.app X) (α.app Y) (G.map f)) := by
  simp only [Iso.homCongr_apply, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Iso.app_inv, Iso.app_hom, Category.assoc]
  have hx := α.inv.naturality eX.inv
  have hy := α.hom.naturality eY.hom
  dsimp only [Functor.comp_map] at hx hy
  rw [← reassoc_of% hx, hy]

end RepresentativeIsomorphisms

section ScalarTowerNaturality
variable
    (comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ),
      (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
        (totalDerivedExtensionScalars.{u, u, v} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{u, u, v} g).comparison.app
            (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (extensionOfScalarsComplexComp.{u, v} f g).inv.app P)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private lemma homComplexBaseChangeHomologyEquivLeftDerivedHom_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app F)]
    (x : (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.HomComplexR A P F)).homology 0) :
    let Ef := (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (.up ℤ)
    let UC := (forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)
    let τ := extensionScalarsUnitComplex g (Ef.obj (CochainComplex.HomComplexR A P F)) ≫
      UC.map (e.inv.app (CochainComplex.HomComplexR A P F))
    homComplexBaseChangeHomologyEquivLeftDerivedHom (g.comp f) P F a b d
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
        (homologyForgetMap (E := Ef.obj (CochainComplex.HomComplexR A P F))
        (F := Efg.obj (CochainComplex.HomComplexR A P F)) τ 0 x) =
      derivedHomBaseChange comp f g
        (homComplexBaseChangeHomologyEquivLeftDerivedHom f P F a b d
          (totalDerivedExtensionScalars.{u, u, v} f).functor
          (totalDerivedExtensionScalars.{u, u, v} f).comparison x) := by
  intro Ef Eg Efg e UC τ
  let ψ := homComplexMap (ModuleCat.extendScalars.{u, u, max u v} g) (Ef.obj P) (Ef.obj F) ≫
    UC.map (Stacks.HomComplex.TensorHomMap.precomp C (Efg.obj P) (Eg.obj (Ef.obj P)) (Eg.obj (Ef.obj
      F)) (e.hom.app P) ≫
      Stacks.HomComplex.TensorHomMap.postcomp C (Efg.obj P) (Eg.obj (Ef.obj F)) (Efg.obj F)
        (e.inv.app F))
  have := isKProjective_extendScalars_obj f P d
  have := isKProjective_extendScalars_obj (g.comp f) P d
  have h := qh_map_homAddEquiv_bijective (Ef.obj P) (Ef.obj F)
  have h' := qh_map_homAddEquiv_bijective (Efg.obj P) (Efg.obj F)
  have hn := homComplexBaseChange_homology_naturality f g P F
  have hx := ConcreteCategory.congr_hom hn x
  change homologyForgetMap (E := CochainComplex.HomComplexR B (Ef.obj P) (Ef.obj F))
      (F :=
        CochainComplex.HomComplexR C (Efg.obj P) (Efg.obj F)) ψ 0 (HomologicalComplex.homologyMap
        (homComplexBaseChange f P F) 0 x) =
    HomologicalComplex.homologyMap (homComplexBaseChange (g.comp f) P F) 0
      (homologyForgetMap (E := Ef.obj (CochainComplex.HomComplexR A P F))
        (F := Efg.obj (CochainComplex.HomComplexR A P F)) τ 0 x) at hx
  show Iso.homCongr
      (asIso ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P)).symm
      (asIso ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app F)).symm
      (homComplexRHomologyEquivDerivedHom (Efg.obj P) (Efg.obj F) h'
        (HomologicalComplex.homologyMap (homComplexBaseChange (g.comp f) P F) 0
          (homologyForgetMap (E := Ef.obj (CochainComplex.HomComplexR A P F))
        (F := Efg.obj (CochainComplex.HomComplexR A P F)) τ 0 x))) = _
  rw [← hx]
  apply homComplexRHomologyEquivDerivedHom_naturality_congr
    (Ef.obj P) (Ef.obj F) (Efg.obj P) (Efg.obj F) h h'
    (asIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P))
    (asIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F))
  intro z
  refine ⟨e.hom.app P ≫ Eg.map z ≫ e.inv.app F, ?_, ?_⟩
  · dsimp only [ψ, HomologicalComplex.comp_f]
    rw [ConcreteCategory.comp_apply, homComplexMap_ofHom]
    exact homComplexPrePostcomp_ofHom (e.hom.app P) (e.inv.app F) (Eg.map z)
  · simp only [asIso_hom, asIso_inv]
    rw [derivedHomBaseChange_ofHom comp hcomp f g P F z]
    simp only [Functor.map_comp, Category.assoc]
    rfl

-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
include hcomp in
private lemma tensorHomComplexHomologyEquivDerivedHom_naturality
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (f' : A →+* C) (h : g.comp f = f')
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f').comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f').comparison.app F)] :
    letI := f.toAlgebra
    letI := f'.toAlgebra
    let q : B →ₐ[A] C := { __ := g, commutes' := fun x ↦ congrArg (fun k : A →+* C ↦ k x) h }
    ∀ x : ((tensorComplexFunctor (CochainComplex.HomComplexR A P F)).obj
        (CommAlgCat.of A B)).homology 0,
      tensorHomComplexHomologyEquivDerivedHom f' P F a b d
        (HomologicalComplex.homologyMap
          ((tensorComplexFunctor (CochainComplex.HomComplexR A P F)).map (CommAlgCat.ofHom q)) 0 x)
            =
      derivedHomBaseChangeAlong comp f g f' h
        (tensorHomComplexHomologyEquivDerivedHom f P F a b d x) := by
  subst f'
  let := f.toAlgebra
  let := (g.comp f).toAlgebra
  intro q x
  rw [derivedHomBaseChangeAlong_rfl]
  dsimp only [tensorHomComplexHomologyEquivDerivedHom, Equiv.trans_apply]
  rw [tensorComplexHomologyEquiv_comp]
  exact homComplexBaseChangeHomologyEquivLeftDerivedHom_comp comp hcomp f g P F a b d _

-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def isColimit_derivedHomFunctor_of_representatives
    {A : Type u} [CommRing A]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (J : I ⥤ Under (CommRingCat.of A)) (c : Cocone J)
    (hc : IsColimit (((commAlgCatEquivUnder (CommRingCat.of A)).inverse ⋙
      forget (CommAlgCat.{u} A)).mapCocone c))
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) (a b d : ℤ)
    [P.IsStrictlyLE d] [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    (hF : ∀ i, IsIso ((totalDerivedExtensionScalars.{u, u, v}
      (J.obj i).hom.hom).comparison.app F))
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} c.pt.hom.hom).comparison.app F)] :
    IsColimit ((derivedHomFunctor comp hcomp (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj F)).mapCocone c) := by
  have (n : ℤ) : Module.Flat A (P.X n) := inferInstance
  have hP (B : Under (CommRingCat.of A)) :
      IsIso ((totalDerivedExtensionScalars.{u, u, v} B.hom.hom).comparison.app P) :=
    isIso_comparison_app_of_isStrictlyLE_flat
      (totalDerivedExtensionScalars.{u, u, v} B.hom.hom) P d
  have (i : I) := hF i
  let T := (commAlgCatEquivUnder (CommRingCat.of A)).inverse ⋙
    tensorComplexFunctor (CochainComplex.HomComplexR A P F) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (.up ℤ) 0 ⋙ forget _
  have hT : IsColimit (T.mapCocone c) :=
    isColimit_tensorComplex_homology_of_isColimit_forget
      (c := (commAlgCatEquivUnder (CommRingCat.of A)).inverse.mapCocone c)
      hc (CochainComplex.HomComplexR A P F) 0
  let H := derivedHomFunctor comp hcomp (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj F)
  have key {X Y : Under (CommRingCat.of A)}
      [IsIso ((totalDerivedExtensionScalars.{u, u, v} X.hom.hom).comparison.app F)]
      [IsIso ((totalDerivedExtensionScalars.{u, u, v} Y.hom.hom).comparison.app F)]
      (φ : X ⟶ Y) (x) :=
    tensorHomComplexHomologyEquivDerivedHom_naturality comp hcomp X.hom.hom φ.right.hom Y.hom.hom
      (congrArg CommRingCat.Hom.hom (Under.w φ)) P F a b d x
  apply isColimit_types_of_equiv (T.mapCocone c) (H.mapCocone c) hT
    (fun i ↦ tensorHomComplexHomologyEquivDerivedHom.{u, v} (A := A) (J.obj i).hom.hom P F a b d)
    (tensorHomComplexHomologyEquivDerivedHom.{u, v} (A := A) c.pt.hom.hom P F a b d)
  · intro i j q x
    exact key (J.map q) x
  · intro i x
    exact key (Y := c.pt) (c.ι.app i) x

-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def isColimit_derivedHomFunctor_of_iso
    {A : Type u} [CommRing A]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (J : I ⥤ Under (CommRingCat.of A)) (c : Cocone J)
    {K L K' L' : DerivedCategory (ModuleCat.{max u v} A)}
    (eK : K ≅ K') (eL : L ≅ L')
    (hc : IsColimit ((derivedHomFunctor comp hcomp K L).mapCocone c)) :
    IsColimit ((derivedHomFunctor comp hcomp K' L').mapCocone c) := by
  apply isColimit_types_of_equiv
    ((derivedHomFunctor comp hcomp K L).mapCocone c)
    ((derivedHomFunctor comp hcomp K' L').mapCocone c) hc
    (fun i ↦ Iso.homCongr
      ((totalDerivedExtensionScalars.{u, u, v} (J.obj i).hom.hom).functor.mapIso eK)
      ((totalDerivedExtensionScalars.{u, u, v} (J.obj i).hom.hom).functor.mapIso eL))
    (Iso.homCongr
      ((totalDerivedExtensionScalars.{u, u, v} c.pt.hom.hom).functor.mapIso eK)
      ((totalDerivedExtensionScalars.{u, u, v} c.pt.hom.hom).functor.mapIso eL))
  all_goals
    have key {X Y : Under (CommRingCat.of A)} (φ : X ⟶ Y) (x) :=
      (homCongr_map_naturality _ _ _
        (comp X.hom.hom φ.right.hom ≪≫
          derivedExtensionScalarsCongr (congrArg CommRingCat.Hom.hom (Under.w φ))) eK eL x).symm
  · intro i j q x
    exact key (J.map q) x
  · intro i x
    exact key (c.ι.app i) x

end ScalarTowerNaturality
end HomComplexHomology

section LiftedHomRepresentatives
universe u v w
attribute [local instance] RingHomInvPair.of_ringEquiv Algebra.TensorProduct.rightAlgebra

private def restrictScalarsSemilinearEquiv {R : Type u} {S : Type v}
    [Ring R] [Ring S] (e : R ≃+* S) (M : ModuleCat.{w} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ≃ₛₗ[RingHomClass.toRingHom e] M :=
  LinearEquiv.ofBijective
    ((ModuleCat.semilinearMapAddEquiv (RingHomClass.toRingHom e) _ M).symm (𝟙 _))
    Function.bijective_id

private lemma free_restrictScalars_of_ringEquiv {R : Type u} {S : Type v}
    [Ring R] [Ring S] (e : R ≃+* S) (M : ModuleCat.{w} S) [Module.Free S M] :
    Module.Free R ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
  Module.Free.of_equiv (restrictScalarsSemilinearEquiv e M).symm

private lemma finite_restrictScalars_of_ringEquiv {R : Type u} {S : Type v}
    [Ring R] [Ring S] (e : R ≃+* S) (M : ModuleCat.{w} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) :=
  Module.Finite.of_surjective (restrictScalarsSemilinearEquiv e M).symm.toLinearMap
    (restrictScalarsSemilinearEquiv e M).symm.surjective

-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
lemma isIso_tensorBaseChange_comparison_app_of_flat
    {R : Type uR} [CommRing R] (A : Type uA) [CommRing A] [Algebra R A]
    [Module.Flat R A] (S : Type uR) [CommRing S] [Algebra R S]
    (P : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{uR} A)) ℤ)
    (d : ℤ) [P.IsStrictlyLE d]
    [∀ n, Module.Flat R ((ModuleCat.restrictScalars
      (algebraMap R (ULift.{uR} A))).obj (P.X n))] :
    IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      ((Algebra.TensorProduct.includeRight.toRingHom : A →+* S ⊗[R] A).comp
        ULift.ringEquiv.toRingHom)).comparison.app P) := by
  let A' := ULift.{uR} A
  let B := S ⊗[R] A
  let f : A' →ₐ[R] B := Algebra.TensorProduct.includeRight.comp ULift.algEquiv.toAlgHom
  let : Algebra A' B := f.toRingHom.toAlgebra
  let : IsScalarTower R A' B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let e : S ⊗[R] A' ≃ₐ[S] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) ULift.algEquiv
  have hp : Algebra.IsPushout R S A' B := Algebra.IsPushout.of_equiv e (by
    ext x
    show e (1 ⊗ₜ[R] x) = f x
    show (Algebra.TensorProduct.map (AlgHom.id S S)
      (ULift.algEquiv : A' ≃ₐ[R] A).toAlgHom) (1 ⊗ₜ[R] x) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl)
  let : Algebra.IsPushout R A' S B := Algebra.IsPushout.symm hp
  let DR := totalDerivedExtensionScalars.{uR, uR, max uA uM} (algebraMap R S)
  let DA := totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f.toRingHom
  let : DR.functor.IsLeftDerivedFunctor DR.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ)) := DR.isLeftDerived
  let : DA.functor.IsLeftDerivedFunctor DA.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A') (.up ℤ)) := DA.isLeftDerived
  let P' : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ :=
    ((ModuleCat.restrictScalars (algebraMap R A')).mapHomologicalComplex (.up ℤ)).obj P
  have (n : ℤ) : Module.Flat R (P'.X n) := inferInstanceAs
    (Module.Flat R ((ModuleCat.restrictScalars (algebraMap R (ULift.{uR} A))).obj (P.X n)))
  have : P'.IsStrictlyLE d := inferInstance
  have : IsIso (DR.comparison.app P') :=
    isIso_comparison_app_of_isStrictlyLE_flat DR P' d
  exact isIso_comparison_app_of_torIndependent.{uR, max uR uA, uR, max uR uA, uM}
    (torIndependent_of_flat (R := R) (A := A') (B := S))
    DR.functor DA.functor DR.comparison DA.comparison P

end LiftedHomRepresentatives

section TorAmplitudeLift

universe u v

open MonoidalCategory

section Coinciding

variable {S : Type u} [CommRing S]

/-- The projective-resolution model of `H^i(K ⊗ᴸ N)` used by
  `StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude`
vanishes as soon as the cohomology of the total left derived functor of termwise tensoring
by `N` does. A K-flat resolution of `K` computes both, since tensoring with the chosen
projective resolution of `N` inverts quasi-isomorphisms. -/
private theorem isZero_derivedTensorHomology_of_termwiseDerived
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (N : ModuleCat.{u} S) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
      ((termwiseDerived N).obj (DerivedCategory.Q.obj K)))) :
    IsZero (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology K N i) := by
  obtain ⟨E, π, hE, _, hπ, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
  have := hπ
  have hPN : (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N).KFlat :=
    kFlat_of_isStrictlyLE_projective (ProjectiveResolution.of N).cochainComplex 0 inferInstance
  have := quasiIso_tensorRight_map hPN π
  have h₁ : IsIso (HomologicalComplex.homologyMap
      ((tensorRight (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)).map π) i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  refine (asIso (HomologicalComplex.homologyMap
    ((tensorRight (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)).map π)
      i)).isZero_iff.1 ?_
  have := quasiIso_tensorLeft_map E hE (ProjectiveResolution.of N).π'
  have h₂ : IsIso (HomologicalComplex.homologyMap
      ((tensorLeft E).map (ProjectiveResolution.of N).π') i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  refine (asIso (HomologicalComplex.homologyMap
    ((tensorLeft E).map (ProjectiveResolution.of N).π') i)).isZero_iff.2 ?_
  refine ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) i).mapIso
    (StacksDraft.TorAmplitude.tensorSwapIso E
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) ≪≫
      StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N E ≪≫
      (NatIso.mapHomologicalComplex (tensorLeftIsoTensorModuleRight.{u, u} N)
        (ComplexShape.up ℤ)).app E)).isZero_iff.2 ?_
  have hcounit : IsIso ((termwiseDerivedCounit N).app E) := by
    have := isLeftDerivedFunctor_termwiseDerivedCounit N
    exact isIso_derivedComparison_app_of_kFlat.{u, u} N (termwiseDerived N)
      (termwiseDerivedCounit N) E hE
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
      ((termwiseDerived N).mapIso (asIso (DerivedCategory.Q.map π)).symm ≪≫
        asIso ((termwiseDerivedCounit N).app E)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app _).isZero_iff.1 h

/-- Termwise tensoring by isomorphic modules gives isomorphic functors. -/
private def tensorModuleRightCongr {N N' : ModuleCat.{u} S} (α : N ≅ N') :
    tensorModuleRight N ≅ tensorModuleRight N' :=
  NatIso.ofComponents
    (fun M ↦ (TensorProduct.congr (LinearEquiv.refl S M) α.toLinearEquiv).toModuleIso) (by
      intro X Y f
      ext : 1
      apply TensorProduct.ext'
      intro x y
      rfl)

/-- The total left derived functors of termwise tensoring by isomorphic modules are
isomorphic, by uniqueness of total left derived functors. -/
private def termwiseDerivedCongr {N N' : ModuleCat.{u} S} (α : N ≅ N') :
    termwiseDerived N ≅ termwiseDerived N' := by
  letI := isLeftDerivedFunctor_termwiseDerivedCounit N
  letI := isLeftDerivedFunctor_termwiseDerivedCounit N'
  exact Functor.leftDerivedNatIso _ _ (termwiseDerivedCounit N) (termwiseDerivedCounit N')
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (tensorModuleRightCongr α) (ComplexShape.up ℤ))
      DerivedCategory.Q)

end Coinciding

section ScalarLift

variable {R : Type u} [CommRing R]

/-- A complex whose localization has Tor amplitude in `[a, b]` for a certified derived tensor
product has, after raising the coefficient ring to the module universe, Tor amplitude in
`[a, b]` in the projective-resolution sense of `StacksDraft.TorAmplitude.FaithfullyFlat`. -/
private theorem hasTorAmplitude_scalarLift_complex
    (D : DerivedTensoringDatum.{u, max u v} R)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (h : HasTorAmplitude D.tensor D.comparison D.isLeftDerived
      (DerivedCategory.Q.obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b := by
  intro N' i hi
  let G := scalarLift.{u, v} (R := R)
  let := scalarLift_isEquivalence.{u, v} (R := R)
  let M := G.objPreimage N'
  let := D.isLeftDerived M
  refine isZero_derivedTensorHomology_of_termwiseDerived _ N' i ?_
  refine ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} R)) i).mapIso
    ((derivedTensorScalarLiftIso.{u, v}
        (D.tensor.flip.obj ((DerivedCategory.singleFunctor
          (ModuleCat.{max u v} R) 0).obj M)) M (D.comparison M)).app
        (DerivedCategory.Q.obj K) ≪≫
      (termwiseDerived (G.obj M)).mapIso (G.mapDerivedCategoryFactors.app K) ≪≫
      (termwiseDerivedCongr (G.objObjPreimageIso N')).app
        (DerivedCategory.Q.obj (((scalarLift.{u, v} (R := R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)))).isZero_iff.1 ?_
  exact scalarLift_map_isZero_homology _ i
    (h M i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi))

end ScalarLift

end TorAmplitudeLift

private theorem exists_bounded_homComplex_representatives
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (D : DerivedTensoringDatum.{uR, max uR uA uM} R)
    (K L : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hL : HasFiniteTorDimension D.tensor D.comparison D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj L)) :
    ∃ (P F : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ Nonempty (DerivedCategory.Q.obj F ≅ L) ∧
      (∃ d : ℤ, P.IsStrictlyLE d) ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      (∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))) := by
  let PK := DerivedCategory.Q.objPreimage K
  let PL := DerivedCategory.Q.objPreimage L
  let eK := DerivedCategory.Q.objObjPreimageIso K
  let eL := DerivedCategory.Q.objObjPreimageIso L
  have hPK : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj PK) := by
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hK
    exact ⟨Q, hQ, ⟨eQ ≪≫ eK.symm⟩⟩
  have hPK' : ∀ m : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      (DerivedCategory.Q.obj PK) m := by
    intro m
    obtain ⟨Q, hQ, α, hα⟩ := (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mp hPK m
    exact ⟨Q, ⟨hQ.lowerBound, hQ.upperBound, hQ.finiteFree⟩, α, hα⟩
  obtain ⟨a, b, hL⟩ := hL
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let PR := (U.mapHomologicalComplex (.up ℤ)).obj PL
  let eR : DerivedCategory.Q.obj PR ≅ U.mapDerivedCategory.obj L :=
    (U.mapDerivedCategoryFactors.app PL).symm ≪≫ U.mapDerivedCategory.mapIso eL
  have hPR : HasTorAmplitude D.tensor D.comparison D.isLeftDerived
      (DerivedCategory.Q.obj PR) a b := by
    intro M i hi
    exact (hL M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((D.tensor.mapIso eR).app ((DerivedCategory.singleFunctor _ 0).obj M)))
  have hPL := hasTorAmplitude_scalarLift_complex.{uR, max uA uM} D PR a b hPR
  have hPL' : ∃ a b : ℤ, StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars ((algebraMap R A).comp
        (ULift.ringEquiv : ULift.{max uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
        (.up ℤ)).obj PL) a b := ⟨a, b, hPL⟩
  obtain ⟨P, F, eP, eF, hd, hP, hFbounds, hF, _⟩ :=
    StacksDraft.RelativelyPerfect.exists_homComplex_representation.{uR, uA, uM, uR} R A PK PL hPK'
      hPL'
  exact ⟨P, F, ⟨eP ≪≫ eK⟩, ⟨eF ≪≫ eL⟩, hd, hP, hFbounds, hF⟩

end PseudoCoherence

end
