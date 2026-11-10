module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.ComplexDescent

/-!
# Base change of Hom complexes

Base change of Hom complexes between bounded complexes, and the identification of the homology
of the Hom complex with morphisms in the derived category.

This is part 5 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
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

section HomComplexBaseChange

universe u v w

open scoped ChangeOfRings

private lemma canonicalHomComplexBaseChangeIso_unique
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ)
    (e₁ e₂ : ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F))
    (h₁ : StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso f P F e₁)
    (h₂ : StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso f P F e₂) : e₁ = e₂ := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (h₁ n p q hpq 1 1 z x).trans (h₂ n p q hpq 1 1 z x).symm


open scoped ModuleCat.Algebra

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

private lemma homCochainBaseChange_ofHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    {P F : CochainComplex (ModuleCat.{w} A) ℤ} (g : P ⟶ F) (a : B) :
    homCochainBaseChange f P F 0
      (a ⊗ₜ[A, f] CochainComplex.HomComplex.Cochain.ofHom g) =
      a • CochainComplex.HomComplex.Cochain.ofHom
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).map g) := by
  let := f.toAlgebra
  change LinearMap.liftBaseChange B (homCochainExtendScalars f P F 0)
    (a ⊗ₜ[A] CochainComplex.HomComplex.Cochain.ofHom g) = _
  rw [LinearMap.liftBaseChange_tmul]
  exact congrArg (a •
    ·) (CochainComplex.HomComplex.Cochain.map_ofHom P F g (ModuleCat.extendScalars.{u, v, w} f))

set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsComp_inv_app_one_tmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : ModuleCat.{max u w} A) (m : M) :
    (ModuleCat.extendScalarsComp.{u, max u w} f g).inv.app M
      ((1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] m)) =
        (1 : C) ⊗ₜ[A, g.comp f] m := by
  rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m]
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalarsComp.{u, max u w} f g).hom_inv_id_app M) _

set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsComp_inv_app_one_tmul_tmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : ModuleCat.{max u w} A) (b : B) (m : M) :
    (ModuleCat.extendScalarsComp.{u, max u w} f g).inv.app M
      ((1 : C) ⊗ₜ[B, g] (b ⊗ₜ[A, f] m)) = (g b) ⊗ₜ[A, g.comp f] m := by
  let := f.toAlgebra
  let := g.toAlgebra
  have hb : b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul f, mul_one]
  have ht : (1 : C) ⊗ₜ[B] (b ⊗ₜ[A] m) =
      g b • ((1 : C) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)) := by
    rw [hb, TensorProduct.tmul_smul]
    change (g b * 1) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] m) =
      g b • ((1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] m))
    rfl
  rw [ht, map_smul]
  rw [extendScalarsComp_inv_app_one_tmul]
  rw [ModuleCat.ExtendScalars.smul_tmul (g.comp f), mul_one]

private lemma homComplexPrePostcomp_v {R : Type u} [CommRing R]
    {P F P' F' : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : P' ⟶ P) (b : F ⟶ F') (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain P F n) (p q : ℤ) (hpq : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.precomp R P' P F a ≫ Stacks.HomComplex.TensorHomMap.postcomp R
      P' F F' b).f n z).v p q hpq) =
      a.f p ≫ z.v p q hpq ≫ b.f q := by
  change (((CochainComplex.HomComplex.Cochain.ofHom a).comp z (zero_add n)).comp
    (CochainComplex.HomComplex.Cochain.ofHom b) (add_zero n)).v p q hpq = _
  simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
-- elaborating the composite natural transformations of derived functors below
private lemma homComplexBaseChange_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (P F : CochainComplex (ModuleCat.{max u w} A) ℤ) :
    let Ef := (ModuleCat.extendScalars.{u, u, max u w} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u w} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u w} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u w} f g) (.up ℤ)
    Eg.map (homComplexBaseChange f P F) ≫
      homComplexBaseChange g (Ef.obj P) (Ef.obj F) ≫
      Stacks.HomComplex.TensorHomMap.precomp C (Efg.obj P) (Eg.obj (Ef.obj P)) (Eg.obj (Ef.obj F))
        (e.hom.app P) ≫
      Stacks.HomComplex.TensorHomMap.postcomp C (Efg.obj P) (Eg.obj (Ef.obj F)) (Efg.obj F)
        (e.inv.app F) =
        e.inv.app (CochainComplex.HomComplexR A P F) ≫ homComplexBaseChange (g.comp f) P F := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  apply ((ModuleCat.extendRestrictScalarsAdj.{max u w} g).homEquiv _ _).injective
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  let Ef := (ModuleCat.extendScalars.{u, u, max u w} f).mapHomologicalComplex (.up ℤ)
  let Eg := (ModuleCat.extendScalars.{u, u, max u w} g).mapHomologicalComplex (.up ℤ)
  let Efg := (ModuleCat.extendScalars.{u, u, max u w} (g.comp f)).mapHomologicalComplex (.up ℤ)
  let e : Efg ≅ Ef ⋙ Eg :=
    NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max u w} f g) (.up ℤ)
  change ((Stacks.HomComplex.TensorHomMap.precomp C (Efg.obj P) (Eg.obj (Ef.obj P)) (Eg.obj (Ef.obj
    F))
      (e.hom.app P) ≫
    Stacks.HomComplex.TensorHomMap.postcomp C (Efg.obj P) (Eg.obj (Ef.obj F)) (Efg.obj F) (e.inv.app
      F)).f n
      (homCochainBaseChange g (Ef.obj P) (Ef.obj F) n
        ((1 : C) ⊗ₜ[B, g] homCochainBaseChange f P F n ((1 : B) ⊗ₜ[A, f] z)))) =
    homCochainBaseChange (g.comp f) P F n
      ((ModuleCat.extendScalarsComp.{u, max u w} f g).inv.app
        ((CochainComplex.HomComplexR A P F).X n)
        ((1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] z)))
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [homComplexPrePostcomp_v]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (ModuleCat.extendScalarsComp.{u, max u w} f g).inv.app (F.X q)
    (((homCochainBaseChange g (Ef.obj P) (Ef.obj F) n)
      ((1 : C) ⊗ₜ[B, g] (homCochainBaseChange f P F n ((1 : B) ⊗ₜ[A, f] z)))).v p q hpq
        ((ModuleCat.extendScalarsComp.{u, max u w} f g).hom.app (P.X p)
          ((1 : C) ⊗ₜ[A, g.comp f] x))) =
    ((homCochainBaseChange (g.comp f) P F n)
      ((ModuleCat.extendScalarsComp.{u, max u w} f g).inv.app
        ((CochainComplex.HomComplexR A P F).X n)
        ((1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] z)))).v p q hpq
          ((1 : C) ⊗ₜ[A, g.comp f] x)
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul f g (P.X p) x,
    extendScalarsComp_inv_app_one_tmul f g]
  have h₁ := homCochainBaseChange_tmul g (Ef.obj P) (Ef.obj F) n p q hpq
    (1 : C) (1 : C) (homCochainBaseChange f P F n ((1 : B) ⊗ₜ[A, f] z))
      ((1 : B) ⊗ₜ[A, f] x)
  have h₂ := homCochainBaseChange_tmul f P F n p q hpq (1 : B) (1 : B) z x
  have h₃ := homCochainBaseChange_tmul (g.comp f) P F n p q hpq (1 : C) (1 : C) z x
  rw [h₁, h₂, h₃]
  simp only [one_mul]
  exact extendScalarsComp_inv_app_one_tmul f g (F.X q) ((z.v p q hpq).hom x)


lemma isIso_homComplexBaseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)] :
    IsIso (homComplexBaseChange f P F) := by
  have (n : ℤ) : IsIso ((homComplexBaseChange f P F).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (homCochainBaseChange_bijective f P F a b n)
  exact
    HomologicalComplex.Hom.isIso_of_components _

private lemma existsUnique_canonicalHomComplexBaseChangeIso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)] :
    ∃! e : ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F),
      StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso f P F e := by
  have := isIso_homComplexBaseChange f P F a b
  refine ⟨asIso (homComplexBaseChange f P F), ?_, ?_⟩
  · exact homCochainBaseChange_tmul f P F
  · intro e he
    exact canonicalHomComplexBaseChangeIso_unique f P F e _ he
      (homCochainBaseChange_tmul f P F)

end HomComplexBaseChange

section HomComplexHomology

universe u v w

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower
open scoped ModuleCat.Algebra ChangeOfRings
universe t

private def homComplexMap {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (Φ : C ⥤ D) [Φ.Additive] (P F : CochainComplex C ℤ) :
    CochainComplex.HomComplex P F ⟶
      CochainComplex.HomComplex
        ((Φ.mapHomologicalComplex (.up ℤ)).obj P)
        ((Φ.mapHomologicalComplex (.up ℤ)).obj F) where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.map Φ
      map_zero' := CochainComplex.HomComplex.Cochain.map_zero P F n Φ
      map_add' := fun z t ↦ CochainComplex.HomComplex.Cochain.map_add z t Φ }
  comm' i j hij := by
    ext z
    exact CochainComplex.HomComplex.δ_map i j z Φ

private lemma homComplexMap_ofHom {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (Φ : C ⥤ D) [Φ.Additive] {P F : CochainComplex C ℤ} (g : P ⟶ F) :
    (homComplexMap Φ P F).f 0 (CochainComplex.HomComplex.Cochain.ofHom g) =
      CochainComplex.HomComplex.Cochain.ofHom ((Φ.mapHomologicalComplex (.up ℤ)).map g) :=
  CochainComplex.HomComplex.Cochain.map_ofHom P F g Φ

private lemma homComplexPrePostcomp_ofHom {R : Type u} [CommRing R]
    {P F P' F' : CochainComplex (ModuleCat.{v} R) ℤ}
    (a : P' ⟶ P) (b : F ⟶ F') (g : P ⟶ F) :
    ((Stacks.HomComplex.TensorHomMap.precomp R P' P F a ≫ Stacks.HomComplex.TensorHomMap.postcomp R
      P' F F' b).f 0)
      (CochainComplex.HomComplex.Cochain.ofHom g) =
        CochainComplex.HomComplex.Cochain.ofHom (a ≫ g ≫ b) := by
  change ((CochainComplex.HomComplex.Cochain.ofHom a).comp
    (CochainComplex.HomComplex.Cochain.ofHom g) (zero_add 0)).comp
      (CochainComplex.HomComplex.Cochain.ofHom b) (add_zero 0) = _
  simp only [← CochainComplex.HomComplex.Cochain.ofHom_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private def extensionScalarsUnitComplex {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type t} {shape : ComplexShape ι}
    (E : HomologicalComplex (ModuleCat.{max w v} A) shape) :
    ((forget₂ (ModuleCat.{max w v} A) Ab).mapHomologicalComplex shape).obj E ⟶
      ((forget₂ (ModuleCat.{max w v} B) Ab).mapHomologicalComplex shape).obj
        (((ModuleCat.extendScalars.{u, w, max w v} f).mapHomologicalComplex shape).obj E) :=
  ((forget₂ (ModuleCat.{max w v} A) Ab).mapHomologicalComplex shape).map
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{v} f).unit shape).app E)

private lemma extensionScalarsUnitComplex_f {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type t} {shape : ComplexShape ι}
    (E : HomologicalComplex (ModuleCat.{max w v} A) shape) (i : ι) (x : E.X i) :
    (extensionScalarsUnitComplex f E).f i x = (1 : B) ⊗ₜ[A, f] x := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma extensionScalarsUnitComplex_naturality {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type t} {shape : ComplexShape ι}
    {E E' : HomologicalComplex (ModuleCat.{max w v} A) shape} (φ : E ⟶ E') :
    ((forget₂ (ModuleCat.{max w v} A) Ab).mapHomologicalComplex shape).map φ ≫
        extensionScalarsUnitComplex f E' =
      extensionScalarsUnitComplex f E ≫
        ((forget₂ (ModuleCat.{max w v} B) Ab).mapHomologicalComplex shape).map
          (((ModuleCat.extendScalars.{u, w, max w v} f).mapHomologicalComplex shape).map φ) := by
  ext i x
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma extensionScalarsUnitComplex_homComplexBaseChange {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{max w v} A) ℤ) :
    extensionScalarsUnitComplex f (CochainComplex.HomComplexR A P F) ≫
      ((forget₂ (ModuleCat.{max w v} B) Ab).mapHomologicalComplex (.up ℤ)).map
        (homComplexBaseChange f P F) =
      homComplexMap (ModuleCat.extendScalars.{u, w, max w v} f) P F := by
  ext n z
  change homCochainBaseChange f P F n ((1 : B) ⊗ₜ[A, f] z) = z.map _
  let := f.toAlgebra
  change LinearMap.liftBaseChange B (homCochainExtendScalars f P F n)
    ((1 : B) ⊗ₜ[A] z) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexBaseChange_naturality_underlying
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    let Ef := (ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)
    let Eg := (ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)
    let Efg := (ModuleCat.extendScalars.{u, u, max u v} (g.comp f)).mapHomologicalComplex (.up ℤ)
    let e : Efg ≅ Ef ⋙ Eg := NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max u v} f g) (.up ℤ)
    let UB := (forget₂ (ModuleCat.{max u v} B) Ab).mapHomologicalComplex (.up ℤ)
    let UC := (forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)
    UB.map (homComplexBaseChange f P F) ≫
      homComplexMap (ModuleCat.extendScalars.{u, u, max u v} g) (Ef.obj P) (Ef.obj F) ≫
      UC.map (Stacks.HomComplex.TensorHomMap.precomp C (Efg.obj P) (Eg.obj (Ef.obj P)) (Eg.obj
        (Ef.obj F)) (e.hom.app
        P) ≫
        Stacks.HomComplex.TensorHomMap.postcomp C (Efg.obj P) (Eg.obj (Ef.obj F)) (Efg.obj F)
          (e.inv.app F)) =
      extensionScalarsUnitComplex g (Ef.obj (CochainComplex.HomComplexR A P F)) ≫
        UC.map (e.inv.app (CochainComplex.HomComplexR A P F) ≫
          homComplexBaseChange (g.comp f) P F) := by
  dsimp only
  rw [← extensionScalarsUnitComplex_homComplexBaseChange]
  rw [← Category.assoc, ← Category.assoc,
    extensionScalarsUnitComplex_naturality g (homComplexBaseChange f P F)]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg
    (fun t ↦ extensionScalarsUnitComplex g
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.HomComplexR A P F)) ≫
      ((forget₂ (ModuleCat.{max u v} C) Ab).mapHomologicalComplex (.up ℤ)).map t)
    (homComplexBaseChange_comp f g P F)

universe s

private def homologyForgetMap
    {R : Type u} {S : Type w} [Ring R] [Ring S]
    {ι : Type t} {shape : ComplexShape ι}
    {E : HomologicalComplex (ModuleCat.{v} R) shape}
    {F : HomologicalComplex (ModuleCat.{v} S) shape}
    (ψ : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).obj E ⟶
      ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F)
    (i : ι) :
    (forget₂ (ModuleCat.{v} R) Ab).obj (E.homology i) ⟶
      (forget₂ (ModuleCat.{v} S) Ab).obj (F.homology i) :=
  ((E.sc i).mapHomologyIso (forget₂ (ModuleCat.{v} R) Ab)).inv ≫
    HomologicalComplex.homologyMap ψ i ≫
      ((F.sc i).mapHomologyIso (forget₂ (ModuleCat.{v} S) Ab)).hom

set_option backward.isDefEq.respectTransparency false in
private lemma homologyForgetMap_comp
    {R : Type u} {S : Type w} {T : Type s} [Ring R] [Ring S] [Ring T]
    {ι : Type t} {shape : ComplexShape ι}
    {E : HomologicalComplex (ModuleCat.{v} R) shape}
    {F : HomologicalComplex (ModuleCat.{v} S) shape}
    {G : HomologicalComplex (ModuleCat.{v} T) shape}
    (ψ : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).obj E ⟶
      ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F)
    (χ : ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F ⟶
      ((forget₂ (ModuleCat.{v} T) Ab).mapHomologicalComplex shape).obj G)
    (i : ι) :
    homologyForgetMap (ψ ≫ χ) i = homologyForgetMap ψ i ≫ homologyForgetMap χ i := by
  simp [homologyForgetMap, HomologicalComplex.homologyMap_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma homologyForgetMap_map
    {R : Type u} [Ring R] {ι : Type t} {shape : ComplexShape ι}
    {E F : HomologicalComplex (ModuleCat.{v} R) shape} (φ : E ⟶ F) (i : ι) :
    homologyForgetMap
      (((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).map φ) i =
        (forget₂ (ModuleCat.{v} R) Ab).map (HomologicalComplex.homologyMap φ i) := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) shape i).map φ)
    (forget₂ (ModuleCat.{v} R) Ab)
  dsimp only [homologyForgetMap]
  change (forget₂ (ModuleCat.{v} R) Ab).map (HomologicalComplex.homologyMap φ i) ≫
      ((F.sc i).mapHomologyIso (forget₂ (ModuleCat.{v} R) Ab)).inv =
    ((E.sc i).mapHomologyIso (forget₂ (ModuleCat.{v} R) Ab)).inv ≫
      HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).map φ) i at h
  rw [← Category.assoc, ← h]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma homologyForgetMap_naturality
    {R : Type u} {S : Type w} [Ring R] [Ring S]
    {ι : Type t} {shape : ComplexShape ι}
    {E E' : HomologicalComplex (ModuleCat.{v} R) shape}
    {F F' : HomologicalComplex (ModuleCat.{v} S) shape}
    (φ : E ⟶ E') (ψ : F ⟶ F')
    (α : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).obj E ⟶
      ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F)
    (β : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).obj E' ⟶
      ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F')
    (h : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).map φ ≫ β =
      α ≫ ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).map ψ)
    (i : ι) :
    (forget₂ (ModuleCat.{v} R) Ab).map (HomologicalComplex.homologyMap φ i) ≫
        homologyForgetMap β i =
      homologyForgetMap α i ≫
        (forget₂ (ModuleCat.{v} S) Ab).map (HomologicalComplex.homologyMap ψ i) := by
  have hh := congrArg (fun η ↦ homologyForgetMap (E := E) (F := F') η i) h
  simpa only [homologyForgetMap_comp, homologyForgetMap_map] using hh

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_homologyForgetMap
    {R : Type u} {S : Type w} [Ring R] [Ring S]
    {ι : Type t} {shape : ComplexShape ι}
    {E : HomologicalComplex (ModuleCat.{v} R) shape}
    {F : HomologicalComplex (ModuleCat.{v} S) shape}
    (ψ : ((forget₂ (ModuleCat.{v} R) Ab).mapHomologicalComplex shape).obj E ⟶
      ((forget₂ (ModuleCat.{v} S) Ab).mapHomologicalComplex shape).obj F)
    [IsIso ψ] (i : ι) : IsIso (homologyForgetMap ψ i) := by
  unfold homologyForgetMap
  infer_instance


private lemma homologyMap_cyclesMk {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) (hy : T.g (f.τ₂ x) = 0) :
    ShortComplex.homologyMap f (S.homologyπ (S.cyclesMk x hx)) =
      T.homologyπ (T.cyclesMk (f.τ₂ x) hy) := by
  have hcy : ShortComplex.cyclesMap f (S.cyclesMk x hx) = T.cyclesMk (f.τ₂ x) hy := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) (S.cyclesMk x hx)
    simpa only [ConcreteCategory.comp_apply, show S.iCycles (S.cyclesMk x hx) =
      x from S.i_cyclesMk x hx,
      show T.iCycles (T.cyclesMk (f.τ₂ x) hy) = f.τ₂ x from T.i_cyclesMk _ _] using h
  have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f)
    (S.cyclesMk x hx)
  simpa only [ConcreteCategory.comp_apply, hcy] using h

private lemma homologyClass_surjective {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (z : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), S.homologyπ (S.cyclesMk x hx) = z := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance z
  have hy : S.g (S.iCycles y) = 0 :=
    ConcreteCategory.congr_hom S.iCycles_g y
  refine ⟨S.iCycles y, hy, congrArg S.homologyπ ?_⟩
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  exact S.i_cyclesMk _ _

private lemma homologyι_homologyClass {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.homologyι (S.homologyπ (S.cyclesMk x hx)) = S.pOpcycles x := by
  have h := ConcreteCategory.congr_hom S.homology_π_ι (S.cyclesMk x hx)
  simpa only [ConcreteCategory.comp_apply,
    show S.iCycles (S.cyclesMk x hx) = x from S.i_cyclesMk x hx] using h

private lemma homologyClass_eq_iff {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (x y : S.X₂)
    (hx : S.g x = 0) (hy : S.g y = 0) :
    S.homologyπ (S.cyclesMk x hx) = S.homologyπ (S.cyclesMk y hy) ↔
      ∃ z : S.X₁, S.f z = x - y := by
  rw [← ((ModuleCat.mono_iff_injective S.homologyι).mp inferInstance).eq_iff,
    homologyι_homologyClass, homologyι_homologyClass,
    S.moduleCat_pOpcycles_eq_iff]
  rfl

private lemma shortComplex_map_cycle {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) : T.g (f.τ₂ x) = 0 := by
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using
    ConcreteCategory.congr_hom f.comm₂₃ x

private lemma homologyMap_cyclesMk_of_eq {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) (y : T.X₂) (hy : T.g y = 0)
    (hxy : f.τ₂ x = y) :
    ShortComplex.homologyMap f (S.homologyπ (S.cyclesMk x hx)) =
      T.homologyπ (T.cyclesMk y hy) := by
  subst y
  exact homologyMap_cyclesMk f x hx hy

set_option backward.isDefEq.respectTransparency false in
private def isColimit_shortComplex_homology_of_isColimit_terms
    {R : Type u} [Ring R] {I : Type uI} [Category.{uJ} I]
    [IsFilteredOrEmpty I] {F : I ⥤ ShortComplex (ModuleCat.{v} R)}
    (c : Cocone F)
    (h₁ : IsColimit ((ShortComplex.π₁ ⋙ forget (ModuleCat.{v} R)).mapCocone c))
    (h₂ : IsColimit ((ShortComplex.π₂ ⋙ forget (ModuleCat.{v} R)).mapCocone c))
    (h₃ : IsColimit ((ShortComplex.π₃ ⋙ forget (ModuleCat.{v} R)).mapCocone c)) :
    IsColimit ((ShortComplex.homologyFunctor (ModuleCat.{v} R) ⋙
      forget (ModuleCat.{v} R)).mapCocone c) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨y, hy, hxy⟩ := homologyClass_surjective c.pt x
    obtain ⟨i, yi, hi⟩ := Types.jointly_surjective _ h₂ y
    change (c.ι.app i).τ₂ yi = y at hi
    have hz : (c.ι.app i).τ₃ ((F.obj i).g yi) = (c.ι.app i).τ₃ 0 := by
      have ht := ConcreteCategory.congr_hom (c.ι.app i).comm₂₃ yi
      change c.pt.g ((c.ι.app i).τ₂ yi) = (c.ι.app i).τ₃ ((F.obj i).g yi) at ht
      simpa only [hi, hy, map_zero] using ht.symm
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' h₃ ((F.obj i).g yi) (0 : (F.obj i).X₃)).mp hz
    change (F.map f).τ₃ ((F.obj i).g yi) = (F.map f).τ₃ 0 at hf
    let z := (F.map f).τ₂ yi
    have hz : (F.obj j).g z = 0 := by
      have ht := ConcreteCategory.congr_hom (F.map f).comm₂₃ yi
      exact ht.trans (hf.trans (map_zero _))
    have hz' : (c.ι.app j).τ₂ z = y := by
      have ht := congrArg (fun t : F.obj i ⟶ c.pt ↦ t.τ₂ yi) (c.w f)
      exact ht.trans hi
    refine ⟨j, (F.obj j).homologyπ ((F.obj j).cyclesMk z hz), ?_⟩
    exact (homologyMap_cyclesMk_of_eq (c.ι.app j) z hz y hy hz').trans hxy |>.symm
  · intro i x y hxy
    obtain ⟨a, ha, rfl⟩ := homologyClass_surjective (F.obj i) x
    obtain ⟨b, hb, rfl⟩ := homologyClass_surjective (F.obj i) y
    change ShortComplex.homologyMap (c.ι.app i) _ =
      ShortComplex.homologyMap (c.ι.app i) _ at hxy
    rw [homologyMap_cyclesMk (c.ι.app i) a ha (shortComplex_map_cycle _ a ha),
      homologyMap_cyclesMk (c.ι.app i) b hb (shortComplex_map_cycle _ b hb)] at hxy
    obtain ⟨z, hz⟩ := (homologyClass_eq_iff c.pt _ _ _ _).mp hxy
    obtain ⟨j, zj, hj⟩ := Types.jointly_surjective _ h₁ z
    change (c.ι.app j).τ₁ zj = z at hj
    have he : (c.ι.app i).τ₂ (a - b) = (c.ι.app j).τ₂ ((F.obj j).f zj) := by
      rw [map_sub, ← hz]
      exact (congrArg c.pt.f hj).symm.trans
        (ConcreteCategory.congr_hom (c.ι.app j).comm₁₂ zj)
    obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff _ h₂).mp he
    change (F.map f).τ₂ (a - b) = (F.map g).τ₂ ((F.obj j).f zj) at hfg
    refine ⟨k, f, ?_⟩
    change ShortComplex.homologyMap (F.map f) _ = ShortComplex.homologyMap (F.map f) _
    rw [homologyMap_cyclesMk (F.map f) a ha (shortComplex_map_cycle _ a ha),
      homologyMap_cyclesMk (F.map f) b hb (shortComplex_map_cycle _ b hb)]
    apply (homologyClass_eq_iff (F.obj k) _ _ _ _).mpr
    refine ⟨(F.map g).τ₁ zj, ?_⟩
    have ht := ConcreteCategory.congr_hom (F.map g).comm₁₂ zj
    exact ht.trans (hfg.symm.trans (map_sub _ _ _))

private lemma homologyIso_cyclesMk (S : ShortComplex Ab.{v})
    (h : S.LeftHomologyData) (y : h.K) (x : S.X₂) (hx : S.g x = 0)
    (hy : h.i y = x) :
    h.homologyIso.hom (S.homologyπ (S.abCyclesIso.inv ⟨x, hx⟩)) = h.π y := by
  have hcy : h.cyclesIso.hom (S.abCyclesIso.inv ⟨x, hx⟩) = y := by
    apply (AddCommGrpCat.mono_iff_injective h.i).mp inferInstance
    have hi := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i (S.abCyclesIso.inv ⟨x, hx⟩)
    exact hi.trans ((S.abCyclesIso_inv_apply_iCycles ⟨x, hx⟩).trans hy.symm)
  have hi := ConcreteCategory.congr_hom (h.homologyπ_comp_homologyIso_hom S)
    (S.abCyclesIso.inv ⟨x, hx⟩)
  simpa only [ConcreteCategory.comp_apply, hcy] using hi

private lemma mapHomologyIso_cyclesMk {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (x : S.X₂) (hx : S.g x = 0) :
    (S.mapHomologyIso (forget₂ (ModuleCat.{v} R) Ab)).inv
        (S.homologyπ (S.cyclesMk x hx)) =
      (S.map (forget₂ (ModuleCat.{v} R) Ab)).homologyπ
        ((S.map (forget₂ (ModuleCat.{v} R) Ab)).abCyclesIso.inv ⟨x, hx⟩) := by
  let U := forget₂ (ModuleCat.{v} R) Ab
  let h := S.homologyData.left
  let k := h.map U
  rw [h.mapHomologyIso_eq U]
  change k.homologyIso.inv (h.homologyIso.hom (S.homologyπ (S.cyclesMk x hx))) = _
  have hh := ConcreteCategory.congr_hom (h.homologyπ_comp_homologyIso_hom S)
    (S.cyclesMk x hx)
  change h.homologyIso.hom (S.homologyπ (S.cyclesMk x hx)) =
    h.π (h.cyclesIso.hom (S.cyclesMk x hx)) at hh
  rw [hh]
  apply (ConcreteCategory.bijective_of_isIso k.homologyIso.hom).1
  have hcancel := ConcreteCategory.congr_hom k.homologyIso.inv_hom_id
    (h.π (h.cyclesIso.hom (S.cyclesMk x hx)))
  change k.homologyIso.hom (k.homologyIso.inv _) = _ at hcancel
  rw [hcancel]
  symm
  apply homologyIso_cyclesMk
  have hi := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i (S.cyclesMk x hx)
  exact hi.trans (S.i_cyclesMk x hx)

private def homComplexRForgetIso {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) :
    ((forget₂ (ModuleCat.{v} A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.HomComplexR A P F) ≅ CochainComplex.HomComplex P F :=
  Iso.refl _
private def homComplexRHomologyAddEquiv {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ) :
    (CochainComplex.HomComplexR A P F).homology n ≃+
      CochainComplex.HomComplex.CohomologyClass P F n := by
  let e := ((CochainComplex.HomComplexR A P F).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{v} A) AddCommGrpCat)
  exact (e.symm ≪≫ (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso
      (homComplexRForgetIso P F)).addCommGroupIsoToAddEquiv.trans
    (CochainComplex.HomComplex.homologyAddEquiv P F n)

private lemma equivHomShift_ofHom_comp_zero
    {C : Type u} [Category.{v} C] [Preadditive C]
    {P F : CochainComplex C ℤ} (g : P ⟶ F) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.ofHom g) ≫
      (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app F = g := by
  ext p
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf,
    CochainComplex.HomComplex.Cochain.rightShift_v,
    CochainComplex.shiftFunctorZero_hom_app_f]

private def homComplexRHomologyEquivDerivedHom {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (h : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P F 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z))) :
    (CochainComplex.HomComplexR A P F).homology 0 ≃
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj F) :=
  (homComplexRHomologyAddEquiv P F 0).toEquiv.trans <|
    (Equiv.ofBijective _ h).trans <|
      Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} A)).app P)
        (((DerivedCategory.quotientCompQhIso (ModuleCat.{v} A)).app (F⟦(0 : ℤ)⟧)) ≪≫
          DerivedCategory.Q.mapIso ((shiftFunctorZero (CochainComplex (ModuleCat.{v} A) ℤ) ℤ).app
            F))

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexRHomologyAddEquiv_cyclesMk {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle P F n) :
    homComplexRHomologyAddEquiv P F n
      ((CochainComplex.HomComplexR A P F).homologyπ n
        (((CochainComplex.HomComplexR A P F).sc n).cyclesMk z.val
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))) =
      CochainComplex.HomComplex.CohomologyClass.mk z := by
  let S := (CochainComplex.HomComplexR A P F).sc n
  simp only [homComplexRHomologyAddEquiv, homComplexRForgetIso,
    Functor.mapIso_refl]
  change CochainComplex.HomComplex.homologyAddEquiv P F n
    ((S.mapHomologyIso (forget₂ (ModuleCat.{v} A) Ab)).inv
      (S.homologyπ (S.cyclesMk z.val _))) = _
  rw [mapHomologyIso_cyclesMk]
  exact homologyIso_cyclesMk _ (CochainComplex.HomComplex.leftHomologyData P F n)
    z z.val _ rfl

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexRHomologyEquivDerivedHom_ofHom {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (h : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P F 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)))
    (g : P ⟶ F) :
    homComplexRHomologyEquivDerivedHom P F h
      ((CochainComplex.HomComplexR A P F).homologyπ 0
        (((CochainComplex.HomComplexR A P F).sc 0).cyclesMk
          (CochainComplex.HomComplex.Cochain.ofHom g)
          (CochainComplex.HomComplex.δ_ofHom g))) = DerivedCategory.Q.map g := by
  change (Iso.homCongr _ _)
    (DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (homComplexRHomologyAddEquiv P F 0 _))) = _
  erw [homComplexRHomologyAddEquiv_cyclesMk P F 0
    (CochainComplex.HomComplex.Cocycle.ofHom g)]
  change (DerivedCategory.quotientCompQhIso (ModuleCat.{v} A)).inv.app P ≫
    ((HomotopyCategory.quotient (ModuleCat.{v} A) (.up ℤ)) ⋙ DerivedCategory.Qh).map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.ofHom g)) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{v} A)).hom.app (F⟦(0 : ℤ)⟧) ≫
        DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex (ModuleCat.{v} A) ℤ) ℤ).hom.app F)
          = _
  rw [(DerivedCategory.quotientCompQhIso (ModuleCat.{v} A)).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, equivHomShift_ofHom_comp_zero]

private lemma homologyMap_abCyclesIso {S T : ShortComplex Ab.{v}}
    (f : S ⟶ T) (x : S.X₂) (hx : S.g x = 0)
    (y : T.X₂) (hy : T.g y = 0) (hxy : f.τ₂ x = y) :
    ShortComplex.homologyMap f (S.homologyπ (S.abCyclesIso.inv ⟨x, hx⟩)) =
      T.homologyπ (T.abCyclesIso.inv ⟨y, hy⟩) := by
  have hcy : ShortComplex.cyclesMap f (S.abCyclesIso.inv ⟨x, hx⟩) =
      T.abCyclesIso.inv ⟨y, hy⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    calc
      _ = f.τ₂ (S.iCycles (S.abCyclesIso.inv ⟨x, hx⟩)) :=
        ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) _
      _ = y := by rw [S.abCyclesIso_inv_apply_iCycles, hxy]
      _ = _ := (T.abCyclesIso_inv_apply_iCycles ⟨y, hy⟩).symm
  have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f)
    (S.abCyclesIso.inv ⟨x, hx⟩)
  simpa only [ConcreteCategory.comp_apply, hcy] using h

set_option backward.isDefEq.respectTransparency false in
private lemma exists_homComplexR_homologyClass_ofHom {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (x : (CochainComplex.HomComplexR A P F).homology 0) :
    ∃ g : P ⟶ F,
      (CochainComplex.HomComplexR A P F).homologyπ 0
        (((CochainComplex.HomComplexR A P F).sc 0).cyclesMk
          (CochainComplex.HomComplex.Cochain.ofHom g)
          (CochainComplex.HomComplex.δ_ofHom g)) = x := by
  obtain ⟨z, hz⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective
    (homComplexRHomologyAddEquiv P F 0 x)
  refine ⟨z.homOf, (homComplexRHomologyAddEquiv P F 0).injective ?_⟩
  erw [homComplexRHomologyAddEquiv_cyclesMk P F 0
    (CochainComplex.HomComplex.Cocycle.ofHom z.homOf)]
  rwa [CochainComplex.HomComplex.Cocycle.ofHom_homOf_eq_self]

set_option backward.isDefEq.respectTransparency false in
private lemma homComplexRHomologyEquivDerivedHom_naturality
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (P' F' : CochainComplex (ModuleCat.{v} B) ℤ)
    (h : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P F 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)))
    (h' : Function.Bijective (fun z : CochainComplex.HomComplex.CohomologyClass P' F' 0 ↦
      DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)))
    (ψ : CochainComplex.HomComplex P F ⟶ CochainComplex.HomComplex P' F')
    (T : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj F) →
      (DerivedCategory.Q.obj P' ⟶ DerivedCategory.Q.obj F'))
    (hψ : ∀ g : P ⟶ F, ∃ g' : P' ⟶ F',
      ψ.f 0 (CochainComplex.HomComplex.Cochain.ofHom g) =
        CochainComplex.HomComplex.Cochain.ofHom g' ∧
      T (DerivedCategory.Q.map g) = DerivedCategory.Q.map g')
    (x : (CochainComplex.HomComplexR A P F).homology 0) :
    homComplexRHomologyEquivDerivedHom P' F' h'
      ((((CochainComplex.HomComplexR B P' F').sc 0).mapHomologyIso
        (forget₂ (ModuleCat.{v} B) Ab)).hom
          (HomologicalComplex.homologyMap ψ 0
            ((((CochainComplex.HomComplexR A P F).sc 0).mapHomologyIso
              (forget₂ (ModuleCat.{v} A) Ab)).inv x))) =
      T (homComplexRHomologyEquivDerivedHom P F h x) := by
  obtain ⟨g, rfl⟩ := exists_homComplexR_homologyClass_ofHom P F x
  obtain ⟨g', hg', hT⟩ := hψ g
  rw [homComplexRHomologyEquivDerivedHom_ofHom, hT]
  erw [mapHomologyIso_cyclesMk]
  have hh := homologyMap_abCyclesIso
    ((HomologicalComplex.shortComplexFunctor Ab (.up ℤ) 0).map ψ)
    (CochainComplex.HomComplex.Cochain.ofHom g)
    (CochainComplex.HomComplex.δ_ofHom g)
    (CochainComplex.HomComplex.Cochain.ofHom g')
    (CochainComplex.HomComplex.δ_ofHom g') hg'
  change _ = _ at hh
  erw [hh]
  erw [← mapHomologyIso_cyclesMk ((CochainComplex.HomComplexR B P' F').sc 0)
    (CochainComplex.HomComplex.Cochain.ofHom g')
    (CochainComplex.HomComplex.δ_ofHom g')]
  have hc := ConcreteCategory.congr_hom
    (((CochainComplex.HomComplexR B P' F').sc 0).mapHomologyIso
      (forget₂ (ModuleCat.{v} B) Ab)).inv_hom_id
    ((CochainComplex.HomComplexR B P' F').homologyπ 0
      (((CochainComplex.HomComplexR B P' F').sc 0).cyclesMk
        (CochainComplex.HomComplex.Cochain.ofHom g')
        (CochainComplex.HomComplex.δ_ofHom g')))
  change _ = _ at hc
  erw [hc]
  exact homComplexRHomologyEquivDerivedHom_ofHom P' F' h' g'

end HomComplexHomology

end PseudoCoherence

end
