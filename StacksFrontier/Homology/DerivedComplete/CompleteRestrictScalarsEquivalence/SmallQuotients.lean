module

public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.LargeUniverse
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.DerivedAdjunction
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.CechTerms
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.LargeUniverse

/-!
# The equivalence via small quotients

Fourth part of `StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence`.
It contains the descent of the equivalence along small quotient rings, the case where all
relevant quotients are small, the degenerate cases, and the main result
`restrictScalars_equivalence_derivedComplete` (Stacks Tag 0925).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe uA uB v u w

namespace CompleteRestrictScalarsEquivalence

set_option backward.isDefEq.respectTransparency false


open StacksDraft.TotalComplexQuasiIso
open scoped ZeroObject

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open scoped DirectSum

open scoped ModuleCat.Algebra

open HomologicalComplex

open scoped ChangeOfRings

private noncomputable def mapDerivedCategoryCompIso
    {C D E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ H.mapDerivedCategory) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫ H.mapDerivedCategoryFactors.symm)

private theorem exists_small_quotient_isDerivedComplete
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R))]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsDerivedComplete I K) :
    ∃ J : Ideal R, Small.{v} (R ⧸ J) ∧
      ∃ hprod : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} (R ⧸ J))),
      letI := hprod
      ∃ L : DerivedCategory (ModuleCat.{v} (R ⧸ J)),
        IsDerivedComplete (I.map (Ideal.Quotient.mk J)) L ∧
        Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapDerivedCategory.obj L ≅ K) :=
          by
  obtain ⟨J, hJ, L, ⟨e⟩⟩ := exists_small_quotient_derived R K
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} (R ⧸ J)) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} (R ⧸ J) ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} (R ⧸ J))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  refine ⟨J, hJ, inferInstance, L, ?_, ⟨e⟩⟩
  exact (isDerivedComplete_restrictScalars_iff
    R (R ⧸ J) (Ideal.Quotient.mk J) I L).mp (isDerivedComplete_of_iso R I e.symm hK)

private noncomputable def restrictScalars_quotient_square
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) :
    (ModuleCat.restrictScalars.{v}
      (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapDerivedCategory ≅
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (J.map f))).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars f).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{v} f
  let G := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (J.map f))
  let H := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk J)
  let K := ModuleCat.restrictScalars.{v} (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{v} (B ⧸ J.map f)) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (K.mapDerivedCategory ⋙ H.mapDerivedCategory))
    (DerivedCategory.Q ⋙ (G.mapDerivedCategory ⋙ F.mapDerivedCategory)) _ _
    (Functor.isoWhiskerRight K.mapDerivedCategoryFactors H.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (K.mapHomologicalComplex (ComplexShape.up ℤ))
        H.mapDerivedCategoryFactors ≪≫
      (Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        F.mapDerivedCategoryFactors).symm ≪≫
      (Functor.isoWhiskerRight G.mapDerivedCategoryFactors F.mapDerivedCategory).symm)

private theorem restrictScalars_quotient_square_hom_app
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A)
    (L : CochainComplex (ModuleCat.{v} (B ⧸ J.map f)) ℤ) :
    let F := ModuleCat.restrictScalars.{v} f
    let G := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (J.map f))
    let H := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk J)
    let K := ModuleCat.restrictScalars.{v}
      (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)
    (restrictScalars_quotient_square f J).hom.app (DerivedCategory.Q.obj L) =
      H.mapDerivedCategory.map (K.mapDerivedCategoryFactors.hom.app L) ≫
        H.mapDerivedCategoryFactors.hom.app ((K.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        F.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app L) := by
  dsimp only
  simp [restrictScalars_quotient_square, Localization.liftNatIso, Localization.liftNatTrans_app,
    Localization.Lifting.iso, Category.assoc]

private theorem bijective_quotientMap_conjugate
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (f : A →+* B) (I : Ideal A) (eA : A' ≃+* A) (eB : B ≃+* B')
    (h : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) :
    let f' := eB.toRingHom.comp (f.comp eA.toRingHom)
    Function.Bijective (Ideal.quotientMap
      ((I.map eA.symm.toRingHom).map f') f' Ideal.le_comap_map) := by
  let f' := eB.toRingHom.comp (f.comp eA.toRingHom)
  let I' := I.map eA.symm.toRingHom
  have hI : I'.map f' = (I.map f).map eB.toRingHom := by
    simp only [I', Ideal.map_map]
    congr 1
    ext x
    simp [f']
  let e := (Ideal.quotientEquiv I I' eA.symm rfl).symm.trans
    ((RingEquiv.ofBijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) h).trans
      (Ideal.quotientEquiv (I.map f) (I'.map f') eB hI))
  have he : (e : _ → _) = Ideal.quotientMap (I'.map f') f' Ideal.le_comap_map := by
    funext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx : Ideal.Quotient.mk I' x =
        (Ideal.quotientEquiv I I' eA.symm rfl) (Ideal.Quotient.mk I (eA x)) := by
      simp
    rw [hx]
    simp [e, f']
  show Function.Bijective (Ideal.quotientMap (I'.map f') f' Ideal.le_comap_map)
  rw [← he]
  exact e.bijective

private theorem isEquivalence_lift_of_isEquivalence
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.IsEquivalence]
    (P : ObjectProperty C) (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (h : ∀ X, Q (F.obj X) ↔ P X)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :
    (Q.lift (P.ι ⋙ F) hF).IsEquivalence := by
  have h' : Q.inverseImage F.asEquivalence.functor = P :=
    funext fun X => propext (h X)
  exact (F.asEquivalence.congrFullSubcategory h').isEquivalence_functor

private theorem isEquivalence_restrictScalars_of_small
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    [Small.{v} A] [Small.{v} B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K => IsDerivedComplete I K
    let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
      fun K => IsDerivedComplete (I.map (algebraMap A B)) K
    let F := (ModuleCat.restrictScalars.{v} (algebraMap A B)).mapDerivedCategory
    ∀ hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj),
      (P.lift (Q.ι ⋙ F) hF).IsEquivalence := by
  intro P Q F hF
  let R := Shrink.{v} A
  let S := Shrink.{v} B
  let a : R ≃+* A := Shrink.ringEquiv A
  let b : S ≃+* B := Shrink.ringEquiv B
  let f := algebraMap A B
  let f' : R →+* S := b.symm.toRingHom.comp (f.comp a.toRingHom)
  let : Algebra R S := f'.toAlgebra
  let J := I.map a.symm.toRingHom
  have hflat' : Module.Flat R S := by
    apply RingHom.flat_algebraMap_iff.mp
    have ha : a.toRingHom.Flat := RingHom.Flat.of_bijective a.bijective
    have hb : b.symm.toRingHom.Flat := RingHom.Flat.of_bijective b.symm.bijective
    exact (ha.comp (RingHom.flat_algebraMap_iff.mpr hflat)).comp hb
  have hquot' : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map) :=
    bijective_quotientMap_conjugate f I a b.symm hquot
  have hJA : J.map a.toRingHom = I := by
    simp [J, Ideal.map_map]
  have hJB : (J.map f').map b.toRingHom = I.map f := by
    simp only [J, Ideal.map_map]
    congr 1
    ext x
    simp [f']
  have hcomp : f.comp a.toRingHom = b.toRingHom.comp f' := by
    ext x
    simp [f']
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} R ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} S) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} S ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} S)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let PR : ObjectProperty (DerivedCategory (ModuleCat.{v} R)) :=
    fun K => IsDerivedComplete J K
  let PS : ObjectProperty (DerivedCategory (ModuleCat.{v} S)) :=
    fun K => IsDerivedComplete (J.map f') K
  let RA := (ModuleCat.restrictScalars.{v} a.toRingHom).mapDerivedCategory
  let RB := (ModuleCat.restrictScalars.{v} b.toRingHom).mapDerivedCategory
  let G₀ := (ModuleCat.restrictScalars.{v} f').mapDerivedCategory
  have hRA (K : DerivedCategory (ModuleCat.{v} A)) : PR (RA.obj K) ↔ P K := by
    simpa only [PR, P, RA, hJA] using
      isDerivedComplete_restrictScalars_iff R A a.toRingHom J K
  have hRB (K : DerivedCategory (ModuleCat.{v} B)) : PS (RB.obj K) ↔ Q K := by
    simpa only [PS, Q, RB, hJB] using
      isDerivedComplete_restrictScalars_iff S B b.toRingHom (J.map f') K
  let EA := PR.lift (P.ι ⋙ RA) (fun K => (hRA K.obj).mpr K.property)
  let EB := PS.lift (Q.ι ⋙ RB) (fun K => (hRB K.obj).mpr K.property)
  let hG : ∀ K : PS.FullSubcategory, PR (G₀.obj K.obj) := fun K =>
    (isDerivedComplete_restrictScalars_iff R S f' J K.obj).mpr K.property
  let G := PR.lift (PS.ι ⋙ G₀) hG
  let : PR.IsClosedUnderIsomorphisms :=
    ⟨fun e h => isDerivedComplete_of_iso R J e h⟩
  let : PS.IsClosedUnderIsomorphisms :=
    ⟨fun e h => isDerivedComplete_of_iso S (J.map f') e h⟩
  let : RA.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv a).functor
  let : RB.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv b).functor
  let : EA.IsEquivalence := isEquivalence_lift_of_isEquivalence RA P PR hRA _
  let : EB.IsEquivalence := isEquivalence_lift_of_isEquivalence RB Q PS hRB _
  let : G.IsEquivalence :=
    isEquivalence_restrictScalars_large R S J (hI.map a.symm.toRingHom) hflat' hquot' hG
  let e₀ : F ⋙ RA ≅ RB ⋙ G₀ :=
    mapDerivedCategoryCompIso _ _ _ (ModuleCat.restrictScalarsComp a.toRingHom f).symm ≪≫
      (mapDerivedCategoryCompIso _ _ _
        (ModuleCat.restrictScalarsComp' f' b.toRingHom (f.comp a.toRingHom) hcomp).symm).symm
  let e : P.lift (Q.ι ⋙ F) hF ⋙ EA ≅ EB ⋙ G :=
    (PR.fullyFaithfulι.whiskeringRight _).preimageIso (Functor.isoWhiskerLeft Q.ι e₀)
  let : (P.lift (Q.ι ⋙ F) hF ⋙ EA).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_right (P.lift (Q.ι ⋙ F) hF) EA

private theorem exists_restrictScalars_iso_of_small_quotients
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (hquotSmall : ∀ J : Ideal A, Small.{v} (A ⧸ J) →
      Small.{v} (B ⧸ J.map (algebraMap A B)))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) :
    ∃ L : DerivedCategory (ModuleCat.{v} B),
      IsDerivedComplete (I.map (algebraMap A B)) L ∧
      Nonempty ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj L ≅ K) := by
  obtain ⟨J, hJ, hprod, K', hK', ⟨eK⟩⟩ := exists_small_quotient_isDerivedComplete A I K hK
  let := hJ
  let := hprod
  let R := A ⧸ J
  let S := B ⧸ J.map (algebraMap A B)
  let : Small.{v} S := hquotSmall J inferInstance
  let I' := I.map (Ideal.Quotient.mk J)
  let f' := algebraMap R S
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} S) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} S ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} S)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have hflat' : Module.Flat R S := flat_quotient_map A B J hflat
  have hquot' : Function.Bijective
      (Ideal.quotientMap (I'.map f') f' Ideal.le_comap_map) :=
    bijective_quotientMap_quotient (algebraMap A B) I J hquot
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} R)) :=
    fun X => IsDerivedComplete I' X
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} S)) :=
    fun X => IsDerivedComplete (I'.map f') X
  let res := (ModuleCat.restrictScalars.{v} f').mapDerivedCategory
  let hres : ∀ X : Q.FullSubcategory, P (res.obj X.obj) := fun X =>
    (isDerivedComplete_restrictScalars_iff R S f' I' X.obj).mpr X.property
  let F := P.lift (Q.ι ⋙ res) hres
  let : F.IsEquivalence := isEquivalence_restrictScalars_of_small
    R S I' (hI.map (Ideal.Quotient.mk J)) hflat' hquot' hres
  let Y := F.objPreimage ⟨K', hK'⟩
  let e := P.ι.mapIso (F.objObjPreimageIso ⟨K', hK'⟩)
  let L := (ModuleCat.restrictScalars (Ideal.Quotient.mk (J.map (algebraMap A
    B)))).mapDerivedCategory.obj Y.obj
  let eL : (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj L ≅ K :=
    ((restrictScalars_quotient_square (algebraMap A B) J).app Y.obj).symm ≪≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapDerivedCategory.mapIso e ≪≫ eK
  refine ⟨L, ?_, ⟨eL⟩⟩
  exact (isDerivedComplete_restrictScalars_iff
    A B (algebraMap A B) I L).mp (isDerivedComplete_of_iso A I eL.symm hK)


private theorem exists_preimage_derived_map_of_roof
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K L N : CochainComplex C ℤ) (X : CochainComplex D ℤ)
    (s : X ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (g : X ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    [QuasiIso s] (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ X) :
    ∃ f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L,
      F.mapDerivedCategory.map f ≫ F.mapDerivedCategoryFactors.hom.app L =
        F.mapDerivedCategoryFactors.hom.app K ≫
          inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let s' : N ⟶ K := FC.preimage (e.hom ≫ s)
  let g' : N ⟶ L := FC.preimage (e.hom ≫ g)
  have : QuasiIso s' := by
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology s' F]
    show QuasiIso (FC.map s')
    simpa only [s', Functor.map_preimage] using (inferInstance : QuasiIso (e.hom ≫ s))
  refine ⟨inv (DerivedCategory.Q.map s') ≫ DerivedCategory.Q.map g', ?_⟩
  apply (cancel_epi (F.mapDerivedCategory.map (DerivedCategory.Q.map s'))).mp
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [F.mapDerivedCategoryFactors_hom_naturality g']
  rw [← Category.assoc (F.mapDerivedCategory.map (DerivedCategory.Q.map s')),
    F.mapDerivedCategoryFactors_hom_naturality s']
  simp [s', g', FC, Functor.map_comp]

private theorem surjective_map_restrictScalars_Q_of_small_quotients
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (hquotSmall : ∀ J : Ideal A, Small.{v} (A ⧸ J) →
      Small.{v} (B ⧸ J.map (algebraMap A B)))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (L M : CochainComplex (ModuleCat.{v} B) ℤ)
    (hL : IsDerivedComplete (I.map (algebraMap A B)) (DerivedCategory.Q.obj L))
    (hM : IsDerivedComplete (I.map (algebraMap A B)) (DerivedCategory.Q.obj M)) :
    Function.Surjective
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.map :
        (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) → _) := by
  classical
  intro u
  let f := algebraMap A B
  let F := ModuleCat.restrictScalars.{v} f
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let cL := F.mapDerivedCategoryFactors.app L
  let cM := F.mapDerivedCategoryFactors.app M
  let u₀ : DerivedCategory.Q.obj (FC.obj L) ⟶ DerivedCategory.Q.obj (FC.obj M) :=
    cL.inv ≫ u ≫ cM.hom
  obtain ⟨N, s, hs, g, hu₀⟩ := DerivedCategory.right_fac u₀
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs
  let modules : ℤ ⊕ (ℤ ⊕ ℤ) → ModuleCat.{v} A :=
    Sum.elim (FC.obj L).X (Sum.elim (FC.obj M).X N.X)
  obtain ⟨J, hJ, hAnn⟩ := exists_small_quotient_annihilator A modules
  let := hJ
  have hJt (i) : Module.IsTorsionBySet A (modules i) J :=
    (Module.isTorsionBySet_iff_subset_annihilator A _).mpr (hAnn i)
  obtain ⟨L', ⟨eL⟩⟩ := exists_quotient_complex B (J.map f) (ComplexShape.up ℤ) L
    (fun n => isTorsionBySet_map_of_restrictScalars f J (L.X n) (hJt (.inl n)))
  obtain ⟨M', ⟨eM⟩⟩ := exists_quotient_complex B (J.map f) (ComplexShape.up ℤ) M
    (fun n => isTorsionBySet_map_of_restrictScalars f J (M.X n) (hJt (.inr (.inl n))))
  obtain ⟨N', ⟨eN⟩⟩ := exists_quotient_complex A J (ComplexShape.up ℤ) N
    (fun n => hJt (.inr (.inr n)))
  let R := A ⧸ J
  let S := B ⧸ J.map f
  let : Small.{v} S := hquotSmall J inferInstance
  let I' := I.map (Ideal.Quotient.mk J)
  let f' := algebraMap R S
  let G := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (J.map f))
  let H := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk J)
  let K := ModuleCat.restrictScalars.{v} f'
  let KC := K.mapHomologicalComplex (ComplexShape.up ℤ)
  let HC := H.mapHomologicalComplex (ComplexShape.up ℤ)
  let eLA : HC.obj (KC.obj L') ≅ FC.obj L := FC.mapIso eL
  let eMA : HC.obj (KC.obj M') ≅ FC.obj M := FC.mapIso eM
  let : H.Full := full_restrictScalars_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨t₀, ht₀⟩ := exists_preimage_derived_map_of_roof H (KC.obj L') (KC.obj M') N' N
    (s ≫ eLA.inv) (g ≫ eMA.inv) eN
  let aL := H.mapDerivedCategoryFactors.app (KC.obj L') ≪≫ DerivedCategory.Q.mapIso eLA
  let aM := H.mapDerivedCategoryFactors.app (KC.obj M') ≪≫ DerivedCategory.Q.mapIso eMA
  have ht : H.mapDerivedCategory.map t₀ ≫ aM.hom = aL.hom ≫ u₀ := by
    simp only [aM, aL, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ← Category.assoc]
    rw [ht₀]
    simp [hu₀, Functor.map_comp, Category.assoc]
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} R ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} S) :=
    moduleCat_hasExactLimitsOfShape_discrete.{v} S ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} S)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have hflat' : Module.Flat R S := flat_quotient_map A B J hflat
  have hquot' : Function.Bijective
      (Ideal.quotientMap (I'.map f') f' Ideal.le_comap_map) :=
    bijective_quotientMap_quotient f I J hquot
  have hI' : I'.map f' = (I.map f).map (Ideal.Quotient.mk (J.map f)) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun q => I.map q) (Ideal.quotientMap_comp_mk (f := f) Ideal.le_comap_map)
  let lB := G.mapDerivedCategoryFactors.app L' ≪≫ DerivedCategory.Q.mapIso eL
  let mB := G.mapDerivedCategoryFactors.app M' ≪≫ DerivedCategory.Q.mapIso eM
  have hcompl : ∀ {X : DerivedCategory (ModuleCat.{v} S)} {Y : DerivedCategory (ModuleCat.{v} B)},
      (G.mapDerivedCategory.obj X ≅ Y) → IsDerivedComplete (I.map f) Y →
      IsDerivedComplete (I'.map f') X := fun e hY => by
    rw [hI']
    exact (isDerivedComplete_restrictScalars_iff B S
      (Ideal.Quotient.mk (J.map f)) (I.map f) _).mp (isDerivedComplete_of_iso B (I.map f) e.symm hY)
  have hL' := hcompl lB hL
  have hM' := hcompl mB hM
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} R)) :=
    fun X => IsDerivedComplete I' X
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} S)) :=
    fun X => IsDerivedComplete (I'.map f') X
  let hK : ∀ X : Q.FullSubcategory, P (K.mapDerivedCategory.obj X.obj) := fun X =>
    (isDerivedComplete_restrictScalars_iff R S f' I' X.obj).mpr X.property
  let T := P.lift (Q.ι ⋙ K.mapDerivedCategory) hK
  let : T.IsEquivalence := isEquivalence_restrictScalars_of_small
    R S I' (hI.map (Ideal.Quotient.mk J)) hflat' hquot' hK
  let bL := K.mapDerivedCategoryFactors.app L'
  let bM := K.mapDerivedCategoryFactors.app M'
  let t := bL.hom ≫ t₀ ≫ bM.inv
  let xL : Q.FullSubcategory := ⟨DerivedCategory.Q.obj L', hL'⟩
  let xM : Q.FullSubcategory := ⟨DerivedCategory.Q.obj M', hM'⟩
  let t' : T.obj xL ⟶ T.obj xM := ObjectProperty.homMk t
  let v' : xL ⟶ xM := T.preimage t'
  have hv : K.mapDerivedCategory.map v'.hom = t := congrArg (fun z => z.hom) (T.map_preimage t')
  let sq := restrictScalars_quotient_square f J
  have hcompL : H.mapDerivedCategory.map bL.hom ≫ aL.hom =
      sq.hom.app (DerivedCategory.Q.obj L') ≫ F.mapDerivedCategory.map lB.hom ≫ cL.hom := by
    simp [sq, restrictScalars_quotient_square_hom_app, lB, bL, cL, aL, eLA,
      F, G, H, K, f', FC, KC, Functor.map_comp, Category.assoc,
      Functor.mapDerivedCategoryFactors_hom_naturality]
    rfl
  have hcompM : H.mapDerivedCategory.map bM.hom ≫ aM.hom =
      sq.hom.app (DerivedCategory.Q.obj M') ≫ F.mapDerivedCategory.map mB.hom ≫ cM.hom := by
    simp [sq, restrictScalars_quotient_square_hom_app, mB, bM, cM, aM, eMA,
      F, G, H, K, f', FC, KC, Functor.map_comp, Category.assoc,
      Functor.mapDerivedCategoryFactors_hom_naturality]
    rfl
  refine ⟨lB.inv ≫ G.mapDerivedCategory.map v'.hom ≫ mB.hom, ?_⟩
  show F.mapDerivedCategory.map (lB.inv ≫ G.mapDerivedCategory.map v'.hom ≫ mB.hom) = u
  apply (cancel_mono cM.hom).mp
  rw [← show cL.hom ≫ u₀ = u ≫ cM.hom by simp [u₀]]
  apply (cancel_epi (sq.hom.app (DerivedCategory.Q.obj L') ≫ F.mapDerivedCategory.map lB.hom)).mp
  calc
    _ = sq.hom.app (DerivedCategory.Q.obj L') ≫
        F.mapDerivedCategory.map (G.mapDerivedCategory.map v'.hom) ≫
        F.mapDerivedCategory.map mB.hom ≫ cM.hom := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← F.mapDerivedCategory.map_comp_assoc, lB.hom_inv_id]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
    _ = H.mapDerivedCategory.map (K.mapDerivedCategory.map v'.hom) ≫
        sq.hom.app (DerivedCategory.Q.obj M') ≫
        F.mapDerivedCategory.map mB.hom ≫ cM.hom :=
      ((reassoc_of% (sq.hom.naturality v'.hom)) (F.mapDerivedCategory.map mB.hom ≫ cM.hom)).symm
    _ = H.mapDerivedCategory.map t ≫ (H.mapDerivedCategory.map bM.hom ≫ aM.hom) := by
      rw [← hcompM, hv]
    _ = H.mapDerivedCategory.map bL.hom ≫ aL.hom ≫ u₀ := by
      simp [t, Functor.map_comp, Category.assoc, ht]
    _ = _ := by rw [reassoc_of% hcompL]; simp only [Category.assoc]


private theorem eq_zero_of_map_eq_zero_of_surjective_retraction
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] [F.ReflectsIsomorphisms]
    (T : Pretriangulated.Triangle C) (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h : Function.Surjective (F.map : (T.obj₃ ⟶ T.obj₂) → _))
    (hf : F.map T.mor₁ = 0) : T.mor₁ = 0 := by
  obtain ⟨s, hs⟩ := (F.mapTriangle.obj T).yoneda_exact₂ (F.map_distinguished T hT)
    (𝟙 (F.obj T.obj₂)) (by change F.map T.mor₁ ≫ 𝟙 _ = 0; simpa using hf)
  obtain ⟨s', rfl⟩ := h s
  have hm : F.map (T.mor₂ ≫ s') = 𝟙 (F.obj T.obj₂) := by
    change 𝟙 _ = F.map T.mor₂ ≫ F.map s' at hs
    simpa only [Functor.map_comp] using hs.symm
  have : IsIso (F.map (T.mor₂ ≫ s')) := by rw [hm]; infer_instance
  have : IsIso (T.mor₂ ≫ s') := isIso_of_reflects_iso (T.mor₂ ≫ s') F
  have : Mono T.mor₂ := mono_of_mono T.mor₂ s'
  apply (cancel_mono T.mor₂).mp
  rw [Pretriangulated.comp_distTriang_mor_zero₁₂ T hT, zero_comp]

private theorem isDerivedComplete_of_distinguished_triangle
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R))]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : IsDerivedComplete I T.obj₁)
    (h₂ : IsDerivedComplete I T.obj₂) :
    IsDerivedComplete I T.obj₃ := by
  rw [isDerivedComplete_iff_isIso_difference] at h₁ h₂ ⊢
  intro f hf
  let P := productTriangle (fun _ : ℕ => T)
  let d : P ⟶ P := productTriangle.lift (fun _ : ℕ => T)
    (fun n => productTriangle.π (fun _ : ℕ => T) n -
      f • productTriangle.π (fun _ : ℕ => T) (n + 1))
  have hd : P ∈ distinguishedTriangles := productTriangle_distinguished _ (fun _ => hT)
  have hd₁ : IsIso d.hom₁ := by
    simpa only [d, P, productTriangle, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      productTriangle.lift_hom₁, Triangle.sub_hom₁, Triangle.smul_hom₁,
      productTriangle.π_hom₁, Linear.comp_smul, Category.comp_id] using h₁ f hf
  have hd₂ : IsIso d.hom₂ := by
    simpa only [d, P, productTriangle, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      productTriangle.lift_hom₂, Triangle.sub_hom₂, Triangle.smul_hom₂,
      productTriangle.π_hom₂, Linear.comp_smul, Category.comp_id] using h₂ f hf
  simpa only [d, P, productTriangle, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
    productTriangle.lift_hom₃, Triangle.sub_hom₃, Triangle.smul_hom₃,
    productTriangle.π_hom₃, Linear.comp_smul, Category.comp_id] using
    isIso₃_of_isIso₁₂ d hd hd hd₁ hd₂

private theorem surjective_map_restrictScalars_of_small_quotients
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (hquotSmall : ∀ J : Ideal A, Small.{v} (A ⧸ J) →
      Small.{v} (B ⧸ J.map (algebraMap A B)))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))]
    (L M : DerivedCategory (ModuleCat.{v} B))
    (hL : IsDerivedComplete (I.map (algebraMap A B)) L)
    (hM : IsDerivedComplete (I.map (algebraMap A B)) M) :
    Function.Surjective
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.map : (L ⟶ M) → _) := by
  classical
  let F := (ModuleCat.restrictScalars.{v} (algebraMap A B)).mapDerivedCategory
  let L' := DerivedCategory.Q.objPreimage L
  let M' := DerivedCategory.Q.objPreimage M
  let eL := DerivedCategory.Q.objObjPreimageIso L
  let eM := DerivedCategory.Q.objObjPreimageIso M
  intro f
  obtain ⟨g, hg⟩ := surjective_map_restrictScalars_Q_of_small_quotients A B I hI hflat hquot
    hquotSmall L' M'
    (isDerivedComplete_of_iso B _ eL.symm hL)
    (isDerivedComplete_of_iso B _ eM.symm hM)
    (F.map eL.hom ≫ f ≫ F.map eM.inv)
  refine ⟨eL.inv ≫ g ≫ eM.hom, ?_⟩
  show F.map (eL.inv ≫ g ≫ eM.hom) = f
  change F.map g = _ at hg
  simp only [Functor.map_comp, hg, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp, eM.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]


private theorem isEquivalence_restrictScalars_of_small_quotients
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (hquotSmall : ∀ J : Ideal A, Small.{v} (A ⧸ J) →
      Small.{v} (B ⧸ J.map (algebraMap A B)))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K => IsDerivedComplete I K
    let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
      fun K => IsDerivedComplete (I.map (algebraMap A B)) K
    let F := (ModuleCat.restrictScalars.{v} (algebraMap A B)).mapDerivedCategory
    ∀ hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj),
      (P.lift (Q.ι ⋙ F) hF).IsEquivalence := by
  classical
  dsimp only
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
    fun K => IsDerivedComplete I K
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
    fun K => IsDerivedComplete (I.map (algebraMap A B)) K
  let R := ModuleCat.restrictScalars.{v} (algebraMap A B)
  let F := R.mapDerivedCategory
  intro hF
  let T := P.lift (Q.ι ⋙ F) hF
  let : F.ReflectsIsomorphisms := reflectsIsomorphisms_mapDerivedCategory R
  let : T.Full := ⟨fun {X Y} f => by
    obtain ⟨g, hg⟩ := surjective_map_restrictScalars_of_small_quotients A B I hI hflat hquot
      hquotSmall
      X.obj Y.obj X.property Y.property f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩⟩
  let : T.Faithful := ⟨fun {X Y} f g hfg => by
    apply ObjectProperty.hom_ext
    apply sub_eq_zero.mp
    obtain ⟨Z, a, b, htri⟩ := Pretriangulated.distinguished_cocone_triangle (f.hom - g.hom)
    let Δ := Pretriangulated.Triangle.mk (f.hom - g.hom) a b
    have hZ : Q Z := isDerivedComplete_of_distinguished_triangle B _ Δ htri
      X.property Y.property
    apply eq_zero_of_map_eq_zero_of_surjective_retraction F Δ htri
      (surjective_map_restrictScalars_of_small_quotients A B I hI hflat hquot hquotSmall Z Y.obj hZ
        Y.property)
    show F.map (f.hom - g.hom) = 0
    rw [Functor.map_sub, sub_eq_zero]
    exact congrArg (fun k => k.hom) hfg⟩
  let : T.EssSurj := ⟨fun X => by
    obtain ⟨Y, hY, ⟨e⟩⟩ := exists_restrictScalars_iso_of_small_quotients A B I hI hflat hquot
      hquotSmall
      X.obj X.property
    exact ⟨⟨Y, hY⟩, ⟨P.isoMk e⟩⟩⟩
  exact Functor.IsEquivalence.mk


private theorem isDerivedComplete_of_isZero
    (R : Type u) [CommRing R] (I : Ideal R)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R))]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsZero K) :
    IsDerivedComplete I K := by
  rw [isDerivedComplete_iff_isIso_difference]
  have hP : IsZero (∏ᶜ fun _ : ℕ => K) := by
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro n
    exact hK.eq_of_tgt _ _
  intro f hf
  exact hP.isIso hP _

private theorem isZero_of_isDerivedComplete_top
    (R : Type u) [CommRing R]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R))]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : IsDerivedComplete (⊤ : Ideal R) K) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  apply eq_zero_of_isIso_smul_of_isDerivedComplete (⊤ : Ideal R) hK
    (f := 1) (by simp) (h := 𝟙 K)
  simp only [one_smul]
  infer_instance

private theorem isEquivalence_lift_of_isZero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    (F : C ⥤ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (hP : ∀ X, P X → IsZero X) (hQ : ∀ Y, Q Y → IsZero Y)
    (X₀ : C) (hX₀ : P X₀)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :
    (Q.lift (P.ι ⋙ F) hF).IsEquivalence := by
  let T := Q.lift (P.ι ⋙ F) hF
  let : T.Full := ⟨fun {X Y} f =>
    ⟨ObjectProperty.homMk 0, Q.hom_ext ((hQ _ (hF X)).eq_of_src _ _)⟩⟩
  let : T.Faithful := ⟨fun {X Y} f g _ => P.hom_ext ((hP X.obj X.property).eq_of_src _ _)⟩
  let : T.EssSurj := ⟨fun Y =>
    ⟨⟨X₀, hX₀⟩, ⟨Q.isoMk ((hQ _ (hF ⟨X₀, hX₀⟩)).iso (hQ Y.obj Y.property))⟩⟩⟩
  exact Functor.IsEquivalence.mk

private theorem isEquivalence_restrictScalars_of_bijective
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K => IsDerivedComplete I K
    let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
      fun K => IsDerivedComplete (I.map f) K
    let F := (ModuleCat.restrictScalars.{v} f).mapDerivedCategory
    ∀ hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj),
      (P.lift (Q.ι ⋙ F) hF).IsEquivalence := by
  dsimp only
  let R := ModuleCat.restrictScalars.{v} f
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
    fun K => IsDerivedComplete I K
  let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
    fun K => IsDerivedComplete (I.map f) K
  let : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (RingEquiv.ofBijective f hf)
  let : R.mapDerivedCategory.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.ofBijective f hf)).functor
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h => isDerivedComplete_of_iso A I e h⟩
  intro hF
  exact isEquivalence_lift_of_isEquivalence R.mapDerivedCategory Q P
    (fun K => isDerivedComplete_restrictScalars_iff A B f I K) hF

private theorem isEquivalence_restrictScalars_of_small_target
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    [Small.{v} B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} B))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K => IsDerivedComplete I K
    let Q : ObjectProperty (DerivedCategory (ModuleCat.{v} B)) :=
      fun K => IsDerivedComplete (I.map (algebraMap A B)) K
    let F := (ModuleCat.restrictScalars.{v} (algebraMap A B)).mapDerivedCategory
    ∀ hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj),
      (P.lift (Q.ι ⋙ F) hF).IsEquivalence :=
  isEquivalence_restrictScalars_of_small_quotients A B I hI hflat hquot (fun _ _ => inferInstance)

/-- If `A → B` is flat and induces an isomorphism modulo a finitely generated ideal `I`, then
restriction of scalars induces an equivalence from the full subcategory of `I B`-derived complete
objects of `D(B)` to the full subcategory of `I`-derived complete objects of `D(A)`. -/
@[stacks 0925]
theorem restrictScalars_equivalence_derivedComplete
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map)) :
    ∃ hprodA : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)),
    ∃ hprodB : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} B)),
    letI := hprodA
    letI := hprodB
    let completeA : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    let completeB : ObjectProperty (DerivedCategory (ModuleCat.{u} B)) :=
      fun K ↦ IsDerivedComplete (I.map (algebraMap A B)) K
    let res := (ModuleCat.restrictScalars.{u} (algebraMap A B)).mapDerivedCategory
    ∃ hres : ∀ K : completeB.FullSubcategory, completeA (res.obj K.obj),
      Functor.IsEquivalence
        (completeA.lift (completeB.ι ⋙ res) (fun K ↦ hres K)) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
    moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} B) :=
    moduleCat_hasExactLimitsOfShape_discrete.{u} B ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} B)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  refine ⟨inferInstance, inferInstance, ?_⟩
  dsimp only
  refine ⟨fun K ↦ (isDerivedComplete_restrictScalars_iff
    A B (algebraMap A B) I K.obj).mpr K.property, ?_⟩
  exact isEquivalence_restrictScalars_large.{u, u, u} A B I hI hflat hquot _

end CompleteRestrictScalarsEquivalence

end
