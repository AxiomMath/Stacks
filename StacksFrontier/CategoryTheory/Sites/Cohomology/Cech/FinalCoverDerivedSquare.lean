module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareMapResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDerived
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The Čech comparison and derived comparison maps along a morphism of sites

Let `(C, R, A, D)` and `(C', R', A', D')` be two instances of the setting of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/FinalCoverDerived.lean`: a site with a sheaf of
rings, a ring mapping to its global sections, and a family of objects covering the final object
with all finite nonempty products. Let `P` be an exact functor from sheaves of `R`-modules to
sheaves of `R'`-modules (a pullback along a morphism of sites, computed by precomposition), let
`ρ : A ⟶ A'` be a ring map, and let

`α : Γ(C, -) ⟶ P ⋙ Γ(C', -) ⋙ res_ρ`

be a comparison of global sections. Its derived form is
`CategoryTheory.Functor.derivedSquareMap α N : RΓ(C, N) ⟶ res_ρ RΓ(C', P N)`.

This file proves that **under the Čech comparisons `Č(D, N) ⟶ RΓ(C, N)` and
`Č(D', P N) ⟶ RΓ(C', P N)` the derived map `derivedSquareMap α N` is the map induced by any map of
Čech complexes `c : Č(D, -) ⟶ P ⋙ Č(D', -) ⋙ res_ρ` compatible with `α` in degree zero**
(`cechToDerivedGlobalSections_comp_derivedSquareMap`).

## The proof

`derivedSquareMap α N` is computed on injective resolutions `N ⟶ I^•` and `P N ⟶ I'^•` together
with a lift `τ : P(I^•) ⟶ I'^•` (`CategoryTheory.Functor.derivedSquareMap_eq_of_resolutions`);
such a lift exists because `I'^•` is K-injective, and it is the identity on `P N` in degree zero
on the nose, because homotopic maps out of a complex concentrated in degree zero into a complex
vanishing in negative degrees agree in degree zero (`exists_lift_resolution`). The Čech
comparisons are computed on the same resolutions, through the total complexes of the Čech double
complexes, and `c` and `τ` induce a map between those total complexes
(`totalCechMap`) compatible with both augmentations; the claim is then a computation in the
bounded below homotopy category.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open Stacks.Cohomology.SiteModules StacksDraft.TotalComplexQuasiIso

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe w v u r r' uA uA' m

namespace Stacks.CechSite.FinalCover

/-! ### Generic lemmas on resolutions -/

section Generic

variable {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]

/-- The augmentation `X[0] ⟶ I^•` of an injective resolution, in the bounded below homotopy
category. -/
abbrev resolutionHom {X : 𝒞} (I : InjectiveResolution X) :
    (HomotopyCategory.Plus.singleFunctor 𝒞 0).obj X ⟶
      (HomotopyCategory.Plus.quotient 𝒞).obj I.plusObj :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map I.ι')

/-- The augmentation of an injective resolution becomes invertible in `D⁺`. -/
lemma isIso_Qh_map_resolutionHom {X : 𝒞} (I : InjectiveResolution X) :
    IsIso (DerivedCategory.Plus.Qh.map (resolutionHom I)) :=
  Functor.isIso_Qh_map_of_mem_quasiIso _
    (Functor.quasiIso_singleHomPlusOfIsStrictlyGE 0 I.ι')

/-- The two identifications of `X[0]` with an injective resolution in `D⁺` agree. -/
lemma singleFunctorPlusIsoCompQh_inv_app_comp_plusQIso_hom {X : 𝒞}
    (I : InjectiveResolution X) :
    (Functor.singleFunctorPlusIsoCompQh (A := 𝒞) 0).inv.app X ≫ I.plusQIso.hom =
      DerivedCategory.Plus.Qh.map (resolutionHom I) ≫
        (DerivedCategory.Plus.qhQIso I.plusObj).hom := by
  have e₁ : ((Functor.singleFunctorPlusIsoCompQh (A := 𝒞) 0).inv.app X).hom = _ :=
    Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app X
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, e₁]
  have e₀ : (DerivedCategory.singleFunctorIsoCompQh 𝒞 0).inv.app X =
      (DerivedCategory.quotientCompQhIso 𝒞).hom.app _ :=
    Iso.inv_ext (f := (DerivedCategory.singleFunctorIsoCompQh 𝒞 0).app X) (by
      show (DerivedCategory.singleFunctorIsoCompQh 𝒞 0).hom.app X ≫ _ = _
      rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
      exact Iso.inv_hom_id_app _ _)
  rw [e₀]
  exact (DerivedCategory.quotientCompQhIso_hom_naturality I.ι').symm

variable {ℳ : Type*} [Category* ℳ] [Abelian ℳ] [HasDerivedCategory ℳ] [EnoughInjectives 𝒞]
  (Γ : 𝒞 ⥤ ℳ) [Γ.Additive]

/-- **The identification `RΓ(X[0]) ≅ Γ(I^•)` of
`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution` is the inverse of
`CategoryTheory.InjectiveResolution.toRightDerivedPlus`**, for an injective resolution. -/
lemma rightDerivedFunctorPlusObjSingleIsoOfResolution_inv {X : 𝒞} (I : InjectiveResolution X)
    (hJ : ∀ n : ℤ, Γ.rightAcyclic
      (((HomotopyCategory.Plus.quotient 𝒞).obj I.plusObj).obj.as.X n)) :
    (Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution Γ (resolutionHom I)
      (isIso_Qh_map_resolutionHom I) hJ).inv = I.toRightDerivedPlus Γ := by
  have h0 := singleFunctorPlusIsoCompQh_inv_app_comp_plusQIso_hom I
  have := isIso_Qh_map_resolutionHom I
  have h : inv (DerivedCategory.Plus.Qh.map (resolutionHom I)) ≫
      (Functor.singleFunctorPlusIsoCompQh (A := 𝒞) 0).inv.app X =
        (DerivedCategory.Plus.qhQIso I.plusObj).hom ≫ I.plusQIso.inv := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← h0, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution,
    Functor.singleFunctorPlusObjIsoQhOfIsIso, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Functor.mapIso_inv, asIso_inv, Iso.app_inv, Functor.map_comp, h,
    InjectiveResolution.toRightDerivedPlus]

omit [HasDerivedCategory 𝒞] [EnoughInjectives 𝒞] in
/-- **Homotopic maps out of a complex concentrated in degree zero into a complex vanishing in
negative degrees agree in degree zero.** -/
lemma f_zero_eq_of_homotopy {K L : CochainComplex 𝒞 ℤ} (hK : IsZero (K.X 1))
    (hL : IsZero (L.X (-1))) {f g : K ⟶ L} (h : Homotopy f g) : f.f 0 = g.f 0 := by
  have := h.comm 0
  rw [dNext_eq h.hom (show (up ℤ).Rel 0 1 by simp), prevD_eq h.hom (show (up ℤ).Rel (-1) 0 by simp),
    hK.eq_of_tgt (K.d 0 1) 0, hL.eq_of_tgt (h.hom 0 (-1)) 0, zero_comp, zero_comp,
    zero_add, zero_add] at this
  exact this

variable {𝒞₀ : Type*} [Category* 𝒞₀] [Abelian 𝒞₀] [HasDerivedCategory 𝒞₀] [EnoughInjectives 𝒞₀]
  [EnoughInjectives 𝒞] (P : 𝒞₀ ⥤ 𝒞) [P.Additive] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P]

/-- **A lift of an injective resolution along an exact functor to an injective resolution of the
image.** For injective resolutions `X ⟶ I^•` and `P X ⟶ I'^•` there is a map of complexes
`τ : P(I^•) ⟶ I'^•` which is compatible with the augmentations in the bounded below homotopy
category and is, in degree zero, compatible with the inclusions `P X ⟶ P(I^0)` and
`P X ⟶ I'^0` on the nose. -/
lemma exists_lift_resolution {X : 𝒞₀} (I : InjectiveResolution X)
    (I' : InjectiveResolution (P.obj X)) :
    ∃ τ : (P.mapHomologicalComplex (up ℤ)).obj I.cochainComplex ⟶ I'.cochainComplex,
      P.mapHomotopyCategoryPlus.map (resolutionHom I) ≫
          (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map τ) :
            P.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient 𝒞₀).obj I.plusObj) ⟶
              (HomotopyCategory.Plus.quotient 𝒞).obj I'.plusObj) =
        (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫ resolutionHom I' ∧
      P.map I.inclusionZero ≫ τ.f 0 = I'.inclusionZero := by
  let J := (HomotopyCategory.Plus.quotient 𝒞₀).obj I.plusObj
  let J' := (HomotopyCategory.Plus.quotient 𝒞).obj I'.plusObj
  have hK : CochainComplex.IsKInjective J'.obj.as :=
    CochainComplex.isKInjective_of_injective I'.cochainComplex 0
  have hs : IsIso (DerivedCategory.Plus.Qh.map ((P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫
      P.mapHomotopyCategoryPlus.map (resolutionHom I))) :=
    Functor.isIso_Qh_map_mapHomotopyCategoryPlusResolution (P := P) (resolutionHom I)
      (isIso_Qh_map_resolutionHom I)
  obtain ⟨τh, hτh⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    (P.mapHomotopyCategoryPlus.obj J) J' hK).2
      (inv (DerivedCategory.Plus.Qh.map ((P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫
        P.mapHomotopyCategoryPlus.map (resolutionHom I))) ≫
        DerivedCategory.Plus.Qh.map (resolutionHom I'))
  have hsτ : ((P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫
      P.mapHomotopyCategoryPlus.map (resolutionHom I)) ≫ τh = resolutionHom I' := by
    refine (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ J' hK).1 ?_
    rw [Functor.map_comp, hτh, IsIso.hom_inv_id_assoc]
  obtain ⟨τ, hτ⟩ := (HomotopyCategory.quotient 𝒞 (up ℤ)).map_surjective τh.hom
  have hτ' : (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map τ) :
      P.mapHomotopyCategoryPlus.obj J ⟶ J') = τh := ObjectProperty.hom_ext _ hτ
  have hcomm : P.mapHomotopyCategoryPlus.map (resolutionHom I) ≫ τh =
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫ resolutionHom I' := by
    rw [← hsτ, Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨τ, by rw [hτ']; exact hcomm, ?_⟩
  -- the degree zero component, from the homotopy
  have hq : (HomotopyCategory.quotient 𝒞 (up ℤ)).map
      ((P.mapHomologicalComplex (up ℤ)).map I.ι' ≫ τ) =
      (HomotopyCategory.quotient 𝒞 (up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex P (up ℤ) 0).hom.app X ≫ I'.ι') := by
    have := congrArg (fun f ↦ f.hom) hcomm
    simp only [ObjectProperty.FullSubcategory.comp_hom] at this
    have e1 : (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom.hom =
        (HomotopyCategory.quotient 𝒞 (up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P (up ℤ) 0).hom.app X) :=
      (HomotopyCategory.Plus.ι 𝒞).map_preimage _
    rw [e1, ← hτ] at this
    rw [Functor.map_comp]
    exact ((HomotopyCategory.quotient 𝒞 (up ℤ)).map_comp _ _).trans this
  have h0 := f_zero_eq_of_homotopy
    (P.map_isZero (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 X 1 one_ne_zero))
    (I'.cochainComplex.isZero_of_isStrictlyGE 0 (-1) (by omega))
    (HomotopyCategory.homotopyOfEq _ _ hq)
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Category.assoc] at h0
  dsimp only [InjectiveResolution.inclusionZero]
  rw [Functor.map_comp, Category.assoc, show P.map (I.ι'.f 0) ≫ τ.f 0 = _ from h0,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Generic

/-! ### An additive functor and total complexes -/

section TotalComparison

variable {ℳ ℳ' : Type*} [Category* ℳ] [Preadditive ℳ] [Category* ℳ'] [Preadditive ℳ']
  (F : ℳ' ⥤ ℳ) [F.Additive]

/-- An additive functor applied termwise to a double complex. -/
abbrev mapBicomplex (K : HomologicalComplex₂ ℳ' (up ℤ) (up ℤ)) :
    HomologicalComplex₂ ℳ (up ℤ) (up ℤ) :=
  ((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj K

/-- **The comparison `Tot(F K) ⟶ F(Tot K)`** for an additive functor `F` and a double complex
`K`: on the summand `F(K^{p,q})` it is `F` of the inclusion of `K^{p,q}` into `Tot K`. -/
def totalComparison (K : HomologicalComplex₂ ℳ' (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    [(mapBicomplex F K).HasTotal (up ℤ)] :
    (mapBicomplex F K).total (up ℤ) ⟶ (F.mapHomologicalComplex (up ℤ)).obj (K.total (up ℤ)) where
  f n := (mapBicomplex F K).totalDesc fun p q h ↦ F.map (K.ιTotal (up ℤ) p q n h)
  comm' n n' hnn' := by
    obtain rfl : n + 1 = n' := hnn'
    refine HomologicalComplex₂.total.hom_ext _ fun p q hpq ↦ ?_
    have hpq' : p + q = n := hpq
    rw [HomologicalComplex₂.ι_totalDesc_assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp, HomologicalComplex₂.ιTotal_d_up_ℤ _ p q n hpq', ← Category.assoc,
      HomologicalComplex₂.ιTotal_d_up_ℤ _ p q n hpq']
    simp only [Units.smul_def, Functor.map_add, Functor.map_zsmul, Functor.map_comp,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
      HomologicalComplex₂.ι_totalDesc]
    rfl

/-- The components of `totalComparison`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalComparison_f (K : HomologicalComplex₂ ℳ' (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    [(mapBicomplex F K).HasTotal (up ℤ)] (p q n : ℤ) (h : p + q = n) :
    (mapBicomplex F K).ιTotal (up ℤ) p q n h ≫ (totalComparison F K).f n =
      F.map (K.ιTotal (up ℤ) p q n h) :=
  HomologicalComplex₂.ι_totalDesc (mapBicomplex F K)
    (fun p q h ↦ F.map (K.ιTotal (up ℤ) p q n h)) p q h

end TotalComparison

/-! ### Bookkeeping -/

section Bookkeeping

/-- Reading `Q(β) ≫ Q(α)⁻¹` through the comparison of the two descriptions of `D⁺`. -/
lemma zigzag_eq {𝒦 : Type*} [Category* 𝒦] {XK X TK T SK S : 𝒦} (eK : XK ≅ X) (eT : TK ≅ T)
    (eS : SK ≅ S) (b : X ⟶ T) (a : S ⟶ T) [IsIso a] (B : XK ⟶ TK) (A : SK ⟶ TK) [IsIso A]
    (hb : B ≫ eT.hom = eK.hom ≫ b) (ha : A ≫ eT.hom = eS.hom ≫ a) :
    b ≫ inv a ≫ eS.inv = eK.inv ≫ B ≫ inv A := by
  have h1 : b = eK.inv ≫ B ≫ eT.hom := by rw [hb, Iso.inv_hom_id_assoc]
  have h2 : inv a = eT.inv ≫ inv A ≫ eS.hom := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [show a = eS.inv ≫ A ≫ eT.hom by rw [ha, Iso.inv_hom_id_assoc]]
    simp
  rw [h1, h2]
  simp

/-- The bookkeeping of `cechToDerivedGlobalSections_comp_derivedSquareMap`, in an arbitrary pair
of categories with a functor between them. -/
lemma derivedSquare_bookkeeping {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (G : 𝒦' ⥤ 𝒦)
    {X Y S S' RN U XK V T0 RT : 𝒦} {U' RN' V' X' Y' S1 T1 : 𝒦'}
    (b0 : X ⟶ Y) (a0 : S ⟶ Y) [IsIso a0] (e0 : S' ≅ S) (t0 : S' ⟶ RN) (w0 : RN ⟶ S')
    (hα : S' ⟶ U) (fiS : U ⟶ G.obj U') (t1 : U' ⟶ RN') (eK : XK ≅ X) (hc : XK ⟶ V)
    (fiK : V ⟶ G.obj V') (eK' : V' ≅ X') (b1 : X' ⟶ Y') (a1 : S1 ⟶ Y') [IsIso a1]
    (e1 : U' ≅ S1) (B0 : XK ⟶ T0) (A0 : S' ⟶ T0) (hA0 : IsIso A0) (Th : T0 ⟶ RT)
    (RA1 : U ⟶ RT) (RB1 : V ⟶ RT) (fiT : RT ⟶ G.obj T1) (B1 : V' ⟶ T1) (A1 : U' ⟶ T1)
    (hA1 : IsIso A1)
    (f1 : t0 ≫ w0 = 𝟙 S') (f3 : b0 ≫ inv a0 ≫ e0.inv = eK.inv ≫ B0 ≫ inv A0)
    (f4 : eK'.hom ≫ b1 ≫ inv a1 ≫ e1.inv = B1 ≫ inv A1) (f5 : A0 ≫ Th = hα ≫ RA1)
    (f6 : B0 ≫ Th = hc ≫ RB1) (f7 : RB1 ≫ fiT = fiK ≫ G.map B1)
    (f8 : RA1 ≫ fiT = fiS ≫ G.map A1) :
    (b0 ≫ inv a0 ≫ e0.inv ≫ t0) ≫ w0 ≫ hα ≫ fiS ≫ G.map t1 =
      eK.inv ≫ hc ≫ fiK ≫ G.map (eK'.hom ≫ b1 ≫ inv a1 ≫ e1.inv ≫ t1) := by
  have k0 : A0 ≫ Th ≫ fiT = hα ≫ fiS ≫ G.map A1 := by rw [reassoc_of% f5, f8]
  have k1 : inv A0 ≫ hα ≫ fiS = Th ≫ fiT ≫ inv (G.map A1) := by
    rw [IsIso.inv_comp_eq, ← cancel_mono (G.map A1)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact k0.symm
  have k2 : G.map (eK'.hom ≫ b1 ≫ inv a1 ≫ e1.inv ≫ t1) =
      G.map B1 ≫ inv (G.map A1) ≫ G.map t1 := by
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      show ((eK'.hom ≫ b1) ≫ inv a1) ≫ e1.inv = B1 ≫ inv A1 by simpa using f4,
      Functor.map_comp, Functor.map_comp, Functor.map_inv, Category.assoc]
  rw [k2]
  simp only [Category.assoc]
  rw [reassoc_of% f1, reassoc_of% f3, reassoc_of% k1, reassoc_of% f6, reassoc_of% f7]

end Bookkeeping

/-! ### The Čech comparison in the bounded below homotopy category -/

section QhForm

attribute [local instance high] hasProducts_moduleCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R) {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [HasSheafify J AddCommGrpCat.{max u v w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (ModuleCat.{max u v w} A)]

/-- Equal composites in the bounded below homotopy category stay equal in `D⁺`. -/
private lemma Qh_map_comp_eq_of_hom_eq {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞]
    [HasDerivedCategory 𝒞] {X Y Z W : HomotopyCategory.Plus 𝒞} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : X ⟶ W) (b' : W ⟶ Z) (h : a.hom ≫ b.hom = a'.hom ≫ b'.hom) :
    DerivedCategory.Plus.Qh.map a ≫ DerivedCategory.Plus.Qh.map b =
      DerivedCategory.Plus.Qh.map a' ≫ DerivedCategory.Plus.Qh.map b' := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (ObjectProperty.hom_ext _ h)

/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺` through the
homotopy category. -/
lemma isIso_Qh_map_quotient_map {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]
    {L L' : CochainComplex.Plus 𝒞} (f : L ⟶ L') (hf : QuasiIso f.hom) :
    IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient 𝒞).map f)) := by
  refine Functor.isIso_Qh_map_of_mem_quasiIso _ ?_
  rw [HomotopyCategory.Plus.quasiIso_iff]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f.hom).2
    ((HomologicalComplex.mem_quasiIso_iff f.hom).2 hf)

/-- **The Čech comparison read in the homotopy category**: `Q(β) ≫ Q(α)⁻¹`, followed by the
comparison of the two descriptions of `D⁺`, is the class of the zigzag `β`, `α` in the bounded
below homotopy category. -/
lemma cechZigzag_eq_Qh (hD : J.CoversTop D) {N : SheafOfModules.{max u v w} R}
    (I : InjectiveResolution N) :
    haveI := isIso_Q_map_totalAugmentationPlus R φ D hD I
    haveI := isIso_Qh_map_quotient_map (totalAugmentationPlus R φ D hD I)
      (quasiIso_totalAugmentation R φ D hD I.cochainComplex)
    DerivedCategory.Plus.Q.map (cechToTotalPlus R φ D I) ≫
        inv (DerivedCategory.Plus.Q.map (totalAugmentationPlus R φ D hD I)) ≫
        (DerivedCategory.Plus.qhQIso (sectionsPlus R φ I)).inv =
      (DerivedCategory.Plus.qhQIso ((cechPlusFunctor R φ D).obj N)).inv ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map (cechToTotalPlus R φ D I)) ≫
        inv (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map (totalAugmentationPlus R φ D hD I))) := by
  have := isIso_Q_map_totalAugmentationPlus R φ D hD I
  have := isIso_Qh_map_quotient_map (totalAugmentationPlus R φ D hD I)
    (quasiIso_totalAugmentation R φ D hD I.cochainComplex)
  exact zigzag_eq _ _ _ _ _ _ _ (DerivedCategory.Plus.qhQIso_naturality _)
    (DerivedCategory.Plus.qhQIso_naturality _)

end QhForm

/-! ### Two sites -/

section Square

attribute [local instance high] hasProducts_moduleCat

attribute [local instance] preservesFiniteLimits_restrictScalars

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/-- Restriction of scalars preserves finite colimits, whatever the universes of the two rings. -/
theorem preservesFiniteColimits_restrictScalars {S S' : Type*} [Ring S] [Ring S'] (f : S →+* S') :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{m} f) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

attribute [local instance] preservesFiniteColimits_restrictScalars

/-- An additive functor applied termwise to a double complex with finite antidiagonals gives a
double complex with finite antidiagonals. -/
lemma diagonalFinite_mapBicomplex {ℳ ℳ' : Type*} [Category* ℳ] [Abelian ℳ] [Category* ℳ']
    [Abelian ℳ'] (F : ℳ' ⥤ ℳ) [F.Additive] {K : HomologicalComplex₂ ℳ' (up ℤ) (up ℤ)}
    (h : DiagonalFinite K) : DiagonalFinite (mapBicomplex F K) :=
  fun n ↦ (h n).subset fun _ hp hz ↦ hp (F.map_isZero hz)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R) {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [HasSheafify J AddCommGrpCat.{max u v w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (SheafOfModules.{max u v w} R)]
  {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'} (R' : Sheaf J' RingCat.{r'})
  {A' : Type uA'} [Ring A'] (φ' : A' →+* GlobalSectionRing R') {ι' : Type w} (D' : ι' → C')
  [∀ (n : ℕ) (x : Fin (n + 1) → ι'), HasProduct (fun a ↦ D' (x a))]
  [HasSheafify J' AddCommGrpCat.{max u v w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (SheafOfModules.{max u v w} R')]
  (P : SheafOfModules.{max u v w} R ⥤ SheafOfModules.{max u v w} R') [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] (ρ : A →+* A')
  (α : baseGlobalSections R φ ⟶ P ⋙ baseGlobalSections R' φ' ⋙ ModuleCat.restrictScalars ρ)
  (c : cechIntFunctor R φ D ⟶
    P ⋙ cechIntFunctor R' φ' D' ⋙ (ModuleCat.restrictScalars ρ).mapHomologicalComplex (up ℤ))

/-- The restriction of scalars of a Čech double complex has a total complex. -/
instance hasTotal_mapBicomplex_cechBicomplex
    (L : CochainComplex (SheafOfModules.{max u v w} R') ℤ) [L.IsStrictlyGE 0] :
    (mapBicomplex (ModuleCat.restrictScalars.{max u v w} ρ)
      (cechBicomplex R' φ' D' L)).HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _
    (diagonalFinite_mapBicomplex _ (diagonalFinite_cechBicomplex R' φ' D' L))

/-- The map of Čech double complexes induced by `c` and a map of complexes `τ : P(L) ⟶ L'`. -/
def cechBicomplexHom {L : CochainComplex (SheafOfModules.{max u v w} R) ℤ}
    {L' : CochainComplex (SheafOfModules.{max u v w} R') ℤ}
    (τ : (P.mapHomologicalComplex (up ℤ)).obj L ⟶ L') :
    cechBicomplex R φ D L ⟶
      mapBicomplex (ModuleCat.restrictScalars.{max u v w} ρ) (cechBicomplex R' φ' D' L') :=
  (NatTrans.mapHomologicalComplex c (up ℤ)).app L ≫
    (((ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
      (up ℤ)).map (((cechIntFunctor R' φ' D').mapHomologicalComplex (up ℤ)).map τ)

/-- **The map of total Čech complexes** induced by `c` and `τ`, landing in the restriction of
scalars of the total Čech complex of `L'`. -/
def totalCechMap {L : CochainComplex (SheafOfModules.{max u v w} R) ℤ}
    {L' : CochainComplex (SheafOfModules.{max u v w} R') ℤ} [L.IsStrictlyGE 0] [L'.IsStrictlyGE 0]
    (τ : (P.mapHomologicalComplex (up ℤ)).obj L ⟶ L') :
    (cechBicomplex R φ D L).total (up ℤ) ⟶
      ((ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ)).obj
        ((cechBicomplex R' φ' D' L').total (up ℤ)) :=
  HomologicalComplex₂.total.map (cechBicomplexHom R φ D R' φ' D' P ρ c τ) (up ℤ) ≫
    totalComparison _ _

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [EnoughInjectives (SheafOfModules.{max u v w} R')] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P] in
/-- The components of `totalCechMap`. -/
lemma ιTotal_totalCechMap_f {L : CochainComplex (SheafOfModules.{max u v w} R) ℤ}
    {L' : CochainComplex (SheafOfModules.{max u v w} R') ℤ} [L.IsStrictlyGE 0] [L'.IsStrictlyGE 0]
    (τ : (P.mapHomologicalComplex (up ℤ)).obj L ⟶ L') (p q n : ℤ) (h : p + q = n) :
    (cechBicomplex R φ D L).ιTotal (up ℤ) p q n h ≫ (totalCechMap R φ D R' φ' D' P ρ c τ).f n =
      (c.app (L.X p)).f q ≫ (ModuleCat.restrictScalars.{max u v w} ρ).map
        (((cechIntFunctor R' φ' D').map (τ.f p)).f q ≫
          (cechBicomplex R' φ' D' L').ιTotal (up ℤ) p q n h) := by
  dsimp only [totalCechMap]
  rw [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc,
    ιTotal_totalComparison_f, Functor.map_comp]
  rfl

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [EnoughInjectives (SheafOfModules.{max u v w} R')] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P] in
/-- **`α` is compatible with the map of total Čech complexes**, for `c` compatible with `α` in
degree zero. -/
lemma totalAugmentation_comp_totalCechMap (hD : J.CoversTop D) (hD' : J'.CoversTop D')
    (hc : ∀ N, augmentationInt R φ D N ≫ (c.app N).f 0 =
      α.app N ≫ (ModuleCat.restrictScalars ρ).map (augmentationInt R' φ' D' (P.obj N)))
    {L : CochainComplex (SheafOfModules.{max u v w} R) ℤ}
    {L' : CochainComplex (SheafOfModules.{max u v w} R') ℤ} [L.IsStrictlyGE 0] [L'.IsStrictlyGE 0]
    [∀ q, Injective (L.X q)] [∀ q, Injective (L'.X q)]
    (τ : (P.mapHomologicalComplex (up ℤ)).obj L ⟶ L') :
    totalAugmentation R φ D hD L ≫ totalCechMap R φ D R' φ' D' P ρ c τ =
      ((NatTrans.mapHomologicalComplex α (up ℤ)).app L ≫
        ((ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ)).map
          (((baseGlobalSections R' φ').mapHomologicalComplex (up ℤ)).map τ)) ≫
        ((ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ)).map
          (totalAugmentation R' φ' D' hD' L') := by
  refine HomologicalComplex.hom_ext _ _ fun q ↦ ?_
  rw [HomologicalComplex.comp_f, totalAugmentation_f, Category.assoc, ιTotal_totalCechMap_f,
    reassoc_of% (hc (L.X q))]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, totalAugmentation_f, Category.assoc, ← Functor.map_comp]
  congr 2
  exact (congrArg (· ≫ _) (augmentationInt_naturality R' φ' D' (τ.f q))).trans
    (Category.assoc _ _ _)

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [EnoughInjectives (SheafOfModules.{max u v w} R')] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P] in
/-- **`β` is compatible with the map of total Čech complexes**, for a lift `τ` which is, in degree
zero, compatible with the inclusions on the nose. -/
lemma cechToTotal_comp_totalCechMap {N : SheafOfModules.{max u v w} R}
    (I : InjectiveResolution N) (I' : InjectiveResolution (P.obj N))
    (τ : (P.mapHomologicalComplex (up ℤ)).obj I.cochainComplex ⟶ I'.cochainComplex)
    (hτ : P.map I.inclusionZero ≫ τ.f 0 = I'.inclusionZero) :
    cechToTotal R φ D I ≫ totalCechMap R φ D R' φ' D' P ρ c τ =
      c.app N ≫ ((ModuleCat.restrictScalars.{max u v w} ρ).mapHomologicalComplex (up ℤ)).map
        (cechToTotal R' φ' D' I') := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  have hn : ((cechIntFunctor R φ D).map I.inclusionZero).f p ≫
      (c.app (I.cochainComplex.X 0)).f p =
        (c.app N).f p ≫ (ModuleCat.restrictScalars ρ).map
          (((cechIntFunctor R' φ' D').map (P.map I.inclusionZero)).f p) :=
    congrArg (fun f ↦ HomologicalComplex.Hom.f f p) (c.naturality I.inclusionZero)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [cechToTotal]
  rw [Category.assoc, ιTotal_totalCechMap_f]
  refine ((reassoc_of% hn) _).trans ?_
  congr 1
  show _ = (ModuleCat.restrictScalars ρ).map
    (((cechIntFunctor R' φ' D').map I'.inclusionZero).f p ≫ _)
  rw [← Functor.map_comp, ← Category.assoc, ← HomologicalComplex.comp_f]
  congr 3
  exact ((cechIntFunctor R' φ' D').map_comp _ _).symm.trans (congrArg _ hτ)

variable [HasDerivedCategory (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (ModuleCat.{max u v w} A)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R')]
  [HasDerivedCategory (ModuleCat.{max u v w} A')] [EnoughInjectives (ModuleCat.{max u v w} A')]

/-- **The map of Čech complexes `Č(D, N) ⟶ res_ρ Č(D', P N)` induced by `c`**, in the bounded
below homotopy category. -/
abbrev cechMapPlus (N : SheafOfModules.{max u v w} R) :
    (HomotopyCategory.Plus.quotient _).obj ((cechPlusFunctor R φ D).obj N) ⟶
      (ModuleCat.restrictScalars.{max u v w} ρ).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj ((cechPlusFunctor R' φ' D').obj (P.obj N))) :=
  ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (c.app N))

/-- **The derived comparison of global sections is the Čech map, under the Čech
comparisons.** Let `α : Γ(C, -) ⟶ P ⋙ Γ(C', -) ⋙ res_ρ` be a comparison of global sections
along an exact functor `P` of sheaves of modules, and let
`c : Č(D, -) ⟶ P ⋙ Č(D', -) ⋙ res_ρ` be a map of Čech complexes which in degree zero is
compatible with `α` and the augmentations. Then for every sheaf of `R`-modules `N`, the
comparison `Č(D, N) ⟶ RΓ(C, N)` of `cechToDerivedGlobalSections` followed by the derived map
`CategoryTheory.Functor.derivedSquareMap α N : RΓ(C, N) ⟶ res_ρ RΓ(C', P N)` is the class of
the map of complexes `c_N : Č(D, N) ⟶ res_ρ Č(D', P N)` followed by `res_ρ` of the comparison
`Č(D', P N) ⟶ RΓ(C', P N)`. -/
theorem cechToDerivedGlobalSections_comp_derivedSquareMap (hD : J.CoversTop D)
    (hD' : J'.CoversTop D')
    (hc : ∀ N, augmentationInt R φ D N ≫ (c.app N).f 0 =
      α.app N ≫ (ModuleCat.restrictScalars ρ).map (augmentationInt R' φ' D' (P.obj N)))
    (N : SheafOfModules.{max u v w} R) :
    (cechToDerivedGlobalSections R φ D hD).app N ≫ Functor.derivedSquareMap α N =
      (DerivedCategory.Plus.qhQIso ((cechPlusFunctor R φ D).obj N)).inv ≫
        DerivedCategory.Plus.Qh.map (cechMapPlus R φ D R' φ' D' P ρ c N) ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).mapDerivedCategoryPlusFactorsh.inv.app _ ≫
        (ModuleCat.restrictScalars.{max u v w} ρ).mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.qhQIso ((cechPlusFunctor R' φ' D').obj (P.obj N))).hom ≫
            (cechToDerivedGlobalSections R' φ' D' hD').app (P.obj N)) := by
  let I := InjectiveResolution.of N
  let I' := InjectiveResolution.of (P.obj N)
  obtain ⟨τ, hτ, hτ0⟩ := exists_lift_resolution P I I'
  have hJ : ∀ n : ℤ, (baseGlobalSections R φ).rightAcyclic
      (((HomotopyCategory.Plus.quotient _).obj I.plusObj).obj.as.X n) := fun n ↦
    Functor.rightAcyclic_of_injective _ (I.cochainComplex.X n)
  have hJ' : ∀ n : ℤ, (baseGlobalSections R' φ').rightAcyclic
      (((HomotopyCategory.Plus.quotient _).obj I'.plusObj).obj.as.X n) := fun n ↦
    Functor.rightAcyclic_of_injective _ (I'.cochainComplex.X n)
  rw [cechToDerivedGlobalSections_app R φ D hD N I,
    cechToDerivedGlobalSections_app R' φ' D' hD' (P.obj N) I',
    Functor.derivedSquareMap_eq_of_resolutions α (resolutionHom I) (isIso_Qh_map_resolutionHom I)
      hJ (resolutionHom I') (isIso_Qh_map_resolutionHom I') hJ' _ hτ,
    rightDerivedFunctorPlusObjSingleIsoOfResolution_inv _ I' hJ']
  -- the facts
  let r := ModuleCat.restrictScalars.{max u v w} ρ
  let TP : totalPlus R φ D I ⟶ r.mapCochainComplexPlus.obj (totalPlus R' φ' D' I') :=
    ObjectProperty.homMk (totalCechMap R φ D R' φ' D' P ρ c τ)
  have f1 := (rightDerivedFunctorPlusObjSingleIsoOfResolution_inv _ I hJ).symm ▸
    (Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution (baseGlobalSections R φ)
      (resolutionHom I) (isIso_Qh_map_resolutionHom I) hJ).inv_hom_id
  have f3 := cechZigzag_eq_Qh R φ D hD I
  have f4 := cechZigzag_eq_Qh R' φ' D' hD' I'
  have f5 : DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (totalAugmentationPlus R φ D hD I)) ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map TP) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app
          ((HomotopyCategory.Plus.quotient _).obj I.plusObj) ≫
        r.mapHomotopyCategoryPlus.map ((baseGlobalSections R' φ').mapHomotopyCategoryPlus.map
          (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map τ) :
            P.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient _).obj I.plusObj) ⟶
              (HomotopyCategory.Plus.quotient _).obj I'.plusObj))) ≫
      DerivedCategory.Plus.Qh.map (r.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient _).map (totalAugmentationPlus R' φ' D' hD' I'))) := by
    refine Qh_map_comp_eq_of_hom_eq _ _ _ _ ?_
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map
        (totalAugmentation_comp_totalCechMap R φ D R' φ' D' P ρ α c hD hD' hc τ)).trans
        (((HomotopyCategory.quotient _ _).map_comp _ _).trans (congrArg (· ≫ _)
          ((HomotopyCategory.quotient _ _).map_comp _ _))))
  have f6 : DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (cechToTotalPlus R φ D I)) ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map TP) =
      DerivedCategory.Plus.Qh.map (cechMapPlus R φ D R' φ' D' P ρ c N) ≫
      DerivedCategory.Plus.Qh.map (r.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient _).map (cechToTotalPlus R' φ' D' I'))) := by
    refine Qh_map_comp_eq_of_hom_eq _ _ _ _ ?_
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map
        (cechToTotal_comp_totalCechMap R φ D R' φ' D' P ρ c I I' τ hτ0)).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _))
  have f7 := r.mapDerivedCategoryPlusFactorsh.inv.naturality
    ((HomotopyCategory.Plus.quotient _).map (cechToTotalPlus R' φ' D' I'))
  have f8 := r.mapDerivedCategoryPlusFactorsh.inv.naturality
    ((HomotopyCategory.Plus.quotient _).map (totalAugmentationPlus R' φ' D' hD' I'))
  have := isIso_Q_map_totalAugmentationPlus R φ D hD I
  have := isIso_Q_map_totalAugmentationPlus R' φ' D' hD' I'
  dsimp only [cechComparison]
  exact derivedSquare_bookkeeping r.mapDerivedCategoryPlus _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (isIso_Qh_map_quotient_map (totalAugmentationPlus R φ D hD I)
      (quasiIso_totalAugmentation R φ D hD I.cochainComplex)) _ _ _ _ _ _
    (isIso_Qh_map_quotient_map (totalAugmentationPlus R' φ' D' hD' I')
      (quasiIso_totalAugmentation R' φ' D' hD' I'.cochainComplex)) f1 f3
    ((congrArg (fun x ↦ (DerivedCategory.Plus.qhQIso
      ((cechPlusFunctor R' φ' D').obj (P.obj N))).hom ≫ x) f4).trans
      (Iso.hom_inv_id_assoc _ _)) f5 f6 f7 f8

end Square

end Stacks.CechSite.FinalCover

end
