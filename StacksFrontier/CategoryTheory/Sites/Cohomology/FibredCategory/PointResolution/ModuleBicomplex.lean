module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Bicomplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBasic

/-!
# The double complex of a complex of presheaves of modules on a fibrewise point resolution

This is `StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Bicomplex` at
module coefficients. For a complex `K^•` of presheaves of `p⁻¹O`-modules on the total category,
evaluating each term on the cosimplicial objects `A_{•,V}` gives the double complex of presheaves
of `O`-modules on the base `Z^{p,q} = (V ↦ K^p(A_{-q,V}))`. This file sets up that double complex,
its augmentation to `V ↦ H_0(K^•(A_{•,V}))`, and its two filtrations (Stacks 0133): the columns
compare `Tot(Z)` with `H_0(K^•(A_{•,•}))` when each `K^p(A_{•,V})` has no positive homology, and
the rows make `Tot(Z)` invariant under quasi-isomorphisms of bounded above complexes, evaluation
being exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open StacksDraft.TotalComplexQuasiIso

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (O : s.base.Cᵒᵖ ⥤ RingCat.{max w uD vD uC vC})

/-- The complex of presheaves `V ↦ G(A_{•,V})` read as a cochain complex over `ℤ`, the simplicial
degree `n` sitting in cohomological degree `-n`. -/
abbrev modulePointMooreCochain : (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) ⥤
    CochainComplex (PresheafOfModules.{max w uD vD uC vC} O) ℤ :=
  modulePointMooreComplex s hA O ⋙ (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _

variable (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O))

/-- The extended complex vanishes in positive degrees. -/
lemma isZero_modulePointMooreCochain_X (q : ℤ) (hq : 0 < q) :
    IsZero (((modulePointMooreCochain s hA O).obj G).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The degree-zero term of the extended complex is `V ↦ G(A_{0,V})`. -/
def modulePointMooreCochainXZeroIso :
    ((modulePointMooreCochain s hA O).obj G).X 0 ≅ ((modulePointMooreComplex s hA O).obj G).X 0 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- The degree `-1` term of the extended complex is `V ↦ G(A_{1,V})`. -/
def modulePointMooreCochainXNegOneIso :
    ((modulePointMooreCochain s hA O).obj G).X (-1) ≅
      ((modulePointMooreComplex s hA O).obj G).X 1 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (by simp)

/-- The differential `d^{-1,0}` of the extended complex is the degree-one differential of the
Moore complex. -/
lemma modulePointMooreCochain_d_neg_one_zero :
    ((modulePointMooreCochain s hA O).obj G).d (-1) 0 =
      (modulePointMooreCochainXNegOneIso s hA O G).hom ≫
        ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫
          (modulePointMooreCochainXZeroIso s hA O G).inv :=
  HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)

/-- The extended complex has no homology in positive degrees. -/
lemma isZero_modulePointMooreCochain_homology_pos (q : ℤ) (hq : 0 < q) :
    IsZero (((modulePointMooreCochain s hA O).obj G).homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.extend_exactAt _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The extended complex has no homology in negative degrees as soon as the Moore complex has none
in positive degrees. -/
lemma isZero_modulePointMooreCochain_homology_neg
    (hzero : ∀ n : ℕ, IsZero (((modulePointMooreComplex s hA O).obj G).homology (n + 1)))
    (q : ℤ) (hq : q < 0) :
    IsZero (((modulePointMooreCochain s hA O).obj G).homology q) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f (n + 1) = q :=
    ⟨(-q - 1).toNat, by simp; omega⟩
  exact ((HomologicalComplex.extendHomologyIso _
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn).isZero_iff).2 (hzero n)

/-! ### The augmentation to the degree-zero cokernel -/

/-- The degree-zero component of the augmentation. -/
def modulePointMooreCochainAug₀ :
    ((modulePointMooreCochain s hA O).obj G).X 0 ⟶ (modulePointZero s hA O).obj G :=
  (modulePointMooreCochainXZeroIso s hA O G).hom ≫
    ((modulePointMooreComplex s hA O).obj G).pOpcycles 0

/-- The degree-zero component of the augmentation kills the differential into degree zero. -/
lemma modulePointMooreCochainAug₀_comp (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    ((modulePointMooreCochain s hA O).obj G).d i 0 ≫ modulePointMooreCochainAug₀ s hA O G = 0 := by
  simp only [ComplexShape.up_Rel] at hi
  obtain rfl : i = -1 := by omega
  rw [modulePointMooreCochainAug₀, modulePointMooreCochain_d_neg_one_zero, Category.assoc,
    Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.d_pOpcycles, comp_zero]

variable {G} in
/-- The augmentation is natural in the presheaf of modules. -/
lemma modulePointMooreCochainAugmentation_naturality
    {G' : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    (η : G ⟶ G') :
    (modulePointMooreCochain s hA O).map η ≫
        HomologicalComplex.mkHomToSingle (modulePointMooreCochainAug₀ s hA O G')
          (modulePointMooreCochainAug₀_comp s hA O G') =
      HomologicalComplex.mkHomToSingle (modulePointMooreCochainAug₀ s hA O G)
          (modulePointMooreCochainAug₀_comp s hA O G) ≫
        (modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map η := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  by_cases hq : q = 0
  · subst hq
    have hmap : ((modulePointMooreCochain s hA O).map η).f 0 =
        (modulePointMooreCochainXZeroIso s hA O G).hom ≫
          ((modulePointMooreComplex s hA O).map η).f 0 ≫
            (modulePointMooreCochainXZeroIso s hA O G').inv :=
      HomologicalComplex.extendMap_f _ _ (by simp)
    have hsingle :
        ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map η).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((modulePointZero s hA O).obj G)).hom ≫
          (modulePointZero s hA O).map η ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              ((modulePointZero s hA O).obj G')).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomToSingle_f,
      hsingle, hmap, modulePointMooreCochainAug₀, modulePointMooreCochainAug₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← HomologicalComplex.p_opcyclesMap_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq).eq_of_tgt _ _

/-- **The augmentation `G(A_{•,•}) ⟶ H_0(G(A_{•,•}))[0]`**, natural in the presheaf `G`. -/
def modulePointMooreCochainAugmentation :
    modulePointMooreCochain s hA O ⟶
      modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0 where
  app G := HomologicalComplex.mkHomToSingle (modulePointMooreCochainAug₀ s hA O G)
    (modulePointMooreCochainAug₀_comp s hA O G)
  naturality _ _ η := modulePointMooreCochainAugmentation_naturality s hA O η

/-- The degree-zero component of the augmentation. -/
lemma modulePointMooreCochainAugmentation_f_zero :
    ((modulePointMooreCochainAugmentation s hA O).app G).f 0 =
      modulePointMooreCochainAug₀ s hA O G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((modulePointZero s hA O).obj G)).inv :=
  HomologicalComplex.mkHomToSingle_f _ (modulePointMooreCochainAug₀_comp s hA O G)

/-- The degree-zero component of the augmentation is a cokernel of the differential `d^{-1,0}`. -/
def modulePointMooreCochainAug₀IsColimit :
    IsColimit (CokernelCofork.ofπ (modulePointMooreCochainAug₀ s hA O G)
      (modulePointMooreCochainAug₀_comp s hA O G (-1) (by simp))) :=
  Stacks.ChaoticSite.GeneralValued.isColimit_cokernelCofork_comp
    (modulePointMooreCochainXNegOneIso s hA O G).hom (modulePointMooreCochainXZeroIso s hA O G).symm
    (((modulePointMooreComplex s hA O).obj G).d_pOpcycles 1 0)
    (((modulePointMooreComplex s hA O).obj G).opcyclesIsCokernel 1 0 (by simp))
    (modulePointMooreCochain_d_neg_one_zero s hA O G) _

/-- **The augmentation is a quasi-isomorphism in degree zero.** -/
lemma quasiIsoAt_modulePointMooreCochainAugmentation_zero :
    QuasiIsoAt ((modulePointMooreCochainAugmentation s hA O).app G) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hdK : ((modulePointMooreCochain s hA O).obj G).d 0 1 = 0 :=
    (isZero_modulePointMooreCochain_X s hA O G 1 (by omega)).eq_of_tgt _ _
  have hdL :
      ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).d 0 1 =
      0 := HomologicalComplex.single_obj_d _ _ _ _ _
  have hdL' :
      ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).d (-1)
      0 = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  have hLp : IsIso (((modulePointZero s hA O ⋙ HomologicalComplex.single _
      (ComplexShape.up ℤ) 0).obj G).pOpcycles 0) :=
    HomologicalComplex.isIso_pOpcycles _ (-1) 0 (by simp) hdL'
  have hg : ((modulePointMooreCochainAugmentation s hA O).app G).f 0 ≫
        ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          G).pOpcycles 0 =
      modulePointMooreCochainAug₀ s hA O G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((modulePointZero s hA O).obj G)).inv ≫
          ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            G).pOpcycles 0 := by
    rw [modulePointMooreCochainAugmentation_f_zero, Category.assoc]
  have hop :
      IsIso (HomologicalComplex.opcyclesMap
        ((modulePointMooreCochainAugmentation s hA O).app G) 0) :=
    Stacks.ChaoticSite.GeneralValued.isIso_of_isColimit_cokernelCofork
      (((modulePointMooreCochain s hA O).obj G).d_pOpcycles (-1) 0)
      (((modulePointMooreCochain s hA O).obj G).opcyclesIsCokernel (-1) 0 (by simp))
      (g := modulePointMooreCochainAug₀ s hA O G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((modulePointZero s hA O).obj G)).inv ≫
          ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            G).pOpcycles 0)
      (by rw [← Category.assoc, modulePointMooreCochainAug₀_comp s hA O G (-1) (by simp),
        zero_comp])
      (Stacks.ChaoticSite.GeneralValued.isColimit_cokernelCofork_comp_iso _
        (modulePointMooreCochainAug₀IsColimit s hA O G)
        (asIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((modulePointZero s hA O).obj G)).inv ≫
          ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            G).pOpcycles 0)) _)
      _ ((HomologicalComplex.p_opcyclesMap _ 0).trans hg)
  have hι1 : IsIso (((modulePointMooreCochain s hA O).obj G).homologyι 0) :=
    HomologicalComplex.isIso_homologyι _ 0 1 (by simp) hdK
  have hι2 : IsIso (((modulePointZero s hA O ⋙ HomologicalComplex.single _
      (ComplexShape.up ℤ) 0).obj G).homologyι 0) :=
    HomologicalComplex.isIso_homologyι _ 0 1 (by simp) hdL
  have hcomp :
      IsIso (HomologicalComplex.homologyMap ((modulePointMooreCochainAugmentation s hA O).app G) 0 ≫
        ((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          G).homologyι 0) := by
    rw [HomologicalComplex.homologyι_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((modulePointZero s hA O ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      G).homologyι 0)

/-- **The extended complex `G(A_{•,•})` is a resolution of `H_0(G(A_{•,•}))`** as soon as its
positive homology vanishes. -/
lemma quasiIso_modulePointMooreCochainAugmentation
    (hzero : ∀ n : ℕ, IsZero (((modulePointMooreComplex s hA O).obj G).homology (n + 1))) :
    QuasiIso ((modulePointMooreCochainAugmentation s hA O).app G) := by
  rw [quasiIso_iff]
  intro q
  rcases lt_trichotomy q 0 with hq | hq | hq
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso (isZero_modulePointMooreCochain_homology_neg s hA O G hzero q hq)
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ q (by omega)) _
  · subst hq
    exact quasiIsoAt_modulePointMooreCochainAugmentation_zero s hA O G
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso (isZero_modulePointMooreCochain_homology_pos s hA O G q hq)
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ q (by omega)) _

/-! ### The double complex -/

/-- **The double complex of a complex of presheaves on the total category**:
`Z^{p,q} = (V ↦ K^p(A_{-q,V}))`, as a functor of the complex. -/
abbrev modulePointBicomplexFunctor :
    CochainComplex (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) ℤ ⥤
      HomologicalComplex₂ (PresheafOfModules.{max w uD vD uC vC} O)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (modulePointMooreCochain s hA O).mapHomologicalComplex (ComplexShape.up ℤ)

variable (P : CochainComplex (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) ℤ)

/-- The double complex of `P`. -/
abbrev modulePointBicomplex :
    HomologicalComplex₂ (PresheafOfModules.{max w uD vD uC vC} O)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (modulePointBicomplexFunctor s hA O).obj P

/-- The double complex vanishes in positive vertical degrees. -/
lemma isZero_modulePointBicomplex_X_X (p q : ℤ) (hq : 0 < q) :
    IsZero (((modulePointBicomplex s hA O P).X p).X q) :=
  isZero_modulePointMooreCochain_X s hA O (P.X p) q hq

/-- The double complex vanishes in the columns where the complex does. -/
lemma isZero_modulePointBicomplex_X (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((modulePointBicomplex s hA O P).X p) :=
  Functor.map_isZero (modulePointMooreCochain s hA O) hp

/-- The double complex of a complex concentrated in degrees `≤ 0` vanishes in positive columns. -/
private lemma isZero_modulePointBicomplex_X_of_pos [P.IsStrictlyLE 0] (p : ℤ) (hp : 0 < p) :
    IsZero ((modulePointBicomplex s hA O P).X p) :=
  isZero_modulePointBicomplex_X s hA O P p (CochainComplex.isZero_of_isStrictlyLE P 0 p hp)

/-- The double complex of a complex concentrated in degrees `≤ 0` vanishes outside the quadrant. -/
private lemma isZero_modulePointBicomplex_X_X_of_pos_or_pos [P.IsStrictlyLE 0] (p q : ℤ)
    (hpq : 0 < p ∨ 0 < q) : IsZero (((modulePointBicomplex s hA O P).X p).X q) := by
  rcases hpq with hp | hq
  · exact Functor.map_isZero (HomologicalComplex.eval _ (ComplexShape.up ℤ) q)
      (isZero_modulePointBicomplex_X_of_pos s hA O P p hp)
  · exact isZero_modulePointBicomplex_X_X s hA O P p q hq

/-- The double complex of a bounded above complex has a total complex. -/
instance hasTotal_modulePointBicomplex [P.IsStrictlyLE 0] :
    (modulePointBicomplex s hA O P).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_modulePointBicomplex_X s hA O P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_modulePointBicomplex_X_X s hA O P p q hq)

/-- The presheaf of `O`-modules `V ↦ G(A_{n,V})` is exact in `G`. -/
instance preservesHomology_modulePointLevel (n : SimplexCategory) :
    (modulePointLevel s hA O n).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  refine (PresheafOfModules.toPresheaf O).reflects_exact_of_faithful _ ?_
  exact (hS.map (PresheafOfModules.toPresheaf (s.p.op ⋙ O))).map
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{max w uD vD uC vC}).obj (pointLevel s A n).op)

/-- Evaluating the extended complex in a fixed degree is exact in the presheaf of modules. -/
instance preservesHomology_modulePointMooreCochain_comp_eval (q : ℤ) :
    (modulePointMooreCochain s hA O ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) q).PreservesHomology := by
  refine Functor.preservesHomology_of_map_exact _ fun S hS => ?_
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    have e : modulePointMooreCochain s hA O ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) q ≅
        modulePointLevel s hA O ⦋n⦌ :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (modulePointMooreComplex s hA O)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso _ hn) ≪≫
        NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)
    exact (ShortComplex.exact_iff_of_iso (S.mapNatIso e.symm)).1 (hS.map _)
  · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_modulePointMooreCochain_X s hA O S.X₂ q hq)

/-- **The columnwise augmentation of the double complex**, `Z ⟶ H_0(P^•(A_{•,•}))[0]`. -/
abbrev modulePointBicomplexColumnMap :
    modulePointBicomplex s hA O P ⟶
      singleRowZero (((modulePointZero s hA O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (modulePointMooreCochainAugmentation s hA O)
    (ComplexShape.up ℤ)).app P

/-- The single row of `H_0` of a bounded above complex vanishes in positive columns. -/
private lemma isZero_singleRowZero_modulePointZero_X [P.IsStrictlyLE 0] (p : ℤ) (hp : 0 < p) :
    IsZero ((singleRowZero (((modulePointZero s hA O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)).X p) :=
  Functor.map_isZero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
    (Functor.map_isZero (modulePointZero s hA O) (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))

/-- The single-row double complex of `H_0` of a complex vanishes in positive rows. -/
private lemma isZero_singleRowZero_modulePointZero_X_X (p q : ℤ) (hq : 0 < q) :
    IsZero (((singleRowZero (((modulePointZero s hA O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)).X p).X q) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega)

/-- The single-row double complex of `H_0` of a bounded above complex has a total complex. -/
instance hasTotal_singleRowZero_modulePointZero [P.IsStrictlyLE 0] :
    (singleRowZero (((modulePointZero s hA O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => Functor.map_isZero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
      (Functor.map_isZero (modulePointZero s hA O)
        (CochainComplex.isZero_of_isStrictlyLE P 0 p hp)))
    (fun p q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega))

/-- **The first filtration**: a columnwise quasi-isomorphic augmentation gives
`Tot(Z) ≃ H_0(P^•(A_{•,•}))`. -/
lemma quasiIso_modulePointBicomplexColumnTotalMap [P.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((modulePointMooreCochainAugmentation s hA O).app (P.X p))) :
    QuasiIso (HomologicalComplex₂.total.map (modulePointBicomplexColumnMap s hA O P)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_upperBound (modulePointBicomplexColumnMap s hA O P) 0 0
    (isZero_modulePointBicomplex_X_of_pos s hA O P) (isZero_modulePointBicomplex_X_X s hA O P)
    (isZero_singleRowZero_modulePointZero_X s hA O P)
    (isZero_singleRowZero_modulePointZero_X_X s hA O P) haug

/-- **The second filtration**: a quasi-isomorphism of bounded above complexes induces one on the
total complexes of the double complexes. -/
lemma quasiIso_modulePointBicomplexTotalMap
    {K L : CochainComplex (PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex₂.total.map ((modulePointBicomplexFunctor s hA O).map f)
      (ComplexShape.up ℤ)) := by
  refine quasiIso_total_map_of_upperBound_flip ((modulePointBicomplexFunctor s hA O).map f) 0 0
    (fun p q hpq => isZero_modulePointBicomplex_X_X_of_pos_or_pos s hA O K p q hpq)
    (fun p q hpq => isZero_modulePointBicomplex_X_X_of_pos_or_pos s hA O L p q hpq) (fun q => ?_)
  · exact HomologicalComplex.quasiIso_map_of_preservesHomology f
      (modulePointMooreCochain s hA O ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) q)

end Stacks.Sites.FibredCategory.FibredCategorySituation
