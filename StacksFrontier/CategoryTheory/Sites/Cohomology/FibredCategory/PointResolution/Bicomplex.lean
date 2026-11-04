module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# The double complex of a complex of presheaves on a fibrewise point resolution

For a complex `K^•` of abelian presheaves on the total category, evaluating each term on the
cosimplicial objects `A_{•,V}` gives the double complex of presheaves on the base
`Z^{p,q} = (V ↦ K^p(A_{-q,V}))`. This file sets up that double complex, its augmentation to
`V ↦ H_0(K^•(A_{•,V}))`, and its two filtrations (Stacks 0133): the columns compare `Tot(Z)` with
`H_0(K^•(A_{•,•}))` when each `K^p(A_{•,V})` has no positive homology, and the rows make `Tot(Z)`
invariant under quasi-isomorphisms of bounded above complexes, evaluation being exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open StacksDraft.TotalComplexQuasiIso

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  (A : s.base.C ⥤ CosimplicialObject s.C)

/-- The complex of presheaves `V ↦ G(A_{•,V})` read as a cochain complex over `ℤ`, the simplicial
degree `n` sitting in cohomological degree `-n`. -/
abbrev pointMooreCochain : (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ⥤
    CochainComplex (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℤ :=
  pointMooreComplex s A ⋙ (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _

variable (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})

/-- The extended complex `G(A_{•,•})` vanishes in positive degrees. -/
lemma isZero_pointMooreCochain_X (q : ℤ) (hq : 0 < q) :
    IsZero (((pointMooreCochain s A).obj G).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The degree-zero term of the extended complex is `V ↦ G(A_{0,V})`. -/
def pointMooreCochainXZeroIso :
    ((pointMooreCochain s A).obj G).X 0 ≅ ((pointMooreComplex s A).obj G).X 0 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- The degree `-1` term of the extended complex is `V ↦ G(A_{1,V})`. -/
def pointMooreCochainXNegOneIso :
    ((pointMooreCochain s A).obj G).X (-1) ≅ ((pointMooreComplex s A).obj G).X 1 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (by simp)

/-- The differential `d^{-1,0}` of the extended complex is the degree-one differential of
`V ↦ G(A_{•,V})`, read through `pointMooreCochainXNegOneIso` and `pointMooreCochainXZeroIso`. -/
lemma pointMooreCochain_d_neg_one_zero :
    ((pointMooreCochain s A).obj G).d (-1) 0 =
      (pointMooreCochainXNegOneIso s A G).hom ≫
        ((pointMooreComplex s A).obj G).d 1 0 ≫ (pointMooreCochainXZeroIso s A G).inv :=
  HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)

/-- The extended complex `G(A_{•,•})` has no cohomology in positive degrees. -/
lemma isZero_pointMooreCochain_homology_pos (q : ℤ) (hq : 0 < q) :
    IsZero (((pointMooreCochain s A).obj G).homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.extend_exactAt _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The extended complex `G(A_{•,•})` has no cohomology in negative degrees when
`V ↦ G(A_{•,V})` has no homology in positive degrees. -/
lemma isZero_pointMooreCochain_homology_neg
    (hzero : ∀ n : ℕ, IsZero (((pointMooreComplex s A).obj G).homology (n + 1)))
    (q : ℤ) (hq : q < 0) :
    IsZero (((pointMooreCochain s A).obj G).homology q) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f (n + 1) = q :=
    ⟨(-q - 1).toNat, by simp; omega⟩
  exact ((HomologicalComplex.extendHomologyIso _
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn).isZero_iff).2 (hzero n)

/-! ### The augmentation to the degree-zero cokernel -/

/-- The degree-zero component of the augmentation. -/
def pointMooreCochainAug₀ :
    ((pointMooreCochain s A).obj G).X 0 ⟶ (pointZero s A).obj G :=
  (pointMooreCochainXZeroIso s A G).hom ≫ ((pointMooreComplex s A).obj G).pOpcycles 0

/-- The degree-zero component of the augmentation kills the differential into degree zero. -/
lemma pointMooreCochainAug₀_comp (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    ((pointMooreCochain s A).obj G).d i 0 ≫ pointMooreCochainAug₀ s A G = 0 := by
  simp only [ComplexShape.up_Rel] at hi
  obtain rfl : i = -1 := by omega
  rw [pointMooreCochainAug₀, pointMooreCochain_d_neg_one_zero, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, HomologicalComplex.d_pOpcycles, comp_zero]

variable {G} in
/-- The augmentation `G(A_{•,•}) ⟶ H_0(G(A_{•,•}))[0]` commutes with the maps induced by
`η : G ⟶ G'`. -/
lemma pointMooreCochainAugmentation_naturality {G' : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (η : G ⟶ G') :
    (pointMooreCochain s A).map η ≫
        HomologicalComplex.mkHomToSingle (pointMooreCochainAug₀ s A G')
          (pointMooreCochainAug₀_comp s A G') =
      HomologicalComplex.mkHomToSingle (pointMooreCochainAug₀ s A G)
          (pointMooreCochainAug₀_comp s A G) ≫
        (pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map η := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  by_cases hq : q = 0
  · subst hq
    have hmap : ((pointMooreCochain s A).map η).f 0 =
        (pointMooreCochainXZeroIso s A G).hom ≫
          ((pointMooreComplex s A).map η).f 0 ≫ (pointMooreCochainXZeroIso s A G').inv :=
      HomologicalComplex.extendMap_f _ _ (by simp)
    have hsingle : ((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map η).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((pointZero s A).obj G)).hom ≫
          (pointZero s A).map η ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              ((pointZero s A).obj G')).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f, hsingle, hmap,
      pointMooreCochainAug₀, Category.assoc, Iso.inv_hom_id_assoc,
      ← HomologicalComplex.p_opcyclesMap_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq).eq_of_tgt _ _

/-- **The augmentation `G(A_{•,•}) ⟶ H_0(G(A_{•,•}))[0]`**, natural in the presheaf `G`. -/
def pointMooreCochainAugmentation :
    pointMooreCochain s A ⟶ pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0 where
  app G := HomologicalComplex.mkHomToSingle (pointMooreCochainAug₀ s A G)
    (pointMooreCochainAug₀_comp s A G)
  naturality _ _ η := pointMooreCochainAugmentation_naturality s A η

/-- The degree-zero component of the augmentation is `pointMooreCochainAug₀` followed by the
identification of the degree-zero term of the single complex. -/
lemma pointMooreCochainAugmentation_f_zero :
    ((pointMooreCochainAugmentation s A).app G).f 0 =
      pointMooreCochainAug₀ s A G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((pointZero s A).obj G)).inv :=
  HomologicalComplex.mkHomToSingle_f _ (pointMooreCochainAug₀_comp s A G)

/-- The degree-zero component of the augmentation is a cokernel of the differential `d^{-1,0}`. -/
def pointMooreCochainAug₀IsColimit :
    IsColimit (CokernelCofork.ofπ (pointMooreCochainAug₀ s A G)
      (pointMooreCochainAug₀_comp s A G (-1) (by simp))) :=
  Stacks.ChaoticSite.GeneralValued.isColimit_cokernelCofork_comp
    (pointMooreCochainXNegOneIso s A G).hom (pointMooreCochainXZeroIso s A G).symm
    (((pointMooreComplex s A).obj G).d_pOpcycles 1 0)
    (((pointMooreComplex s A).obj G).opcyclesIsCokernel 1 0 (by simp))
    (pointMooreCochain_d_neg_one_zero s A G) _

/-- **The augmentation is a quasi-isomorphism in degree zero.** -/
lemma quasiIsoAt_pointMooreCochainAugmentation_zero :
    QuasiIsoAt ((pointMooreCochainAugmentation s A).app G) 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hdK : ((pointMooreCochain s A).obj G).d 0 1 = 0 :=
    (isZero_pointMooreCochain_X s A G 1 (by omega)).eq_of_tgt _ _
  have hdL : ((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).d 0 1 =
      0 := HomologicalComplex.single_obj_d _ _ _ _ _
  have hdL' : ((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).d (-1)
      0 = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  have hLp : IsIso (((pointZero s A ⋙ HomologicalComplex.single _
      (ComplexShape.up ℤ) 0).obj G).pOpcycles 0) :=
    HomologicalComplex.isIso_pOpcycles _ (-1) 0 (by simp) hdL'
  have hg : ((pointMooreCochainAugmentation s A).app G).f 0 ≫
        ((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).pOpcycles 0 =
      pointMooreCochainAug₀ s A G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((pointZero s A).obj G)).inv ≫
          ((pointZero s A ⋙ HomologicalComplex.single _
            (ComplexShape.up ℤ) 0).obj G).pOpcycles 0 := by
    rw [pointMooreCochainAugmentation_f_zero, Category.assoc]
  have hop : IsIso (HomologicalComplex.opcyclesMap ((pointMooreCochainAugmentation s A).app G) 0) :=
    Stacks.ChaoticSite.GeneralValued.isIso_of_isColimit_cokernelCofork
      (((pointMooreCochain s A).obj G).d_pOpcycles (-1) 0)
      (((pointMooreCochain s A).obj G).opcyclesIsCokernel (-1) 0 (by simp))
      (g := pointMooreCochainAug₀ s A G ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((pointZero s A).obj G)).inv ≫
          ((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).pOpcycles 0)
      (by rw [← Category.assoc, pointMooreCochainAug₀_comp s A G (-1) (by simp), zero_comp])
      (Stacks.ChaoticSite.GeneralValued.isColimit_cokernelCofork_comp_iso _
        (pointMooreCochainAug₀IsColimit s A G)
        (asIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((pointZero s A).obj G)).inv ≫
          ((pointZero s A ⋙ HomologicalComplex.single _
            (ComplexShape.up ℤ) 0).obj G).pOpcycles 0)) _)
      _ ((HomologicalComplex.p_opcyclesMap _ 0).trans hg)
  have hι1 : IsIso (((pointMooreCochain s A).obj G).homologyι 0) :=
    HomologicalComplex.isIso_homologyι _ 0 1 (by simp) hdK
  have hι2 : IsIso (((pointZero s A ⋙ HomologicalComplex.single _
      (ComplexShape.up ℤ) 0).obj G).homologyι 0) :=
    HomologicalComplex.isIso_homologyι _ 0 1 (by simp) hdL
  have hcomp : IsIso (HomologicalComplex.homologyMap ((pointMooreCochainAugmentation s A).app G) 0 ≫
        ((pointZero s A ⋙ HomologicalComplex.single _
          (ComplexShape.up ℤ) 0).obj G).homologyι 0) := by
    rw [HomologicalComplex.homologyι_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((pointZero s A ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).homologyι 0)

/-- **The extended complex `G(A_{•,•})` is a resolution of `H_0(G(A_{•,•}))`** as soon as its
positive homology vanishes. -/
lemma quasiIso_pointMooreCochainAugmentation
    (hzero : ∀ n : ℕ, IsZero (((pointMooreComplex s A).obj G).homology (n + 1))) :
    QuasiIso ((pointMooreCochainAugmentation s A).app G) := by
  rw [quasiIso_iff]
  intro q
  rcases lt_trichotomy q 0 with hq | hq | hq
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso (isZero_pointMooreCochain_homology_neg s A G hzero q hq)
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ q (by omega)) _
  · subst hq
    exact quasiIsoAt_pointMooreCochainAugmentation_zero s A G
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso (isZero_pointMooreCochain_homology_pos s A G q hq)
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ q (by omega)) _

/-! ### The double complex -/

/-- **The double complex of a complex of presheaves on the total category**:
`Z^{p,q} = (V ↦ K^p(A_{-q,V}))`, as a functor of the complex. -/
abbrev pointBicomplexFunctor :
    CochainComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℤ ⥤
      HomologicalComplex₂ (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (pointMooreCochain s A).mapHomologicalComplex (ComplexShape.up ℤ)

variable (P : CochainComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℤ)

/-- The double complex of `P`. -/
abbrev pointBicomplex :
    HomologicalComplex₂ (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (pointBicomplexFunctor s A).obj P

/-- The double complex `Z^{p,q}` vanishes for `q > 0`. -/
lemma isZero_pointBicomplex_X_X (p q : ℤ) (hq : 0 < q) :
    IsZero (((pointBicomplex s A P).X p).X q) :=
  isZero_pointMooreCochain_X s A (P.X p) q hq

/-- The column `Z^{p,•}` vanishes when `P^p` does. -/
lemma isZero_pointBicomplex_X (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((pointBicomplex s A P).X p) :=
  Functor.map_isZero (pointMooreCochain s A) hp

/-- The terms `Z^{p,q}` of the double complex of a complex concentrated in degrees `≤ 0` vanish
outside the quadrant `p ≤ 0`, `q ≤ 0`. -/
private lemma isZero_pointBicomplex_X_X_of_or [P.IsStrictlyLE 0] (p q : ℤ)
    (hpq : 0 < p ∨ 0 < q) : IsZero (((pointBicomplex s A P).X p).X q) := by
  rcases hpq with hp | hq
  · exact Functor.map_isZero (HomologicalComplex.eval _ (ComplexShape.up ℤ) q)
      (isZero_pointBicomplex_X s A P p (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
  · exact isZero_pointBicomplex_X_X s A P p q hq

/-- The double complex of a complex concentrated in degrees `≤ 0` has a total complex. -/
instance hasTotal_pointBicomplex [P.IsStrictlyLE 0] :
    (pointBicomplex s A P).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_pointBicomplex_X s A P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_pointBicomplex_X_X s A P p q hq)

/-- Evaluating the extended complex in a fixed degree is exact in the presheaf: in degree `-n` it
is restriction along `V ↦ A_{n,V}`. -/
instance preservesHomology_pointMooreCochain_comp_eval (q : ℤ) :
    (pointMooreCochain s A ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) q).PreservesHomology := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    have e : pointMooreCochain s A ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) q ≅
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max w uD vD uC vC}).obj
          ((pointEvaluationShape s A).obj (op ⦋n⦌)) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pointMooreComplex s A)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso _ hn) ≪≫
        NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)
    have := preservesFiniteLimits_of_natIso e.symm
    have := preservesFiniteColimits_of_natIso e.symm
    infer_instance
  · exact Functor.preservesHomology_of_map_exact _ fun S _ =>
      ShortComplex.exact_of_isZero_X₂ _ (isZero_pointMooreCochain_X s A S.X₂ q hq)

/-- **The columnwise augmentation of the double complex**, `Z ⟶ H_0(P^•(A_{•,•}))[0]`. -/
abbrev pointBicomplexColumnMap :
    pointBicomplex s A P ⟶
      singleRowZero (((pointZero s A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (pointMooreCochainAugmentation s A) (ComplexShape.up ℤ)).app P

/-- The single-row double complex `H_0(P^•(A_{•,•}))` of a complex concentrated in degrees `≤ 0`
has a total complex. -/
instance hasTotal_singleRowZero_pointZero [P.IsStrictlyLE 0] :
    (singleRowZero (((pointZero s A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => Functor.map_isZero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
      (Functor.map_isZero (pointZero s A) (CochainComplex.isZero_of_isStrictlyLE P 0 p hp)))
    (fun p q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega))

/-- If the augmentation is a quasi-isomorphism on every column, then it induces a
quasi-isomorphism `Tot(Z) ⟶ H_0(P^•(A_{•,•}))`. -/
lemma quasiIso_pointBicomplexColumnTotalMap [P.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((pointMooreCochainAugmentation s A).app (P.X p))) :
    QuasiIso (HomologicalComplex₂.total.map (pointBicomplexColumnMap s A P)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_upperBound (pointBicomplexColumnMap s A P) 0 0
    (fun p hp => isZero_pointBicomplex_X s A P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_pointBicomplex_X_X s A P p q hq)
    (fun p hp => Functor.map_isZero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
        (Functor.map_isZero (pointZero s A) (CochainComplex.isZero_of_isStrictlyLE P 0 p hp)))
    (fun p q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega))
    haug

/-- A quasi-isomorphism of complexes concentrated in degrees `≤ 0` induces a quasi-isomorphism of
the total complexes of their double complexes. -/
lemma quasiIso_pointBicomplexTotalMap
    {K L : CochainComplex (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex₂.total.map ((pointBicomplexFunctor s A).map f)
      (ComplexShape.up ℤ)) := by
  refine quasiIso_total_map_of_upperBound_flip ((pointBicomplexFunctor s A).map f) 0 0
    (fun p q hpq => isZero_pointBicomplex_X_X_of_or s A K p q hpq)
    (fun p q hpq => isZero_pointBicomplex_X_X_of_or s A L p q hpq) (fun q => ?_)
  · exact HomologicalComplex.quasiIso_map_of_preservesHomology f
      (pointMooreCochain s A ⋙ HomologicalComplex.eval _ (ComplexShape.up ℤ) q)

end Stacks.Sites.FibredCategory.FibredCategorySituation
