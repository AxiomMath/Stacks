module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.DeltaFunctor
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right deriving an everywhere defined functor is for left exact functors

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories and assume that the right
derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined, that is, that for every bounded below
complex `K` the ind-object `(s : K ⟶ L) ↦ F(L)` over the quasi-isomorphisms out of `K` is
essentially constant (`CategoryTheory.Functor.IsRightDerivable`, [Stacks, Tag 05SV]). Writing
`R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`, then `R ⁱ F = 0` for `i < 0`, the functor `R ⁰ F` is left exact, and
the canonical map `F ⟶ R ⁰ F` is an isomorphism if and only if `F` is left exact.

The proof is the source's. The value of `RF` at `A[0]` is a retract of `F(K)` for a
quasi-isomorphism `A[0] ⟶ K`, and the good truncation `K ⟶ τ_{≥ 0}K` is again such an index, so
the value is a retract of a complex concentrated in degrees `≥ 0`; this gives part (1). An
everywhere defined right derived functor is exact
(`CategoryTheory.Functor.isTriangulated_of_isRightDerivable`), so the triangle of a short exact
sequence and the long exact homology sequence give part (2). For part (3), if `F` is left exact
and `s : A[0] ⟶ K` is a quasi-isomorphism with `K` concentrated in degrees `≥ 0`, then
`0 ⟶ A ⟶ K⁰ ⟶ K¹` is exact, hence so is `0 ⟶ F(A) ⟶ F(K⁰) ⟶ F(K¹)`, and `H⁰(F(s))` is an
isomorphism; the essential constancy of the ind-object then shows that `H⁰` of the coprojection
of the value at such an index is both split epi and mono.

## Main results

* `CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_of_isRightDerivable`:
  [Stacks, Tag 05TD].

## References

* [Stacks, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV), everywhere defined `RF`
* [Stacks, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC), the truncation argument
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

open _root_.DerivedCategory

section

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- The quasi-isomorphisms of `K⁺(A)` form a saturated class. -/
private lemma plusQuasiIso_isSaturated :
    (HomotopyCategory.Plus.quasiIso A).IsSaturated := by
  have hleft : (HomotopyCategory.Plus.quasiIso A).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have hright : (HomotopyCategory.Plus.quasiIso A).HasRightCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  refine ⟨hleft, hright, ?_⟩
  intro X Y Z T f g h hfg hgh n
  let H := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n
  have : IsIso (H.map f.hom ≫ H.map g.hom) := by
    rw [← H.map_comp]; exact hfg n
  have : IsIso (H.map g.hom ≫ H.map h.hom) := by
    rw [← H.map_comp]; exact hgh n
  have : Epi (H.map g.hom) := epi_of_epi (H.map f.hom) (H.map g.hom)
  have : Mono (H.map g.hom) := mono_of_mono (H.map g.hom) (H.map h.hom)
  exact isIso_of_mono_of_epi (H.map g.hom)

/-- For a left exact `F` and a morphism `φ : K ⟶ M` of cochain complexes vanishing in degree `-1`,
if `H⁰(φ)` is an isomorphism then so is `H⁰(F(φ))`: in degree `0` the homology of such a complex
is the kernel of its differential, and `F` preserves kernels. -/
private lemma isIso_homologyMap_mapHomologicalComplex_zero (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] {K M : CochainComplex A ℤ} (φ : K ⟶ M)
    (hK : IsZero (K.X (-1))) (hM : IsZero (M.X (-1)))
    (hφ : IsIso (HomologicalComplex.homologyMap φ 0)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
  have hprev : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  have hKf : (K.sc 0).f = 0 := by
    refine IsZero.eq_of_src ?_ _ _
    change IsZero (K.X ((ComplexShape.up ℤ).prev 0))
    rw [hprev]
    exact hK
  have hMf : (M.sc 0).f = 0 := by
    refine IsZero.eq_of_src ?_ _ _
    change IsZero (M.X ((ComplexShape.up ℤ).prev 0))
    rw [hprev]
    exact hM
  have := F.preservesLeftHomology_of_zero_f (K.sc 0) hKf
  have := F.preservesLeftHomology_of_zero_f (M.sc 0) hMf
  let ψ := (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).map φ
  have : IsIso (ShortComplex.homologyMap ψ) := hφ
  have e := ShortComplex.mapHomologyIso_hom_naturality ψ F
  have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map ψ) ≫
      ((M.sc 0).mapHomologyIso F).hom) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right (ShortComplex.homologyMap (F.mapShortComplex.map ψ))
    ((M.sc 0).mapHomologyIso F).hom

variable [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- Every index `s : A[0] ⟶ K` of the ind-object computing `RF(A[0])` maps to an index whose
target is concentrated in degrees `≥ 0`: the good truncation `K ⟶ τ_{≥ 0}K` is a
quasi-isomorphism, `K` having no cohomology in negative degrees. -/
private lemma exists_under_isStrictlyGE (X : A)
    (s : (HomotopyCategory.Plus.quasiIso A).Under ⊤
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) :
    ∃ (t : (HomotopyCategory.Plus.quasiIso A).Under ⊤
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) (_ : s ⟶ t),
      CochainComplex.IsStrictlyGE t.right.obj.as 0 ∧
        ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj t.right).IsGE 0 := by
  let W := HomotopyCategory.Plus.quasiIso A
  have hX : CochainComplex.IsGE
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as 0 :=
    inferInstanceAs (CochainComplex.IsGE
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) 0)
  have hs : CochainComplex.IsGE s.right.obj.as 0 := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hz : IsZero (((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as.homology n) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact (CochainComplex.isGE_iff _ 0).1 hX n hn
    have : IsIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).map
        s.hom.hom) := s.prop n
    exact hz.of_iso
      (((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n).app
          s.right.obj.as).symm ≪≫
        (asIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).map
          s.hom.hom)).symm ≪≫
        (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n).app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as)
  let Y : HomotopyCategory.Plus A :=
    (HomotopyCategory.Plus.quotient A).obj
      ⟨CochainComplex.truncGE s.right.obj.as 0, ⟨0, inferInstance⟩⟩
  let q : s.right ⟶ Y := ObjectProperty.homMk
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (CochainComplex.πTruncGE s.right.obj.as 0))
  have hq : W q :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((CochainComplex.quasiIso_πTruncGE_iff _ 0).2 hs)
  have hY : CochainComplex.IsStrictlyGE Y.obj.as 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (CochainComplex.truncGE s.right.obj.as 0) 0)
  refine ⟨MorphismProperty.Under.mk ⊤ (s.hom ≫ q) (W.comp_mem _ _ s.prop hq),
    MorphismProperty.Under.homMk q rfl, hY, ?_⟩
  exact isGE_Qh_obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.truncGE s.right.obj.as 0)) ⟨0, inferInstance⟩ 0 inferInstance

/-- Part (1) of [Stacks, Tag 05TD] at the level of values: a value of the right derived functor
at `A[0]` is cohomologically `≥ 0`, being a retract of `F(K)` for a complex `K` concentrated in
degrees `≥ 0`. -/
private lemma isGE_pt_of_isRightDerivedValueAt (X : A)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.Plus.quasiIso A) ⊤
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ⋙
      Under.forget ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ⋙
      (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)))
    (hc : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivedValueAt
      (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X) c) :
    c.pt.IsGE 0 := by
  obtain ⟨s₀, r, hr, -⟩ := hc
  obtain ⟨t, u, -, ht⟩ := exists_under_isStrictlyGE F X s₀
  have hw : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u.right ≫ c.ι.app t = c.ι.app s₀ :=
    c.w u
  have hret : (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u.right) ≫ c.ι.app t = 𝟙 c.pt :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hw).trans hr)
  rw [← Plus.isGE_ι_obj_iff]
  exact StacksDraft.RightDerivedMovesRight.isGE_of_retract
    (Plus.ι.map (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u.right))
    (Plus.ι.map (c.ι.app t))
    ((Plus.ι.map_comp _ _).symm.trans ((congrArg Plus.ι.map hret).trans (Plus.ι.map_id _))) 0
    inferInstance

/-- For a left exact `F` and an index `t : A[0] ⟶ K` of the ind-object computing `RF(A[0])` with
`K` concentrated in degrees `≥ 0`, the map `H⁰(F(t)) : F(A) ⟶ H⁰(F(K))` is an isomorphism:
`0 ⟶ A ⟶ K⁰ ⟶ K¹` is exact and `F` is left exact. -/
private lemma isIso_homologyFunctor_map_map_hom [PreservesFiniteLimits F] (X : A)
    (t : (HomotopyCategory.Plus.quasiIso A).Under ⊤
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
    (ht : CochainComplex.IsStrictlyGE t.right.obj.as 0) :
    IsIso ((Plus.homologyFunctor B 0).map
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t.hom)) := by
  let φ := t.hom.hom.out
  have hφ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ = t.hom.hom :=
    HomotopyCategory.quotient_map_out _
  have h₀ : IsIso (HomologicalComplex.homologyMap φ 0) := by
    have : IsIso ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ)) := by
      rw [hφ]
      exact t.prop 0
    exact (NatIso.isIso_map_iff
      (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) 0) φ).1 this
  have hK : IsZero (((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as.X (-1)) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X (-1) (by decide)
  have hM : IsZero (t.right.obj.as.X (-1)) := by
    have := ht
    exact CochainComplex.isZero_of_isStrictlyGE t.right.obj.as 0 (-1)
  have h₁ := isIso_homologyMap_mapHomologicalComplex_zero F φ hK hM h₀
  have h₂ : IsIso ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) 0).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) :=
    (NatIso.isIso_map_iff
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) 0) _).2 h₁
  rw [← Functor.mapHomotopyCategory_map, hφ] at h₂
  change IsIso ((DerivedCategory.homologyFunctor B 0).map
    (DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map t.hom.hom)))
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh B 0) _).2 h₂

/-- The `⇐` direction of part (3) of [Stacks, Tag 05TD] at the level of values: for a left exact
`F`, `H⁰` of the coprojection at the index `𝟙 A[0]` of a value of the right derived functor at
`A[0]` is an isomorphism. -/
private lemma isIso_homologyFunctor_map_ι_app_id [PreservesFiniteLimits F] (X : A)
    (c : Cocone (MorphismProperty.Under.forget (HomotopyCategory.Plus.quasiIso A) ⊤
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ⋙
      Under.forget ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ⋙
      (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)))
    (hc : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivedValueAt
      (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X) c) :
    IsIso ((Plus.homologyFunctor B 0).map (c.ι.app (MorphismProperty.Under.mk ⊤
      (𝟙 ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
      (MorphismProperty.id_mem _ _)))) := by
  obtain ⟨s₀, r, hr, hb⟩ := hc
  obtain ⟨t₀, u₀, ht₀, -⟩ := exists_under_isStrictlyGE F X s₀
  have hret : (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₀.right) ≫ c.ι.app t₀ =
      𝟙 c.pt :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (c.w u₀)).trans hr)
  obtain ⟨t₁, u₁, v₁, hv⟩ := hb t₀
  obtain ⟨t₂, u₂, ht₂, -⟩ := exists_under_isStrictlyGE F X t₁
  have i₀ := isIso_homologyFunctor_map_map_hom F X t₀ ht₀
  have i₂ := isIso_homologyFunctor_map_map_hom F X t₂ ht₂
  have hcomp : t₀.hom ≫ (u₁.right ≫ u₂.right) = t₂.hom := by
    rw [← Category.assoc, MorphismProperty.Under.w u₁, MorphismProperty.Under.w u₂]
  have e₁₂ : (Plus.homologyFunctor B 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₀.hom) ≫
      (Plus.homologyFunctor B 0).map
        ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map (u₁.right ≫ u₂.right)) =
      (Plus.homologyFunctor B 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₂.hom) :=
    ((Plus.homologyFunctor B 0).map_comp _ _).symm.trans
      (congrArg (Plus.homologyFunctor B 0).map
        (((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map_comp _ _).symm.trans
          (congrArg (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map hcomp)))
  have i₁₂ : IsIso ((Plus.homologyFunctor B 0).map
      ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map (u₁.right ≫ u₂.right))) := by
    have : IsIso ((Plus.homologyFunctor B 0).map
          ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₀.hom) ≫
        (Plus.homologyFunctor B 0).map
          ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map (u₁.right ≫ u₂.right))) := by
      rw [e₁₂]
      exact i₂
    exact IsIso.of_isIso_comp_left
      ((Plus.homologyFunctor B 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₀.hom)) _
  have hfac : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map (u₁.right ≫ u₂.right) =
      c.ι.app t₀ ≫ (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right ≫
        (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₂.right) :=
    ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map_comp _ _).trans
      ((congrArg (· ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₂.right) hv).trans
        ((Category.assoc _ _ _).trans (congrArg (c.ι.app t₀ ≫ ·) (Category.assoc _ _ _))))
  have hmono : Mono ((Plus.homologyFunctor B 0).map (c.ι.app t₀)) := by
    have e : (Plus.homologyFunctor B 0).map (c.ι.app t₀) ≫
        (Plus.homologyFunctor B 0).map (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right ≫
          (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₂.right) =
        (Plus.homologyFunctor B 0).map
          ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map (u₁.right ≫ u₂.right)) :=
      ((Plus.homologyFunctor B 0).map_comp _ _).symm.trans
        (congrArg (Plus.homologyFunctor B 0).map hfac.symm)
    have : Mono ((Plus.homologyFunctor B 0).map (c.ι.app t₀) ≫
        (Plus.homologyFunctor B 0).map (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right ≫
          (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₂.right)) := by
      rw [e]
      exact @IsIso.mono_of_iso _ _ _ _ _ i₁₂
    exact mono_of_mono _ ((Plus.homologyFunctor B 0).map
      (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map v₁.right ≫
        (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₂.right))
  have hepi : Epi ((Plus.homologyFunctor B 0).map (c.ι.app t₀)) := by
    have : IsSplitEpi ((Plus.homologyFunctor B 0).map (c.ι.app t₀)) :=
      IsSplitEpi.mk' ⟨(Plus.homologyFunctor B 0).map
          (r ≫ (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map u₀.right),
        ((Plus.homologyFunctor B 0).map_comp _ _).symm.trans
          ((congrArg (Plus.homologyFunctor B 0).map hret).trans
            ((Plus.homologyFunctor B 0).map_id _))⟩
    infer_instance
  have : IsIso ((Plus.homologyFunctor B 0).map (c.ι.app t₀)) := isIso_of_mono_of_epi _
  have hw : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₀.hom ≫ c.ι.app t₀ =
      c.ι.app (MorphismProperty.Under.mk ⊤
        (𝟙 ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) (MorphismProperty.id_mem _ _)) :=
    c.w (MorphismProperty.Under.homMk (A := MorphismProperty.Under.mk ⊤
      (𝟙 ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) (MorphismProperty.id_mem _ _))
      (B := t₀) t₀.hom (Category.id_comp _))
  have e : (Plus.homologyFunctor B 0).map (c.ι.app (MorphismProperty.Under.mk ⊤
        (𝟙 ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) (MorphismProperty.id_mem _ _))) =
      (Plus.homologyFunctor B 0).map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map t₀.hom) ≫
        (Plus.homologyFunctor B 0).map (c.ι.app t₀) :=
    (congrArg (Plus.homologyFunctor B 0).map hw.symm).trans
      ((Plus.homologyFunctor B 0).map_comp _ _)
  rw [e]
  exact IsIso.comp_isIso' i₀ this

variable [HasDerivedCategory A]
  (hF : (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).IsRightDerivable (HomotopyCategory.Plus.quasiIso A))
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)]

include hF α in
/-- `RF(A[0])` is cohomologically `≥ 0` when `RF` is everywhere defined: `RF(A[0])` is a value of
the right derived functor at `A[0]`. -/
private lemma isGE_RF_obj_single_of_isRightDerivable (X : A) :
    (RF.obj ((Plus.singleFunctor A 0).obj X)).IsGE 0 := by
  have := (plusQuasiIso_isSaturated (A := A)).hasLeftCalculusOfFractions
  have hv := isRightDerivedValueAt_derivedUnitCocone (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
    (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α hF
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X)
  have : (RF.obj (Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj X))).IsGE 0 :=
    isGE_pt_of_isRightDerivedValueAt F X _ hv
  have e : RF.obj (Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) ≅
      RF.obj ((Plus.singleFunctor A 0).obj X) :=
    (RF.mapIso ((singleFunctorPlusIsoCompQh 0).app X)).symm
  exact Plus.TStructure.t.isGE_of_iso e 0

include hF α in
/-- Part (1) of [Stacks, Tag 05TD]: `R ⁱ F = 0` for `i < 0`. -/
private lemma isZero_singleFunctor_comp_homologyFunctor_of_isRightDerivable (i : ℤ)
    (hi : i < 0) :
    IsZero (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B i) := by
  rw [Functor.isZero_iff]
  intro X
  have := isGE_RF_obj_single_of_isRightDerivable F hF RF α X
  exact Plus.isZero_homology_of_isGE _ 0 i hi

include hF α in
/-- Part (3) of [Stacks, Tag 05TD]: the canonical map `F ⟶ R ⁰ F`, that is `H⁰(α)` at the
complexes `A[0]`, is an isomorphism if and only if `F` is left exact; part (2) is passed in as
`h₂`. For `⇒`, `F ≅ R ⁰ F`, which is left exact by part (2). For `⇐`, `α` at `A[0]` is the
coprojection at the index `𝟙 A[0]` of the value `RF(A[0])`, up to an isomorphism, and `H⁰` of that
coprojection is an isomorphism. -/
private lemma isIso_homologyFunctor_map_α_app_iff_of_isRightDerivable
    (h₂ : PreservesFiniteLimits (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0)) :
    (∀ X : A, IsIso ((Plus.homologyFunctor B 0).map
        (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))) ↔
      PreservesFiniteLimits F := by
  set β := Functor.whiskerRight (Functor.whiskerLeft
    (HomotopyCategory.Plus.singleFunctor A 0) α) (Plus.homologyFunctor B 0)
  have hβ : ∀ X : A, β.app X = (Plus.homologyFunctor B 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := fun _ => rfl
  constructor
  · intro h
    have : ∀ X, IsIso (β.app X) := fun X => (hβ X) ▸ h X
    have : IsIso β := NatIso.isIso_of_isIso_app β
    exact preservesFiniteLimits_of_natIso
      ((rightDerivedZeroSourceIso F).symm ≪≫ asIso β ≪≫ rightDerivedZeroTargetIso RF).symm
  · intro hF' X
    have := (plusQuasiIso_isSaturated (A := A)).hasLeftCalculusOfFractions
    let X₀ := (HomotopyCategory.Plus.singleFunctor A 0).obj X
    have hv := isRightDerivedValueAt_derivedUnitCocone (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
      (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α hF X₀
    have hι := derivedUnitCocone_ι_app (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
      (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α X₀
      (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))
    have e : (Plus.homologyFunctor B 0).map ((derivedUnitCocone
        (F.mapHomotopyCategoryPlus ⋙ Plus.Qh) (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α
          X₀).ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))) =
        (Plus.homologyFunctor B 0).map (α.app X₀) ≫ (Plus.homologyFunctor B 0).map
          (RF.map (((HomotopyCategory.Plus.quasiIso A).underIso Plus.Qh X₀
            (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))).inv)) :=
      (congrArg (Plus.homologyFunctor B 0).map hι).trans ((Plus.homologyFunctor B 0).map_comp _ _)
    have hfg : IsIso ((Plus.homologyFunctor B 0).map (α.app X₀) ≫ (Plus.homologyFunctor B 0).map
        (RF.map (((HomotopyCategory.Plus.quasiIso A).underIso Plus.Qh X₀
          (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))).inv))) := by
      have h₃ : IsIso ((Plus.homologyFunctor B 0).map ((derivedUnitCocone
          (F.mapHomotopyCategoryPlus ⋙ Plus.Qh) (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α
            X₀).ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _)))) :=
        isIso_homologyFunctor_map_ι_app_id F X _ hv
      rw [e] at h₃
      exact h₃
    have hg : IsIso ((Plus.homologyFunctor B 0).map
        (RF.map (((HomotopyCategory.Plus.quasiIso A).underIso Plus.Qh X₀
          (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))).inv))) :=
      Iso.isIso_hom ((Plus.homologyFunctor B 0).mapIso
        (RF.mapIso (((HomotopyCategory.Plus.quasiIso A).underIso Plus.Qh X₀
          (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))).symm)))
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ ((Plus.homologyFunctor B 0).map (α.app X₀))
      ((Plus.homologyFunctor B 0).map (RF.map (((HomotopyCategory.Plus.quasiIso A).underIso
        Plus.Qh X₀ (MorphismProperty.Under.mk ⊤ (𝟙 X₀) (MorphismProperty.id_mem _ _))).inv)))
      hg hfg

end

/-- **Right deriving is for left exact functors**, [Stacks, Tag 05TD].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories and assume that the right
derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined: for every bounded below complex `K`
the ind-object `(s : K ⟶ L) ↦ F(L)` over the quasi-isomorphisms `s` out of `K` is essentially
constant ([Stacks, Tag 05SV]). Let `RF`, with unit `α`, be the right derived functor, so that
`R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`. Then
1. `R ⁱ F = 0` for `i < 0`,
2. `R ⁰ F` is left exact, and
3. the canonical map `F ⟶ R ⁰ F`, that is `H ⁰(α)` at the complexes `X[0]`, is an
   isomorphism if and only if `F` is left exact. -/
@[stacks 05TD]
public theorem isZero_and_preservesFiniteLimits_and_isIso_iff_of_isRightDerivable
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (hF : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsRightDerivable
      (HomotopyCategory.Plus.quasiIso A))
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    (∀ i < 0, IsZero (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF ⋙
        DerivedCategory.Plus.homologyFunctor B i)) ∧
      PreservesFiniteLimits (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF ⋙
        DerivedCategory.Plus.homologyFunctor B 0) ∧
      ((∀ X : A, IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map
          (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))) ↔
        PreservesFiniteLimits F) := by
  -- Part (2): the everywhere defined `RF` is exact, so it carries the distinguished triangle of a
  -- short exact sequence of `A` to a distinguished triangle, whose long exact homology sequence is
  -- exact at the first two spots because `R⁻¹ F = 0`.
  have h₂ : PreservesFiniteLimits (DerivedCategory.Plus.singleFunctor A 0 ⋙ RF ⋙
      DerivedCategory.Plus.homologyFunctor B 0) := by
    let := Functor.IsRightDerivedFunctor.commShift RF α (HomotopyCategory.Plus.quasiIso A) ℤ
    let := Functor.IsRightDerivedFunctor.natTrans_commShift RF α
      (HomotopyCategory.Plus.quasiIso A) ℤ
    have : (HomotopyCategory.Plus.quasiIso A).IsCompatibleWithTriangulation := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
      infer_instance
    have := isTriangulated_of_isRightDerivable (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
      (HomotopyCategory.Plus.quasiIso A) Plus.Qh RF α plusQuasiIso_isSaturated hF
    have : (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0).Additive := inferInstance
    rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
    intro S hS
    obtain ⟨δ, hT⟩ := exists_distTriang_singleFunctor (A := A) hS
    have hT' : RF.mapTriangle.obj
        (Pretriangulated.Triangle.mk ((Plus.singleFunctor A 0).map S.f)
          ((Plus.singleFunctor A 0).map S.g) δ) ∈ distTriang (DerivedCategory.Plus B) :=
      RF.map_distinguished _ hT
    have hz : IsZero (((Plus.homologyFunctor B 0).shift (-1 : ℤ)).obj
        (RF.obj ((Plus.singleFunctor A 0).obj S.X₃))) := by
      have := isGE_RF_obj_single_of_isRightDerivable F hF RF α S.X₃
      exact Plus.isZero_homology_of_isGE _ 0 (-1) (by norm_num)
    refine ⟨(Plus.homologyFunctor B 0).homologySequence_exact₂ _ hT' 0, ?_⟩
    exact ((Plus.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      _ hT' (-1) 0 (by ring)).2 (hz.eq_of_src _ _)
  exact ⟨fun i hi => isZero_singleFunctor_comp_homologyFunctor_of_isRightDerivable F hF RF α i hi,
    h₂, isIso_homologyFunctor_map_α_app_iff_of_isRightDerivable F hF RF α h₂⟩

end CategoryTheory.Functor
