module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention.BaseChangeToLimit
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeDescentUnderConvention.BaseChangeToLimit

/-!
# Descent of frames along the limit of a system of algebraic spaces

Regular functions and equations between them on finitely many base changes to the limit come from
a stage; the transition matrices of a module with frames on the base changes of finitely many
charts descend to a later stage, and the glued module there pulls back to the given module.
-/

/-! ## Descent of the frames and their transition matrices -/

noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hconv : SiteContainsBaseChangeLimits B S hS D)
  (hQcL : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  {j : I}

include hconv hQcL hQc hQs in
/-- A finite family of regular functions on base changes to the limit comes from one stage. -/
private theorem Conv.exists_common_stage {ι : Type} [Finite ι] (T : ι → SmallEtale B S hS (D.obj
    j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left))
    (y : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (Conv.limChart B S hS D hconv hQcL hD hAffine (T i)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤)),
      ∀ i, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T i) s) (x i) = y i := by
  have := Fintype.ofFinite ι
  choose s₀ x₀ hx₀ using fun i => Conv.exists_gpb_limToStage_eq B S hS D hconv hQcL hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (y i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (Discrete.functor s₀)
  refine ⟨c.pt, fun i => gpb (stageToStage B S hS D hD hAffine (T i) (c.π.app ⟨i⟩)) (x₀ i),
    fun i => ?_⟩
  rw [← gpb_comp, Conv.limToStage_stageToStage]
  exact hx₀ i

include hconv hQcL hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, holding
on the base changes to the limit, holds at a later stage. -/
private theorem Conv.exists_common_stage_eq {ι : Type} [Finite ι]
    (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T i) s) (x₁ i) =
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T i) s) (x₂ i)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i) := by
  classical
  have := Fintype.ofFinite ι
  choose s₀ d₀ hd₀ using fun i => Conv.exists_gpb_stageToStage_eq B S hS D hconv hQcL hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (x₁ i) (x₂ i) (h i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (WidePullbackShape.wideCospan s s₀ d₀)
  refine ⟨c.pt, c.π.app none, fun i => ?_⟩
  have hw : c.π.app (some i) ≫ d₀ i = c.π.app none := c.w (WidePullbackShape.Hom.term i)
  rw [← hw, stageToStage_comp, gpb_comp, gpb_comp, hd₀]

include hconv hQcL hQc hQs in
/-- A finite family of matrices of regular functions on base changes to the limit comes from one
stage. -/
private theorem Conv.exists_common_stage_matrix {K : Type} [Finite K] (n : K → ℕ)
    (T : K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l, IsQuasiCompactSpace B S hS (yoneda.obj (T k l).obj.left))
    (hTqs : ∀ k l, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l).obj.left))
    (y : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
      (Conv.limChart B S hS D hconv hQcL hD hAffine (T k l)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T k l) s).obj.left, ⊤)),
      ∀ k l a b, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T k l) s) (x k l a b) =
        y k l a b := by
  obtain ⟨s, x, hx⟩ := Conv.exists_common_stage B S hS hZ D hconv hQcL hD hAffine hQc hQs
    (ι := Σ p : K × K, Fin (n p.1) × Fin (n p.2)) (fun i => T i.1.1 i.1.2)
    (fun i => hTqc _ _) (fun i => hTqs _ _) (fun i => y i.1.1 i.1.2 i.2.1 i.2.2)
  exact ⟨s, fun k l a b => x ⟨(k, l), (a, b)⟩, fun k l a b => hx ⟨(k, l), (a, b)⟩⟩

include hconv hQcL hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, indexed
over a finite family of charts, holding on the base changes to the limit, holds at a later
stage. -/
private theorem Conv.exists_common_stage_eq_family {ι : Type} [Finite ι] (κ : ι → Type)
    [∀ i, Finite (κ i)] (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, κ i → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i c, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T i) s) (x₁ i c) =
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T i) s) (x₂ i c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i c,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i c) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i c) := by
  obtain ⟨s', d, hd⟩ := Conv.exists_common_stage_eq B S hS hZ D hconv hQcL hD hAffine hQc hQs
    (ι := Σ i, κ i) (fun p => T p.1) (fun p => hTqc _) (fun p => hTqs _)
    (fun p => x₁ p.1 p.2) (fun p => x₂ p.1 p.2) (fun p => h p.1 p.2)
  exact ⟨s', d, fun i c => hd ⟨i, c⟩⟩

include hconv hQcL hQc hQs in
/-- `AlgebraicGeometry.Space.exists_common_stage_eq_family` for a family of charts indexed by
triples. -/
private theorem Conv.exists_common_stage_eq_triple {K : Type} [Finite K]
    (κ : K → K → K → Type) [∀ k l m, Finite (κ k l m)]
    (T : K → K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l m, IsQuasiCompactSpace B S hS (yoneda.obj (T k l m).obj.left))
    (hTqs : ∀ k l m, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l m).obj.left))
    {s : Over j} (x₁ x₂ : ∀ k l m, κ k l m → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T k l m) s).obj.left, ⊤))
    (h : ∀ k l m c, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T k l m) s) (x₁ k l m c) =
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (T k l m) s) (x₂ k l m c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ k l m c,
      gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₁ k l m c) =
        gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₂ k l m c) := by
  obtain ⟨s', d, hd⟩ := Conv.exists_common_stage_eq_family B S hS hZ D hconv hQcL hD hAffine hQc
    hQs (fun p : K × K × K => κ p.1 p.2.1 p.2.2) (fun p => T p.1 p.2.1 p.2.2)
    (fun p => hTqc _ _ _) (fun p => hTqs _ _ _) (fun p => x₁ p.1 p.2.1 p.2.2)
    (fun p => x₂ p.1 p.2.1 p.2.2) (fun p => h p.1 p.2.1 p.2.2)
  exact ⟨s', d, fun k l m c => hd (k, l, m) c⟩

/-! ### The transition matrices of a module with frames on the base changes -/

section LimitMatrices

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
    (convLimitSpace B S hS D hconv hQcL hD hAffine).2)
  {n : K → ℕ} {e : ∀ k, Fin (n k) → (sval E).obj (op (Conv.limChart B S hS D hconv hQcL hD hAffine
      (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

/-- Base change to the limit. -/
private abbrev Conv.sbl :=
  smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine j)
    (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine j)

/-- The transition matrices of the frames of `E`, on the base changes of the products. -/
private def Conv.limMatrix (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    Γ((BigFppfOver.toScheme B S hS).obj
      (Conv.limChart B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace
          B S hS D hD j).1 (W k) (W l))).obj.left, ⊤) :=
  trans he ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
    ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (W l))) a b

private theorem Conv.gpb_trans {T T' : SmallEtale B S hS (convLimitSpace B S hS D hconv hQcL hD
    hAffine).1}
    (g : T' ⟶ T) {k l : K}
    (α : T ⟶ Conv.limChart B S hS D hconv hQcL hD hAffine (W k))
    (β : T ⟶ Conv.limChart B S hS D hconv hQcL hD hAffine (W l)) (a : Fin (n k)) (b : Fin (n l)) :
    gpb g.hom.left (trans he α β a b) = trans he (g ≫ α) (g ≫ β) a b :=
  trans_res he g α β a b

/-- Restricting a transition matrix to a chart over the product of two charts. -/
private theorem Conv.gpb_map_limMatrix {T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD
    j).1} {k l : K} (f : T ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1
      (W k) (W l)) (a : Fin (n k)) (b : Fin (n l)) :
    gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map f).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b) =
      trans he ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (f ≫ SmallEtale.prodFst B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
        ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (f ≫ SmallEtale.prodSnd B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) a b := by
  rw [Conv.limMatrix, Conv.gpb_trans, Functor.map_comp, Functor.map_comp]

private theorem Conv.limMatrix_diag (k : K) (a b : Fin (n k)) :
    gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (stageChartDiagonal B S hS D hD W
        k)).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k k a b) =
      if a = b then 1 else 0 := by
  rw [Conv.gpb_map_limMatrix, stageChartDiagonal_fst, stageChartDiagonal_snd,
    CategoryTheory.Functor.map_id]
  exact trans_self he _ a b

private theorem Conv.limMatrix_cocycle (k l m : K) (a : Fin (n k)) (b : Fin (n m)) :
    ∑ x, gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (tripPair₁₂ B S hS D hD W k l
        m)).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a x) *
      gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
            B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he l m x b) =
    gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k m a b) := by
  simp only [Conv.gpb_map_limMatrix, tripPair₁₂_fst, tripPair₁₂_snd, tripPair₁₃_fst,
    tripPair₁₃_snd, Functor.map_comp]
  exact trans_comp he _ _ _ a b

end LimitMatrices

/-! ### Moving functions along base changes of chart morphisms -/

section Moving

variable {T T' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1} (h : T ⟶ T')

private theorem Conv.gpb_limToStage_map (s : Over j)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤)) :
    gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s)
        (gpb ((sbs B S hS D hD hAffine s).map h).hom.left y) =
      gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map h).hom.left
        (gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T' s) y) :=
  (gpb_comp _ _ y).symm.trans ((congrArg (fun g => gpb g y)
    (Conv.limToStage_naturality B S hS D hconv hQcL hD hAffine h s).symm).trans (gpb_comp _ _ y))

end Moving

/-! ### The glueing data at a stage -/

private theorem Conv.stageToLim_naturality_sbs {T T' : SmallEtale B S hS (stageAlgebraicSpace B S
    hS D hD j).1}
    (h : T ⟶ T') (s : Over j) :
    (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s.left)).map
        ((sbs B S hS D hD hAffine s).map h) ≫ Conv.stageToLim B S hS D hconv hQcL hD hAffine T' s =
      Conv.stageToLim B S hS D hconv hQcL hD hAffine T s ≫
        (Conv.sbl B S hS D hconv hQcL hD hAffine).map h :=
  Conv.stageToLim_naturality B S hS D hconv hQcL hD hAffine h s

/-! ### The coordinates of the frames of `E` on the base changes of a later stage -/

section Comparison

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
    (convLimitSpace B S hS D hconv hQcL hD hAffine).2)
  {n : K → ℕ}
  {e : ∀ k, Fin (n k) → (sval E).obj (op (Conv.limChart B S hS D hconv hQcL hD hAffine (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

private theorem Conv.gpb_sbcProj_stageToStage_eq_trans {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K)
    (a : Fin (n k)) (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b) :
    gpb (sbcProj (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection
        B S hS D hconv hQcL hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      trans he ((Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((Conv.sbl B S hS D hconv hQcL
          hD hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) ((Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((Conv.sbl B S hS D hconv hQcL
          hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) a b := by
  have e5 : (Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂).hom.left ≫ Conv.limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁ =
      sbcProj (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
          (Conv.rep_limitProjection B
          S hS D hconv hQcL hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
          (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫
        stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D
            hD j).1 (W k) (W l)) d :=
    (congrArg (_ ≫ ·) (Conv.limToStage_stageToStage B S hS D hconv hQcL hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) d)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (Conv.stageToLim_limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
            (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)))
  refine (gpb_comp _ _ x).symm.trans ?_
  refine (congrArg (fun t => gpb t x) e5.symm).trans ?_
  refine (gpb_comp _ _ x).trans ?_
  refine (congrArg (gpb (Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂).hom.left) hx).trans ?_
  exact Conv.gpb_trans B S hS D hconv hQcL hD hAffine W E he (Conv.stageToLim B S hS D hconv hQcL hD
      hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂) ((Conv.sbl B S hS D hconv hQcL hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) ((Conv.sbl B S hS D hconv hQcL hD
      hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) a b

private theorem Conv.res_stageToLim_prodSnd {s₂ : Over j} (k l : K) (b : Fin (n l)) :
    res (sval E) ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
        s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W l) s₂) (e l
        b)) =
      res (sval E) ((Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ (Conv.sbl B S hS D hconv hQcL hD
          hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l))) (e l b) :=
  (res_comp _ _ _ _).symm.trans (congrArg (fun t => res (sval E) t (e l b))
    (Conv.stageToLim_naturality_sbs B S hS D hconv hQcL hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))

private theorem Conv.trans_stageToLim_eq_coord_restrict {s₂ : Over j} (k l : K) (a : Fin (n k))
    (b : Fin (n l)) :
    trans he ((Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((Conv.sbl B S hS D hconv hQcL hD
        hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) ((Conv.stageToLim B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((Conv.sbl B S hS D hconv hQcL hD
        hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) a b =
      ((he k).restrict (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
          s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
            s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W l)
            s₂) (e l b))) a := by
  refine Eq.trans ?_ (congrFun (IsFrame.coord_restrict (he k) (Conv.stageToLim B S hS D hconv hQcL
      hD hAffine (W k) s₂)
    ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l))))
    (res (sval E) ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
        s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W l) s₂) (e l
        b)))) a).symm
  have e3 : (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
      (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S hS D hD
      hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) ≫ (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k) s₂) = (Conv.stageToLim B S hS D
          hconv
      hQcL hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
      (W l)) s₂) ≫ (Conv.sbl B S hS D hconv hQcL hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) :=
    Conv.stageToLim_naturality_sbs B S hS D hconv hQcL hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂
  show (he k).coord _ _ a = (he k).coord _ _ a
  rw [Conv.res_stageToLim_prodSnd B S hS D hconv hQcL hD hAffine W E k l b, e3]

/-- The coordinates of the frames of `E`, restricted to the base changes of a later stage, are the
pullbacks of descended transition matrices. -/
private theorem Conv.coord_restrict_stageToLim {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K) (a : Fin (n
    k))
    (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b) :
    gpb (sbcProj (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection
        B S hS D hconv hQcL hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      ((he k).restrict (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
          s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
            s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W l)
            s₂) (e l b))) a :=
  (Conv.gpb_sbcProj_stageToStage_eq_trans B S hS D hconv hQcL hD hAffine W E he d k l a b x
      hx).trans
    (Conv.trans_stageToLim_eq_coord_restrict B S hS D hconv hQcL hD hAffine W E he k l a b)

end Comparison

/-! ### The descent -/

section Descent

variable {K : Type} [Fintype K] [DecidableEq K]
  (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1) {n : K → ℕ}

variable {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (x : ∀ k l, Fin (n k) → Fin (n l) →
    Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B
    S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁).obj.left, ⊤))

variable {W d x}

omit [Fintype K] [DecidableEq K] in
variable (W) in
private theorem Conv.stage_lift_limit (s₂ : Over j) (V : SmallEtale B S hS
      (convLimitSpace B S hS D hconv hQcL hD hAffine).1) (k l : K)
    (h : V ⟶ (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (W k) s₂)) (h' : V ⟶ (smallBaseChange B S hS (convLimitProjection B S hS D
        hconv hQcL hD hAffine s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine
        s₂.left)).obj (laterStageChart B S hS D hD hAffine (W l) s₂)) :
    ∃ t : V ⟶ (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) s₂),
      t ≫ (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
          (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S hS D hD
          hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l))) = h ∧ t ≫ (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD
          hAffine s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine
          s₂.left)).map ((sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) = h' := by
  exact ⟨_, (BinaryFan.IsLimit.lift' (isLimitSmallBaseChangeOfIsLimit
      (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left) (Conv.rep_limitProjection B S hS
          D
      hconv hQcL hD hAffine s₂.left)
    (stageProdIsLimit B S hS D hD hAffine s₂ (W k) (W l))) h h').2⟩

variable (W d x) in
private theorem Conv.stageGlueModule_hcoord
    (E : Modules.{u, u} B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
      (convLimitSpace B S hS D hconv hQcL hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (Conv.limChart B S hS D hconv hQcL hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    ((smallBaseChangeSharp B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).hom.app (op
        (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
        hS D hD j).1 (W k) (W l)) s₂))).hom
        ((isFrame_stageGlueModule B S hS D hD hAffine hU hC k).coord ((sbs B S hS D hD hAffine
            s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
          (res (sval (stageGlueModule B S hS D hD hAffine hU hC)) ((sbs B S hS D hD hAffine
              s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
              l))) (stageGlueFrame B S hS D hD hAffine hU hC l b)) a) =
      ((he k).restrict (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
          s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
            s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W l)
            s₂) (e l b))) a :=
  (smallBaseChangeSharp_app_eq_gpb B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
      s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left) _ _).trans
    ((congrArg (gpb (sbcProj (convLimitProjection B S hS D hconv hQcL hD hAffine s₂.left)
        (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left) (laterStageChart B S hS D
        hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₂)))
      (stageGlueModule_coord B S hS D hD hAffine hU hC k l a b)).trans
    (Conv.coord_restrict_stageToLim B S hS D hconv hQcL hD hAffine W E he d k l a b (x k l a b)
      (hx k l a b)))

omit [Fintype K] [DecidableEq K] in
private theorem Conv.coversTop_stageLimChart (hW : PointsCover W) (s₂ : Over j) :
    (SmallEtale.topology B S hS (convLimitSpace B S hS D hconv hQcL hD
        hAffine).1).CoversTop
      (fun k => (smallBaseChange B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
          s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)).obj
          (laterStageChart B S hS D hD hAffine (W k) s₂)) :=
  coversTop_of_pointsCover (pointsCover_smallBaseChange (convLimitProjection B S hS D hconv hQcL
      hD hAffine s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)
    (pointsCover_smallBaseChange (stageTransition B S hS D hD s₂.hom)
      (rep_stageTransition B S hS D hD hAffine s₂.hom) hW))

omit [DecidableEq K] in
variable (W d x) in
/-- **The glued module pulls back to `E`.** -/
private theorem Conv.nonempty_iso_stageGlueModule (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
      (convLimitSpace B S hS D hconv hQcL hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (Conv.limChart B S hS D hconv hQcL hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) :
    Nonempty (E ≅ (modulePullback B S hS (convLimitProjection B S hS D hconv hQcL hD hAffine
        s₂.left)).obj (stageGlueModule B S hS D hD hAffine hU hC)) := by
  classical
  refine nonempty_iso_modulePullback_of_frames (convLimitProjection B S hS D hconv hQcL hD hAffine
      s₂.left) (Conv.rep_limitProjection B S hS D hconv hQcL hD hAffine s₂.left)
    (W := fun k => (laterStageChart B S hS D hD hAffine (W k) s₂))
    (coversTop_stageChart B S hS D hD hAffine hW s₂) (stageGlueModule B S hS D hD hAffine hU hC)
    (isFrame_stageGlueModule B S hS D hD hAffine hU hC) E
    (e' := fun k a => res (sval E) (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k) s₂) (e k
        a))
    (fun k => (he k).restrict (Conv.stageToLim B S hS D hconv hQcL hD hAffine (W k) s₂))
    (Conv.coversTop_stageLimChart B S hS D hconv hQcL hD hAffine hW s₂)
    (P := fun k l => laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)
    (p₁ := fun k l => (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (p₂ := fun k l => (sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))
    (Conv.stage_lift_limit B S hS D hconv hQcL hD hAffine W s₂)
    (fun k l a b => ?_)
    (stage_lift B S hS D hD hAffine W s₂)
  convert Conv.stageGlueModule_hcoord B S hS D hconv hQcL hD hAffine W d x E he hx hU hC k l a b
    using 3

omit [Fintype K] [DecidableEq K] in
include hZ hQc hQs in
/-- **A module with frames on the base changes of finitely many charts descends to a stage.** -/
private theorem Conv.exists_stage_model_of_frames [Finite K]
    (hWqc : ∀ k, IsQuasiCompactSpace B S hS (yoneda.obj (W k).obj.left))
    (hWqs : ∀ k, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (W k).obj.left))
    (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (convLimitSpace B S hS D hconv hQcL hD hAffine).1
      (convLimitSpace B S hS D hconv hQcL hD hAffine).2)
    {n : K → ℕ}
    {e : ∀ k, Fin (n k) → (sval E).obj (op (Conv.limChart B S hS D hconv hQcL hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k)) :
    ∃ (s : Over j) (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD s.left).1
        (stageAlgebraicSpace B S hS D hD s.left).2),
      (∀ k, ∃ e' : Fin (n k) → (sval M).obj (op (laterStageChart B S hS D hD hAffine (W k) s)),
        IsFrame (sval M) e') ∧
      Nonempty (E ≅ (modulePullback B S hS
        (convLimitProjection B S hS D hconv hQcL hD hAffine s.left)).obj M) := by
  classical
  have := Fintype.ofFinite K
  have hPqc : ∀ k l, IsQuasiCompactSpace B S hS
      (yoneda.obj (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l)).obj.left) := fun k l =>
    isQuasiCompactSpace_prodObj hZ (hD j) (hQs j) (hWqc k) (hWqc l)
  have hPqs : ∀ k l, IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l)).obj.left) := fun k l =>
    isAbsolutelyQuasiSeparated_prodObj hZ (hD j) (hWqs k) (hWqs l)
  obtain ⟨s₁, x, hx⟩ := Conv.exists_common_stage_matrix B S hS hZ D hconv hQcL hD hAffine hQc hQs n
    (fun k l => SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) hPqc hPqs (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he)
  have hmap : ∀ {T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1} {k l : K}
      (f : T ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      (a : Fin (n k)) (b : Fin (n l)),
      gpb (Conv.limToStage B S hS D hconv hQcL hD hAffine T s₁)
        (gpb ((sbs B S hS D hD hAffine s₁).map f).hom.left (x k l a b)) =
      gpb ((Conv.sbl B S hS D hconv hQcL hD hAffine).map f).hom.left
        (Conv.limMatrix B S hS D hconv hQcL hD hAffine W E he k l a b) := fun f a b =>
    (Conv.gpb_limToStage_map B S hS D hconv hQcL hD hAffine f s₁ (x _ _ a b)).trans
      (congrArg _ (hx _ _ a b))
  obtain ⟨sᵤ, dᵤ, hdᵤ⟩ := Conv.exists_common_stage_eq_family B S hS hZ D hconv hQcL hD hAffine hQc
    hQs (fun k => Fin (n k) × Fin (n k)) W hWqc hWqs
    (fun k c => gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
      (x k k c.1 c.2))
    (fun k c => if c.1 = c.2 then 1 else 0) (fun k c => by
      refine ((hmap _ c.1 c.2).trans
        (Conv.limMatrix_diag B S hS D hconv hQcL hD hAffine W E he k c.1 c.2)).trans ?_
      split_ifs <;> simp)
  obtain ⟨s_c, d_c, hd_c⟩ := Conv.exists_common_stage_eq_triple B S hS hZ D hconv hQcL hD hAffine
    hQc hQs (fun k _ m => Fin (n k) × Fin (n m)) (fun k l m => SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (fun k l m => isQuasiCompactSpace_prodObj hZ (hD j) (hQs j) (hWqc _) (hPqc _ _))
    (fun k l m => isAbsolutelyQuasiSeparated_prodObj hZ (hD j) (hWqs _) (hPqs _ _))
    (fun k l m c => ∑ z,
      gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₂ B S hS D hD W k l m)).hom.left
        (x k l c.1 z) *
      gpb ((sbs B S hS D hD hAffine s₁).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
            B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))).hom.left
        (x l m z c.2))
    (fun k l m c =>
      gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
        (x k m c.1 c.2)) (fun k l m c => by
      refine (map_sum _ _ _).trans ?_
      refine Eq.trans ?_ ((Conv.limMatrix_cocycle B S hS D hconv hQcL hD hAffine W E he
        k l m c.1 c.2).trans (hmap _ c.1 c.2).symm)
      exact Finset.sum_congr rfl fun z _ =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (hmap _ _ _) (hmap _ _ _)))
  obtain ⟨s₂, d, e₁, e₂, hdu, hdc⟩ : ∃ (s₂ : Over j) (d : s₂ ⟶ s₁) (e₁ : s₂ ⟶ sᵤ) (e₂ : s₂ ⟶ s_c),
      e₁ ≫ dᵤ = d ∧ e₂ ≫ d_c = d := by
    obtain ⟨c⟩ := IsCofiltered.cone_nonempty (cospan dᵤ d_c)
    exact ⟨c.pt, c.π.app WalkingCospan.one, c.π.app WalkingCospan.left,
      c.π.app WalkingCospan.right, c.w WalkingCospan.Hom.inl, c.w WalkingCospan.Hom.inr⟩
  have hunit : ∀ k (a b : Fin (n k)), gpb (stageToStage B S hS D hD hAffine (W k) d)
      (gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (x k k a b)) =
      gpb (stageToStage B S hS D hD hAffine (W k) d) (if a = b then 1 else 0) := fun k a b =>
    gpb_stageToStage_eq_of_comp B S hS D hD hAffine (W k) dᵤ e₁ hdu (hdᵤ k (a, b))
  have hcoc : ∀ k l m (a : Fin (n k)) (b : Fin (n m)),
      gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) d) (∑ z,
        gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₂ B S hS D hD W k l m)).hom.left
          (x k l a z) *
        gpb ((sbs B S hS D hD hAffine s₁).map
          (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
              (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
              m)))).hom.left (x l m z b)) =
      gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) d)
        (gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
          (x k m a b)) := fun k l m a b =>
    gpb_stageToStage_eq_of_comp B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) d_c e₂ hdc
      (hd_c k l m (a, b))
  have hU := stageGlueData_unit B S hS D hD hAffine W d x hunit
  have hC := stageGlueData_cocycle B S hS D hD hAffine W d x hcoc
  exact ⟨s₂, stageGlueModule B S hS D hD hAffine hU hC,
    fun k => ⟨_, isFrame_stageGlueModule B S hS D hD hAffine hU hC k⟩,
    Conv.nonempty_iso_stageGlueModule B S hS D hconv hQcL hD hAffine W d x hW E he hx hU hC⟩

end Descent

end AlgebraicGeometry.Space

end
