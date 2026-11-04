module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FramedModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedStageChartSystem

/-!
# A module with frames on base-changed charts descends to a stage of a system bounded by the cutoff

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated algebraic
spaces with affine transition morphisms which is bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), and let `W k` be a finite family of étale charts
of a stage `X_j`, jointly surjective on points. Let `E` be an `𝒪_X`-module with frames over the
base changes `W k ×_{X_j} X`. Then at some later stage `X_s` there is an `𝒪_{X_s}`-module `M` with
frames of the same sizes over the base changes `W k ×_{X_j} X_s`, such that `E ≅ f_s^* M`.

## Main definitions

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.limMatrix`: the transition matrices of the frames
  of `E` on the base changes of the products of the charts.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_common_stage`: a finite family of regular
  functions on base changes to the limit comes from one stage.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.nonempty_iso_stageGlueModule`: the module glued at
  a stage from descended transition matrices pulls back to `E`.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_stage_model_of_frames`: a module with
  frames on the base changes of finitely many charts descends to a stage.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space.IsCutoffBoundedSystem

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hc : IsCutoffBoundedSystem B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  {j : I}

include hc hQc hQs in
/-- A finite family of regular functions on base changes to the limit comes from one stage. -/
theorem exists_common_stage {ι : Type} [Finite ι] (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left))
    (y : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hc hD hAffine (T i)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤)),
      ∀ i, gpb (limToStage B S hS D hc hD hAffine (T i) s) (x i) = y i := by
  have := Fintype.ofFinite ι
  choose s₀ x₀ hx₀ using fun i ↦ exists_gpb_limToStage_eq B S hS D hc hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (y i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (Discrete.functor s₀)
  refine ⟨c.pt, fun i ↦ gpb (stageToStage B S hS D hD hAffine (T i) (c.π.app ⟨i⟩)) (x₀ i),
    fun i ↦ ?_⟩
  rw [← gpb_comp, limToStage_stageToStage]
  exact hx₀ i

include hc hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, holding
on the base changes to the limit, holds at a later stage. -/
theorem exists_common_stage_eq {ι : Type} [Finite ι]
    (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i, gpb (limToStage B S hS D hc hD hAffine (T i) s) (x₁ i) =
      gpb (limToStage B S hS D hc hD hAffine (T i) s) (x₂ i)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i) := by
  classical
  have := Fintype.ofFinite ι
  choose s₀ d₀ hd₀ using fun i ↦ exists_gpb_stageToStage_eq B S hS D hc hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (x₁ i) (x₂ i) (h i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (WidePullbackShape.wideCospan s s₀ d₀)
  refine ⟨c.pt, c.π.app none, fun i ↦ ?_⟩
  have hw : c.π.app (some i) ≫ d₀ i = c.π.app none := c.w (WidePullbackShape.Hom.term i)
  rw [← hw, stageToStage_comp, gpb_comp, gpb_comp, hd₀]

include hc hQc hQs in
/-- A finite family of matrices of regular functions on base changes to the limit comes from one
stage. -/
theorem exists_common_stage_matrix {K : Type} [Finite K] (n : K → ℕ)
    (T : K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l, IsQuasiCompactSpace B S hS (yoneda.obj (T k l).obj.left))
    (hTqs : ∀ k l, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l).obj.left))
    (y : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hc hD hAffine (T k l)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T k l) s).obj.left, ⊤)),
      ∀ k l a b, gpb (limToStage B S hS D hc hD hAffine (T k l) s) (x k l a b) =
        y k l a b := by
  obtain ⟨s, x, hx⟩ := exists_common_stage B S hS hZ D hc hD hAffine hQc hQs
    (ι := Σ p : K × K, Fin (n p.1) × Fin (n p.2)) (fun i ↦ T i.1.1 i.1.2)
    (fun i ↦ hTqc _ _) (fun i ↦ hTqs _ _) (fun i ↦ y i.1.1 i.1.2 i.2.1 i.2.2)
  exact ⟨s, fun k l a b ↦ x ⟨(k, l), (a, b)⟩, fun k l a b ↦ hx ⟨(k, l), (a, b)⟩⟩

include hc hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, indexed
over a finite family of charts, holding on the base changes to the limit, holds at a later
stage. -/
theorem exists_common_stage_eq_family {ι : Type} [Finite ι] (κ : ι → Type)
    [∀ i, Finite (κ i)] (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, κ i → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i c, gpb (limToStage B S hS D hc hD hAffine (T i) s) (x₁ i c) =
      gpb (limToStage B S hS D hc hD hAffine (T i) s) (x₂ i c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i c,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i c) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i c) := by
  obtain ⟨s', d, hd⟩ := exists_common_stage_eq B S hS hZ D hc hD hAffine hQc hQs
    (ι := Σ i, κ i) (fun p ↦ T p.1) (fun p ↦ hTqc _) (fun p ↦ hTqs _)
    (fun p ↦ x₁ p.1 p.2) (fun p ↦ x₂ p.1 p.2) (fun p ↦ h p.1 p.2)
  exact ⟨s', d, fun i c ↦ hd ⟨i, c⟩⟩

include hc hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, indexed
over a finite family of charts indexed by triples, holding on the base changes to the limit, holds
at a later stage. -/
theorem exists_common_stage_eq_triple {K : Type} [Finite K]
    (κ : K → K → K → Type) [∀ k l m, Finite (κ k l m)]
    (T : K → K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l m, IsQuasiCompactSpace B S hS (yoneda.obj (T k l m).obj.left))
    (hTqs : ∀ k l m, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l m).obj.left))
    {s : Over j} (x₁ x₂ : ∀ k l m, κ k l m → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T k l m) s).obj.left, ⊤))
    (h : ∀ k l m c, gpb (limToStage B S hS D hc hD hAffine (T k l m) s) (x₁ k l m c) =
      gpb (limToStage B S hS D hc hD hAffine (T k l m) s) (x₂ k l m c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ k l m c,
      gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₁ k l m c) =
        gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₂ k l m c) := by
  obtain ⟨s', d, hd⟩ := exists_common_stage_eq_family B S hS hZ D hc hD hAffine hQc
    hQs (fun p : K × K × K ↦ κ p.1 p.2.1 p.2.2) (fun p ↦ T p.1 p.2.1 p.2.2)
    (fun p ↦ hTqc _ _ _) (fun p ↦ hTqs _ _ _) (fun p ↦ x₁ p.1 p.2.1 p.2.2)
    (fun p ↦ x₂ p.1 p.2.1 p.2.2) (fun p ↦ h p.1 p.2.1 p.2.2)
  exact ⟨s', d, fun k l m c ↦ hd (k, l, m) c⟩

/-! ### The transition matrices of a module with frames on the base changes -/

section LimitMatrices

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
    (limitAlgebraicSpace B S hS D hc hD hAffine).2)
  {n : K → ℕ} {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hc hD hAffine
      (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

/-- Base change to the limit. -/
abbrev sbl :=
  smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j)
    (rep_limitProjection B S hS D hc hD hAffine j)

/-- The transition matrices of the frames of `E`, on the base changes of the products. -/
def limMatrix (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hc hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace
          B S hS D hD j).1 (W k) (W l))).obj.left, ⊤) :=
  trans he ((sbl B S hS D hc hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
    ((sbl B S hS D hc hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (W l))) a b

/-- Pulling back the transition coordinate `trans he α β a b` along `g` gives the transition
coordinate of `g ≫ α` and `g ≫ β`. -/
theorem gpb_trans {T T' : SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD
    hAffine).1}
    (g : T' ⟶ T) {k l : K}
    (α : T ⟶ limChart B S hS D hc hD hAffine (W k))
    (β : T ⟶ limChart B S hS D hc hD hAffine (W l)) (a : Fin (n k)) (b : Fin (n l)) :
    gpb g.hom.left (trans he α β a b) = trans he (g ≫ α) (g ≫ β) a b :=
  trans_res he g α β a b

/-- Pulling back `limMatrix k l a b` along the base change of `g` is the transition coordinate of
the base changes of the composites of `g` with the projections. -/
private theorem gpb_limMatrix {T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1}
    {k l : K} (g : T ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
    (g₁ : T ⟶ W k) (g₂ : T ⟶ W l)
    (h₁ : g ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = g₁)
    (h₂ : g ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = g₂)
    (a : Fin (n k)) (b : Fin (n l)) :
    gpb ((sbl B S hS D hc hD hAffine).map g).hom.left
        (limMatrix B S hS D hc hD hAffine W E he k l a b) =
      trans he ((sbl B S hS D hc hD hAffine).map g₁) ((sbl B S hS D hc hD hAffine).map g₂) a b := by
  subst h₁ h₂
  rw [limMatrix, gpb_trans, Functor.map_comp, Functor.map_comp]

/-- The pullback of the transition matrix `limMatrix k k` along the diagonal of `W k` is the
identity matrix. -/
theorem limMatrix_diag (k : K) (a b : Fin (n k)) :
    gpb ((sbl B S hS D hc hD hAffine).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (limMatrix B S hS D hc hD hAffine W E he k k a b) =
      if a = b then 1 else 0 := by
  rw [gpb_limMatrix B S hS D hc hD hAffine W E he _ _ _ (stageChartDiagonal_fst B S hS D hD W k)
    (stageChartDiagonal_snd B S hS D hD W k), CategoryTheory.Functor.map_id]
  exact trans_self he _ a b

/-- The transition matrices satisfy the cocycle condition on the base changes of the triple
products of the charts. -/
theorem limMatrix_cocycle (k l m : K) (a : Fin (n k)) (b : Fin (n m)) :
    ∑ x, gpb ((sbl B S hS D hc hD hAffine).map (tripPair₁₂ B S hS D hD W k l
        m)).hom.left
        (limMatrix B S hS D hc hD hAffine W E he k l a x) *
      gpb ((sbl B S hS D hc hD hAffine).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
            B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))).hom.left
        (limMatrix B S hS D hc hD hAffine W E he l m x b) =
    gpb ((sbl B S hS D hc hD hAffine).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
        (limMatrix B S hS D hc hD hAffine W E he k m a b) := by
  rw [gpb_limMatrix B S hS D hc hD hAffine W E he _ _ _ (tripPair₁₃_fst B S hS D hD W k l m)
    (tripPair₁₃_snd B S hS D hD W k l m)]
  simp only [gpb_limMatrix B S hS D hc hD hAffine W E he _ _ _ (tripPair₁₂_fst B S hS D hD W k l m)
    (tripPair₁₂_snd B S hS D hD W k l m), gpb_limMatrix B S hS D hc hD hAffine W E he _ _ _ rfl rfl,
    Functor.map_comp]
  exact trans_comp he _ _ _ a b

end LimitMatrices

/-! ### Moving functions along base changes of chart morphisms -/

section Moving

variable {T T' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1} (h : T ⟶ T')

/-- Pulling back along `limToStage` commutes with pulling back along the base changes of a
morphism of charts `h`. -/
theorem gpb_limToStage_map (s : Over j)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤)) :
    gpb (limToStage B S hS D hc hD hAffine T s)
        (gpb ((sbs B S hS D hD hAffine s).map h).hom.left y) =
      gpb ((sbl B S hS D hc hD hAffine).map h).hom.left
        (gpb (limToStage B S hS D hc hD hAffine T' s) y) :=
  (gpb_comp _ _ y).symm.trans ((congrArg (fun g ↦ gpb g y)
    (limToStage_naturality B S hS D hc hD hAffine h s).symm).trans (gpb_comp _ _ y))

/-- If `y` at the stage `s` pulls back to `z` on the limit, then `y` pulled back along the base
change of `h` pulls back to `z` pulled back along the base change of `h` on the limit. -/
private theorem gpb_limToStage_map_eq (s : Over j)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤))
    (z : Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hc hD hAffine T').obj.left, ⊤))
    (hy : gpb (limToStage B S hS D hc hD hAffine T' s) y = z) :
    gpb (limToStage B S hS D hc hD hAffine T s)
        (gpb ((sbs B S hS D hD hAffine s).map h).hom.left y) =
      gpb ((sbl B S hS D hc hD hAffine).map h).hom.left z :=
  (gpb_limToStage_map B S hS D hc hD hAffine h s y).trans (congrArg _ hy)

end Moving

/-- `stageToLim` is natural with respect to the base changes of a morphism of charts `h`. -/
theorem stageToLim_naturality_sbs {T T' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1}
    (h : T ⟶ T') (s : Over j) :
    (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s.left)
        (rep_limitProjection B S hS D hc hD hAffine s.left)).map
        ((sbs B S hS D hD hAffine s).map h) ≫ stageToLim B S hS D hc hD hAffine T' s =
      stageToLim B S hS D hc hD hAffine T s ≫
        (sbl B S hS D hc hD hAffine).map h :=
  stageToLim_naturality B S hS D hc hD hAffine h s

/-! ### The coordinates of the frames of `E` on the base changes of a later stage -/

section Comparison

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
    (limitAlgebraicSpace B S hS D hc hD hAffine).2)
  {n : K → ℕ}
  {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hc hD hAffine (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

/-- If `x` at the stage `s₁` pulls back to the entry `limMatrix k l a b` on the limit, then its
pullback to the stage `s₂` and then to the limit is the transition coordinate of the frames of `E`
along the composites of `stageToLim` with the two projections. -/
theorem gpb_sbcProj_stageToStage_eq_trans {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K)
    (a : Fin (n k)) (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      limMatrix B S hS D hc hD hAffine W E he k l a b) :
    gpb (sbcProj (limitProjection B S hS D hc hD hAffine s₂.left) (rep_limitProjection
        B S hS D hc hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      trans he ((stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hc
          hD hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) ((stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hc
          hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) a b := by
  have e5 : (stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂).hom.left ≫ limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁ =
      sbcProj (limitProjection B S hS D hc hD hAffine s₂.left) (rep_limitProjection B
          S hS D hc hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
          (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫
        stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D
            hD j).1 (W k) (W l)) d :=
    (congrArg (_ ≫ ·) (limToStage_stageToStage B S hS D hc hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) d)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (stageToLim_limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
            (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)))
  refine (gpb_comp _ _ x).symm.trans ?_
  refine (congrArg (fun t ↦ gpb t x) e5.symm).trans ?_
  refine (gpb_comp _ _ x).trans ?_
  refine (congrArg (gpb (stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂).hom.left) hx).trans ?_
  exact gpb_trans B S hS D hc hD hAffine W E he (stageToLim B S hS D hc hD
      hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂) ((sbl B S hS D hc hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) ((sbl B S hS D hc hD
      hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) a b

/-- Restricting `e l b` along `stageToLim` and then along the base change of the second projection
is restricting it along `stageToLim` of the product followed by the second projection. -/
theorem res_stageToLim_prodSnd {s₂ : Over j} (k l : K) (b : Fin (n l)) :
    res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
        s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (stageToLim B S hS D hc hD hAffine (W l) s₂) (e l
        b)) =
      res (sval E) ((stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ (sbl B S hS D hc hD
          hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l))) (e l b) :=
  (res_comp _ _ _ _).symm.trans (congrArg (fun t ↦ res (sval E) t (e l b))
    (stageToLim_naturality_sbs B S hS D hc hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))

/-- The transition coordinate of the frames of `E` along the composites of `stageToLim` with the
two projections is a coordinate of the frame of `E` restricted along `stageToLim`. -/
theorem trans_stageToLim_eq_coord_restrict {s₂ : Over j} (k l : K) (a : Fin (n k))
    (b : Fin (n l)) :
    trans he ((stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hc hD
        hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) ((stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hc hD
        hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) a b =
      ((he k).restrict (stageToLim B S hS D hc hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
          s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
            s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hc hD hAffine (W l)
            s₂) (e l b))) a := by
  refine Eq.trans ?_ (congrFun (IsFrame.coord_restrict (he k) (stageToLim B S hS D hc
      hD hAffine (W k) s₂)
    ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
        (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l))))
    (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
        s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (stageToLim B S hS D hc hD hAffine (W l) s₂) (e l
        b)))) a).symm
  have e3 : (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
      (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S hS D hD
      hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) ≫ (stageToLim B S hS D hc hD hAffine (W k) s₂) =
        (stageToLim B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k)
      (W l)) s₂) ≫ (sbl B S hS D hc hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) :=
    stageToLim_naturality_sbs B S hS D hc hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂
  show (he k).coord _ _ a = (he k).coord _ _ a
  rw [res_stageToLim_prodSnd B S hS D hc hD hAffine W E k l b, e3]

/-- The coordinates of the frames of `E`, restricted to the base changes of a later stage, are the
pullbacks of descended transition matrices. -/
theorem coord_restrict_stageToLim {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K) (a : Fin (n k))
    (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      limMatrix B S hS D hc hD hAffine W E he k l a b) :
    gpb (sbcProj (limitProjection B S hS D hc hD hAffine s₂.left) (rep_limitProjection
        B S hS D hc hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      ((he k).restrict (stageToLim B S hS D hc hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
          s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
            s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hc hD hAffine (W l)
            s₂) (e l b))) a :=
  (gpb_sbcProj_stageToStage_eq_trans B S hS D hc hD hAffine W E he d k l a b x hx).trans
    (trans_stageToLim_eq_coord_restrict B S hS D hc hD hAffine W E he k l a b)

end Comparison

/-! ### The descent -/

section Descent

variable {K : Type} [Fintype K]
  (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1) {n : K → ℕ}

variable {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (x : ∀ k l, Fin (n k) → Fin (n l) →
    Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B
    S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁).obj.left, ⊤))

variable {W d x}

omit [Fintype K] in
variable (W) in
/-- Two morphisms from `V` to the base changes to the limit of the charts `W k` and `W l` at the
stage `s₂` factor through the base change of the product chart. -/
theorem stage_lift_limit (s₂ : Over j) (V : SmallEtale B S hS
      (limitAlgebraicSpace B S hS D hc hD hAffine).1) (k l : K)
    (h : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
        (rep_limitProjection B S hS D hc hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (W k) s₂)) (h' : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D
        hc hD hAffine s₂.left) (rep_limitProjection B S hS D hc hD hAffine
        s₂.left)).obj (laterStageChart B S hS D hD hAffine (W l) s₂)) :
    ∃ t : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
        (rep_limitProjection B S hS D hc hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) s₂),
      t ≫ (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
          (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S hS D hD
          hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l))) = h ∧ t ≫ (smallBaseChange B S hS (limitProjection B S hS D hc hD
          hAffine s₂.left) (rep_limitProjection B S hS D hc hD hAffine
          s₂.left)).map ((sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) = h' :=
  ⟨_, (BinaryFan.IsLimit.lift' (isLimitSmallBaseChangeOfIsLimit
      (limitProjection B S hS D hc hD hAffine s₂.left) (rep_limitProjection B S hS D
      hc hD hAffine s₂.left)
    (stageProdIsLimit B S hS D hD hAffine s₂ (W k) (W l))) h h').2⟩

variable (W d x) in
/-- The coordinates of the frames of the module glued at the stage `s₂`, transported to the limit,
are the coordinates of the frames of `E` restricted along `stageToLim`. -/
theorem stageGlueModule_hcoord
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hc hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      limMatrix B S hS D hc hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    ((smallBaseChangeSharp B S hS (limitProjection B S hS D hc hD hAffine s₂.left)
        (rep_limitProjection B S hS D hc hD hAffine s₂.left)).hom.app (op
        (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
        hS D hD j).1 (W k) (W l)) s₂))).hom
        ((open scoped Classical in isFrame_stageGlueModule B S hS D hD hAffine hU hC k).coord
          ((sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS
            (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
          (res (sval (stageGlueModule B S hS D hD hAffine hU hC)) ((sbs B S hS D hD hAffine
              s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
              l))) (stageGlueFrame B S hS D hD hAffine hU hC l b)) a) =
      ((he k).restrict (stageToLim B S hS D hc hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
          s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
            s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hc hD hAffine (W l)
            s₂) (e l b))) a := by
  classical
  exact (smallBaseChangeSharp_app_eq_gpb B S hS (limitProjection B S hS D hc hD hAffine
      s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left) _ _).trans
    ((congrArg (gpb (sbcProj (limitProjection B S hS D hc hD hAffine s₂.left)
        (rep_limitProjection B S hS D hc hD hAffine s₂.left) (laterStageChart B S hS D
        hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₂)))
      (stageGlueModule_coord B S hS D hD hAffine hU hC k l a b)).trans
    (coord_restrict_stageToLim B S hS D hc hD hAffine W E he d k l a b (x k l a b)
      (hx k l a b)))

omit [Fintype K] in
/-- The base changes to the limit of the charts `W k` at the stage `s₂` cover the limit. -/
theorem coversTop_stageLimChart (hW : PointsCover W) (s₂ : Over j) :
    (SmallEtale.topology B S hS (limitAlgebraicSpace B S hS D hc hD
        hAffine).1).CoversTop
      (fun k ↦ (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine
          s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)).obj
          (laterStageChart B S hS D hD hAffine (W k) s₂)) :=
  coversTop_of_pointsCover (pointsCover_smallBaseChange (limitProjection B S hS D hc
      hD hAffine s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)
    (pointsCover_smallBaseChange (stageTransition B S hS D hD s₂.hom)
      (rep_stageTransition B S hS D hD hAffine s₂.hom) hW))

variable (W d x) in
/-- The module glued at the stage `s₂` from the descended transition matrices pulls back to `E`. -/
theorem nonempty_iso_stageGlueModule (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hc hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (limToStage B S hS D hc hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      limMatrix B S hS D hc hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) :
    Nonempty (E ≅ (modulePullback B S hS (limitProjection B S hS D hc hD hAffine
        s₂.left)).obj (stageGlueModule B S hS D hD hAffine hU hC)) := by
  classical
  refine nonempty_iso_modulePullback_of_frames (limitProjection B S hS D hc hD hAffine
      s₂.left) (rep_limitProjection B S hS D hc hD hAffine s₂.left)
    (W := fun k ↦ (laterStageChart B S hS D hD hAffine (W k) s₂))
    (coversTop_stageChart B S hS D hD hAffine hW s₂) (stageGlueModule B S hS D hD hAffine hU hC)
    (isFrame_stageGlueModule B S hS D hD hAffine hU hC) E
    (e' := fun k a ↦ res (sval E) (stageToLim B S hS D hc hD hAffine (W k) s₂) (e k a))
    (fun k ↦ (he k).restrict (stageToLim B S hS D hc hD hAffine (W k) s₂))
    (coversTop_stageLimChart B S hS D hc hD hAffine hW s₂)
    (P := fun k l ↦ laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)
    (p₁ := fun k l ↦ (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (p₂ := fun k l ↦ (sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))
    (stage_lift_limit B S hS D hc hD hAffine W s₂)
    (fun k l a b ↦ ?_)
    (stage_lift B S hS D hD hAffine W s₂)
  have H := stageGlueModule_hcoord B S hS D hc hD hAffine W d x E he hx hU hC k l a b
  convert H using 3

omit [Fintype K] in
include hZ hQc hQs in
/-- A module with frames on the base changes of finitely many charts descends to a stage. -/
theorem exists_stage_model_of_frames [Finite K]
    (hWqc : ∀ k, IsQuasiCompactSpace B S hS (yoneda.obj (W k).obj.left))
    (hWqs : ∀ k, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (W k).obj.left))
    (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1
      (limitAlgebraicSpace B S hS D hc hD hAffine).2)
    {n : K → ℕ}
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hc hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k)) :
    ∃ (s : Over j) (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD s.left).1
        (stageAlgebraicSpace B S hS D hD s.left).2),
      (∀ k, ∃ e' : Fin (n k) → (sval M).obj (op (laterStageChart B S hS D hD hAffine (W k) s)),
        IsFrame (sval M) e') ∧
      Nonempty (E ≅ (modulePullback B S hS
        (limitProjection B S hS D hc hD hAffine s.left)).obj M) := by
  classical
  have := Fintype.ofFinite K
  have hPqc : ∀ k l, IsQuasiCompactSpace B S hS
      (yoneda.obj (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l)).obj.left) := fun k l ↦
    isQuasiCompactSpace_prodObj hZ (hD j) (hQs j) (hWqc k) (hWqc l)
  have hPqs : ∀ k l, IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l)).obj.left) := fun k l ↦
    isAbsolutelyQuasiSeparated_prodObj hZ (hD j) (hWqs k) (hWqs l)
  obtain ⟨s₁, x, hx⟩ := exists_common_stage_matrix B S hS hZ D hc hD hAffine hQc hQs n
    (fun k l ↦ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) hPqc hPqs (limMatrix B S hS D hc hD hAffine W E he)
  obtain ⟨sᵤ, dᵤ, hdᵤ⟩ := exists_common_stage_eq_family B S hS hZ D hc hD hAffine hQc
    hQs (fun k ↦ Fin (n k) × Fin (n k)) W hWqc hWqs
    (fun k c ↦ gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
      (x k k c.1 c.2))
    (fun k c ↦ if c.1 = c.2 then 1 else 0) (fun k c ↦ by
      refine (gpb_limToStage_map_eq B S hS D hc hD hAffine _ s₁ _ _ (hx k k c.1 c.2)).trans
        ((limMatrix_diag B S hS D hc hD hAffine W E he k c.1 c.2).trans ?_)
      split_ifs <;> simp)
  obtain ⟨s_c, d_c, hd_c⟩ := exists_common_stage_eq_triple B S hS hZ D hc hD hAffine
    hQc hQs (fun k _ m ↦ Fin (n k) × Fin (n m)) (fun k l m ↦ SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (fun k l m ↦ isQuasiCompactSpace_prodObj hZ (hD j) (hQs j) (hWqc _) (hPqc _ _))
    (fun k l m ↦ isAbsolutelyQuasiSeparated_prodObj hZ (hD j) (hWqs _) (hPqs _ _))
    (fun k l m c ↦ ∑ z,
      gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₂ B S hS D hD W k l m)).hom.left
        (x k l c.1 z) *
      gpb ((sbs B S hS D hD hAffine s₁).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
            B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))).hom.left
        (x l m z c.2))
    (fun k l m c ↦
      gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
        (x k m c.1 c.2)) (fun k l m c ↦ by
      refine (map_sum _ _ _).trans ?_
      refine Eq.trans ?_ ((limMatrix_cocycle B S hS D hc hD hAffine W E he
        k l m c.1 c.2).trans ?_)
      · refine Finset.sum_congr rfl (fun z _ ↦ ?_)
        exact (map_mul _ _ _).trans (congrArg₂ (· * ·)
          (gpb_limToStage_map_eq B S hS D hc hD hAffine _ s₁ _ _ (hx _ _ _ _))
          (gpb_limToStage_map_eq B S hS D hc hD hAffine _ s₁ _ _ (hx _ _ _ _)))
      · exact (gpb_limToStage_map_eq B S hS D hc hD hAffine _ s₁ _ _ (hx _ _ _ _)).symm)
  obtain ⟨s₂, d, e₁, e₂, hdu, hdc⟩ : ∃ (s₂ : Over j) (d : s₂ ⟶ s₁) (e₁ : s₂ ⟶ sᵤ) (e₂ : s₂ ⟶ s_c),
      e₁ ≫ dᵤ = d ∧ e₂ ≫ d_c = d := by
    obtain ⟨c⟩ := IsCofiltered.cone_nonempty (cospan dᵤ d_c)
    exact ⟨c.pt, c.π.app WalkingCospan.one, c.π.app WalkingCospan.left,
      c.π.app WalkingCospan.right, c.w WalkingCospan.Hom.inl, c.w WalkingCospan.Hom.inr⟩
  have hunit : ∀ k (a b : Fin (n k)), gpb (stageToStage B S hS D hD hAffine (W k) d)
      (gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (x k k a b)) =
      gpb (stageToStage B S hS D hD hAffine (W k) d) (if a = b then 1 else 0) := fun k a b ↦
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
          (x k m a b)) := fun k l m a b ↦
    gpb_stageToStage_eq_of_comp B S hS D hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) d_c e₂ hdc (hd_c k l m (a, b))
  have hU := stageGlueData_unit B S hS D hD hAffine W d x hunit
  have hC := stageGlueData_cocycle B S hS D hD hAffine W d x hcoc
  exact ⟨s₂, stageGlueModule B S hS D hD hAffine hU hC,
    fun k ↦ ⟨_, isFrame_stageGlueModule B S hS D hD hAffine hU hC k⟩,
    nonempty_iso_stageGlueModule B S hS D hc hD hAffine W d x hW E he hx hU hC⟩

end Descent

end AlgebraicGeometry.Space.IsCutoffBoundedSystem

end
