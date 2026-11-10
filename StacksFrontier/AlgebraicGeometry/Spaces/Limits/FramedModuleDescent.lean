module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StageChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFramePullbackComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TransitionMatrixGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# A module with frames on base-changed charts descends to a stage

Let `X = lim Xᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated algebraic
spaces with affine transition morphisms, and let `W k` be a finite family of affine étale charts
of a stage `X_j`, jointly surjective on points.  Let `E` be an `𝒪_X`-module with frames over the
base changes `W k ×_{X_j} X`.  Then at some later stage `X_s` there is an `𝒪_{X_s}`-module `M`
with frames of the same sizes over the base changes `W k ×_{X_j} X_s`, such that `E ≅ f_s^* M`.

The transition matrices between the frames of `E`, regular functions on the base changes of the
products `W k ×_{X_j} W l`, descend to a stage, together with the identity and cocycle relations
they satisfy, by Stacks 0CP4 for the affine line
(`AlgebraicGeometry.Space.exists_gpb_limToStage_eq` and
`AlgebraicGeometry.Space.exists_gpb_stageToStage_eq`); `M` is glued from them
(`Stacks.SheafOfModules.ChartFrames.GlueData.module`), and the comparison with `E` is
`AlgebraicGeometry.Space.nonempty_iso_modulePullback_of_frames`.

## Main results

* `AlgebraicGeometry.Space.exists_stage_model_of_frames`: a module with frames on the base changes
  of finitely many jointly surjective charts of a stage is the pullback of a module with frames at
  a later stage.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal Stacks.SheafOfModules.ChartFrames

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

section QcqsProd

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F) {A A' : SmallEtale B S hS F}

include hF hFqs in
/-- The product of two quasi-compact étale objects over a quasi-separated algebraic space is
quasi-compact. -/
theorem isQuasiCompactSpace_prodObj (hA : IsQuasiCompactSpace B S hS (yoneda.obj A.obj.left))
    (hA' : IsQuasiCompactSpace B S hS (yoneda.obj A'.obj.left)) :
    IsQuasiCompactSpace B S hS (yoneda.obj (SmallEtale.prodObj B S hS F A A').obj.left) :=
  isQuasiCompactSpace_of_iso B S hS (A.property.rep.isPullback A'.obj.hom).isoPullback.symm
    (isQuasiCompactSpace_pullback B S hS hZ _ _ (isAlgebraicSpace_yoneda B S hS _) hF hA hA' hFqs)

include hF in
/-- The product of two quasi-separated étale objects over an algebraic space is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_prodObj
    (hA : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj A.obj.left))
    (hA' : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj A'.obj.left)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (SmallEtale.prodObj B S hS F A A').obj.left) :=
  isAbsolutelyQuasiSeparated_of_iso B S hS hZ (isAlgebraicSpace_yoneda B S hS _)
    (A.property.rep.isPullback A'.obj.hom).isoPullback
    (isAbsolutelyQuasiSeparated_pullback B S hS hZ _ _ (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _) hF hA hA')

end QcqsProd

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  {j : I}

include hSize hHomSize hQc hQs in
/-- A finite family of regular functions on base changes to the limit comes from one stage. -/
theorem exists_common_stage {ι : Type} [Finite ι] (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left))
    (y : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hSize hHomSize hD hAffine (T i)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤)),
      ∀ i, gpb (limToStage B S hS D hSize hHomSize hD hAffine (T i) s) (x i) = y i := by
  have := Fintype.ofFinite ι
  choose s₀ x₀ hx₀ using fun i => exists_gpb_limToStage_eq B S hS D hSize hHomSize hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (y i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (Discrete.functor s₀)
  refine ⟨c.pt, fun i => gpb (stageToStage B S hS D hD hAffine (T i) (c.π.app ⟨i⟩)) (x₀ i),
    fun i => ?_⟩
  rw [← gpb_comp, limToStage_stageToStage]
  exact hx₀ i

include hSize hHomSize hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, holding
on the base changes to the limit, holds at a later stage. -/
theorem exists_common_stage_eq {ι : Type} [Finite ι]
    (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i, gpb (limToStage B S hS D hSize hHomSize hD hAffine (T i) s) (x₁ i) =
      gpb (limToStage B S hS D hSize hHomSize hD hAffine (T i) s) (x₂ i)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i) := by
  classical
  have := Fintype.ofFinite ι
  choose s₀ d₀ hd₀ using fun i => exists_gpb_stageToStage_eq B S hS D hSize hHomSize hD hAffine
    (T i) hZ hQc hQs (hTqc i) (hTqs i) (x₁ i) (x₂ i) (h i)
  obtain ⟨c⟩ := IsCofiltered.cone_nonempty (WidePullbackShape.wideCospan s s₀ d₀)
  refine ⟨c.pt, c.π.app none, fun i => ?_⟩
  have hw : c.π.app (some i) ≫ d₀ i = c.π.app none := c.w (WidePullbackShape.Hom.term i)
  rw [← hw, stageToStage_comp, gpb_comp, gpb_comp, hd₀]

include hSize hHomSize hQc hQs in
/-- A finite family of matrices of regular functions on base changes to the limit comes from one
stage. -/
theorem exists_common_stage_matrix {K : Type} [Finite K] (n : K → ℕ)
    (T : K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l, IsQuasiCompactSpace B S hS (yoneda.obj (T k l).obj.left))
    (hTqs : ∀ k l, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l).obj.left))
    (y : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hSize hHomSize hD hAffine (T k l)).obj.left, ⊤)) :
    ∃ (s : Over j) (x : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine (T k l) s).obj.left, ⊤)),
      ∀ k l a b, gpb (limToStage B S hS D hSize hHomSize hD hAffine (T k l) s) (x k l a b) =
        y k l a b := by
  obtain ⟨s, x, hx⟩ := exists_common_stage B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    (ι := Σ p : K × K, Fin (n p.1) × Fin (n p.2)) (fun i => T i.1.1 i.1.2)
    (fun i => hTqc _ _) (fun i => hTqs _ _) (fun i => y i.1.1 i.1.2 i.2.1 i.2.2)
  exact ⟨s, fun k l a b => x ⟨(k, l), (a, b)⟩, fun k l a b => hx ⟨(k, l), (a, b)⟩⟩

include hSize hHomSize hQc hQs in
/-- A finite family of equations between regular functions on base changes to a stage, indexed
over a finite family of charts, holding on the base changes to the limit, holds at a later
stage. -/
theorem exists_common_stage_eq_family {ι : Type} [Finite ι] (κ : ι → Type)
    [∀ i, Finite (κ i)] (T : ι → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ i, IsQuasiCompactSpace B S hS (yoneda.obj (T i).obj.left))
    (hTqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T i).obj.left)) {s : Over j}
    (x₁ x₂ : ∀ i, κ i → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T i) s).obj.left, ⊤))
    (h : ∀ i c, gpb (limToStage B S hS D hSize hHomSize hD hAffine (T i) s) (x₁ i c) =
      gpb (limToStage B S hS D hSize hHomSize hD hAffine (T i) s) (x₂ i c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ i c,
      gpb (stageToStage B S hS D hD hAffine (T i) d) (x₁ i c) =
        gpb (stageToStage B S hS D hD hAffine (T i) d) (x₂ i c) := by
  obtain ⟨s', d, hd⟩ := exists_common_stage_eq B S hS hZ D hSize hHomSize hD hAffine hQc hQs
    (ι := Σ i, κ i) (fun p => T p.1) (fun p => hTqc _) (fun p => hTqs _)
    (fun p => x₁ p.1 p.2) (fun p => x₂ p.1 p.2) (fun p => h p.1 p.2)
  exact ⟨s', d, fun i c => hd ⟨i, c⟩⟩

include hSize hHomSize hQc hQs in
/-- `AlgebraicGeometry.Space.exists_common_stage_eq_family` for a family of charts indexed by
triples. -/
theorem exists_common_stage_eq_triple {K : Type} [Finite K]
    (κ : K → K → K → Type) [∀ k l m, Finite (κ k l m)]
    (T : K → K → K → SmallEtale B S hS (D.obj j))
    (hTqc : ∀ k l m, IsQuasiCompactSpace B S hS (yoneda.obj (T k l m).obj.left))
    (hTqs : ∀ k l m, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T k l m).obj.left))
    {s : Over j} (x₁ x₂ : ∀ k l m, κ k l m → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (T k l m) s).obj.left, ⊤))
    (h : ∀ k l m c, gpb (limToStage B S hS D hSize hHomSize hD hAffine (T k l m) s) (x₁ k l m c) =
      gpb (limToStage B S hS D hSize hHomSize hD hAffine (T k l m) s) (x₂ k l m c)) :
    ∃ (s' : Over j) (d : s' ⟶ s), ∀ k l m c,
      gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₁ k l m c) =
        gpb (stageToStage B S hS D hD hAffine (T k l m) d) (x₂ k l m c) := by
  obtain ⟨s', d, hd⟩ := exists_common_stage_eq_family B S hS hZ D hSize hHomSize hD hAffine hQc
    hQs (fun p : K × K × K => κ p.1 p.2.1 p.2.2) (fun p => T p.1 p.2.1 p.2.2)
    (fun p => hTqc _ _ _) (fun p => hTqs _ _ _) (fun p => x₁ p.1 p.2.1 p.2.2)
    (fun p => x₂ p.1 p.2.1 p.2.2) (fun p => h p.1 p.2.1 p.2.2)
  exact ⟨s', d, fun k l m c => hd (k, l, m) c⟩

omit [IsCofiltered I] in
/-- An equation between regular functions on a stage persists to every later stage. -/
theorem gpb_stageToStage_eq_of_comp (T : SmallEtale B S hS (D.obj j)) {s s' s'' : Over j}
    (d : s' ⟶ s) (e : s'' ⟶ s') {d' : s'' ⟶ s} (h : e ≫ d = d')
    {y₁ y₂ : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T
        s).obj.left, ⊤)}
    (hy : gpb (stageToStage B S hS D hD hAffine T d) y₁ =
      gpb (stageToStage B S hS D hD hAffine T d) y₂) :
    gpb (stageToStage B S hS D hD hAffine T d') y₁ =
      gpb (stageToStage B S hS D hD hAffine T d') y₂ := by
  subst h
  rw [stageToStage_comp, gpb_comp, gpb_comp, hy]

/-! ### Products of the charts -/

section Products

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)

/-- The diagonal of a chart. -/
def stageChartDiagonal (k : K) :
    W k ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W k) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      k)).lift (BinaryFan.mk (𝟙 _) (𝟙 _))

omit [IsCofiltered I] in
/-- The diagonal of a chart followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem stageChartDiagonal_fst (k : K) :
    stageChartDiagonal B S hS D hD W k ≫
      SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W k) = 𝟙 _ :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      k)).fac _ ⟨WalkingPair.left⟩

omit [IsCofiltered I] in
/-- The diagonal of a chart followed by the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem stageChartDiagonal_snd (k : K) :
    stageChartDiagonal B S hS D hD W k ≫
      SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W k) = 𝟙 _ :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      k)).fac _ ⟨WalkingPair.right⟩

/-- The projection of a triple product to the product of its first two factors. -/
def tripPair₁₂ (k l m : K) : SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
    k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
    m)) ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l)).lift (BinaryFan.mk
    (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S
        hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S
        hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)) ≫ SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))

/-- The projection of a triple product to the product of its first and last factors. -/
def tripPair₁₃ (k l m : K) : SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
    k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
    m)) ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W m) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      m)).lift (BinaryFan.mk
    (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S
        hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S
        hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)) ≫ SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))

omit [IsCofiltered I] in
/-- The first projection of `tripPair₁₂` is the first projection of the triple product. -/
@[reassoc (attr := simp)]
theorem tripPair₁₂_fst (k l m : K) :
    tripPair₁₂ B S hS D hD W k l m ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W l) =
      SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B
          S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l)).fac _ ⟨WalkingPair.left⟩

omit [IsCofiltered I] in
/-- The second projection of `tripPair₁₂` is the projection of the triple product to its second
factor. -/
@[reassoc (attr := simp)]
theorem tripPair₁₂_snd (k l m : K) :
    tripPair₁₂ B S hS D hD W k l m ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W l) =
      SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B
          S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m)) ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l)).fac _ ⟨WalkingPair.right⟩

omit [IsCofiltered I] in
/-- The first projection of `tripPair₁₃` is the first projection of the triple product. -/
@[reassoc (attr := simp)]
theorem tripPair₁₃_fst (k l m : K) :
    tripPair₁₃ B S hS D hD W k l m ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W m) =
      SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B
          S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      m)).fac _ ⟨WalkingPair.left⟩

omit [IsCofiltered I] in
/-- The second projection of `tripPair₁₃` is the projection of the triple product to its third
factor. -/
@[reassoc (attr := simp)]
theorem tripPair₁₃_snd (k l m : K) :
    tripPair₁₃ B S hS D hD W k l m ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W m) =
      SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B
          S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m)) ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m) :=
  (SmallEtale.prodIsLimit B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      m)).fac _ ⟨WalkingPair.right⟩

end Products

/-! ### The transition matrices of a module with frames on the base changes -/

section LimitMatrices

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
    (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
  {n : K → ℕ} {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hSize hHomSize hD hAffine
      (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

/-- Base change to the limit. -/
abbrev sbl :=
  smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine j)
    (rep_limitProjection B S hS D hSize hHomSize hD hAffine j)

/-- The transition matrices of the frames of `E`, on the base changes of the products. -/
def limMatrix (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    Γ((BigFppfOver.toScheme B S hS).obj
      (limChart B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace
          B S hS D hD j).1 (W k) (W l))).obj.left, ⊤) :=
  trans he ((sbl B S hS D hSize hHomSize hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
    ((sbl B S hS D hSize hHomSize hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (W l))) a b

/-- Pulling a transition matrix back along `g` gives the transition matrix of the composites. -/
theorem gpb_trans {T T' : SmallEtale B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD
    hAffine).1}
    (g : T' ⟶ T) {k l : K}
    (α : T ⟶ limChart B S hS D hSize hHomSize hD hAffine (W k))
    (β : T ⟶ limChart B S hS D hSize hHomSize hD hAffine (W l)) (a : Fin (n k)) (b : Fin (n l)) :
    gpb g.hom.left (trans he α β a b) = trans he (g ≫ α) (g ≫ β) a b :=
  trans_res he g α β a b
/-- Pulling the transition matrix of two charts back along the base change of `u` gives the
transition matrix of the base changes of its components. -/
private theorem gpb_limMatrix_of_comp {P : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1}
    {k l : K} (u : P ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
    {α : P ⟶ W k} {β : P ⟶ W l}
    (hα : u ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = α)
    (hβ : u ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = β)
    (a : Fin (n k)) (b : Fin (n l)) :
    gpb ((sbl B S hS D hSize hHomSize hD hAffine).map u).hom.left
        (limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a b) =
      trans he ((sbl B S hS D hSize hHomSize hD hAffine).map α)
        ((sbl B S hS D hSize hHomSize hD hAffine).map β) a b := by
  subst hα hβ
  rw [limMatrix, gpb_trans, Functor.map_comp, Functor.map_comp]

/-- The transition matrix of a frame with itself restricts to the identity matrix on the diagonal.
-/
theorem limMatrix_diag (k : K) (a b : Fin (n k)) :
    gpb ((sbl B S hS D hSize hHomSize hD hAffine).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (limMatrix B S hS D hSize hHomSize hD hAffine W E he k k a b) =
      if a = b then 1 else 0 := by
  rw [gpb_limMatrix_of_comp B S hS D hSize hHomSize hD hAffine W E he _
    (stageChartDiagonal_fst B S hS D hD W k) (stageChartDiagonal_snd B S hS D hD W k),
    CategoryTheory.Functor.map_id]
  exact trans_self he _ a b

/-- The transition matrices `limMatrix` satisfy the cocycle relation on the base change of a
triple product. -/
theorem limMatrix_cocycle (k l m : K) (a : Fin (n k)) (b : Fin (n m)) :
    ∑ x, gpb ((sbl B S hS D hSize hHomSize hD hAffine).map (tripPair₁₂ B S hS D hD W k l
        m)).hom.left
        (limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a x) *
      gpb ((sbl B S hS D hSize hHomSize hD hAffine).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
            B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))).hom.left
        (limMatrix B S hS D hSize hHomSize hD hAffine W E he l m x b) =
    gpb ((sbl B S hS D hSize hHomSize hD hAffine).map (tripPair₁₃ B S hS D hD W k l m)).hom.left
        (limMatrix B S hS D hSize hHomSize hD hAffine W E he k m a b) := by
  refine Eq.trans ?_ (gpb_limMatrix_of_comp B S hS D hSize hHomSize hD hAffine W E he _
    (tripPair₁₃_fst B S hS D hD W k l m) (tripPair₁₃_snd B S hS D hD W k l m) a b).symm
  refine Eq.trans ?_ (trans_comp he _
    ((sbl B S hS D hSize hHomSize hD hAffine).map (SmallEtale.prodSnd B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)) ≫ SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) _ a b)
  exact Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·)
    (gpb_limMatrix_of_comp B S hS D hSize hHomSize hD hAffine W E he _
      (tripPair₁₂_fst B S hS D hD W k l m) (tripPair₁₂_snd B S hS D hD W k l m) a x)
    (gpb_limMatrix_of_comp B S hS D hSize hHomSize hD hAffine W E he _ rfl rfl x b)

end LimitMatrices

/-! ### Moving functions along base changes of chart morphisms -/

section Moving

variable {T T' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1} (h : T ⟶ T')

/-- Base change to a stage. -/
abbrev sbs (s : Over j) :=
  smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom)

/-- Pulling back to the limit commutes with pulling back along the base change of a chart
morphism. -/
theorem gpb_limToStage_map (s : Over j)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤)) :
    gpb (limToStage B S hS D hSize hHomSize hD hAffine T s)
        (gpb ((sbs B S hS D hD hAffine s).map h).hom.left y) =
      gpb ((sbl B S hS D hSize hHomSize hD hAffine).map h).hom.left
        (gpb (limToStage B S hS D hSize hHomSize hD hAffine T' s) y) :=
  (gpb_comp _ _ y).symm.trans ((congrArg (fun g => gpb g y)
    (limToStage_naturality B S hS D hSize hHomSize hD hAffine h s).symm).trans (gpb_comp _ _ y))

/-- If the pullback of `y` to the limit is `m`, then the pullback of `y` along a chart morphism, to
the limit, is the pullback of `m` along its base change to the limit. -/
private theorem gpb_limToStage_map_of_eq (s : Over j)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤)) {m : Γ((BigFppfOver.toScheme B S hS).obj
        (limChart B S hS D hSize hHomSize hD hAffine T').obj.left, ⊤)}
    (hy : gpb (limToStage B S hS D hSize hHomSize hD hAffine T' s) y = m) :
    gpb (limToStage B S hS D hSize hHomSize hD hAffine T s)
        (gpb ((sbs B S hS D hD hAffine s).map h).hom.left y) =
      gpb ((sbl B S hS D hSize hHomSize hD hAffine).map h).hom.left m := by
  rw [gpb_limToStage_map, hy]

omit [IsCofiltered I] in
/-- Pulling back to a later stage commutes with pulling back along the base change of a chart
morphism. -/
theorem gpb_stageToStage_map {s s' : Over j} (d : s' ⟶ s)
    (y : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T' s).obj.left,
        ⊤)) :
    gpb (stageToStage B S hS D hD hAffine T d) (gpb ((sbs B S hS D hD hAffine s).map h).hom.left
        y) =
      gpb ((sbs B S hS D hD hAffine s').map h).hom.left
        (gpb (stageToStage B S hS D hD hAffine T' d) y) :=
  (gpb_comp _ _ y).symm.trans ((congrArg (fun g => gpb g y)
    (stageToStage_naturality B S hS D hD hAffine h d).symm).trans (gpb_comp _ _ y))

end Moving

/-! ### The glueing data at a stage -/

section StageGlue

variable {K : Type} [Fintype K] (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)

/-- The base change of a product of charts to a stage is a product. -/
def stageProdIsLimit (s : Over j) (A A' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1) :
    IsLimit (BinaryFan.mk ((sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 A A'))
      ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
          j).1 A A'))) :=
  BinaryFan.isLimitMk
    (fun c => prodLift (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom) c.fst c.snd)
    (fun _ => prodLift_fst _ _ _ _) (fun _ => prodLift_snd _ _ _ _)
    (fun _ _ h₁ h₂ => prod_hom_ext _ _ (h₁.trans (prodLift_fst _ _ _ _).symm)
      (h₂.trans (prodLift_snd _ _ _ _).symm))

/-- The glueing data at a stage, from matrices on the base changes of the products of the
charts. -/
def stageGlueData (s : Over j) (n : K → ℕ)
    (g : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (W l)) s).obj.left, ⊤)) :
    GlueData (structureSheaf B S hS (stageAlgebraicSpace B S hS D hD s.left).1
      (stageAlgebraicSpace B S hS D hD s.left).2) K where
  W k := laterStageChart B S hS D hD hAffine (W k) s
  n := n
  P k l := laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
      hS D hD j).1 (W k) (W l)) s
  p₁ k l := (sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS
      D hD j).1 (W k) (W l))
  p₂ k l := (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS
      D hD j).1 (W k) (W l))
  isLimit k l := stageProdIsLimit B S hS D hD hAffine s (W k) (W l)
  g := g

variable {W} (s : Over j) (n : K → ℕ)
  (g : ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj
      (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (W l)) s).obj.left, ⊤))

omit [IsCofiltered I] in
/-- The first projections of `stageGlueData` are the base changes of the product projections. -/
theorem stageGlueData_p₁ (k l : K) : (stageGlueData B S hS D hD hAffine W s n g).p₁ k l =
    (sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W l)) := rfl

omit [IsCofiltered I] in
/-- The second projections of `stageGlueData` are the base changes of the product projections.
-/
theorem stageGlueData_p₂ (k l : K) : (stageGlueData B S hS D hD hAffine W s n g).p₂ k l =
    (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
        j).1 (W k) (W l)) := rfl

omit [IsCofiltered I] in /-- `pairLift` of base changes is a base change. -/ private theorem
    stageGlueData_pairLift_map {A : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD
      j).1} {k l : K} (u : A ⟶ SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1
      (W k) (W l)) {α : A ⟶ W k} {β : A ⟶ W l}
    (hα : u ≫ SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = α)
    (hβ : u ≫ SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l) = β)
    {a : (sbs B S hS D hD hAffine s).obj A ⟶ (stageGlueData B S hS D hD hAffine W s n g).W k}
    {b : (sbs B S hS D hD hAffine s).obj A ⟶ (stageGlueData B S hS D hD hAffine W s n g).W l}
    (ha : (sbs B S hS D hD hAffine s).map α = a) (hb : (sbs B S hS D hD hAffine s).map β = b) :
    (stageGlueData B S hS D hD hAffine W s n g).pairLift a b =
      (sbs B S hS D hD hAffine s).map u :=
  (stageGlueData B S hS D hD hAffine W s n g).pair_ext
    ((GlueData.pairLift_p₁ _ _ _).trans (ha.symm.trans
      ((congrArg (sbs B S hS D hD hAffine s).map hα).symm.trans
        ((sbs B S hS D hD hAffine s).map_comp _ _))))
    ((GlueData.pairLift_p₂ _ _ _).trans (hb.symm.trans
      ((congrArg (sbs B S hS D hD hAffine s).map hβ).symm.trans
        ((sbs B S hS D hD hAffine s).map_comp _ _))))

omit [IsCofiltered I] in
/-- The pair of identities into the product of a chart with itself is the base change of the
diagonal. -/
theorem stageGlueData_pairLift_diag (k : K) :
    (stageGlueData B S hS D hD hAffine W s n g).pairLift (𝟙 ((stageGlueData B S hS D hD hAffine W
        s n g).W k)) (𝟙 ((stageGlueData B S hS D hD hAffine W s n g).W k)) = (sbs B S hS D hD
        hAffine s).map (stageChartDiagonal B S hS D hD W k) :=
  stageGlueData_pairLift_map B S hS D hD hAffine s n g _ (stageChartDiagonal_fst B S hS D hD W k)
    (stageChartDiagonal_snd B S hS D hD W k) (CategoryTheory.Functor.map_id _ _)
    (CategoryTheory.Functor.map_id _ _)

omit [IsCofiltered I] in
/-- The pair of the projections of a triple product to its first two factors is the base change of
`tripPair₁₂`. -/
theorem stageGlueData_pairLift₁₂ (k l m : K) :
    (stageGlueData B S hS D hD hAffine W s n g).pairLift ((sbs B S hS D hD hAffine s).map
        (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
        B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))))
      ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
          j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m))) ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B
          S hS D hD j).1 (W l) (W m))) =
      (sbs B S hS D hD hAffine s).map (tripPair₁₂ B S hS D hD W k l m) :=
  stageGlueData_pairLift_map B S hS D hD hAffine s n g _ (tripPair₁₂_fst B S hS D hD W k l m)
    (tripPair₁₂_snd B S hS D hD W k l m) rfl (CategoryTheory.Functor.map_comp _ _ _)

omit [IsCofiltered I] in
/-- The pair of the projections of a triple product to its last two factors is the base change of
the second projection. -/
theorem stageGlueData_pairLift₂₃ (k l m : K) :
    (stageGlueData B S hS D hD hAffine W s n g).pairLift ((sbs B S hS D hD hAffine s).map
        (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
        B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) ≫ (sbs B S hS D hD hAffine
        s).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
      ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
          j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m))) ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B
          S hS D hD j).1 (W l) (W m))) =
      (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
          j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m))) :=
  stageGlueData_pairLift_map B S hS D hD hAffine s n g _ rfl rfl
    (CategoryTheory.Functor.map_comp _ _ _) (CategoryTheory.Functor.map_comp _ _ _)

omit [IsCofiltered I] in
/-- The pair of the projections of a triple product to its first and last factors is the base
change of `tripPair₁₃`. -/
theorem stageGlueData_pairLift₁₃ (k l m : K) :
    (stageGlueData B S hS D hD hAffine W s n g).pairLift ((sbs B S hS D hD hAffine s).map
        (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
        B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))))
      ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
          j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m))) ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B
          S hS D hD j).1 (W l) (W m))) =
      (sbs B S hS D hD hAffine s).map (tripPair₁₃ B S hS D hD W k l m) :=
  stageGlueData_pairLift_map B S hS D hD hAffine s n g _ (tripPair₁₃_fst B S hS D hD W k l m)
    (tripPair₁₃_snd B S hS D hD W k l m) rfl (CategoryTheory.Functor.map_comp _ _ _)

omit [IsCofiltered I] in
/-- Three morphisms into the charts of `stageGlueData` lift to the base change of the triple
product. -/
theorem stageGlueData_triple_lift (k l m : K)
    {T : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD s.left).1}
    (a : T ⟶ (stageGlueData B S hS D hD hAffine W s n g).W k) (b : T ⟶ (stageGlueData B S hS D hD
        hAffine W s n g).W l) (c : T ⟶ (stageGlueData B S hS D hD hAffine W s n g).W m) :
    ∃ t : T ⟶ laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
        l) (W m))) s,
      t ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D
          hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W
          m))) = a ∧
      t ≫ ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodFst B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) = b ∧
      t ≫ ((sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) ≫ (sbs B S hS D hD hAffine s).map (SmallEtale.prodSnd B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) = c := by
  obtain ⟨u, hu₁, hu₂⟩ := BinaryFan.IsLimit.lift' ((stageGlueData B S hS D hD hAffine W s n
      g).isLimit l m) b c
  obtain ⟨t, ht₁, ht₂⟩ := BinaryFan.IsLimit.lift'
    (stageProdIsLimit B S hS D hD hAffine s (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W l) (W m))) a u
  exact ⟨t, ht₁, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht₂).trans hu₁),
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht₂).trans hu₂)⟩

end StageGlue

/-- `stageToLim` is natural in the chart: it commutes with the base changes of a chart morphism
`h` to the stage and to the limit. -/
theorem stageToLim_naturality_sbs {T T' : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1}
    (h : T ⟶ T') (s : Over j) :
    (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s.left)).map
        ((sbs B S hS D hD hAffine s).map h) ≫ stageToLim B S hS D hSize hHomSize hD hAffine T' s =
      stageToLim B S hS D hSize hHomSize hD hAffine T s ≫
        (sbl B S hS D hSize hHomSize hD hAffine).map h :=
  stageToLim_naturality B S hS D hSize hHomSize hD hAffine h s

/-! ### The coordinates of the frames of `E` on the base changes of a later stage -/

section Comparison

variable {K : Type} (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1)
  (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
    (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
  {n : K → ℕ}
  {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hSize hHomSize hD hAffine (W k)))}
  (he : ∀ k, IsFrame (sval E) (e k))

/-- A descended transition matrix, moved to a later stage and pulled back to the limit, is the
transition matrix of the frames of `E` along the composites with `stageToLim`. -/
theorem gpb_sbcProj_stageToStage_eq_trans {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K)
    (a : Fin (n k)) (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a b) :
    gpb (sbcProj (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) (rep_limitProjection
        B S hS D hSize hHomSize hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      trans he ((stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hSize hHomSize
          hD hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) ((stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hSize hHomSize
          hD hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l)))) a b := by
  have e5 : (stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂).hom.left ≫ limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁ =
      sbcProj (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) (rep_limitProjection B
          S hS D hSize hHomSize hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
          (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫
        stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D
            hD j).1 (W k) (W l)) d :=
    (congrArg (_ ≫ ·) (limToStage_stageToStage B S hS D hSize hHomSize hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) d)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (stageToLim_limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
            (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)))
  refine (gpb_comp _ _ x).symm.trans ?_
  refine (congrArg (fun t => gpb t x) e5.symm).trans ?_
  refine (gpb_comp _ _ x).trans ?_
  refine (congrArg (gpb (stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂).hom.left) hx).trans ?_
  exact gpb_trans B S hS D hSize hHomSize hD hAffine W E he (stageToLim B S hS D hSize hHomSize hD
      hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
      s₂) ((sbl B S hS D hSize hHomSize hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) ((sbl B S hS D hSize hHomSize hD
      hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) a b

/-- Restricting a frame of `E` along `stageToLim` and then along the second projection is
restricting it along the composite. -/
theorem res_stageToLim_prodSnd {s₂ : Over j} (k l : K) (b : Fin (n l)) :
    res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
        s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W l) s₂) (e l
        b)) =
      res (sval E) ((stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ (sbl B S hS D hSize hHomSize hD
          hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
          l))) (e l b) :=
  (res_comp _ _ _ _).symm.trans (congrArg (fun t => res (sval E) t (e l b))
    (stageToLim_naturality_sbs B S hS D hSize hHomSize hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))

/-- The transition matrix of the frames of `E` along the composites with `stageToLim` is given by
the coordinates of the frames restricted along `stageToLim`. -/
theorem trans_stageToLim_eq_coord_restrict {s₂ : Over j} (k l : K) (a : Fin (n k))
    (b : Fin (n l)) :
    trans he ((stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hSize hHomSize hD
        hAffine).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) ((stageToLim B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂) ≫ ((sbl B S hS D hSize hHomSize hD
        hAffine).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))) a b =
      ((he k).restrict (stageToLim B S hS D hSize hHomSize hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
          s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
            s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W l)
            s₂) (e l b))) a := by
  refine Eq.trans ?_ (congrFun (IsFrame.coord_restrict (he k) (stageToLim B S hS D hSize hHomSize
      hD hAffine (W k) s₂)
    ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l))))
    (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
        s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S
        hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1
        (W k) (W l)))) (res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W l) s₂) (e l
        b)))) a).symm
  have e3 : (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
      (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S hS D hD
      hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
      l))) ≫ (stageToLim B S hS D hSize hHomSize hD hAffine (W k) s₂) = (stageToLim B S hS D hSize
      hHomSize hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
      (W l)) s₂) ≫ (sbl B S hS D hSize hHomSize hD hAffine).map (SmallEtale.prodFst B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) :=
    stageToLim_naturality_sbs B S hS D hSize hHomSize hD hAffine (T := (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂
  change (he k).coord _ _ a = (he k).coord _ _ a
  rw [res_stageToLim_prodSnd B S hS D hSize hHomSize hD hAffine W E k l b, e3]

/-- The coordinates of the frames of `E`, restricted to the base changes of a later stage, are the
pullbacks of descended transition matrices. -/
theorem coord_restrict_stageToLim {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (k l : K) (a : Fin (n k))
    (b : Fin (n l))
    (x : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₁).obj.left, ⊤))
    (hx : gpb (limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) x =
      limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a b) :
    gpb (sbcProj (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) (rep_limitProjection
        B S hS D hSize hHomSize hD hAffine s₂.left) (laterStageChart B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂))
        (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (W l)) d) x) =
      ((he k).restrict (stageToLim B S hS D hSize hHomSize hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
          s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
            s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W l)
            s₂) (e l b))) a :=
  (gpb_sbcProj_stageToStage_eq_trans B S hS D hSize hHomSize hD hAffine W E he d k l a b x hx).trans
    (trans_stageToLim_eq_coord_restrict B S hS D hSize hHomSize hD hAffine W E he k l a b)

end Comparison

/-! ### The descent -/

section Descent

variable {K : Type} [Fintype K] [DecidableEq K]
  (W : K → SmallEtale B S hS (stageAlgebraicSpace B S hS D hD j).1) {n : K → ℕ}

/-- The sheaf condition of the structure sheaf of an algebraic space, on underlying sets. -/
theorem isSheaf_structureSheaf_forget (X : AlgebraicSpaces B S hS) :
    Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      ((structureSheaf B S hS X.1 X.2).obj ⋙ CategoryTheory.forget CommRingCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (structureSheaf B S hS X.1 X.2).property)

/-- Matrices of regular functions on the base changes of the products to a stage, moved to a
later stage. -/
def descMatrix {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (x : ∀ k l, Fin (n k) → Fin (n l) →
    Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B
    S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁).obj.left, ⊤)) :
    ∀ k l, Fin (n k) → Fin (n l) → Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D
        hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₂).obj.left, ⊤) :=
  fun k l a b => gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) d) (x k l a b)

variable {s₁ s₂ : Over j} (d : s₂ ⟶ s₁) (x : ∀ k l, Fin (n k) → Fin (n l) →
    Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B
    S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁).obj.left, ⊤))

omit [DecidableEq K] [IsCofiltered I] in
/-- If the descended matrices restrict to the identity on the diagonals at a later stage, the
glueing data there satisfies the unit condition. -/
theorem stageGlueData_unit
    (hunit : ∀ k (a b : Fin (n k)), gpb (stageToStage B S hS D hD hAffine (W k) d)
      (gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (x k k a b)) =
      gpb (stageToStage B S hS D hD hAffine (W k) d) (if a = b then 1 else 0)) :
    (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d x)).Unit := by
  refine GlueData.unit_of_diag _ (fun k a b => ?_)
  have hp := stageGlueData_pairLift_diag B S hS D hD hAffine s₂ n (descMatrix B S hS D hD hAffine
      W d x) k
  rw [hp]
  refine (gpb_stageToStage_map B S hS D hD hAffine (stageChartDiagonal B S hS D hD W k) d
    (x k k a b)).symm.trans ((hunit k a b).trans ?_)
  by_cases h : a = b
  · exact (congrArg (gpb (stageToStage B S hS D hD hAffine (W k) d)) (ite_eq_left h)).trans
      ((map_one _).trans (ite_eq_left h).symm)
  · exact (congrArg (gpb (stageToStage B S hS D hD hAffine (W k) d)) (ite_eq_right h)).trans
      ((map_zero _).trans (ite_eq_right h).symm)

omit [DecidableEq K] [IsCofiltered I] in
/-- If the descended matrices satisfy the cocycle relation at a later stage, the glueing data
there satisfies the cocycle condition. -/
theorem stageGlueData_cocycle
    (hcoc : ∀ k l m (a : Fin (n k)) (b : Fin (n m)),
      gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) d) (∑ z,
        gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₂ B S hS D hD W k l m)).hom.left (x k l a
            z) *
        gpb ((sbs B S hS D hD hAffine s₁).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S
            hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
            l) (W m)))).hom.left
          (x l m z b)) =
      gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS
          D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l)
          (W m))) d)
        (gpb ((sbs B S hS D hD hAffine s₁).map (tripPair₁₃ B S hS D hD W k l m)).hom.left (x k m a
            b))) :
    (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d x)).Cocycle := by
  refine GlueData.cocycle_of_triple _
    (fun k l m => laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) s₂)
    (fun k l m => (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
        l) (W m))))
    (fun k l m => (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
        l) (W m))) ≫ (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (fun k l m => (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W
        l) (W m))) ≫ (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m)))
    (fun k l m T a b c => stageGlueData_triple_lift B S hS D hD hAffine s₂ n (descMatrix B S hS D
        hD hAffine W d x) k l m a b c)
    (fun k l m a b => ?_)
  have h12 := stageGlueData_pairLift₁₂ B S hS D hD hAffine s₂ n (descMatrix B S hS D hD hAffine W
      d x) k l m
  have h23 := stageGlueData_pairLift₂₃ B S hS D hD hAffine s₂ n (descMatrix B S hS D hD hAffine W
      d x) k l m
  have h13 := stageGlueData_pairLift₁₃ B S hS D hD hAffine s₂ n (descMatrix B S hS D hD hAffine W
      d x) k l m
  dsimp only [GlueData.gAt]
  rw [h12, h23, h13]
  refine (Finset.sum_congr rfl fun z _ => congrArg₂ (· * ·)
    (gpb_stageToStage_map B S hS D hD hAffine (tripPair₁₂ B S hS D hD W k l m) d
      (x k l a z)).symm
    (gpb_stageToStage_map B S hS D hD hAffine
      (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B
          S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) d (x l m z b)).symm).trans ?_
  refine Eq.trans ?_ (gpb_stageToStage_map B S hS D hD hAffine (tripPair₁₃ B S hS D hD W k l m) d
    (x k m a b))
  refine Eq.trans ?_ (hcoc k l m a b)
  exact ((map_sum (gpb (stageToStage B S hS D hD hAffine (SmallEtale.prodObj B S hS
      (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS (stageAlgebraicSpace
      B S hS D hD j).1 (W l) (W m))) d)) _ _).trans
    (Finset.sum_congr rfl fun z _ => map_mul (gpb (stageToStage B S hS D hD hAffine
        (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj
        B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) d)) _ _)).symm

variable {W d x} in
/-- The glued module at a later stage. -/
def stageGlueModule (_hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD
    hAffine W d x)).Unit) (_hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD
    hAffine W d x)).Cocycle) :
    Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD s₂.left).1 (stageAlgebraicSpace B S hS
        D hD s₂.left).2 :=
  (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
      x)).module (isSheaf_structureSheaf_forget B S hS (stageAlgebraicSpace B S hS D hD s₂.left))

variable {W d x}

/-- The frames of the glued module. -/
def stageGlueFrame (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
    W d x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
    W d x)).Cocycle) (k : K) :
    Fin (n k) → (sval (stageGlueModule B S hS D hD hAffine hU hC)).obj (op (laterStageChart B S hS
        D hD hAffine (W k) s₂)) :=
  (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d x)).frame' hC k

omit [DecidableEq K] [IsCofiltered I] in
/-- `stageGlueFrame` is a frame of the glued module. -/
theorem isFrame_stageGlueModule (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS
    D hD hAffine W d x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS
    D hD hAffine W d x)).Cocycle) (k : K) :
    IsFrame (sval (stageGlueModule B S hS D hD hAffine hU hC)) (stageGlueFrame B S hS D hD hAffine
        hU hC k) :=
  (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
      x)).isFrame_frame' hU hC k

omit [DecidableEq K] [IsCofiltered I] in
/-- The transition matrices of the frames of the glued module are the descended matrices. -/
theorem stageGlueModule_coord (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D
    hD hAffine W d x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D
    hD hAffine W d x)).Cocycle) (k l : K) (a : Fin (n k))
    (b : Fin (n l)) :
    (isFrame_stageGlueModule B S hS D hD hAffine hU hC k).coord ((sbs B S hS D hD hAffine s₂).map
        (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
        (res (sval (stageGlueModule B S hS D hD hAffine hU hC)) ((sbs B S hS D hD hAffine s₂).map
            (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
            (stageGlueFrame B S hS D hD hAffine hU hC l b)) a =
      descMatrix B S hS D hD hAffine W d x k l a b :=
  (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
      x)).coord_res_p₂_frame' hU hC k l b a

omit [Fintype K] [DecidableEq K] in
/-- The comparison map of a small base change, on global sections of a chart, is pullback along
the projection. -/
theorem smallBaseChangeSharp_app_eq_gpb {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (z : Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)) :
    ((smallBaseChangeSharp B S hS f hf).hom.app (op V)).hom z = gpb (sbcProj f hf V) z :=
  rfl

omit [Fintype K] [DecidableEq K] in
variable (W) in
/-- A pair of morphisms into the base changes to the limit of two charts lifts to the base change
of their product. -/
theorem stage_lift_limit (s₂ : Over j) (V : SmallEtale B S hS
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1) (k l : K)
    (h : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (W k) s₂)) (h' : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D
        hSize hHomSize hD hAffine s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine
        s₂.left)).obj (laterStageChart B S hS D hD hAffine (W l) s₂)) :
    ∃ t : V ⟶ (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).obj (laterStageChart B S
        hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) s₂),
      t ≫ (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
          (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S hS D hD
          hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
          (W l))) = h ∧ t ≫ (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD
          hAffine s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine
          s₂.left)).map ((sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS
          (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) = h' := by
  obtain ⟨t, ht₁, ht₂⟩ := BinaryFan.IsLimit.lift' (isLimitSmallBaseChangeOfIsLimit
      (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) (rep_limitProjection B S hS D
      hSize hHomSize hD hAffine s₂.left)
    (stageProdIsLimit B S hS D hD hAffine s₂ (W k) (W l))) h h'
  exact ⟨t, ht₁, ht₂⟩

omit [Fintype K] [DecidableEq K] [IsCofiltered I] in
variable (W) in
/-- A pair of morphisms into the base changes to a stage of two charts lifts to the base change of
their product. -/
theorem stage_lift (s₂ : Over j) (V : SmallEtale B S hS (stageAlgebraicSpace B S hS D hD s₂.left).1)
    (k l : K) (h : V ⟶ (laterStageChart B S hS D hD hAffine (W k) s₂)) (h' : V ⟶ (laterStageChart
        B S hS D hD hAffine (W l) s₂)) :
    ∃ t : V ⟶ (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace
        B S hS D hD j).1 (W k) (W l)) s₂), t ≫ (sbs B S hS D hD hAffine
        s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) = h ∧ t ≫ (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) = h' := by
  obtain ⟨t, ht₁, ht₂⟩ := BinaryFan.IsLimit.lift'
    (stageProdIsLimit B S hS D hD hAffine s₂ (W k) (W l)) h h'
  exact ⟨t, ht₁, ht₂⟩

variable (W d x) in
omit [DecidableEq K] in
/-- The transition matrices of the frames of the glued module, pulled back to the limit, are the
coordinates of the restricted frames of `E`. -/
theorem stageGlueModule_hcoord
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hSize hHomSize hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) (k l : K) (a : Fin (n k)) (b : Fin (n l)) :
    ((smallBaseChangeSharp B S hS (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).hom.app (op
        (laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S
        hS D hD j).1 (W k) (W l)) s₂))).hom
        ((isFrame_stageGlueModule B S hS D hD hAffine hU hC k).coord ((sbs B S hS D hD hAffine
            s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)))
          (res (sval (stageGlueModule B S hS D hD hAffine hU hC)) ((sbs B S hS D hD hAffine
              s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
              l))) (stageGlueFrame B S hS D hD hAffine hU hC l b)) a) =
      ((he k).restrict (stageToLim B S hS D hSize hHomSize hD hAffine (W k)
          s₂)).coord ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
          s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B S
          hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS (stageAlgebraicSpace B S hS D hD j).1
          (W k) (W l))))
        (res (sval E) ((smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
            s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).map ((sbs B
            S hS D hD hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD
            j).1 (W k) (W l)))) (res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W l)
            s₂) (e l b))) a :=
  (smallBaseChangeSharp_app_eq_gpb B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
      s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) _ _).trans
    ((congrArg (gpb (sbcProj (limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
        (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left) (laterStageChart B S hS D
        hD hAffine (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))
        s₂)))
      (stageGlueModule_coord B S hS D hD hAffine hU hC k l a b)).trans
    (coord_restrict_stageToLim B S hS D hSize hHomSize hD hAffine W E he d k l a b (x k l a b)
      (hx k l a b)))

omit [Fintype K] [DecidableEq K] [IsCofiltered I] in
/-- The base changes of jointly surjective charts to a stage cover it. -/
theorem coversTop_stageChart (hW : PointsCover W) (s₂ : Over j) :
    (SmallEtale.topology B S hS (stageAlgebraicSpace B S hS D hD s₂.left).1).CoversTop
      (fun k => (laterStageChart B S hS D hD hAffine (W k) s₂)) :=
  coversTop_of_pointsCover (pointsCover_smallBaseChange (stageTransition B S hS D hD s₂.hom)
    (rep_stageTransition B S hS D hD hAffine s₂.hom) hW)

omit [Fintype K] [DecidableEq K] in
/-- The base changes to the limit of the base changes of jointly surjective charts to a stage cover
it. -/
theorem coversTop_stageLimChart (hW : PointsCover W) (s₂ : Over j) :
    (SmallEtale.topology B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD
        hAffine).1).CoversTop
      (fun k => (smallBaseChange B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
          s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)).obj
          (laterStageChart B S hS D hD hAffine (W k) s₂)) :=
  coversTop_of_pointsCover (pointsCover_smallBaseChange (limitProjection B S hS D hSize hHomSize
      hD hAffine s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
    (pointsCover_smallBaseChange (stageTransition B S hS D hD s₂.hom)
      (rep_stageTransition B S hS D hD hAffine s₂.hom) hW))

variable (W d x) in
omit [DecidableEq K] in
/-- **The glued module pulls back to `E`.** -/
theorem nonempty_iso_stageGlueModule (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hSize hHomSize hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k))
    (hx : ∀ k l a b, gpb (limToStage B S hS D hSize hHomSize hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₁) (x k l a b) =
      limMatrix B S hS D hSize hHomSize hD hAffine W E he k l a b)
    (hU : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine W d
        x)).Unit) (hC : (stageGlueData B S hS D hD hAffine W s₂ n (descMatrix B S hS D hD hAffine
        W d x)).Cocycle) :
    Nonempty (E ≅ (modulePullback B S hS (limitProjection B S hS D hSize hHomSize hD hAffine
        s₂.left)).obj (stageGlueModule B S hS D hD hAffine hU hC)) := by
  refine nonempty_iso_modulePullback_of_frames (limitProjection B S hS D hSize hHomSize hD hAffine
      s₂.left) (rep_limitProjection B S hS D hSize hHomSize hD hAffine s₂.left)
    (W := fun k => (laterStageChart B S hS D hD hAffine (W k) s₂))
    (coversTop_stageChart B S hS D hD hAffine hW s₂) (stageGlueModule B S hS D hD hAffine hU hC)
    (isFrame_stageGlueModule B S hS D hD hAffine hU hC) E
    (e' := fun k a => res (sval E) (stageToLim B S hS D hSize hHomSize hD hAffine (W k) s₂) (e k a))
    (fun k => (he k).restrict (stageToLim B S hS D hSize hHomSize hD hAffine (W k) s₂))
    (coversTop_stageLimChart B S hS D hSize hHomSize hD hAffine hW s₂)
    (P := fun k l => laterStageChart B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l)) s₂)
    (p₁ := fun k l => (sbs B S hS D hD hAffine s₂).map (SmallEtale.prodFst B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (W l))) (p₂ := fun k l => (sbs B S hS D hD
        hAffine s₂).map (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)))
    (stage_lift_limit B S hS D hSize hHomSize hD hAffine W s₂)
    (fun k l a b => ?_)
    (stage_lift B S hS D hD hAffine W s₂)
  have H := stageGlueModule_hcoord B S hS D hSize hHomSize hD hAffine W d x E he hx hU hC k l a b
  convert H using 3

omit [Fintype K] [DecidableEq K] in
include hZ hQc hQs in
/-- **A module with frames on the base changes of finitely many charts descends to a stage.** -/
theorem exists_stage_model_of_frames [Finite K]
    (hWqc : ∀ k, IsQuasiCompactSpace B S hS (yoneda.obj (W k).obj.left))
    (hWqs : ∀ k, IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (W k).obj.left))
    (hW : PointsCover W)
    (E : Modules.{u, u} B S hS (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2)
    {n : K → ℕ}
    {e : ∀ k, Fin (n k) → (sval E).obj (op (limChart B S hS D hSize hHomSize hD hAffine (W k)))}
    (he : ∀ k, IsFrame (sval E) (e k)) :
    ∃ (s : Over j) (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD s.left).1
        (stageAlgebraicSpace B S hS D hD s.left).2),
      (∀ k, ∃ e' : Fin (n k) → (sval M).obj (op (laterStageChart B S hS D hD hAffine (W k) s)),
        IsFrame (sval M) e') ∧
      Nonempty (E ≅ (modulePullback B S hS
        (limitProjection B S hS D hSize hHomSize hD hAffine s.left)).obj M) := by
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
  obtain ⟨s₁, x, hx⟩ := exists_common_stage_matrix B S hS hZ D hSize hHomSize hD hAffine hQc hQs n
    (fun k l => SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k) (W
        l)) hPqc hPqs (limMatrix B S hS D hSize hHomSize hD hAffine W E he)
  obtain ⟨sᵤ, dᵤ, hdᵤ⟩ := exists_common_stage_eq_family B S hS hZ D hSize hHomSize hD hAffine hQc
    hQs (fun k => Fin (n k) × Fin (n k)) W hWqc hWqs
    (fun k c => gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
      (x k k c.1 c.2))
    (fun k c => if c.1 = c.2 then 1 else 0) (fun k c => by
      refine ((gpb_limToStage_map_of_eq B S hS D hSize hHomSize hD hAffine
        (stageChartDiagonal B S hS D hD W k) s₁ _ (hx k k c.1 c.2)).trans
        (limMatrix_diag B S hS D hSize hHomSize hD hAffine W E he k c.1 c.2)).trans ?_
      split_ifs <;> simp)
  obtain ⟨s_c, d_c, hd_c⟩ := exists_common_stage_eq_triple B S hS hZ D hSize hHomSize hD hAffine
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
      refine Eq.trans ?_ ((limMatrix_cocycle B S hS D hSize hHomSize hD hAffine W E he
        k l m c.1 c.2).trans ?_)
      · refine Finset.sum_congr rfl (fun z _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
        · exact gpb_limToStage_map_of_eq B S hS D hSize hHomSize hD hAffine
            (tripPair₁₂ B S hS D hD W k l m) s₁ _ (hx _ _ _ _)
        · exact gpb_limToStage_map_of_eq B S hS D hSize hHomSize hD hAffine
            (SmallEtale.prodSnd B S hS (stageAlgebraicSpace B S hS D hD j).1 (W k)
              (SmallEtale.prodObj B S hS (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) s₁ _
            (hx _ _ _ _)
      · exact (gpb_limToStage_map_of_eq B S hS D hSize hHomSize hD hAffine
          (tripPair₁₃ B S hS D hD W k l m) s₁ _ (hx _ _ _ _)).symm)
  obtain ⟨s₂, d, e₁, e₂, hdu, hdc⟩ : ∃ (s₂ : Over j) (d : s₂ ⟶ s₁) (e₁ : s₂ ⟶ sᵤ) (e₂ : s₂ ⟶ s_c),
      e₁ ≫ dᵤ = d ∧ e₂ ≫ d_c = d := by
    obtain ⟨c⟩ := IsCofiltered.cone_nonempty (cospan dᵤ d_c)
    exact ⟨c.pt, c.π.app WalkingCospan.one, c.π.app WalkingCospan.left,
      c.π.app WalkingCospan.right, c.w WalkingCospan.Hom.inl, c.w WalkingCospan.Hom.inr⟩
  have hunit : ∀ k (a b : Fin (n k)), gpb (stageToStage B S hS D hD hAffine (W k) d)
      (gpb ((sbs B S hS D hD hAffine s₁).map (stageChartDiagonal B S hS D hD W k)).hom.left
        (x k k a b)) =
      gpb (stageToStage B S hS D hD hAffine (W k) d) (if a = b then 1 else 0) := by
    intro k a b
    exact gpb_stageToStage_eq_of_comp B S hS D hD hAffine (W k) dᵤ e₁ hdu (hdᵤ k (a, b))
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
          (x k m a b)) := by
    intro k l m a b
    exact gpb_stageToStage_eq_of_comp B S hS D hD hAffine (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W k) (SmallEtale.prodObj B S hS
        (stageAlgebraicSpace B S hS D hD j).1 (W l) (W m))) d_c e₂ hdc
      (hd_c k l m (a, b))
  have hU := stageGlueData_unit B S hS D hD hAffine W d x hunit
  have hC := stageGlueData_cocycle B S hS D hD hAffine W d x hcoc
  exact ⟨s₂, stageGlueModule B S hS D hD hAffine hU hC,
    fun k => ⟨_, isFrame_stageGlueModule B S hS D hD hAffine hU hC k⟩,
    nonempty_iso_stageGlueModule B S hS D hSize hHomSize hD hAffine W d x hW E he hx hU hC⟩

end Descent

end AlgebraicGeometry.Space
