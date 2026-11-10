module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.ChartHyps

/-!
# The theorem of the cube: normalized sections over a chart

A section of `N` over an open `O ⊆ (A × A) × A` is *normalized* when its pullbacks to the two
faces are the restrictions of the face generators (`Stacks.Cube.NormSec`). Over an affine chart
all of whose fibres are trivial there is exactly one normalized section
(`Stacks.Cube.exists_normSec`, `Stacks.Cube.normSec_unique`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator Stacks.FlatComplexNakayama

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  (N : (P A).Modules)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)

/-- **A normalized section**: its pullbacks to the faces are the face generators. -/
def NormSec (O : (P A).Opens) (s : Γ(N, O)) : Prop :=
  pbS (face₁ A) N O (face₁ A ⁻¹ᵁ O) le_rfl s = resTop _ g₁ _ ∧
    pbS (face₂ A) N O (face₂ A ⁻¹ᵁ O) le_rfl s = resTop _ g₂ _

variable {N}

/-- The restriction of a normalized section to a smaller open is normalized. -/
theorem NormSec.res {O O' : (P A).Opens} (h : O' ≤ O) {s : Γ(N, O)}
    (hs : NormSec N (g₁ := g₁) (g₂ := g₂) O s) :
    NormSec N (g₁ := g₁) (g₂ := g₂) O' (N.presheaf.map (homOfLE h).op s) := by
  refine ⟨?_, ?_⟩
  · rw [pbS_map, ← pbS_res (face₁ A) N O le_rfl (Scheme.Hom.preimage_mono _ h), hs.1, resTop_res]
  · rw [pbS_map, ← pbS_res (face₂ A) N O le_rfl (Scheme.Hom.preimage_mono _ h), hs.2, resTop_res]

/-- The degree-zero Čech cochain of restrictions of a section. -/
noncomputable def resCochain {X : Scheme.{u}} {I : Type u} (W : I → X.Opens) (G : X.Modules)
    {O : X.Opens} (hW : ∀ i, W i ≤ O) (s : Γ(G, O)) :
    ∀ i : Fin 1 → I, Γ(G, CechCochains.inter W i) := fun i =>
  G.presheaf.map (homOfLE ((iInf_le (fun m => W (i m)) 0).trans (hW (i 0)))).op s

/-- Restricting a section along `O₂ ≤ O` and then along `O₁ ≤ O₂` is restricting it along `O₁ ≤ O`.
-/
theorem map_map_eq {X : Scheme.{u}} (G : X.Modules) {O₁ O₂ O : X.Opens} (h₁ : O₁ ≤ O₂)
    (h₂ : O₂ ≤ O) (h : O₁ ≤ O) (s : Γ(G, O)) :
    G.presheaf.map (homOfLE h₁).op (G.presheaf.map (homOfLE h₂).op s) =
      G.presheaf.map (homOfLE h).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- The Čech differential of the cochain of restrictions of a section vanishes. -/
theorem cechD_resCochain {X : Scheme.{u}} {I : Type u} (W : I → X.Opens) (G : X.Modules)
    {O : X.Opens} (hW : ∀ i, W i ≤ O) (s : Γ(G, O)) :
    CechCochains.cechD W G.presheaf 0 (resCochain W G hW s) = 0 := by
  funext i
  rw [cechD_apply', Fin.sum_univ_two]
  have hi : CechCochains.inter W i ≤ O := (iInf_le (fun m => W (i m)) 0).trans (hW (i 0))
  have e : ∀ j : Fin 2, G.presheaf.map (homOfLE (CechCochains.inter_le_omit W i j)).op
      (resCochain W G hW s (i ∘ j.succAbove)) = G.presheaf.map (homOfLE hi).op s :=
    fun j => map_map_eq G _ _ _ s
  rw [e 0, e 1]
  simp

/-! ### Sections over a chart -/

section Chart

variable {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} [Fintype ι] [DecidableEq ι]
  (U : ι → A.left.Opens) {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)

attribute [local instance] faceModule

variable (N) in
/-- The Čech cochain of restrictions of a section over the chart. -/
noncomputable def secCochain (s : Γ(chartModule N V, ⊤)) : CX hV U N 0 :=
  ⟨resCochain (chartCover U V) (chartModule N V) (fun _ => le_top) s,
    isAlternating_zero (chartCover U V) (chartModule N V).presheaf _⟩

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- The cochain of restrictions of a section over the chart is a cocycle. -/
theorem d₀_secCochain (s : Γ(chartModule N V, ⊤)) : d₀ hV U N (secCochain N hV U s) = 0 := by
  apply Subtype.ext
  rw [d_apply_val]
  exact cechD_resCochain (chartCover U V) (chartModule N V) (fun _ => le_top) s

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- `secCochain` is compatible with subtraction of sections. -/
theorem secCochain_sub (s s' : Γ(chartModule N V, ⊤)) :
    secCochain N hV U (s - s') = secCochain N hV U s - secCochain N hV U s' :=
  Subtype.ext <| funext fun _ => map_sub _ _ _

omit [GrpObj A] in
/-- If the pullback of `s` along `b` is the restriction of the generator `g`, then `faceRes` of
every restriction of `s` equals `1`. -/
theorem faceRes_sec {b : B A ⟶ P A} {g : Γ((Scheme.Modules.pullback b).obj N, ⊤)} (hg : IsGen _ g)
    (O : (P A).Opens) (s : Γ(N, O)) (hs : pbS b N O (b ⁻¹ᵁ O) le_rfl s = resTop _ g _)
    (O' : (P A).Opens) (hO : O' ≤ O) (W : (B A).Opens) (hW : W ≤ b ⁻¹ᵁ O') :
    faceRes N b hg O' W hW (N.presheaf.map (homOfLE hO).op s) = 1 := by
  rw [faceRes_map, faceRes_apply, ← pbS_res b N O le_rfl (hW.trans (Scheme.Hom.preimage_mono _ hO)),
    hs, resTop_res, divGen_resTop]

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- If the pullback of `s` along `b` is the restriction of the generator `g`, then `faceMap` sends
the cochain of restrictions of `s` to the constant cochain `1`. -/
theorem faceMap_secCochain {b : B A ⟶ P A} {g : Γ((Scheme.Modules.pullback b).obj N, ⊤)}
    (hg : IsGen _ g) (sel : ι → ι × ι)
    (hsel : ∀ {n : ℕ} (i : Fin n → ι),
      faceOpen V U i ≤ b ⁻¹ᵁ ((PV V).ι ''ᵁ CechCochains.inter (chartCover U V) (sel ∘ i)))
    (s : Γ(chartModule N V, ⊤))
    (hs : pbS b N ((PV V).ι ''ᵁ ⊤) (b ⁻¹ᵁ ((PV V).ι ''ᵁ ⊤)) le_rfl s = resTop _ g _)
    (j : Fin 1 → ι) :
    faceMap N b hg U sel hsel 0 (secCochain N hV U s).1 j = 1 := by
  rw [faceMap_apply]
  exact faceRes_sec hg ((PV V).ι ''ᵁ ⊤) s hs _ (Scheme.Hom.image_mono _ le_top) _ _

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- `faceψ` sends the unit cochain `one U` to the constant cochain `1`. -/
theorem faceψ_one (j : Fin 1 → ι) :
    letI := cochainModule U A.hom 0
    faceψ V U 0 (one U) j = 1 := by
  rw [faceψ_apply]
  exact map_one ((bx A).appLE _ _ _).hom

omit [Fintype ι] [DecidableEq ι] in
/-- `phi₀` sends the cochain of restrictions of a normalized section to `w₁ U`. -/
theorem phi₀_secCochain (s : Γ(chartModule N V, ⊤))
    (hs : NormSec N (g₁ := g₁) (g₂ := g₂) ((PV V).ι ''ᵁ ⊤) s) :
    phi₀ hV U ha₀ N hg₁ hg₂ (secCochain N hV U s) = w₁ U := by
  let := cochainModule U A.hom 0
  refine Prod.ext ?_ ?_
  · funext j
    exact (faceMap_secCochain hV U hg₁ _ (le_face₁ U V ha₀) s hs.1 j).trans (faceψ_one U j).symm
  · funext j
    exact (faceMap_secCochain hV U hg₂ _ (le_face₂ U V ha₀) s hs.2 j).trans (faceψ_one U j).symm

end Chart

/-- Sections of a module agreeing on an open cover agree. -/
theorem sec_ext {X : Scheme.{u}} (G : X.Modules) {I : Type u} (W : I → X.Opens) (O : X.Opens)
    (hW : ∀ i, W i ≤ O) (hcov : O ≤ ⨆ i, W i) (s t : Γ(G, O))
    (h : ∀ i, G.presheaf.map (homOfLE (hW i)).op s = G.presheaf.map (homOfLE (hW i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨G.presheaf, Scheme.Modules.isSheaf G⟩ : TopCat.Sheaf Ab X) W O
    (fun i => homOfLE (hW i)) hcov s t h

section Chart2

variable {V : A.left.Opens} (hV : IsAffineOpen V) {ι : Type u} [Fintype ι] [DecidableEq ι]
  {U : ι → A.left.Opens} {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)

attribute [local instance] faceModule

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- If `U` covers `A`, the preimage under a face `b` of the image of the chart is covered by the
opens `faceOpen V U (fun _ => c)`. -/
theorem face_cover (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a) {b : B A ⟶ P A}
    (hb : b ≫ r A = bz A) :
    b ⁻¹ᵁ ((PV V).ι ''ᵁ ⊤) ≤ ⨆ c : ι, faceOpen V U (fun _ : Fin 1 => c) := by
  intro x hx
  have hxV : bz A x ∈ V := by
    rw [Scheme.Opens.ι_image_top] at hx
    change (b ≫ r A) x ∈ V at hx
    rwa [hb] at hx
  have h1 : bx A x ∈ (⨆ a, U a) := by rw [← hUcov]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, (mem_inter U _ _).mpr fun _ => hc, hxV⟩

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- Each open `faceOpen V U (fun _ => c)` lies in the preimage under the face `b` of the image of
the chart. -/
theorem face_le {b : B A ⟶ P A} (hb : b ≫ r A = bz A) (c : ι) :
    faceOpen V U (fun _ : Fin 1 => c) ≤ b ⁻¹ᵁ ((PV V).ι ''ᵁ ⊤) := by
  intro x hx
  rw [Scheme.Opens.ι_image_top]
  change (b ≫ r A) x ∈ V
  rw [hb]
  exact hx.2

omit [GrpObj A] in
/-- If `faceRes` of `s` on `W` equals `1`, then on `W` the pullback of `s` along `b` agrees with
the restriction of the generator `g`. -/
theorem pbS_eq_of_faceRes {b : B A ⟶ P A} {g : Γ((Scheme.Modules.pullback b).obj N, ⊤)}
    (hg : IsGen _ g) (O : (P A).Opens) (W : (B A).Opens) (hW : W ≤ b ⁻¹ᵁ O) (s : Γ(N, O))
    (h : faceRes N b hg O W hW s = 1) :
    ((Scheme.Modules.pullback b).obj N).presheaf.map (homOfLE hW).op
        (pbS b N O (b ⁻¹ᵁ O) le_rfl s) =
      ((Scheme.Modules.pullback b).obj N).presheaf.map (homOfLE hW).op
        (resTop _ g (b ⁻¹ᵁ O)) := by
  refine (pbS_res b N O le_rfl hW s).trans (Eq.trans ?_ (resTop_res hW).symm)
  rw [faceRes_apply, divGen_eq_iff, one_smul] at h
  exact h.symm

/-- If `faceRes` of `s` is `1` on each `faceOpen V U (fun _ => c)`, the pullback of `s` along the
face `b` is the restriction of the generator `g`. -/
private theorem pbS_eq_resTop_of_faceRes {k : Type u} [Field k] {A : Over (Spec (.of k))}
    {N : (P A).Modules} {V : A.left.Opens} {ι : Type u} {U : ι → A.left.Opens} {b : B A ⟶ P A}
    {g : Γ((Scheme.Modules.pullback b).obj N, ⊤)} (hg : IsGen _ g) (hb : b ≫ r A = bz A)
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a) (s : Γ(N, (PV V).ι ''ᵁ ⊤))
    (h : ∀ c : ι,
      faceRes N b hg ((PV V).ι ''ᵁ ⊤) (faceOpen V U fun _ : Fin 1 => c) (face_le hb c) s = 1) :
    pbS b N ((PV V).ι ''ᵁ ⊤) (b ⁻¹ᵁ ((PV V).ι ''ᵁ ⊤)) le_rfl s = resTop _ g _ := by
  refine sec_ext _ _ _ (fun c => face_le hb c) (face_cover hUcov hb) _ _ fun c => ?_
  exact pbS_eq_of_faceRes hg _ _ _ s (h c)

omit [Fintype ι] [DecidableEq ι] in
/-- From a cocycle mapping to the constant face cocycle, a normalized section. -/
theorem normSec_of_cocycle (h : ChartHyp hV U N) (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (y : CX hV U N 0) (hy : d₀ hV U N y = 0) (hφ : phi₀ hV U ha₀ N hg₁ hg₂ y = w₁ U) :
    ∃ s : Γ(N, (PV V).ι ''ᵁ ⊤), NormSec N (g₁ := g₁) (g₂ := g₂) ((PV V).ι ''ᵁ ⊤) s ∧
      secCochain N hV U s = y := by
  let := cochainModule U A.hom 0
  have hy' : CechCochains.cechD (chartCover U V) (chartModule N V).presheaf 0 y.1 = 0 := by
    rw [← d_apply_val, hy]
    rfl
  obtain ⟨s, hs⟩ := exists_section_of_cechD_eq_zero (chartCover U V) (chartModule N V) h.cov
    y.1 hy'
  have hsy : secCochain N hV U s = y := Subtype.ext (funext hs)
  subst hsy
  exact ⟨s, ⟨pbS_eq_resTop_of_faceRes hg₁ face₁_r hUcov s fun c =>
      (faceRes_map N _ hg₁ (Scheme.Hom.image_mono _ le_top) _ _ s).symm.trans
        ((congrFun (congrArg Prod.fst hφ) fun _ => c).trans (faceψ_one U _)),
    pbS_eq_resTop_of_faceRes hg₂ face₂_r hUcov s fun c =>
      (faceRes_map N _ hg₂ (Scheme.Hom.image_mono _ le_top) _ _ s).symm.trans
        ((congrFun (congrArg Prod.snd hφ) fun _ => c).trans (faceψ_one U _))⟩, rfl⟩

end Chart2

end Stacks.Cube

end
