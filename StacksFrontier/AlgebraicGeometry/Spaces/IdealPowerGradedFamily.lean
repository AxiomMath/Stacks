module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.CategoryTheory.Abelian.CommutingFamilyTwistVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# The graded pieces `IⁿF/Iⁿ⁺¹F` as a commuting family

Let `X` be an algebraic space, `I ⊆ 𝒪_X` a sheaf of ideals and `F` an `𝒪_X`-module.  Global
functions `a₁, …, a_r` of `X` lying in `I` act on the graded pieces `IⁿF/Iⁿ⁺¹F` by maps of degree
one which commute: a `Stacks.CommutingFamily`, the shape of the graded module
`⊕ₙ IⁿF/Iⁿ⁺¹F` over the polynomial ring in the `aᵢ`.  When the `aᵢ` generate `I` on the affine
étale charts of `X`, this family is generated in degree `0`.

This is the graded module `⊕ 𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ` of the proof of Stacks 0D39, which "is generated in
degree zero" over `Gr_𝔪(A)`; the generators of `𝔪` act through the structure morphism.

## Main definitions

* `AlgebraicGeometry.Space.idealPowGradedPiece`: `IⁿF/Iⁿ⁺¹F`.
* `AlgebraicGeometry.Space.idealPowSmulHom`: multiplication by a global function of `I`,
  `IⁿF ⟶ Iⁿ⁺¹F`.
* `AlgebraicGeometry.Space.idealPowGradedFamily`: the commuting family.

## Main results

* `AlgebraicGeometry.Space.idealPowSmul_succ_eq_idealSmul`: `Iⁿ⁺¹ N = I (Iⁿ N)`.
* `AlgebraicGeometry.Space.eq_zero_of_comp_idealSmulHom_eq_zero`: the multiplications by local
  generators are jointly epimorphic onto `I N`.
* `AlgebraicGeometry.Space.generatedFrom_idealPowGradedFamily`: the family is generated in
  degree `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules (globalSmul)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **`Iⁿ⁺¹ N = I · (Iⁿ N)`**, the factor of the ideal split off on the left; the base
`Stacks.Sites.idealPowSmul_succ` splits it off on the right. -/
theorem idealPowSmul_succ_eq_idealSmul (I : IdealSheaves B S hS X.1 X.2)
    {M : Modules.{u, u} B S hS X.1 X.2} (n : ℕ) (N : M.Submodule) :
    Stacks.Sites.idealPowSmul (M := M) I (n + 1) N =
      Stacks.Sites.idealSmul (M := M) I (Stacks.Sites.idealPowSmul (M := M) I n N) := by
  induction n generalizing N with
  | zero =>
    exact (Stacks.Sites.idealPowSmul_one (M := M) I N).trans
      (congrArg _ (Stacks.Sites.idealPowSmul_zero (M := M) I N).symm)
  | succ n ih =>
    exact (Stacks.Sites.idealPowSmul_succ (M := M) I (n + 1) N).trans ((ih _).trans
      (congrArg _ (Stacks.Sites.idealPowSmul_succ (M := M) I n N).symm))

/-! ### Multiplication by a global function of the ideal -/

section Smul

variable (I : IdealSheaves B S hS X.1 X.2)
  (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
  (ha : ∀ W : SmallEtale B S hS X.1, a.1 (op W) ∈ I.obj (op W))
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **Multiplication by a global function of `I`, from `N` to `I N`.** -/
def idealSmulHom (N : M.Submodule) (P : M.Submodule)
    (hP : Stacks.Sites.idealSmul I N ≤ P) : N.toSheafOfModules ⟶ P.toSheafOfModules :=
  P.factorThru (N.ι ≫ globalSmul _ a M) fun W x => hP W
    (Stacks.Sites.smul_mem_idealSmul I (ha W.unop) x.2)

/-- `idealSmulHom I a ha N P hP` followed by the inclusion of `P` is the inclusion of `N` followed
by multiplication by `a`. -/
@[reassoc (attr := simp)]
theorem idealSmulHom_ι (N P : M.Submodule) (hP : Stacks.Sites.idealSmul I N ≤ P) :
    idealSmulHom I a ha N P hP ≫ P.ι = N.ι ≫ globalSmul _ a M :=
  P.factorThru_ι _ _

/-- On sections, `idealSmulHom I a ha N P hP` sends `x` to `a • x`. -/
theorem idealSmulHom_val_app (N P : M.Submodule) (hP : Stacks.Sites.idealSmul I N ≤ P)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : N.toSheafOfModules.val.obj W) :
    ((idealSmulHom I a ha N P hP).val.app W x).1 = a.1 W • x.1 :=
  rfl

/-- Multiplication by `a` commutes with the inclusions `N₁ ≤ N₂` and `P₁ ≤ P₂`. -/
theorem homOfLE_comp_idealSmulHom {N₁ N₂ P₁ P₂ : M.Submodule} (hN : N₁ ≤ N₂) (hPP : P₁ ≤ P₂)
    (hP₁ : Stacks.Sites.idealSmul I N₁ ≤ P₁) (hP₂ : Stacks.Sites.idealSmul I N₂ ≤ P₂) :
    Stacks.SheafOfModules.Submodule.homOfLE hN ≫ idealSmulHom I a ha N₂ P₂ hP₂ =
      idealSmulHom I a ha N₁ P₁ hP₁ ≫ Stacks.SheafOfModules.Submodule.homOfLE hPP := by
  rw [← cancel_mono P₂.ι, Category.assoc, Category.assoc, idealSmulHom_ι,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι, idealSmulHom_ι,
    Stacks.SheafOfModules.Submodule.homOfLE_comp_ι_assoc]

/-- Multiplications by two global functions `a`, `b` of `I` commute: `N₁ ⟶ N₂ ⟶ N₃` by `a` then `b`
equals `b` then `a`. -/
theorem idealSmulHom_comm (b : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (hb : ∀ W : SmallEtale B S hS X.1, b.1 (op W) ∈ I.obj (op W)) {N₁ N₂ N₃ : M.Submodule}
    (h₁ : Stacks.Sites.idealSmul I N₁ ≤ N₂) (h₂ : Stacks.Sites.idealSmul I N₂ ≤ N₃) :
    idealSmulHom I a ha N₁ N₂ h₁ ≫ idealSmulHom I b hb N₂ N₃ h₂ =
      idealSmulHom I b hb N₁ N₂ h₁ ≫ idealSmulHom I a ha N₂ N₃ h₂ := by
  rw [← cancel_mono N₃.ι, Category.assoc, Category.assoc, idealSmulHom_ι, idealSmulHom_ι,
    idealSmulHom_ι_assoc, idealSmulHom_ι_assoc, Stacks.Cohomology.SiteModules.comp_globalSmul]

end Smul

/-! ### Joint surjectivity onto `I N` -/

/-- **Multiplications by local generators of `I` are jointly epimorphic onto `I N`.**  Let
`a₁, …, a_r` be global functions of `X` in `I` which generate `I(A)` as a left ideal on every
affine étale chart `A`.  A morphism out of `I N` which vanishes after each multiplication
`aᵢ : N ⟶ I N` is zero. -/
theorem eq_zero_of_comp_idealSmulHom_eq_zero (I : IdealSheaves B S hS X.1 X.2) {r : ℕ}
    (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W))
    (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (a i).1 (op A))
    {M : Modules.{u, u} B S hS X.1 X.2} (N P : M.Submodule)
    (hP : Stacks.Sites.idealSmul I N = P) {Q : Modules.{u, u} B S hS X.1 X.2}
    (h : P.toSheafOfModules ⟶ Q) (hh : ∀ i, idealSmulHom I (a i) (ha i) N P hP.le ≫ h = 0) :
    h = 0 := by
  subst hP
  have key : ∀ (A : (smallEtaleRingedSite B S hS X.1 X.2).C),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ x, x ∈ (Stacks.Sites.presheafIdealSmul I N.toSubmodule).obj (op A) →
      ∀ hx : x ∈ (Stacks.Sites.idealSmul I N).obj (op A),
        h.val.app (op A) ⟨x, hx⟩ = 0 := by
    intro A hA x hx
    have hmem : ∀ {y}, y ∈ (Stacks.Sites.presheafIdealSmul I N.toSubmodule).obj (op A) →
        y ∈ (Stacks.Sites.idealSmul I N).obj (op A) := fun hy =>
      Stacks.SheafOfModules.le_sheafifySubmodule _ (op A) hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, m, hm, rfl⟩ := hx
      intro hx'
      obtain ⟨c, rfl⟩ := hgen A hA b hb
      have hsum : (⟨(∑ i, c i * (a i).1 (op A)) • m, hx'⟩ :
          (Stacks.Sites.idealSmul I N).toSheafOfModules.val.obj (op A)) =
          ∑ i, c i • (idealSmulHom I (a i) (ha i) N _ le_rfl).val.app (op A) ⟨m, hm⟩ := by
        refine (fun y z (hyz : ((Stacks.Sites.idealSmul I N).ι.val.app (op A)) y =
          ((Stacks.Sites.idealSmul I N).ι.val.app (op A)) z) => Subtype.ext hyz) _ _ ?_
        rw [map_sum]
        simp only [map_smul]
        have hι : ∀ i, ((Stacks.Sites.idealSmul I N).ι.val.app (op A))
            ((idealSmulHom I (a i) (ha i) N _ le_rfl).val.app (op A) ⟨m, hm⟩) =
              (a i).1 (op A) • m := fun i => rfl
        simp only [hι]
        show (∑ i, c i * (a i).1 (op A)) • m = _
        rw [Finset.sum_smul]
        simp only [mul_smul]
      rw [hsum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul]
      have h0 : h.val.app (op A) ((idealSmulHom I (a i) (ha i) N _ le_rfl).val.app (op A)
          ⟨m, hm⟩) = 0 := by
        have := congrArg (fun φ => φ.val.app (op A) ⟨m, hm⟩) (hh i)
        exact this
      rw [h0, smul_zero]
    | zero =>
      intro hx
      exact (congrArg (h.val.app (op A))
        (rfl : (⟨0, hx⟩ : (Stacks.Sites.idealSmul I N).toSheafOfModules.val.obj (op A)) = 0)).trans
        (map_zero _)
    | add x y hx hy ihx ihy =>
      intro hxy
      exact (map_add (h.val.app (op A)).hom ⟨x, hmem hx⟩ ⟨y, hmem hy⟩).trans
        (by rw [ihx (hmem hx), ihy (hmem hy), add_zero])
    | smul c x hx ih =>
      intro hcx
      exact (map_smul (h.val.app (op A)).hom c ⟨x, hmem hx⟩).trans
        (by rw [ih (hmem hx), smul_zero])
  refine SheafOfModules.hom_ext ?_
  ext W y
  obtain ⟨S₁, hS₁, h₁⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule y.2
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hS₁ fun V g hg => ?_
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _
    (coverByImage_affineEtaleInclusion_mem B S hS X.1 X.2 V) fun V' g' hg' => ?_
  obtain ⟨⟨A', g₁, g₂, hfac⟩⟩ := hg'
  have hz : Q.val.map g₂.op (Q.val.map g.op (h.val.app W y)) = 0 := by
    have e1 := PresheafOfModules.naturality_apply h.val g.op y
    have e2 := PresheafOfModules.naturality_apply h.val g₂.op
      ((Stacks.Sites.idealSmul I N).toSheafOfModules.val.map g.op y)
    exact (congrArg _ e1.symm).trans (e2.symm.trans (key _ A'.2 _
      ((Stacks.Sites.presheafIdealSmul I N.toSubmodule).map g₂.op (h₁ g hg)) _))
  subst hfac
  have e3 : Q.val.map (g₁ ≫ g₂).op (Q.val.map g.op (h.val.app W y)) =
      Q.val.map g₁.op (Q.val.map g₂.op (Q.val.map g.op (h.val.app W y))) :=
    PresheafOfModules.map_comp_apply Q.val g₂.op g₁.op _
  exact e3.trans ((congrArg _ hz).trans (map_zero _))

/-! ### The graded pieces and the commuting family -/

section Graded

variable (I : IdealSheaves B S hS X.1 X.2) (F : Modules.{u, u} B S hS X.1 X.2)

/-- `I (Iⁿ F) = Iⁿ⁺¹ F`. -/
theorem idealSmul_idealPowSubmodule (n : ℕ) :
    Stacks.Sites.idealSmul I (idealPowSubmodule I n F) = idealPowSubmodule I (n + 1) F :=
  (idealPowSmul_succ_eq_idealSmul I n ⊤).symm

/-- **The graded piece `IⁿF/Iⁿ⁺¹F`.** -/
abbrev idealPowGradedPiece (n : ℕ) : Modules.{u, u} B S hS X.1 X.2 :=
  cokernel (Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I n F))

/-- The projection `IⁿF ⟶ IⁿF/Iⁿ⁺¹F`. -/
abbrev idealPowGradedπ (n : ℕ) :
    (idealPowSubmodule I n F).toSheafOfModules ⟶ idealPowGradedPiece I F n :=
  cokernel.π _

/-- **The sections of `I` kill the graded pieces.** -/
theorem smul_idealPowGradedPiece_eq_zero (n : ℕ) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (b : (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj W) (hb : b ∈ I.obj W)
    (g : (idealPowGradedPiece I F n).val.obj W) : b • g = 0 :=
  Stacks.Sites.smul_cokernel_homOfLE_eq_zero (X := smallEtaleRingedSite B S hS X.1 X.2) I
    (idealPowSubmodule_succ_le I n F) (idealSmul_idealPowSubmodule I F n).le W b hb g

variable (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
  (ha : ∀ W : SmallEtale B S hS X.1, a.1 (op W) ∈ I.obj (op W))

/-- Multiplication by a global function of `I`, `IⁿF ⟶ Iⁿ⁺¹F`. -/
abbrev idealPowSmulHom (n : ℕ) :
    (idealPowSubmodule I n F).toSheafOfModules ⟶ (idealPowSubmodule I (n + 1) F).toSheafOfModules :=
  idealSmulHom I a ha _ _ (idealSmul_idealPowSubmodule I F n).le

/-- Multiplication by `a` commutes with the inclusions `Iⁿ⁺¹F ≤ IⁿF` and `Iⁿ⁺²F ≤ Iⁿ⁺¹F`. -/
theorem homOfLE_comp_idealPowSmulHom (n : ℕ) :
    Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I n F) ≫
        idealPowSmulHom I F a ha n =
      idealPowSmulHom I F a ha (n + 1) ≫
        Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I (n + 1) F) :=
  homOfLE_comp_idealSmulHom I a ha _ _ _ _

/-- **Multiplication by a global function of `I` on the graded pieces**,
`IⁿF/Iⁿ⁺¹F ⟶ Iⁿ⁺¹F/Iⁿ⁺²F`. -/
def idealPowGradedSmul (n : ℕ) : idealPowGradedPiece I F n ⟶ idealPowGradedPiece I F (n + 1) :=
  cokernel.desc _ (idealPowSmulHom I F a ha n ≫ idealPowGradedπ I F (n + 1)) (by
    rw [← Category.assoc, homOfLE_comp_idealPowSmulHom, Category.assoc, cokernel.condition,
      comp_zero])

/-- The projection `IⁿF ⟶ IⁿF/Iⁿ⁺¹F` followed by multiplication by `a` on the graded pieces is
multiplication by `a` on `IⁿF` followed by the projection `Iⁿ⁺¹F ⟶ Iⁿ⁺¹F/Iⁿ⁺²F`. -/
@[reassoc (attr := simp)]
theorem idealPowGradedπ_comp_idealPowGradedSmul (n : ℕ) :
    idealPowGradedπ I F n ≫ idealPowGradedSmul I F a ha n =
      idealPowSmulHom I F a ha n ≫ idealPowGradedπ I F (n + 1) :=
  cokernel.π_desc _ _ _

/-- Multiplications by two global functions `a`, `b` of `I`, `IⁿF ⟶ Iⁿ⁺²F`, commute. -/
theorem idealPowSmulHom_comm (b : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (hb : ∀ W : SmallEtale B S hS X.1, b.1 (op W) ∈ I.obj (op W)) (n : ℕ) :
    idealPowSmulHom I F a ha n ≫ idealPowSmulHom I F b hb (n + 1) =
      idealPowSmulHom I F b hb n ≫ idealPowSmulHom I F a ha (n + 1) :=
  idealSmulHom_comm I a ha b hb _ _

/-- **The commuting family `n ↦ IⁿF/Iⁿ⁺¹F`** with the multiplications by global functions
`a₁, …, a_r` of `I`. -/
def idealPowGradedFamily {r : ℕ}
    (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W)) :
    Stacks.CommutingFamily (Modules.{u, u} B S hS X.1 X.2) r where
  obj := idealPowGradedPiece I F
  act i := idealPowGradedSmul I F (a i) (ha i)
  comm i j n := by
    rw [← cancel_epi (idealPowGradedπ I F n)]
    rw [idealPowGradedπ_comp_idealPowGradedSmul_assoc,
      idealPowGradedπ_comp_idealPowGradedSmul_assoc,
      idealPowGradedπ_comp_idealPowGradedSmul, idealPowGradedπ_comp_idealPowGradedSmul,
      ← Category.assoc, idealPowSmulHom_comm, Category.assoc]

/-- **The graded pieces are generated in degree `0`** when the `aᵢ` generate `I` on the affine
étale charts. -/
theorem generatedFrom_idealPowGradedFamily {r : ℕ}
    (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W))
    (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (a i).1 (op A)) :
    (idealPowGradedFamily I F a ha).GeneratedFrom 0 := by
  intro n _ Q g hg
  have h0 : idealPowGradedπ I F (n + 1) ≫ g = 0 := by
    refine eq_zero_of_comp_idealSmulHom_eq_zero I a ha hgen _ _
      (idealSmul_idealPowSubmodule I F n) _ fun i => ?_
    have := hg i
    change idealPowGradedSmul I F (a i) (ha i) n ≫ g = 0 at this
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g)
      (idealPowGradedπ_comp_idealPowGradedSmul I F (a i) (ha i) n).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg _ this).trans comp_zero)))
  exact (cancel_epi (idealPowGradedπ I F (n + 1))).1 (h0.trans comp_zero.symm)

end Graded

end AlgebraicGeometry.Space

end
