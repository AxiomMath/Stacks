module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartDatumThickening
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoAffineCechSurjective
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Coordinates
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# The two-chart datum of two sections of a tensor power

Let `L` be an invertible module on a scheme `X` and `σ`, `τ` global sections of `L^{⊗ n}` whose
nonvanishing loci `U = X_σ` and `V = X_τ` are affine and cover `X`. Then `σ` trivializes
`L^{⊗ n}` on `U` and `τ` on `V`, and the ratios `b = τ / σ` on `U` and `a = σ / τ` on `V` form a
two-chart datum (`AlgebraicGeometry.C1590Private.twoChartDatumOfSections`): `U ∩ V = D(b) = D(a)`
and `a b = 1` on `U ∩ V`.

The `(j+1)`-st powers of `σ` and `τ` trivialize `L^{⊗ n (j+1)}` on `U` and `V`, with transition
function `b^{j+1}` (`Stacks.TensorPowerTrivialize.resTop_sectionPow`). Reading sections of
`L^{⊗ n (j+1)}` in these trivializations:

* `AlgebraicGeometry.C1590Private.surjective_cechDiff_of_isZero_Hgroup`: if
  `H¹(X, L^{⊗ n (j+1)}) = 0`, the Čech differential `(x, y) ↦ x - b^{j+1} y` of the datum is
  onto (`AlgebraicGeometry.C1590Private.exists_sub_eq_of_isZero_Hgroup_one`);
* `AlgebraicGeometry.C1590Private.surjective_sectionsOfGlobal`: every element of the section
  module of the datum in degree `j+1` comes from a global section of `L^{⊗ n (j+1)}`, linearly
  over the base ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowerTrivialize Stacks.GradedSections Stacks.SectionProduct

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

/-- Multiplication by a section of an invertible module is injective over any open inside its
nonvanishing locus. -/
theorem smul_resTop_injective (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (s : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s)
    {x y : Γ(X, W)} (h : x • resTop M s W = y • resTop M s W) : x = y :=
  (trivEquiv M s hW).injective h

/-- Every section over an open inside the nonvanishing locus of `s` is a multiple of `s`. -/
theorem exists_smul_resTop_eq (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (s : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s)
    (m : Γ(M, W)) : ∃ x : Γ(X, W), x • resTop M s W = m :=
  (trivEquiv M s hW).surjective m

/-- The inverse trivialization by `s` of the restriction of a sum is the sum. -/
theorem trivEquiv_symm_resTop_add (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (s : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s)
    (m m' : Γ(M, ⊤)) :
    (trivEquiv M s hW).symm (resTop M (m + m') W) =
      (trivEquiv M s hW).symm (resTop M m W) + (trivEquiv M s hW).symm (resTop M m' W) := by
  rw [← map_add]
  exact congrArg _ (map_add _ _ _)

/-- The inverse trivialization by `s` of the restriction of `c • m` is the restriction of `c`
times that of `m`. -/
theorem trivEquiv_symm_resTop_smul (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (s : Γ(M, ⊤)) {W : X.Opens} (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s)
    (c : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    (trivEquiv M s hW).symm (resTop M (c • m) W) =
      X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op c * (trivEquiv M s hW).symm (resTop M m W) := by
  dsimp only [resTop]
  rw [Scheme.Modules.map_smul, LinearEquiv.map_smul, smul_eq_mul]

/-- Sections over `U` and `V` agreeing on `U ⊓ V`, where `U ⊔ V = ⊤`, glue to a global
section. -/
theorem exists_resTop_eq_of_res_eq (F : X.Modules) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    (α : Γ(F, U)) (β : Γ(F, V))
    (h : F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op α =
      F.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op β) :
    ∃ g : Γ(F, ⊤), resTop F g U = α ∧ resTop F g V = β := by
  have hW : ∀ (W : X.Opens) (hW : W ≤ U ⊓ V),
      F.presheaf.map (homOfLE (hW.trans inf_le_left)).op α =
        F.presheaf.map (homOfLE (hW.trans inf_le_right)).op β := by
    intro W hW
    rw [← Stacks.AmpleThickeningAscent.modules_res_res F (homOfLE inf_le_left) (homOfLE hW),
      ← Stacks.AmpleThickeningAscent.modules_res_res F (homOfLE inf_le_right) (homOfLE hW), h]
  obtain ⟨g, hg⟩ := Stacks.AmpleThickeningAscent.modules_exists_gluing F
    (fun b : Bool => cond b V U) ⊤ (fun _ => homOfLE le_top) (by
      rw [top_le_iff, eq_top_iff, ← hUV]
      exact sup_le (le_iSup_of_le false le_rfl) (le_iSup_of_le true le_rfl))
    (fun b => Bool.rec (motive := fun b => Γ(F, cond b V U)) α β b) (by
      intro i k
      cases i <;> cases k
      · rfl
      · exact hW _ le_rfl
      · exact (hW _ (inf_comm V U).le).symm
      · rfl)
  exact ⟨g, hg false, hg true⟩

variable (σ τ : powSections L n)

/-- The ratio `τ / σ` on `X_σ`. -/
abbrev ratioOn : Γ(X, Stacks.AmpleFiniteAvoidance.nvOpen L σ) :=
  Stacks.NonvanishingOpen.trivTop
    (trivializationOfSection (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ σ)
      (le_refl (Stacks.AmpleFiniteAvoidance.nvOpen L σ))) (globalSection X _ τ)

/-- On `X_σ`, the restriction of `τ` equals `ratioOn L σ τ` times the restriction of `σ`. -/
theorem resTop_eq_ratioOn_smul :
    resTop (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ τ)
        (Stacks.AmpleFiniteAvoidance.nvOpen L σ) =
      ratioOn L σ τ • resTop (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ σ)
        (Stacks.AmpleFiniteAvoidance.nvOpen L σ) :=
  resTop_eq_ratio_smul _ _ _ _

/-- The basic open of the ratio `τ / σ` in `X_σ` is `X_σ ∩ X_τ`. -/
theorem basicOpen_ratioOn :
    X.basicOpen (ratioOn L σ τ) =
      Stacks.AmpleFiniteAvoidance.nvOpen L σ ⊓ Stacks.AmpleFiniteAvoidance.nvOpen L τ := by
  refine Opens.ext ((nonvanishingLocus_inter_eq_basicOpen (Stacks.TensorPowers.natTensorPow L n)
    (globalSection X _ σ) (globalSection X _ τ)
    (le_refl (Stacks.AmpleFiniteAvoidance.nvOpen L σ))).symm.trans ?_)
  rw [Opens.coe_inf, Set.inter_comm]
  rfl

/-- On any open `W ⊆ X_σ`, the restriction of `τ` equals the restriction of `ratioOn L σ τ`
times the restriction of `σ`. -/
theorem resTop_eq_ratioOn_smul_of_le {W : X.Opens}
    (hW : W ≤ Stacks.AmpleFiniteAvoidance.nvOpen L σ) :
    resTop (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ τ) W =
      X.presheaf.map (homOfLE hW).op (ratioOn L σ τ) •
        resTop (Stacks.TensorPowers.natTensorPow L n) (globalSection X _ σ) W := by
  rw [← res_resTop _ _ (homOfLE hW), resTop_eq_ratioOn_smul, map_smul_resTop]

/-- On any open `W ⊆ X_σ`, the restriction of `τ^{j+1}` equals the `(j+1)`-st power of the
restriction of `ratioOn L σ τ` times the restriction of `σ^{j+1}`. -/
theorem resTop_sectionPow_eq_ratioOn (j : ℕ) {W : X.Opens}
    (hW : W ≤ Stacks.AmpleFiniteAvoidance.nvOpen L σ) :
    resTop (Stacks.TensorPowers.natTensorPow L (powDeg n j))
        (globalSection X _ (sectionPow L τ j)) W =
      X.presheaf.map (homOfLE hW).op (ratioOn L σ τ) ^ (j + 1) •
        resTop (Stacks.TensorPowers.natTensorPow L (powDeg n j))
          (globalSection X _ (sectionPow L σ j)) W := by
  exact resTop_sectionPow L σ τ _ (resTop_eq_ratioOn_smul_of_le L σ τ hW) j

variable {L σ τ}
variable (hσ : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L σ))
  (hτ : IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L τ))
  (hcov : Stacks.AmpleFiniteAvoidance.nvOpen L σ ⊔ Stacks.AmpleFiniteAvoidance.nvOpen L τ = ⊤)

include hσ hτ hcov in
/-- **The two-chart datum of two sections.** For global sections `σ`, `τ` of `L^{⊗ n}` with
affine nonvanishing loci covering `X`: `U = X_σ`, `V = X_τ`, `b = τ / σ`, `a = σ / τ`. -/
def twoChartDatumOfSections : TwoChartDatum X where
  U := Stacks.AmpleFiniteAvoidance.nvOpen L σ
  V := Stacks.AmpleFiniteAvoidance.nvOpen L τ
  isAffineOpen_U := hσ
  isAffineOpen_V := hτ
  sup_eq_top := hcov
  b := ratioOn L σ τ
  a := ratioOn L τ σ
  basicOpen_b := basicOpen_ratioOn L σ τ
  basicOpen_a := (basicOpen_ratioOn L τ σ).trans (inf_comm _ _)
  mul_eq_one := by
    set U := Stacks.AmpleFiniteAvoidance.nvOpen L σ
    set V := Stacks.AmpleFiniteAvoidance.nvOpen L τ
    set M := Stacks.TensorPowers.natTensorPow L n
    have h1 := resTop_eq_ratioOn_smul_of_le L σ τ (inf_le_left : U ⊓ V ≤ U)
    have h2 := resTop_eq_ratioOn_smul_of_le L τ σ (inf_le_right : U ⊓ V ≤ V)
    have h3 : resTop M (globalSection X _ σ) (U ⊓ V) =
        (X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op (ratioOn L σ τ) *
          X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op (ratioOn L τ σ)) •
          resTop M (globalSection X _ σ) (U ⊓ V) := by
      rw [mul_comm, mul_smul, ← h1, ← h2]
    exact smul_resTop_injective M (globalSection X _ σ)
      (show U ⊓ V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M (globalSection X _ σ) from
        inf_le_left) (h3.symm.trans (one_smul _ _).symm)

/-- `AlgebraicGeometry.C1590Private.exists_sub_eq_of_isZero_Hgroup_one` in the spelling of the
sections of an `𝒪_X`-module. -/
theorem exists_sub_eq_of_isZero_Hgroup_one' (F : X.Modules) [F.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (hH : IsZero (Hgroup X.ringCatSheaf (U ⊔ V) 1 F)) (c : Γ(F, U ⊓ V)) :
    ∃ (x : Γ(F, U)) (y : Γ(F, V)),
      c = F.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op y -
        F.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op x :=
  exists_sub_eq_of_isZero_Hgroup_one F hU hV hUV hH c

section Powers

/-- The nonvanishing locus `X_σ` is contained in the nonvanishing locus of `σ^{j+1}`. -/
theorem le_nonvanishingOpen_sectionPow (j : ℕ) :
    Stacks.AmpleFiniteAvoidance.nvOpen L σ ≤
      Stacks.NonvanishingOpen.nonvanishingOpen X
        (Stacks.TensorPowers.natTensorPow L (powDeg n j))
        (globalSection X _ (sectionPow L σ j)) :=
  (nonvanishingOpen_sectionPow L σ j).ge

include hσ hτ hcov in
/-- **`H¹(X, L^{⊗ n (j+1)}) = 0` makes the Čech differential of the datum onto in degree
`j+1`.** A function `w` on `U ∩ V` is read as the section `w σ^{j+1}` of `L^{⊗ n (j+1)}`, which
splits as `β - α` with `α = x σ^{j+1}` on `U` and `β = y τ^{j+1} = y b^{j+1} σ^{j+1}` on `V`. -/
theorem surjective_cechDiff_of_isZero_Hgroup (j : ℕ)
    (hH : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      (Stacks.Ample.tensorPowModule X L ((powDeg n j : ℕ) : ℤ)))) :
    Function.Surjective ((twoChartDatumOfSections hσ hτ hcov).cechDiff (j + 1)) := by
  set U := Stacks.AmpleFiniteAvoidance.nvOpen L σ
  set V := Stacks.AmpleFiniteAvoidance.nvOpen L τ
  set F := Stacks.TensorPowers.natTensorPow L (powDeg n j)
  set sj := globalSection X F (sectionPow L σ j)
  set tj := globalSection X F (sectionPow L τ j)
  have : F.IsQuasicoherent := Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible _ F
  have hUV : IsAffineOpen (U ⊓ V) := basicOpen_ratioOn L σ τ ▸ hσ.basicOpen (ratioOn L σ τ)
  have hF : F = Stacks.Ample.tensorPowModule X L ((powDeg n j : ℕ) : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow _ L _
  have hH' : IsZero (Hgroup X.ringCatSheaf (U ⊔ V) 1 F) := by rwa [hcov, hF]
  intro (w : Γ(X, U ⊓ V))
  obtain ⟨α, β, hαβ⟩ := exists_sub_eq_of_isZero_Hgroup_one' F hσ hτ hUV hH'
    (w • resTop F sj (U ⊓ V))
  obtain ⟨x, rfl⟩ := exists_smul_resTop_eq F sj (le_nonvanishingOpen_sectionPow j) α
  obtain ⟨y, rfl⟩ := exists_smul_resTop_eq F tj (le_nonvanishingOpen_sectionPow j) β
  rw [map_smul_resTop, map_smul_resTop, resTop_sectionPow_eq_ratioOn L σ τ j inf_le_left,
    smul_smul, ← sub_smul] at hαβ
  have hw := smul_resTop_injective F sj
    ((inf_le_left : U ⊓ V ≤ U).trans (le_nonvanishingOpen_sectionPow j)) hαβ
  set D := twoChartDatumOfSections hσ hτ hcov
  have key : ∀ (x' : Γ(X, D.U)) (y' : Γ(X, D.V)),
      D.resU (-x') - D.resU D.b ^ (j + 1) * D.resV (-y') =
        D.resV y' * D.resU D.b ^ (j + 1) - D.resU x' := by
    intro x' y'
    rw [map_neg, map_neg]
    ring
  exact ⟨(-x, -y), (key x y).trans hw.symm⟩

include hσ hτ hcov in
/-- **The section modules of the datum are quotients of the global sections.** A global section
`g` of `L^{⊗ n (j+1)}` gives the pair of its coordinates `(g / σ^{j+1}, g / τ^{j+1})`, a section
of the datum in degree `j+1`, and every section of the datum arises so by gluing. Hence the
section module is finite over `R` as soon as `Γ(X, L^{⊗ n (j+1)})` is. -/
theorem finite_sections_of_finite {R : Type u} [CommRing R] (σR : R →+* Γ(X, ⊤)) (j : ℕ)
    (hfin : Module.Finite R ((ModuleCat.restrictScalars σR).obj
      ((moduleGlobalSections X).obj (Stacks.TensorPowers.natTensorPow L (powDeg n j))))) :
    letI := (twoChartDatumOfSections hσ hτ hcov).algebraU σR
    letI := (twoChartDatumOfSections hσ hτ hcov).algebraV σR
    Module.Finite R ((twoChartDatumOfSections hσ hτ hcov).sections σR (j + 1)) := by
  set D := twoChartDatumOfSections hσ hτ hcov
  let := D.algebraU σR
  let := D.algebraV σR
  set U := D.U
  set V := D.V
  set F := Stacks.TensorPowers.natTensorPow L (powDeg n j)
  set sj := globalSection X F (sectionPow L σ j)
  set tj := globalSection X F (sectionPow L τ j)
  have hU : U ≤ Stacks.NonvanishingOpen.nonvanishingOpen X F sj := le_nonvanishingOpen_sectionPow j
  have hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X F tj := le_nonvanishingOpen_sectionPow j
  have htj : resTop F tj (U ⊓ V) =
      X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op D.b ^ (j + 1) •
        resTop F sj (U ⊓ V) := resTop_sectionPow_eq_ratioOn L σ τ j inf_le_left
  have hcoord : ∀ (x : Γ(X, U)) (y : Γ(X, V)),
      X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op x • resTop F sj (U ⊓ V) =
        X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op y • resTop F tj (U ⊓ V) ↔
      D.cechDiff (j + 1) (x, y) = 0 := by
    intro x y
    rw [htj, smul_smul, TwoChartDatum.cechDiff_apply, sub_eq_zero]
    refine ⟨fun h => (smul_resTop_injective F sj (inf_le_left.trans hU) h).trans (mul_comm _ _),
      fun h => ?_⟩
    exact congrArg (· • resTop F sj (U ⊓ V))
      (h.trans (mul_comm _ _) : D.resU x = D.resV y * D.resU D.b ^ (j + 1))
  let coord : Γ(F, ⊤) → Γ(X, U) × Γ(X, V) := fun g =>
    ((trivEquiv F sj hU).symm (resTop F g U), (trivEquiv F tj hV).symm (resTop F g V))
  have hcoordU : ∀ g, (coord g).1 • resTop F sj U = resTop F g U := fun g =>
    (trivEquiv F sj hU).apply_symm_apply _
  have hcoordV : ∀ g, (coord g).2 • resTop F tj V = resTop F g V := fun g =>
    (trivEquiv F tj hV).apply_symm_apply _
  have hmem : ∀ g, coord g ∈ D.sections σR (j + 1) := fun g => (hcoord _ _).1 <| by
    rw [← map_smul_resTop, ← map_smul_resTop, hcoordU, hcoordV, res_resTop, res_resTop]
  let Φ : (ModuleCat.restrictScalars σR).obj ((moduleGlobalSections X).obj F) →ₗ[R]
      D.sections σR (j + 1) :=
    { toFun := fun g => ⟨coord g, hmem g⟩
      map_add' := fun g g' => Subtype.ext (Prod.ext (trivEquiv_symm_resTop_add F sj hU g g')
        (trivEquiv_symm_resTop_add F tj hV g g'))
      map_smul' := fun r g => Subtype.ext (Prod.ext (trivEquiv_symm_resTop_smul F sj hU (σR r) g)
        (trivEquiv_symm_resTop_smul F tj hV (σR r) g)) }
  refine Module.Finite.of_surjective Φ ?_
  rintro ⟨⟨x, y⟩, hxy⟩
  have hxy' : D.cechDiff (j + 1) (x, y) = 0 := hxy
  obtain ⟨g, hgU, hgV⟩ := exists_resTop_eq_of_res_eq F D.sup_eq_top (x • resTop F sj U)
    (y • resTop F tj V) (by rw [map_smul_resTop, map_smul_resTop]; exact (hcoord x y).2 hxy')
  exact ⟨g, Subtype.ext (Prod.ext ((LinearEquiv.symm_apply_eq _).2 hgU)
    ((LinearEquiv.symm_apply_eq _).2 hgV))⟩

end Powers

end AlgebraicGeometry.C1590Private
