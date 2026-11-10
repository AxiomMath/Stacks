module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.LocalGenerator
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.PullbackNonvanishing

/-!
# Local coordinates of sections of the powers of an invertible module

Let `M` be an `𝒪_X`-module with sectionwise trivializations `τ i` over a family of opens `U i`,
with basis sections `b i`. On an overlap the basis sections differ by the *transition functions*
`w i j`, defined by `b j = w i j • b i` on `U i ⊓ U j`; they satisfy the cocycle rule
`w i l = w i j * w j l` on triple overlaps.

The powers `b i ^ (m + 1)` (`Stacks.TensorSectionPower.secPow`) are bases of `M ^ (m + 1)`, with
transition functions `w i j ^ (m + 1)`. A family of functions `f i` on the `U i` transforming by
`f i = w i j ^ (m + 1) * f j` is therefore the family of coordinates of exactly one global section
of `M ^ (m + 1)`, whose nonvanishing locus meets `U i` in the basic open of `f i`.

## Main definitions

* `Stacks.AmpleThickeningAscent.transition`: the transition functions.

## Main results

* `Stacks.AmpleThickeningAscent.res_basis_eq_transition_smul`: `b j = w i j • b i`.
* `Stacks.AmpleThickeningAscent.transition_cocycle`: the cocycle rule.
* `Stacks.AmpleThickeningAscent.res_secPow_basis`:
  `b j ^ (m + 1) = w i j ^ (m + 1) • b i ^ (m + 1)`.
* `Stacks.AmpleThickeningAscent.exists_section_of_coordinates`: the gluing of a transforming
  family, and the nonvanishing locus of the glued section.
* `Stacks.AmpleThickeningAscent.exists_coordinates_pullback`: conversely, the coordinates of a
  global section of `(k^* M) ^ (m + 1)` against the pulled-back bases `k^* b i ^ (m + 1)`, for a
  morphism `k : Y ⟶ X`; they transform by `(k^♯ w i j) ^ (m + 1)`, and their basic opens are the
  nonvanishing locus of the section met with `k⁻¹ U i`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff
  nonvanishingLocusOn_top)
open Stacks.TensorSectionPower (powObj secPow map_secPow secPow_smul)
open Stacks.NonvanishingOpen (basis triv)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleThickeningAscent

variable {X : Scheme.{u}}

/-! ### Restriction in two steps -/

/-- Restricting a section of a module in two steps is restricting it once. -/
theorem modules_res_res (M : X.Modules) {A B C : X.Opens} (h₁ : B ⟶ A) (h₂ : C ⟶ B)
    (h₃ : C ⟶ A) (x : Γ(M, A)) :
    M.presheaf.map h₂.op (M.presheaf.map h₁.op x) = M.presheaf.map h₃.op x := by
  have : h₂ ≫ h₁ = h₃ := Subsingleton.elim _ _
  rw [← this, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restricting a function in two steps is restricting it once. -/
theorem ring_res_res {A B C : X.Opens} (h₁ : B ⟶ A) (h₂ : C ⟶ B) (h₃ : C ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map h₂.op (X.presheaf.map h₁.op x) = X.presheaf.map h₃.op x := by
  have : h₂ ≫ h₁ = h₃ := Subsingleton.elim _ _
  rw [← this, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-! ### Transition functions -/

variable (M : X.Modules) {ι : Type*} {U : ι → X.Opens}
  (τ : ∀ i, Stacks.SheafDescent.Trivialization X.presheaf M.val (U i))

/-- **The transition function** `w i j` on `U i ⊓ U j`: the coordinate of the basis section of
`τ j` in the trivialization `τ i`. -/
noncomputable def transition (i j : ι) : Γ(X, U i ⊓ U j) :=
  triv (τ i) (homOfLE inf_le_left) (M.presheaf.map (homOfLE inf_le_right).op (basis (τ j)))

/-- `b j = w i j • b i` on `U i ⊓ U j`. -/
theorem res_basis_eq_transition_smul (i j : ι) :
    M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (basis (τ j)) =
      transition M τ i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
        (basis (τ i)) :=
  Stacks.SectionProduct.eq_triv_smul_res_basis (τ i) _ _

/-- The restriction of `b j` to an open `T` inside `U i ⊓ U j` is the restriction of `w i j`
times that of `b i`. -/
theorem res_basis_eq_res_transition_smul (i j : ι) {T : X.Opens} (hT : T ≤ U i ⊓ U j) :
    M.presheaf.map (homOfLE (hT.trans inf_le_right)).op (basis (τ j)) =
      X.presheaf.map (homOfLE hT).op (transition M τ i j) •
        M.presheaf.map (homOfLE (hT.trans inf_le_left)).op (basis (τ i)) := by
  rw [← modules_res_res M (homOfLE inf_le_right) (homOfLE hT),
    res_basis_eq_transition_smul, Scheme.Modules.map_smul, modules_res_res]

/-- **The cocycle rule** `w i j * w j l = w i l` on `U i ⊓ U j ⊓ U l`. -/
theorem transition_cocycle (i j l : ι) :
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j)).op
        (transition M τ i j) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U i ⊓ U j ⊓ U l ≤ U j ⊓ U l)).op (transition M τ j l) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U i ⊓ U j ⊓ U l ≤ U i ⊓ U l)).op (transition M τ i l) := by
  have hTi : U i ⊓ U j ⊓ U l ≤ U i := inf_le_left.trans inf_le_left
  refine Stacks.TensorSectionPower.smul_res_basis_injective (τ i) (homOfLE hTi) ?_
  have h1 := res_basis_eq_res_transition_smul M τ i l
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U i ⊓ U j ⊓ U l ≤ U i ⊓ U l)
  have h2 := res_basis_eq_res_transition_smul M τ j l
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U l ≤ U j ⊓ U l)
  have h3 := res_basis_eq_res_transition_smul M τ i j
    (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j)
  rw [mul_comm, mul_smul, ← h3, ← h2, h1]

/-- **The transition functions of the powers**: `b j ^ (m + 1) = w i j ^ (m + 1) • b i ^ (m + 1)`
on `U i ⊓ U j`. -/
theorem res_secPow_basis (m : ℕ) (i j : ι) :
    (powObj M m).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
        (secPow M (basis (τ j)) m) =
      transition M τ i j ^ (m + 1) •
        (powObj M m).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
          (secPow M (basis (τ i)) m) := by
  rw [map_secPow, map_secPow, res_basis_eq_transition_smul, secPow_smul]

/-- The basis section of a trivialization vanishes nowhere, nor does any of its powers. -/
theorem nonvanishingLocusOn_secPow_basis [Stacks.Ample.IsInvertibleModule X M] (m : ℕ) (i : ι) :
    nonvanishingLocusOn (powObj M m) (U i) (secPow M (basis (τ i)) m) = U i := by
  rw [Stacks.SectionPowerOpen.nonvanishingLocusOn_secPow, nonvanishingLocusOn_basis]

/-! ### Gluing a transforming family -/

/-- **A family of coordinates transforming by the transition functions of `M ^ (m + 1)` glues to a
global section**, whose nonvanishing locus meets each `U i` in the basic open of its coordinate. -/
theorem exists_section_of_coordinates [Stacks.Ample.IsInvertibleModule X M]
    (hcov : (⊤ : X.Opens) ≤ ⨆ i, U i) (m : ℕ) (f : ∀ i, Γ(X, U i))
    (hf : ∀ i j, X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f i) =
      transition M τ i j ^ (m + 1) *
        X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (f j)) :
    ∃ T : Γ(powObj M m, ⊤),
      (∀ i, (powObj M m).presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op T =
        f i • secPow M (basis (τ i)) m) ∧
      ∀ i, Stacks.Ample.nonvanishingLocus (powObj M m) T ∩ (U i : Set X) =
        (X.basicOpen (f i) : Set X) := by
  obtain ⟨T, hT⟩ := modules_exists_gluing (powObj M m) U ⊤ (fun i => homOfLE le_top) hcov
    (fun i => f i • secPow M (basis (τ i)) m) fun i j => by
      rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, hf, res_secPow_basis, mul_smul]
      exact smul_comm _ _ _
  refine ⟨T, hT, fun i => ?_⟩
  have h := nonvanishingLocusOn_res (powObj M m) (le_top : U i ≤ ⊤) T
  rw [hT i, nonvanishingLocusOn_smul, nonvanishingLocusOn_secPow_basis, nonvanishingLocusOn_top]
    at h
  rw [Set.inter_comm, ← h]
  exact Set.inter_eq_left.mpr (X.basicOpen_le (f i))

/-! ### Coordinates of a section of a power of a pulled-back module -/

section Pullback

variable {Y : Scheme.{u}} (k : Y ⟶ X) [Stacks.Ample.IsInvertibleModule X M]

local notation "L" => pullbackModule k M

/-- **The coordinates of a global section of `(k^* M) ^ (m + 1)`** against the pulled-back bases
`k^* b i ^ (m + 1)` over the opens `k⁻¹ U i`. They transform by `(k^♯ w i j) ^ (m + 1)`, and the
basic open of the `i`-th one is the nonvanishing locus of the section met with `k⁻¹ U i`. -/
theorem exists_coordinates_pullback (m : ℕ) (σ : Γ(powObj (pullbackModule k M) m, ⊤)) :
    ∃ ρ : ∀ i, Γ(Y, k ⁻¹ᵁ U i),
      (∀ i j, Y.presheaf.map (homOfLE (k.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i))).op
          (ρ i) =
        (k.app (U i ⊓ U j) (transition M τ i j)) ^ (m + 1) *
          Y.presheaf.map (homOfLE (k.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j))).op
            (ρ j)) ∧
      ∀ i, (Y.basicOpen (ρ i) : Set Y) =
        (k ⁻¹ᵁ U i : Set Y) ∩ Stacks.Ample.nonvanishingLocus (powObj (pullbackModule k M) m) σ := by
  let e : ∀ i, Γ(powObj L m, k ⁻¹ᵁ U i) := fun i =>
    secPow L (pullbackSection k M (basis (τ i))) m
  have he : ∀ i, nonvanishingLocusOn (powObj L m) (k ⁻¹ᵁ U i) (e i) = k ⁻¹ᵁ U i := by
    intro i
    simp only [e]
    rw [Stacks.SectionPowerOpen.nonvanishingLocusOn_secPow,
      nonvanishingLocusOn_pullbackSection, nonvanishingLocusOn_basis]
    rfl
  -- the transition rule of the pulled-back bases
  have htr : ∀ i j, (powObj L m).presheaf.map
        (homOfLE (k.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j))).op (e j) =
      (k.app (U i ⊓ U j) (transition M τ i j)) ^ (m + 1) •
        (powObj L m).presheaf.map
          (homOfLE (k.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i))).op (e i) := by
    intro i j
    simp only [e]
    rw [map_secPow, map_secPow, pullbackSection_res k M (inf_le_left : U i ⊓ U j ≤ U i),
      pullbackSection_res k M (inf_le_right : U i ⊓ U j ≤ U j),
      res_basis_eq_transition_smul, pullbackSection_smul, secPow_smul]
  -- the coordinates
  have hbij : ∀ i, Function.Bijective fun a : Γ(Y, k ⁻¹ᵁ U i) => a • e i := fun i =>
    bijective_smul_of_nonvanishing (powObj L m) (e i) (by rw [he i])
  choose ρ hρ using fun i => (hbij i).2
    ((powObj L m).presheaf.map (homOfLE (le_top : k ⁻¹ᵁ U i ≤ ⊤)).op σ)
  have hρ' : ∀ i, ρ i • e i =
      (powObj L m).presheaf.map (homOfLE (le_top : k ⁻¹ᵁ U i ≤ ⊤)).op σ := hρ
  refine ⟨ρ, fun i j => ?_, fun i => ?_⟩
  · -- uniqueness of coordinates over the overlap
    set P := k ⁻¹ᵁ (U i ⊓ U j)
    have hPi : P ≤ k ⁻¹ᵁ U i := k.preimage_mono inf_le_left
    have hPj : P ≤ k ⁻¹ᵁ U j := k.preimage_mono inf_le_right
    have hnv : (P : Set Y) ⊆ nonvanishingLocusOn (powObj L m) P
        ((powObj L m).presheaf.map (homOfLE hPi).op (e i)) := by
      rw [nonvanishingLocusOn_res, he i]
      exact fun y hy => ⟨hy, hPi hy⟩
    refine (bijective_smul_of_nonvanishing (powObj L m) _ hnv).1 ?_
    change Y.presheaf.map (homOfLE hPi).op (ρ i) • _ =
      ((k.app (U i ⊓ U j) (transition M τ i j)) ^ (m + 1) *
        Y.presheaf.map (homOfLE hPj).op (ρ j)) • _
    rw [mul_smul, smul_comm, ← htr, ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul,
      hρ' i, hρ' j, modules_res_res _ _ _ (homOfLE le_top),
      modules_res_res _ _ _ (homOfLE le_top)]
  · have h := nonvanishingLocusOn_res (powObj L m) (le_top : k ⁻¹ᵁ U i ≤ ⊤) σ
    rw [← hρ' i, nonvanishingLocusOn_smul, he i, nonvanishingLocusOn_top] at h
    exact (Set.inter_eq_left.mpr (Y.basicOpen_le (ρ i))).symm.trans h

end Pullback

end Stacks.AmpleThickeningAscent

end
