module

public import StacksFrontier.Topology.Sheaves.Modules.Generators.KernelTensorInvertible
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# Generating sections of an invertible module embed the structure sheaf

Let `L` be an invertible sheaf of modules on a ringed space whose stalks are local rings, and let
`s_i ∈ Γ(X, L)`, `i ∈ I` finite, be global sections generating `L`.  Then the morphism
`𝒪_X ⟶ L^{⊕ I}`, `c ↦ (c • s_i)_i`, is a monomorphism.

At every point `x` some `s_i` does not vanish (its germ escapes `𝔪_x L_x`), since the germs of
the `s_i` span `L_x` and `L_x ≠ 𝔪_x L_x` for an invertible module over a local ring; on the
nonvanishing locus of `s_i` multiplication by `s_i` is injective
(`Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`, [Stacks, Tag 01CY]).  So a
section of `𝒪_X` killed by every `s_i` has zero germ everywhere.

## Main results

* `Stacks.SheafOfModules.not_top_le_maximalIdeal_smul_of_tensorEquiv`: an invertible module
  over a local ring is not `𝔪 M`.
* `Stacks.SheafOfModules.exists_mem_nonvanishingOpen_of_generatingSections`: generating
  sections of an invertible module have nonvanishing loci covering the space.
* `Stacks.SheafOfModules.mono_biproductLift_unitHomEquiv_symm`: the monomorphism above, for any
  finite family of sections whose nonvanishing loci cover the space.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.SheafOfModules

/-- **An invertible module over a local ring is not `𝔪 M`.**  If `M ⊗ P ≃ R` over a local ring
`R`, then `M ≠ 𝔪 M`. -/
theorem not_top_le_maximalIdeal_smul_of_tensorEquiv {R M P : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (Θ : M ⊗[R] P ≃ₗ[R] R) :
    ¬ (⊤ : Submodule R M) ≤ maximalIdeal R • ⊤ := by
  intro h
  have key : ∀ ξ : M ⊗[R] P, Θ ξ ∈ maximalIdeal R := by
    intro ξ
    induction ξ using TensorProduct.inductionOn with
    | tmul m n =>
      have hm : m ∈ maximalIdeal R • (⊤ : Submodule R M) := h Submodule.mem_top
      refine Submodule.smul_induction_on (p := fun m => Θ (m ⊗ₜ n) ∈ maximalIdeal R) hm ?_ ?_
      · intro a ha y _
        rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ ha
      · intro y z hy hz
        rw [TensorProduct.add_tmul, map_add]
        exact add_mem hy hz
    | add ξ η h1 h2 =>
      rw [map_add]
      exact add_mem h1 h2
  exact (maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using key (Θ.symm 1)))

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- **The nonvanishing loci of generating sections of an invertible module cover the space.** -/
theorem exists_mem_nonvanishingOpen_of_generatingSections (g : L.GeneratingSections)
    (x : X.carrier) : ∃ i : g.I, x ∈ nonvanishingOpen L (g.s i) := by
  by_contra hne
  push Not at hne
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  refine not_top_le_maximalIdeal_smul_of_tensorEquiv (stalkPairing ψ x)
    ((span_sGerm_eq_top X L g x).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact not_not.mp (hne i)

/-- **Sections of an invertible module whose nonvanishing loci cover the space embed the
structure sheaf.**  For a finite family `s_j` of global sections of an invertible `L` such that
every point lies in some `X_{s_j}`, the morphism `𝒪_X ⟶ L^{⊕ J}`, `c ↦ (c • s_j)_j`, is a
monomorphism. -/
theorem mono_biproductLift_unitHomEquiv_symm {J : Type} [Finite J] (s : J → L.sections)
    (hs : ∀ x : X.carrier, ∃ j, x ∈ nonvanishingOpen L (s j))
    [HasFiniteBiproducts (SheafOfModules.{u} (structureSheafRing X))] :
    Mono (biproduct.lift fun j : J => L.unitHomEquiv.symm (s j)) := by
  set φ := biproduct.lift fun j : J => L.unitHomEquiv.symm (s j)
  have hinj : ∀ (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U),
      φ.val.app U r = 0 → r = 0 := by
    intro U r hr
    have hi : ∀ j : J, r • (s j).eval U = 0 := by
      intro j
      have h := congrArg (fun t => (biproduct.π (fun _ : J => L) j).val.app U t) hr
      simp only [map_zero] at h
      have hc : (φ ≫ biproduct.π (fun _ : J => L) j) = L.unitHomEquiv.symm (s j) :=
        biproduct.lift_π _ _
      have h2 := congrArg (fun k => k.val.app U r) hc
      exact h2.symm.trans h
    refine TopCat.Presheaf.section_ext X.sheaf U.unop r 0 fun x hx => ?_
    obtain ⟨j, hxj⟩ := hs x
    let W : Opens X.carrier := U.unop ⊓ nonvanishingOpen L (s j)
    have hxW : x ∈ W := ⟨hx, hxj⟩
    have hWU : W ≤ U.unop := inf_le_left
    have hres : X.presheaf.map (homOfLE hWU).op r = 0 := by
      refine (bijective_smul_eval_of_le_nonvanishingOpen L (s j) W inf_le_right).1 ?_
      have h := congrArg (fun t => L.val.map (homOfLE hWU).op t) (hi j)
      simp only [map_zero] at h
      rw [PresheafOfModules.map_smul] at h
      change X.presheaf.map (homOfLE hWU).op r • (s j).eval (op W) =
        (0 : X.presheaf.obj (op W)) • (s j).eval (op W)
      have hs' : L.val.map (homOfLE hWU).op ((s j).eval U) = (s j).eval (op W) :=
        PresheafOfModules.sections_property (s j) (homOfLE hWU).op
      rwa [zero_smul, ← hs']
    rw [← X.sheaf.presheaf.germ_res_apply (homOfLE hWU) x hxW r, map_zero]
    change X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hWU).op r) = 0
    rw [hres, map_zero]
  refine ⟨fun {Z} a b hab => ?_⟩
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  have h : φ.val.app U (a.val.app U z) = φ.val.app U (b.val.app U z) :=
    congrArg (fun k => k.val.app U z) hab
  exact sub_eq_zero.mp (hinj U _ (by rw [map_sub]; exact sub_eq_zero.mpr h))

end Stacks.SheafOfModules

end
