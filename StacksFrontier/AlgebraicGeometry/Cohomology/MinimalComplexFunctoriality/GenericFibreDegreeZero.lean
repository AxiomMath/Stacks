module

public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift

/-!
# A complex over a local domain with a one-dimensional degree-zero term and a generic class

Let `A` be a local domain with fraction field `K` and residue field `κ`, and let `F` be a complex
of finite free `A`-modules whose degree-zero term is free of rank one. If the generic fibre
`F ⊗_A K` has nonzero cohomology in degree zero, then the differential `F⁰ ⟶ F¹` vanishes, so a
generator of `F⁰` is a degree-zero cycle of `F` whose image in the special fibre `F ⊗_A κ` is
nonzero. Moreover the cohomology of any fibre of a complex of finite free modules has dimension
at most the rank of the corresponding term.

This is the module-theoretic step of the proof of Stacks 0DNJ. There `F` is the minimal complex
of Stacks 0BCC representing `RΓ(X_R, L)` for an invertible module `L` on a proper flat family
`X_R` over a valuation ring `R`: its terms have the ranks of the cohomology of the closed fibre,
so the bound below gives `h⁰(X_κ, L_κ) ≥ h⁰(X_K, L_K)`, and once `L_κ` is trivial the degree-zero
term has rank one; triviality of `L_K` makes the generic degree-zero cohomology nonzero, and the
conclusion produces a global section of `L` which does not vanish on the closed fibre.

## Main results

* `StacksDraft.Perfect.FibreCycleLift.fibreElt_eq_zero_iff_of_injective`: for a free module and
  an injective ring map to a field, `1 ⊗ x` vanishes only for `x = 0`.
* `StacksDraft.Perfect.FibreCycleLift.finrank_homology_fibreComplex_le`: the cohomology of a fibre
  of a complex of finite free modules has dimension at most the rank of the term.
* `StacksDraft.Perfect.FibreCycleLift.d_zero_one_eq_zero_of_nontrivial_generic`: the differential
  out of a rank-one degree-zero term vanishes once the generic fibre has degree-zero cohomology.
* `StacksDraft.Perfect.FibreCycleLift.exists_cycle_fibreElt_ne_zero_of_nontrivial_generic`: over
  a local domain, the generator of `F⁰` is then a cycle of nonzero special fibre.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.FibreCycleLift

section Injective

variable {A : Type u} [CommRing A] {K : Type u} [Field K] (χ : A →+* K)

/-- **For a free module and an injective map to a field, the fibre is faithful on elements.**
The coordinates of `1 ⊗ x` in the basis of `K ⊗_A M` induced by a basis of `M` are the images of
the coordinates of `x`. -/
theorem fibreElt_eq_zero_iff_of_injective (hχ : Function.Injective χ) (M : ModuleCat.{u} A)
    [Module.Free A M] (x : M) : fibreElt χ M x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun hx => ?_, fun hx => by
    subst hx
    exact TensorProduct.tmul_zero (R := A) M (show fibreScalars χ from (1 : K))⟩
  let b := Module.Free.chooseBasis A M
  let e : fibreScalars χ ⊗[A] M ≃ₗ[A] (Module.Free.ChooseBasisIndex A M →₀ fibreScalars χ) :=
    (b.repr.lTensor (fibreScalars χ)).trans (TensorProduct.finsuppScalarRight A A _ _)
  have hcoord : ∀ i, χ (b.repr x i) = 0 := by
    intro i
    have h1 : e (TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x) i = 0 := by
      rw [show TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x = 0 from hx, map_zero]
      rfl
    have h2 : e (TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x) i =
        (b.repr x i) • (show fibreScalars χ from (1 : K)) := by
      simp only [e, LinearEquiv.trans_apply]
      exact TensorProduct.finsuppScalarRight_apply_tmul_apply _ _ _
    rw [h2] at h1
    have h4 : (χ (b.repr x i) * 1 : K) = 0 := h1
    simpa using h4
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.zero_apply]
  exact hχ ((hcoord i).trans (map_zero χ).symm)

/-- The homology of a short complex of `K`-vector spaces with finite dimensional middle term is
finite dimensional, of dimension at most that of the kernel of the outgoing map. -/
private theorem finrank_homology_le_finrank_ker (S : ShortComplex (ModuleCat.{u} K))
    [FiniteDimensional K S.X₂] :
    Module.Finite K S.homology ∧
      Module.finrank K S.homology ≤ Module.finrank K (LinearMap.ker S.g.hom) := by
  let e := S.moduleCatHomologyIso.toLinearEquiv
  have : Module.Finite K S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq ▸ Submodule.finrank_quotient_le _⟩

/-- **The cohomology of a fibre is bounded by the rank of the term.** For a complex `F` of finite
free `A`-modules with `Fⁱ` free of rank `r i`, the degree-`i` cohomology of `F ⊗_A K` has
dimension at most `r i`, being a subquotient of `Fⁱ ⊗_A K`. -/
theorem finrank_homology_fibreComplex_le [IsLocalRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℤ → ℕ)
    (hF : ∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A)))) (i : ℤ) :
    Module.finrank K ((fibreComplex χ F).homology i) ≤ r i := by
  obtain ⟨hrk, hfd⟩ := finrank_fibre_ulift χ (r i) (F.X i) (hF i).some
  have : FiniteDimensional K ((fibreComplex χ F).sc i).X₂ := hfd
  have hle := Submodule.finrank_le (LinearMap.ker ((fibreComplex χ F).sc i).g.hom)
  have hrk' : Module.finrank K ((fibreComplex χ F).sc i).X₂ = r i := hrk
  have : Module.finrank K ((fibreComplex χ F).homology i) ≤ _ :=
    (finrank_homology_le_finrank_ker ((fibreComplex χ F).sc i)).2
  omega

end Injective

section Generic

variable {A : Type u} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
/-- **The differential out of a rank-one degree-zero term vanishes once the generic fibre has
degree-zero cohomology.** Let `F` be a complex of `A`-modules over a domain with `F⁰` free of
rank one and `F¹` free. If `H⁰(F ⊗_A K) ≠ 0`, `K` the fraction field, then `F⁰ ⟶ F¹` is zero:
the generic differential `F⁰ ⊗ K ⟶ F¹ ⊗ K` has a nonzero kernel in a one-dimensional space, so
it vanishes, and `F¹ ⟶ F¹ ⊗ K` is injective. -/
theorem d_zero_one_eq_zero_of_nontrivial_generic {K : Type u} [Field K] (χ : A →+* K)
    (hχ : Function.Injective χ) (F : CochainComplex (ModuleCat.{u} A) ℤ)
    (e₀ : F.X 0 ≅ ModuleCat.of A (ULift.{u} (Fin 1 → A))) [Module.Free A (F.X 1)]
    (hgen : Nontrivial ((fibreComplex χ F).homology 0)) :
    F.d 0 1 = 0 := by
  let S := (fibreComplex χ F).sc' (-1) 0 1
  have eH : (fibreComplex χ F).homology 0 ≅ S.homology :=
    (fibreComplex χ F).homologyIsoSc' (-1) 0 1 (by simp) (by simp)
  obtain ⟨hrk, hfd⟩ := finrank_fibre_ulift χ 1 (F.X 0) e₀
  have : FiniteDimensional K S.X₂ := hfd
  have hrk' : Module.finrank K S.X₂ = 1 := hrk
  have : Nontrivial S.homology := eH.toLinearEquiv.symm.toEquiv.nontrivial
  obtain ⟨_, hH⟩ := finrank_homology_le_finrank_ker S
  have hpos := Module.finrank_pos (R := K) (M := S.homology)
  have hle := Submodule.finrank_le (LinearMap.ker S.g.hom)
  have htop : LinearMap.ker S.g.hom = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have hg : ∀ x : S.X₂, S.g x = 0 := fun x =>
    (htop ▸ Submodule.mem_top : x ∈ LinearMap.ker S.g.hom)
  ext x
  refine (fibreElt_eq_zero_iff_of_injective χ hχ (F.X 1) _).1 ?_
  rw [← map_fibreElt]
  exact hg (fibreElt χ _ x)

/-- **Over a local domain the generator of the degree-zero term is a cycle with nonzero special
fibre**, in the situation of
`StacksDraft.Perfect.FibreCycleLift.d_zero_one_eq_zero_of_nontrivial_generic`: the differential
out of `F⁰` vanishes, and a generator `z` of `F⁰ ≅ A` has nonzero image in `F⁰ ⊗_A κ` because
the images of the multiples of `z` span the one-dimensional space `F⁰ ⊗_A κ`. -/
theorem exists_cycle_fibreElt_ne_zero_of_nontrivial_generic {K : Type u} [Field K]
    (χ : A →+* K) (hχ : Function.Injective χ) (F : CochainComplex (ModuleCat.{u} A) ℤ)
    (e₀ : F.X 0 ≅ ModuleCat.of A (ULift.{u} (Fin 1 → A))) [Module.Free A (F.X 1)]
    (hgen : Nontrivial ((fibreComplex χ F).homology 0)) :
    F.d 0 1 = 0 ∧ ∃ z : F.X 0, F.d 0 1 z = 0 ∧
      fibreElt (IsLocalRing.residue A) (F.X 0) z ≠ 0 := by
  have hd := d_zero_one_eq_zero_of_nontrivial_generic χ hχ F e₀ hgen
  refine ⟨hd, e₀.inv (ULift.up fun _ => 1), by rw [hd]; rfl, fun hz => ?_⟩
  let ρ := IsLocalRing.residue A
  have hall : ∀ x : F.X 0, fibreElt ρ (F.X 0) x = 0 := by
    intro x
    have hx : x = (e₀.hom x).down 0 • e₀.inv (ULift.up fun _ => 1) := by
      rw [← map_smul]
      have : (e₀.hom x).down 0 • (ULift.up fun _ : Fin 1 => (1 : A)) = e₀.hom x := by
        ext j
        obtain rfl : j = 0 := Subsingleton.elim j 0
        change (e₀.hom x).down 0 * 1 = (e₀.hom x).down 0
        rw [mul_one]
      rw [this]
      exact (ConcreteCategory.congr_hom e₀.hom_inv_id x).symm
    rw [hx, fibreElt_smul, hz, smul_zero]
  have hbot : (⊤ : Submodule (IsLocalRing.ResidueField A)
      ((ModuleCat.extendScalars ρ).obj (F.X 0))) = ⊥ := by
    rw [← fibreElt_span ρ (F.X 0), eq_bot_iff]
    exact (Submodule.span_mono (Set.range_subset_iff.2 hall)).trans
      (Submodule.span_singleton_eq_bot.2 rfl).le
  have hrk := (finrank_fibre_ulift ρ 1 (F.X 0) e₀).1
  rw [← finrank_top, hbot, finrank_bot] at hrk
  exact zero_ne_one hrk

end Generic

end StacksDraft.Perfect.FibreCycleLift

end
