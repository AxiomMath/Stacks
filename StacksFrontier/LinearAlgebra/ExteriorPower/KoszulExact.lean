module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationArrow
public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# Exactness of the Koszul complex of a functional

Let `R` be a commutative ring, `M` an `R`-module and `ψ : M → R` a linear functional. The Koszul
complex of `ψ` is `⋯ ⟶ ⋀² M ⟶ M ⟶ R`, with the contraction against `ψ` as differential. It is
exact at `⋀ⁿ⁺¹ M` for every `n`

* if `ψ` takes the value `1` somewhere, wedging with a preimage of `1` being a contracting
  homotopy; and
* if `M` has a finite basis `e` and the sequence `ψ(e₁), …, ψ(e_r)` is Koszul-regular, the
  complex then being the Koszul complex `K_•(ψ(e₁), …, ψ(e_r))` of Stacks 0623.

## Main results

* `Koszul.exists_d_eq_of_isZero_homology`: if the homology of the Koszul complex of a sequence
  vanishes in degree `n + 1`, every cycle of degree `n + 1` is a boundary.
* `exteriorPower.exists_contraction_eq_of_eq_one`: the Koszul complex of a functional taking the
  value `1` is exact.
* `exteriorPower.exists_contraction_eq_of_isKoszulRegular`: the Koszul complex of a functional
  with Koszul-regular values on a finite basis is exact in every positive degree.
-/

@[expose] public section

universe u

namespace Koszul

variable {R : Type u} [CommRing R]

/-- **Exactness of the Koszul complex of a sequence, elementwise**: vanishing of its homology in
degree `n + 1` says that every cycle of degree `n + 1` is a boundary. -/
theorem exists_d_eq_of_isZero_homology {r : ℕ} (f : Fin r → R) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero ((seqComplex f).homology (n + 1)))
    (x : ⋀[R]^(n + 1) (Fin r → R)) (hx : d (seqDual f) n x = 0) :
    ∃ y : ⋀[R]^(n + 2) (Fin r → R), d (seqDual f) (n + 1) y = x := by
  have hex : (seqComplex f).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 h
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)] at hex
  obtain ⟨y, hy⟩ := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).1 hex x (by
    change ((seqComplex f).d (n + 1) n).hom x = 0
    rwa [seqComplex_d f n])
  refine ⟨y, ?_⟩
  change ((seqComplex f).d (n + 2) (n + 1)).hom y = x at hy
  rwa [seqComplex_d f (n + 1)] at hy

end Koszul

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- **The Koszul complex of a functional taking the value `1` is exact**: if `ψ v = 1`, every
cycle `z` of degree `n + 1` is the contraction of some `w` of degree `n + 2`. -/
theorem exists_contraction_eq_of_eq_one (ψ : M →ₗ[R] R) {v : M} (hv : ψ v = 1) (n : ℕ)
    (z : ⋀[R]^(n + 1) M) (hz : contraction ψ n z = 0) :
    ∃ w : ⋀[R]^(n + 2) M, contraction ψ (n + 1) w = z := by
  refine ⟨wedgeLeft v (n + 1) z, ?_⟩
  simpa only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, hz, map_zero,
    add_zero, LinearMap.id_coe, id_eq, hv, one_smul] using
    DFunLike.congr_fun (contraction_comp_wedgeLeft_add_wedgeLeft_comp_contraction ψ v n) z

/-- **The Koszul complex of a functional with Koszul-regular values on a basis is exact** in
every positive degree. -/
theorem exists_contraction_eq_of_isKoszulRegular {r : ℕ} (ψ : M →ₗ[R] R)
    (e : Module.Basis (Fin r) R M) (hreg : Koszul.IsKoszulRegular (fun i => ψ (e i))) (n : ℕ)
    (z : ⋀[R]^(n + 1) M) (hz : contraction ψ n z = 0) :
    ∃ w : ⋀[R]^(n + 2) M, contraction ψ (n + 1) w = z := by
  set f : Fin r → R := fun i ↦ ψ (e i)
  set g : M ≃ₗ[R] (Fin r → R) := e.equivFun
  have hψ : ψ = Koszul.seqDual f ∘ₗ g.toLinearMap := by
    refine e.ext fun i ↦ ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change ψ (e i) = Koszul.seqDual f (e.equivFun (e i))
    have he : e.equivFun (e i) = Pi.single i 1 := by
      funext j
      rw [Module.Basis.equivFun_self]
      simp [Pi.single_apply, eq_comm]
    rw [he, Koszul.seqDual_single]
  have hnat : ∀ m : ℕ, map m g.toLinearMap ∘ₗ contraction ψ m =
      contraction (Koszul.seqDual f) m ∘ₗ map (m + 1) g.toLinearMap := fun m ↦ by
    rw [hψ]
    exact map_comp_contraction _ _ m
  have hz' : Koszul.d (Koszul.seqDual f) n (map (n + 1) g.toLinearMap z) = 0 := by
    rw [← contraction_eq_koszulD, ← LinearMap.comp_apply, ← hnat, LinearMap.comp_apply, hz,
      map_zero]
  obtain ⟨w', hw'⟩ := Koszul.exists_d_eq_of_isZero_homology f n (hreg (n + 1) (by omega)) _ hz'
  refine ⟨map (n + 2) g.symm.toLinearMap w', ?_⟩
  refine map_injective (n := n + 1) g.symm.toLinearMap (LinearMap.ext g.symm_apply_apply) ?_
  rwa [← LinearMap.comp_apply (map (n + 1) g.toLinearMap), hnat, LinearMap.comp_apply,
    ← LinearMap.comp_apply (map (n + 2) g.toLinearMap), ← map_comp,
    show g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id from
      LinearMap.ext g.apply_symm_apply, map_id, LinearMap.id_apply, contraction_eq_koszulD]

end exteriorPower
