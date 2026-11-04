module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaIsomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension

/-!
# The determinant of an exact periodic complex

Let `R` be a local ring and let `φ` and `ψ` be the two differentials of an exact two-periodic
complex on a finite-length `R`-module `M`. The two short exact sequences formed from their
images give two canonical identifications of the determinant of `M`. After interchanging the
two tensor factors, their ratio is a unit of the residue field, called the periodic
determinant.

## Main definitions

* `AlgebraicGeometry.periodicGamma` is the determinant map of the short exact sequence
  `0 → range ψ → M → range φ → 0`.
* `AlgebraicGeometry.IsPeriodicDeterminant` is the defining property of the periodic
  determinant.
* `AlgebraicGeometry.periodicDeterminant` is the determinant of an exact two-periodic complex.

## Main results

* `AlgebraicGeometry.existsUnique_periodicDeterminant`: the defining property determines a
  unique residue-field unit.
* `AlgebraicGeometry.periodicDeterminant_spec` and
  `AlgebraicGeometry.eq_periodicDeterminant` are the two halves of that characterization.

## Implementation notes

The two-periodic complex is presented by endomorphisms `φ` and `ψ` together with the two
`Function.Exact` assertions. Instead of choosing an inverse for `periodicGamma φ ψ`, the
defining equality is multiplied on the right by it: it says directly that `periodicGamma ψ φ`
after the tensor symmetry is the prescribed scalar multiple of `periodicGamma φ ψ`. Since the
determinant maps are isomorphisms, this is equivalent to the composition in the source.

## References

* [Stacks Project, Tag 02PJ](https://stacks.math.columbia.edu/tag/02PJ)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- The determinant map associated to `0 → LinearMap.range ψ → M → LinearMap.range φ → 0` in
an exact periodic complex. -/
noncomputable def periodicGamma
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    determinant R (LinearMap.range ψ) ⊗[IsLocalRing.ResidueField R]
        determinant R (LinearMap.range φ) →ₗ[IsLocalRing.ResidueField R] determinant R M :=
  determinantExactSequenceMap (LinearMap.range ψ).subtype φ.rangeRestrict
    (Submodule.injective_subtype (LinearMap.range ψ))
    (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ))
    (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      exact hψφ.linearMap_ker_eq)
    (hM.of_injective (LinearMap.range ψ).subtype_injective) hM
    (hM.of_surjective (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict φ)))

/-- A residue-field unit has the defining property of the determinant of an exact periodic
complex when, up to the prescribed sign, it compares the two determinant exact-sequence maps
after interchanging their tensor factors. -/
def IsPeriodicDeterminant
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M)
    (d : (IsLocalRing.ResidueField R)ˣ) : Prop :=
  periodicGamma ψ φ hφψ hM ∘ₗ
      (TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R (LinearMap.range ψ))
        (determinant R (LinearMap.range φ))).toLinearMap =
    (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R (LinearMap.range φ) * moduleLength R (LinearMap.range ψ))) *
      (d : IsLocalRing.ResidueField R)) • periodicGamma φ ψ hψφ hM

/-- The determinant map of an exact periodic complex is bijective. -/
private theorem periodicGamma_bijective
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    Function.Bijective (periodicGamma φ ψ hψφ hM) := by
  unfold periodicGamma
  exact determinantExactSequenceMap_bijective _ _ _ _ _ _ _ _

/-- There is a unique residue-field unit satisfying the determinant comparison for an exact
finite-length periodic complex. -/
theorem existsUnique_periodicDeterminant
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    ∃! d : (IsLocalRing.ResidueField R)ˣ, IsPeriodicDeterminant φ ψ hφψ hψφ hM d := by
  let K := IsLocalRing.ResidueField R
  let A := determinant R (LinearMap.range ψ)
  let B := determinant R (LinearMap.range φ)
  let D := determinant R M
  let T := A ⊗[K] B
  let swap : T →ₗ[K] B ⊗[K] A :=
    (TensorProduct.comm K A B).toLinearMap
  let f : T →ₗ[K] D := (periodicGamma ψ φ hφψ hM).comp swap
  let g : T →ₗ[K] D := periodicGamma φ ψ hψφ hM
  have hD : Module.finrank K D = 1 := finrank_determinant_eq_one hM
  have hswap : Function.Bijective swap := (TensorProduct.comm K A B).bijective
  have hf : Function.Bijective f := (periodicGamma_bijective ψ φ hφψ hM).comp hswap
  have hg : Function.Bijective g := periodicGamma_bijective φ ψ hψφ hM
  let : Module.Finite K D := Module.finite_of_finrank_eq_succ hD
  let ge : T ≃ₗ[K] D := LinearEquiv.ofBijective g hg
  let e : D →ₗ[K] D := f.comp ge.symm.toLinearMap
  have he : Function.Bijective e := hf.comp ge.symm.bijective
  obtain ⟨c, hc, hc_unique⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hD e
  have hc_ne : c ≠ 0 := by
    intro hc0
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hD]; norm_num)
    have he_zero : e = 0 := by simpa [hc0] using hc
    exact hx (he.injective (by simp [he_zero]))
  let cu : Kˣ := Units.mk0 c hc_ne
  let s : K := (-1 : K) ^
    (moduleLength R (LinearMap.range φ) * moduleLength R (LinearMap.range ψ))
  have hs : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  let su : Kˣ := Units.mk0 s hs
  refine ⟨su⁻¹ * cu, ?_, ?_⟩
  · show f = (s * ((su⁻¹ * cu : Kˣ) : K)) • g
    have hscalar : c = s * ((su⁻¹ * cu : Kˣ) : K) := by
      show c = s * (s⁻¹ * c)
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    calc
      f = e.comp g := by ext x; simp [e, ge]
      _ = (c • LinearMap.id).comp g := by rw [hc]
      _ = (s * ((su⁻¹ * cu : Kˣ) : K)) • g := by
        ext x
        simp [hscalar]
  · intro d hd
    change f = (s * (d : K)) • g at hd
    have hd' : e = (s * (d : K)) • LinearMap.id := by
      have hginv : g.comp ge.symm.toLinearMap = LinearMap.id :=
        LinearMap.ext (fun x => ge.apply_symm_apply x)
      calc
        e = f.comp ge.symm.toLinearMap := rfl
        _ = ((s * (d : K)) • g).comp ge.symm.toLinearMap := by rw [hd]
        _ = (s * (d : K)) • LinearMap.id := by
          rw [LinearMap.smul_comp, hginv]
    have hdc : s * (d : K) = c := hc_unique _ hd'
    exact eq_inv_mul_of_mul_eq (Units.ext (by simpa [su, cu, s] using hdc))

/-- **Stacks Project, Tag 02PJ.** The determinant of an exact two-periodic complex on a
finite-length module over a local ring. -/
@[stacks 02PJ]
noncomputable def periodicDeterminant
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    (IsLocalRing.ResidueField R)ˣ :=
  Classical.choose (existsUnique_periodicDeterminant φ ψ hφψ hψφ hM)

/-- The periodic determinant satisfies its defining signed comparison of determinant maps. -/
theorem periodicDeterminant_spec
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    IsPeriodicDeterminant φ ψ hφψ hψφ hM
      (periodicDeterminant φ ψ hφψ hψφ hM) :=
  (Classical.choose_spec (existsUnique_periodicDeterminant φ ψ hφψ hψφ hM)).1

/-- A residue-field unit satisfying the signed comparison of determinant maps is the periodic
determinant. -/
theorem eq_periodicDeterminant
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M)
    {d : (IsLocalRing.ResidueField R)ˣ}
    (hd : IsPeriodicDeterminant φ ψ hφψ hψφ hM d) :
    d = periodicDeterminant φ ψ hφψ hψφ hM :=
  (Classical.choose_spec
    (existsUnique_periodicDeterminant φ ψ hφψ hψφ hM)).2 d hd

end AlgebraicGeometry

end
