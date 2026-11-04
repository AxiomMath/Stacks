module

public import Mathlib.Algebra.MvPolynomial.Funext
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpanningTupleOpen

/-!
# A smooth member of a linear system defined over the base field

Let `k` be an infinite field, `X` a smooth `k`-scheme, `L` an invertible `𝒪_X`-module and
`ψ : V → Γ(X, L)` a finite dimensional linear system generating `L` whose morphism to `𝐏(V)` is
an immersion. [Stacks, Tag 0FD6] says that `H_v = Z(ψ(v))` is smooth for general `v`, that is
for `v` in a nonempty open of the parameter space `𝔸^r_k`. Over an infinite field such an open
has `k`-points, and they can be chosen off any finite family of hyperplanes of `V`; this file
records that, in the form the iterated Bertini argument of [Stacks, Tag 0FH5] consumes: there is
a vector `v ∈ V` itself, not one over an extension of `k`, with `Z(ψ(v))` smooth over `k` and
`ℓ(v) ≠ 0` for finitely many prescribed nonzero linear forms `ℓ` on `V`.

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_parameterPoint_mem_and_ne_zero`: a nonempty open of the
  parameter space contains the `k`-point of a vector avoiding finitely many hyperplanes.
* `Stacks.Bertini.FamilyDivisors.smooth_zeroScheme_of_smooth_specializedDivisor`: the divisor
  `H_v` over `k` itself is the zero scheme of `ψ(v)` on `X`.
* `Stacks.Bertini.FamilyDivisors.exists_smooth_zeroScheme_sectionOf`: a vector `v ∈ V` with
  `Z(ψ(v))` smooth over `k` and off finitely many hyperplanes.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- The linear polynomial on the parameter space recording a linear form on `V` in the
coordinates of the chosen basis. -/
def linearFormPolynomial (ℓ : D.V →ₗ[D.k] D.k) : MvPolynomial D.basisIndex D.k :=
  ∑ i : Fin (Module.finrank D.k D.V), C (ℓ (D.basis i)) * MvPolynomial.X (ULift.up i)

/-- Evaluating `linearFormPolynomial ℓ` at the coordinates `a` gives the value of `ℓ` on the
vector `∑ i, a i • basis i`. -/
theorem eval_linearFormPolynomial (ℓ : D.V →ₗ[D.k] D.k) (a : Fin (Module.finrank D.k D.V) → D.k) :
    eval (fun i : D.basisIndex => a i.down) (D.linearFormPolynomial ℓ) =
      ℓ (∑ i, a i • D.basis i) := by
  simp [linearFormPolynomial, map_sum, mul_comm]

/-- The polynomial of a nonzero linear form is nonzero. -/
theorem linearFormPolynomial_ne_zero {ℓ : D.V →ₗ[D.k] D.k} (hℓ : ℓ ≠ 0) :
    D.linearFormPolynomial ℓ ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, ℓ (D.basis i) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hℓ (D.basis.ext fun i => by simpa using h i)
  intro h0
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single (ULift.up i) 1)) h0
  rw [linearFormPolynomial, MvPolynomial.coeff_sum] at hc
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, coeff_zero] at hc
  rw [Finset.sum_eq_single i] at hc
  · exact hi (by simpa using hc)
  · intro j _ hj
    have : Finsupp.single (ULift.up j : D.basisIndex) 1 ≠ Finsupp.single (ULift.up i) 1 := by
      intro h
      exact hj (ULift.up_injective (Finsupp.single_left_injective one_ne_zero h))
    simp [this]
  · simp

/-- The spectrum map of the identity algebra map `k → k` is the identity. -/
private theorem spec_map_algebraMap_self (k : Type u) [CommRing k] :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- The parameter point of a `k`-point is the point of `𝔸^r_k` over `Spec k` with those
coordinates. -/
theorem parameterPoint_self (a : Fin (Module.finrank D.k D.V) → D.k) :
    D.parameterPoint a = AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of D.k)))
      (fun q => (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv (a q.down)) := by
  simp only [parameterPoint, spec_map_algebraMap_self]

/-- **A nonempty open of the parameter space contains the `k`-point of a vector avoiding
finitely many hyperplanes**, when `k` is infinite. The open contains a nonempty basic open of a
polynomial function, and the product of that polynomial with the linear forms is a nonzero
polynomial over an infinite field, so it does not vanish at some `k`-point. -/
theorem exists_parameterPoint_mem_and_ne_zero [Infinite D.k]
    (U : (𝔸(D.basisIndex; Spec (.of D.k))).Opens) (hU : U.1.Nonempty)
    {ι : Type*} [Finite ι] (ℓ : ι → D.V →ₗ[D.k] D.k) (hℓ : ∀ c, ℓ c ≠ 0) :
    ∃ a : Fin (Module.finrank D.k D.V) → D.k,
      (∀ p : Spec (.of D.k), D.parameterPoint a p ∈ U) ∧ ∀ c, ℓ c (∑ i, a i • D.basis i) ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨p₀, hp₀⟩ := hU
  obtain ⟨-, ⟨-, ⟨G, rfl⟩, rfl⟩, hp₀G, hGU⟩ :=
    (isBasis_basicOpen (𝔸(D.basisIndex; Spec (.of D.k)))).exists_subset_of_mem_open hp₀ U.isOpen
  have hG0 : G ≠ 0 := by
    rintro rfl
    simp at hp₀G
  set e := Scheme.ΓSpecIso (CommRingCat.of D.k)
  set P : MvPolynomial D.basisIndex D.k :=
    MvPolynomial.map e.hom.hom ((AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).hom G) with hP
  have hPG : (AffineSpace.ΓIso D.basisIndex (Spec (.of D.k))).inv (MvPolynomial.map e.inv.hom P) =
      G := by
    rw [hP, MvPolynomial.map_map]
    have : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, e.hom_inv_id]; rfl
    rw [this, MvPolynomial.map_id, ← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  have hP0 : P ≠ 0 := by
    intro h0
    apply hG0
    rw [← hPG, h0, map_zero, map_zero]
  set Q := P * ∏ c, D.linearFormPolynomial (ℓ c)
  have hQ0 : Q ≠ 0 :=
    mul_ne_zero hP0 (Finset.prod_ne_zero_iff.mpr fun c _ => D.linearFormPolynomial_ne_zero (hℓ c))
  obtain ⟨a', ha'⟩ : ∃ a' : D.basisIndex → D.k, eval a' Q ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hQ0 (MvPolynomial.funext fun x => by simpa using h x)
  refine ⟨fun i => a' (ULift.up i), fun p => ?_, fun c => ?_⟩
  · apply hGU
    have hval := AffineSpace.homOfVector_appTop_ΓIso_inv_map a' P
    rw [hPG] at hval
    rw [D.parameterPoint_self]
    show p ∈ _ ⁻¹ᵁ (𝔸(D.basisIndex; Spec (.of D.k))).basicOpen G
    rw [Scheme.preimage_basicOpen_top]
    have hfun : (fun q : D.basisIndex => e.inv (a' (ULift.up q.down))) =
        fun q => e.inv (a' q) := rfl
    rw [hfun, hval, Scheme.basicOpen_of_isUnit]
    · exact Opens.mem_top p
    · refine IsUnit.map e.inv.hom (isUnit_iff_ne_zero.mpr ?_)
      intro h0
      exact ha' (by simp [Q, h0])
  · have h := D.eval_linearFormPolynomial (ℓ c) (fun i => a' (ULift.up i))
    rw [← h]
    intro h0
    apply ha'
    simp only [Q, eval_mul, eval_prod]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ c) h0)

/-- **`H_v` over `k` itself is the zero scheme of `ψ(v)`.** For a `k`-point the base change
`X_k` is `X`, and the divisor `H_v` of [Stacks, Tag 0G47] is the zero scheme of the section
`ψ(Σ aᵢ vᵢ)`; so smoothness of the one is smoothness of the other. -/
theorem smooth_zeroScheme_of_smooth_specializedDivisor (a : Fin (Module.finrank D.k D.V) → D.k)
    (h : Smooth ((D.specializedDivisor D.k a).subschemeι ≫ D.baseChangeToSpec D.k)) :
    Smooth ((Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf (∑ i, a i • D.basis i))).subschemeι ≫
      D.toBase) := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap D.k D.k))
  have hφ : φ = 𝟙 _ := spec_map_algebraMap_self D.k
  have : IsIso φ := by rw [hφ]; infer_instance
  set e : D.baseChange D.k ⟶ D.X := D.baseChangeToX D.k
  have : IsIso e := by
    show IsIso (pullback.fst D.toBase φ)
    infer_instance
  have hsnd : D.baseChangeToSpec D.k = e ≫ D.toBase := by
    show pullback.snd D.toBase φ = pullback.fst D.toBase φ ≫ D.toBase
    rw [pullback.condition, hφ, Category.comp_id]
  -- the scalars of the base change are the pulled-back scalars
  have hscalar : ∀ c : D.k, D.baseChangeScalar D.k c = e.appTop (D.baseScalar c) := by
    intro c
    show (pullback.snd D.toBase φ).appTop ((Scheme.ΓSpecIso (.of D.k)).inv c) = _
    rw [show pullback.snd D.toBase φ = e ≫ D.toBase from hsnd, Scheme.Hom.comp_appTop]
    rfl
  set s := D.sectionOf (∑ i, a i • D.basis i)
  have hsec : D.specializedSection D.k a = pullbackGlobalSections e D.L s := by
    have hs : s = ∑ i, D.baseScalar (a i) • D.sectionOf (D.basis i) := by
      show D.ψ (∑ i, a i • D.basis i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => D.sectionOf_smul _ _
    rw [specializedSection, hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul, hscalar]
  have hdiv : D.specializedDivisor D.k a = (Stacks.Divisors.zeroScheme D.X D.L s).comap e := by
    rw [specializedDivisor, hsec]
    exact Stacks.Divisors.zeroScheme_pullback e D.L s
  set I := Stacks.Divisors.zeroScheme D.X D.L s
  have hpb := Scheme.IdealSheafData.isPullback_comap I e
  set m := Scheme.IdealSheafData.subschemeMap (I.comap e) I e (I.le_map_comap e)
  have : IsIso m := hpb.isIso_snd_of_isIso
  rw [hdiv, hsnd, ← Category.assoc, hpb.w, Category.assoc] at h
  have heq : I.subschemeι ≫ D.toBase = inv m ≫ (m ≫ I.subschemeι ≫ D.toBase) := by simp
  rw [heq]
  infer_instance

/-- **A smooth member of the linear system defined over `k`, off finitely many hyperplanes.**
In the situation of [Stacks, Tag 0FD6] over an infinite field `k` — `X` smooth over `k`, `V`
generating `L`, and `X → 𝐏(V)` an immersion — for every finite family of nonzero linear forms
`ℓ` on `V` there is a vector `v ∈ V` with `ℓ(v) ≠ 0` for each of them and with `Z(ψ(v))` smooth
over `k`. -/
theorem exists_smooth_zeroScheme_sectionOf [Infinite D.k] [Smooth D.toBase]
    (hgen : D.Generates)
    (himm : ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) D.k D.V),
      D.IsImmersive b (D.generatesBy_basis hgen b))
    {ι : Type*} [Finite ι] (ℓ : ι → D.V →ₗ[D.k] D.k) (hℓ : ∀ c, ℓ c ≠ 0) :
    ∃ v : D.V, Smooth ((Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf v)).subschemeι ≫
      D.toBase) ∧ ∀ c, ℓ c v ≠ 0 := by
  obtain ⟨U, hU, hgenU⟩ := D.forGeneral_smooth_specializedDivisor hgen himm
  obtain ⟨a, ha, hℓa⟩ := D.exists_parameterPoint_mem_and_ne_zero U hU ℓ hℓ
  exact ⟨_, D.smooth_zeroScheme_of_smooth_specializedDivisor a (hgenU D.k a ha a rfl), hℓa⟩

end Stacks.Bertini.FamilyDivisors

end
