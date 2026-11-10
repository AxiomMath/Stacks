module

public import StacksFrontier.RingTheory.Ideal.MinimalGeneratorsAtPrime
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Lifting a presentation along a surjection, for Stacks 0CJV

Let `π : B' → A₀` be a surjective ring map with kernel `J`, and let `D` be a finitely presented
`A₀`-algebra with a prime `𝔭`. Present `D = A₀[x₁, …, xₙ] / I`, choose minimal generators
`f₁, …, fᵣ` of `I` at `𝔭` together with `g ∉ 𝔭` such that `g I ⊆ (f)`, and lift `f` and `g` to
`f''`, `g''` in `B'[x]`. With `M = B'[x][1/g'']`, `S₁ = M / (f'')` and `X = S₁ / J S₁`, this
file shows that `X` is the localization of `D` at the image of `g`, compatibly with `B'`, and
that every relation among the images of the `f''` in `M / J M` has its coefficients in the prime
of `M / J M` lying under `𝔭`.

These are the ring-level inputs of the local step of Stacks 0CJV: the equations of an affine
member of the étale covering, inside an affine space over the chart of `𝒳`, lifted to the
thickened chart of `𝒳'`.
-/

@[expose] public section

open MvPolynomial

namespace Algebra.LiftedPresentation

universe u

variable {B' A₀ : Type u} [CommRing B'] [CommRing A₀] (π : B' →+* A₀)
  (hπ : Function.Surjective π) {n : ℕ} (g'' : MvPolynomial (Fin n) B')

/-- The ring `M ⧸ J M`, for `M = B'[x][1/g'']` and `J` the kernel of `π`. -/
abbrev AmbientReduced :=
  Localization.Away g'' ⧸ (RingHom.ker π).map (algebraMap B' (Localization.Away g''))

/-- The map `A₀ → M ⧸ J M` induced by `B' → M`. -/
noncomputable def baseReduction : A₀ →+* AmbientReduced π g'' :=
  (Ideal.Quotient.lift (RingHom.ker π)
    ((Ideal.Quotient.mk _).comp (algebraMap B' (Localization.Away g''))) (fun j hj => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hj)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- The map `A₀ → M ⧸ J M` sends `π b` to the class of the image of `b` in `M`. -/
theorem baseReduction_apply (b : B') :
    baseReduction π hπ g'' (π b) = Ideal.Quotient.mk _ (algebraMap B' _ b) := by
  simp only [baseReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingHom.quotientKerEquivOfSurjective_symm_apply,
    Ideal.Quotient.lift_mk]

/-- The reduction `A₀[x] → M ⧸ J M`. -/
noncomputable def reduction : MvPolynomial (Fin n) A₀ →+* AmbientReduced π g'' :=
  eval₂Hom (baseReduction π hπ g'') fun i =>
    Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) B') (Localization.Away g'') (X i))

/-- The reduction `A₀[x] → M ⧸ J M` sends the image under `π` of a polynomial `p ∈ B'[x]` to the
class of the image of `p` in `M`. -/
theorem reduction_map (p : MvPolynomial (Fin n) B') :
    reduction π hπ g'' (map π p) =
      Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') p) := by
  have h : (reduction π hπ g'').comp (map π) =
      (Ideal.Quotient.mk _).comp (algebraMap _ (Localization.Away g'')) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, map_C, reduction, eval₂Hom_C, baseReduction_apply]
      rw [IsScalarTower.algebraMap_apply B' (MvPolynomial (Fin n) B') (Localization.Away g''),
        MvPolynomial.algebraMap_eq]
    · intro i
      simp [reduction]
  exact RingHom.congr_fun h p

/-- The reduction of the image of `g''` under `π` is a unit of `M ⧸ J M`. -/
theorem isUnit_reduction : IsUnit (reduction π hπ g'' (map π g'')) := by
  rw [reduction_map]
  exact (IsLocalization.Away.algebraMap_isUnit g'').map _

/-- A polynomial over `A₀` whose reduction in `M ⧸ J M` vanishes is killed by a power of the
image of `g''` under `π`. -/
theorem exists_pow_mul_eq_zero_of_reduction {x : MvPolynomial (Fin n) A₀}
    (hx : reduction π hπ g'' x = 0) : ∃ m : ℕ, map π g'' ^ m * x = 0 := by
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective π hπ x
  rw [reduction_map, Ideal.Quotient.eq_zero_iff_mem,
    IsScalarTower.algebraMap_eq B' (MvPolynomial (Fin n) B') (Localization.Away g''),
    ← Ideal.map_map, IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g'')] at hx
  obtain ⟨⟨⟨i, hi⟩, ⟨_, k, rfl⟩⟩, h⟩ := hx
  simp only [← map_mul] at h
  obtain ⟨⟨_, l, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers g'') h
  have hi0 : map π i = 0 := by
    rw [← RingHom.mem_ker, MvPolynomial.ker_map, ← MvPolynomial.algebraMap_eq]
    exact hi
  refine ⟨l + k, ?_⟩
  have := congrArg (map π) hc
  simp only [map_mul, map_pow, hi0, mul_zero] at this
  rw [pow_add, mul_assoc, ← this]
  ring

/-- Every element of `M ⧸ J M`, multiplied by a suitable power of the reduction of the image of
`g''`, is the reduction of a polynomial over `A₀`. -/
theorem exists_mul_pow_eq_reduction (z : AmbientReduced π g'') :
    ∃ (k : ℕ) (x : MvPolynomial (Fin n) A₀),
      z * reduction π hπ g'' (map π g'') ^ k = reduction π hπ g'' x := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨⟨p, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g'') m
  refine ⟨k, map π p, ?_⟩
  rw [reduction_map, ← map_pow, reduction_map, ← map_mul, ← map_pow]
  exact congrArg _ h

/-- If `gᵐ * (a - b) = 0` for some `m`, then `gᵐ * a = gᵐ * b` for some `m`. -/
private theorem exists_pow_mul_eq_of_exists_pow_mul_sub_eq_zero {R : Type*} [CommRing R]
    {g a b : R} (h : ∃ m : ℕ, g ^ m * (a - b) = 0) : ∃ m : ℕ, g ^ m * a = g ^ m * b := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rwa [mul_sub, sub_eq_zero] at hm⟩

/-- **`M ⧸ J M` is the localization of `A₀[x]` at the image of `g''`.** -/
theorem isLocalization_reduction :
    @IsLocalization.Away _ _ (map π g'') (AmbientReduced π g'') _
      (reduction π hπ g'').toAlgebra := by
  let := (reduction π hπ g'').toAlgebra
  refine IsLocalization.Away.mk _ (isUnit_reduction π hπ g'') ?_ ?_
  · intro z
    obtain ⟨k, x, h⟩ := exists_mul_pow_eq_reduction π hπ g'' z
    exact ⟨k, x, h⟩
  · intro a b hab
    have h0 : reduction π hπ g'' (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hab
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_reduction π hπ g'' h0
    exact exists_pow_mul_eq_of_exists_pow_mul_sub_eq_zero ⟨m, hm⟩

variable {r : ℕ} (f'' : Fin r → MvPolynomial (Fin n) B')

/-- Finitely many elements of `M ⧸ J M` become reductions of polynomials over `A₀` after
multiplying by a common power of the reduction of the image of `g''`. -/
private theorem exists_reduction_eq_pow_mul (a : Fin r → AmbientReduced π g'') :
    ∃ (k : ℕ) (b : Fin r → MvPolynomial (Fin n) A₀), ∀ i,
      reduction π hπ g'' (b i) = reduction π hπ g'' (map π g'' ^ k) * a i := by
  let := (reduction π hπ g'').toAlgebra
  have := isLocalization_reduction π hπ g''
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers (map π g'')) Finset.univ a
  choose b hb using fun i => hk i (Finset.mem_univ i)
  refine ⟨k, b, fun i => ?_⟩
  rw [← RingHom.algebraMap_toAlgebra (reduction π hπ g''), hb i, Algebra.smul_def]

/-- The ring `S₁ = M ⧸ (f'')`. -/
abbrev Chart :=
  Localization.Away g'' ⧸ Ideal.span (Set.range (algebraMap _ (Localization.Away g'') ∘ f''))

/-- The ring `X = S₁ ⧸ J S₁`. -/
abbrev Reduced := Chart g'' f'' ⧸ (RingHom.ker π).map (algebraMap B' (Chart g'' f''))

/-- The map `M ⧸ J M → X`. -/
noncomputable def toReduced : AmbientReduced π g'' →+* Reduced π g'' f'' :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)) (fun y hy => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsScalarTower.algebraMap_eq B' (Localization.Away g'') (Chart g'' f''), ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hy)

/-- The map `M ⧸ J M → X` sends the class of `m ∈ M` to the class of the image of `m` in `S₁`. -/
theorem toReduced_mk (m : Localization.Away g'') :
    toReduced π g'' f'' (Ideal.Quotient.mk _ m) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ m) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The map `M ⧸ J M → X` is surjective. -/
theorem toReduced_surjective : Function.Surjective (toReduced π g'' f'') := by
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact ⟨_, toReduced_mk π g'' f'' m⟩

/-- The reduction of the image of each `f''ᵢ` under `π` maps to zero in `X`. -/
theorem toReduced_reduction_f (i : Fin r) :
    toReduced π g'' f'' (reduction π hπ g'' (map π (f'' i))) = 0 := by
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range
      (algebraMap _ (Localization.Away g'') ∘ f''))) (algebraMap _ _ (f'' i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [reduction_map, toReduced_mk, h0, map_zero]

/-- An element of `M ⧸ J M` that maps to zero in `X` lies in the ideal generated by the
reductions of the images of the `f''ᵢ` under `π`. -/
theorem mem_span_of_toReduced_eq_zero {w : AmbientReduced π g''}
    (hw : toReduced π g'' f'' w = 0) :
    w ∈ Ideal.span (Set.range fun i => reduction π hπ g'' (map π (f'' i))) := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [toReduced_mk, Ideal.Quotient.eq_zero_iff_mem,
    IsScalarTower.algebraMap_eq B' (Localization.Away g'') (Chart g'' f''), ← Ideal.map_map,
    Ideal.Quotient.algebraMap_eq,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hw
  obtain ⟨m', hm', he⟩ := hw
  have hd : m - m' ∈ Ideal.span (Set.range (algebraMap _ (Localization.Away g'') ∘ f'')) := by
    rw [← Ideal.Quotient.eq]
    exact he.symm
  have hm0 : (Ideal.Quotient.mk ((RingHom.ker π).map
      (algebraMap B' (Localization.Away g'')))) m' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hm'
  have : Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap B' (Localization.Away g''))) m =
      Ideal.Quotient.mk _ (m - m') := by
    rw [map_sub, hm0, sub_zero]
  rw [this]
  have hmap := Ideal.mem_map_of_mem
    (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap B' (Localization.Away g'')))) hd
  rw [Ideal.map_span, ← Set.range_comp] at hmap
  convert hmap using 3
  ext i
  simp [reduction_map]

variable {D : Type u} [CommRing D] (σ : MvPolynomial (Fin n) A₀ →+* D)
  (hσ : Function.Surjective σ)

/-- If the image of `g''` under `π` times `x` lies in the ideal generated by the images of the
`f''ᵢ`, then the reduction of `x` maps to zero in `X`. -/
theorem toReduced_reduction_eq_zero
    {x : MvPolynomial (Fin n) A₀}
    (hx : map π g'' * x ∈ Ideal.span (Set.range fun i => map π (f'' i))) :
    toReduced π g'' f'' (reduction π hπ g'' x) = 0 := by
  let φ := (toReduced π g'' f'').comp (reduction π hπ g'')
  have hspan : Ideal.span (Set.range fun i => map π (f'' i)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact toReduced_reduction_f π hπ g'' f'' i
  have h1 : φ (map π g'' * x) = 0 := hspan hx
  rw [map_mul] at h1
  have hu : IsUnit ((toReduced π g'' f'') (reduction π hπ g'' (map π g''))) :=
    (isUnit_reduction π hπ g'').map _
  exact (hu.mul_right_eq_zero).mp h1

/-- The map `λ : D → X`. -/
noncomputable def lam
    (hgI : ∀ x, σ x = 0 → map π g'' * x ∈ Ideal.span (Set.range fun i => map π (f'' i))) :
    D →+* Reduced π g'' f'' :=
  (Ideal.Quotient.lift (RingHom.ker σ) ((toReduced π g'' f'').comp (reduction π hπ g''))
    (fun x hx => toReduced_reduction_eq_zero π hπ g'' f''
      (hgI x (RingHom.mem_ker.mp hx)))).comp
    (RingHom.quotientKerEquivOfSurjective hσ).symm.toRingHom

variable (hgI : ∀ x, σ x = 0 → map π g'' * x ∈ Ideal.span (Set.range fun i => map π (f'' i)))

/-- The map `λ : D → X` sends `σ x` to the image in `X` of the reduction of `x`. -/
theorem lam_apply (x : MvPolynomial (Fin n) A₀) :
    lam π hπ g'' f'' σ hσ hgI (σ x) = toReduced π g'' f'' (reduction π hπ g'' x) := by
  simp only [lam, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]

/-- **`X` is the localization of `D` at the image of `g`.** -/
theorem isLocalization_lam (hfI : ∀ i, σ (map π (f'' i)) = 0) :
    @IsLocalization.Away D _ (σ (map π g'')) (Reduced π g'' f'') _
      (lam π hπ g'' f'' σ hσ hgI).toAlgebra := by
  let := (lam π hπ g'' f'' σ hσ hgI).toAlgebra
  have hlam : ∀ x, algebraMap D (Reduced π g'' f'') (σ x) =
      toReduced π g'' f'' (reduction π hπ g'' x) := lam_apply π hπ g'' f'' σ hσ hgI
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hlam]
    exact (isUnit_reduction π hπ g'').map _
  · intro z
    obtain ⟨w, rfl⟩ := toReduced_surjective π g'' f'' z
    obtain ⟨k, x, h⟩ := exists_mul_pow_eq_reduction π hπ g'' w
    refine ⟨k, σ x, ?_⟩
    rw [hlam, hlam, ← h, map_mul, map_pow]
  · intro a b hab
    refine exists_pow_mul_eq_of_exists_pow_mul_sub_eq_zero ?_
    obtain ⟨x, hx⟩ := hσ (a - b)
    have h0 : toReduced π g'' f'' (reduction π hπ g'' x) = 0 := by
      rw [← hlam, hx, map_sub]
      exact sub_eq_zero.mpr hab
    have hmem := mem_span_of_toReduced_eq_zero π hπ g'' f'' h0
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hmem
    obtain ⟨k, b, hb⟩ := exists_reduction_eq_pow_mul π hπ g'' c
    have hred : reduction π hπ g'' (map π g'' ^ k * x - ∑ i, b i * map π (f'' i)) = 0 := by
      rw [map_sub, map_mul, map_sum, ← hc, Finset.mul_sum]
      refine sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_mul, ← mul_assoc, hb i]
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_reduction π hπ g'' hred
    refine ⟨m + k, ?_⟩
    rw [← hx, ← map_pow, ← map_mul]
    have hsum : map π g'' ^ (m + k) * x = map π g'' ^ m * ∑ i, b i * map π (f'' i) := by
      rw [pow_add, mul_assoc, ← sub_eq_zero, ← mul_sub]
      exact hm
    rw [hsum, map_mul, map_sum]
    simp [hfI]

/-- The `B'`-compatibility of `λ`. -/
theorem lam_comp_C (b : B') :
    lam π hπ g'' f'' σ hσ hgI (σ (C (π b))) =
      algebraMap B' (Reduced π g'' f'') b := by
  rw [lam_apply]
  simp only [reduction, eval₂Hom_C, baseReduction_apply, toReduced_mk]
  rfl

variable (𝔮 : Ideal (MvPolynomial (Fin n) A₀)) [𝔮.IsPrime]

/-- **Minimal relations survive the localization.** -/
theorem mem_map_reduction_of_relation (hg𝔮 : map π g'' ∉ 𝔮)
    (hrel : ∀ a : Fin r → MvPolynomial (Fin n) A₀, ∑ i, a i * map π (f'' i) = 0 →
      ∀ i, a i ∈ 𝔮)
    (a : Fin r → AmbientReduced π g'')
    (ha : ∑ i, a i * Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') (f'' i)) = 0)
    (i : Fin r) : a i ∈ 𝔮.map (reduction π hπ g'') := by
  obtain ⟨k, b, hb⟩ := exists_reduction_eq_pow_mul π hπ g'' a
  have hred : reduction π hπ g'' (∑ i, b i * map π (f'' i)) = 0 := by
    simp only [map_sum, map_mul, hb, reduction_map, mul_assoc, ← Finset.mul_sum, ha, mul_zero]
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_reduction π hπ g'' hred
  have hrel' := hrel (fun i => map π g'' ^ m * b i) (by
    rw [Finset.mul_sum] at hm
    simpa only [mul_assoc] using hm) i
  have hbi : b i ∈ 𝔮 := by
    rcases Ideal.IsPrime.mem_or_mem inferInstance hrel' with h | h
    · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance m h) hg𝔮
    · exact h
  have hmem : reduction π hπ g'' (map π g'' ^ k) * a i ∈ 𝔮.map (reduction π hπ g'') := by
    rw [← hb]
    exact Ideal.mem_map_of_mem _ hbi
  have hu : IsUnit (reduction π hπ g'' (map π g'' ^ k)) := by
    rw [map_pow]
    exact (isUnit_reduction π hπ g'').pow k
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have := Ideal.mul_mem_left _ v hmem
  rwa [← mul_assoc, hv, one_mul] at this

end Algebra.LiftedPresentation

namespace Algebra

open LiftedPresentation

universe u

variable {B' A₀ D : Type u} [CommRing B'] [CommRing A₀] [CommRing D] (π : B' →+* A₀)
  (hπ : Function.Surjective π)

include hπ in
/-- **A lifted presentation at a prime.** Let `π : B' → A₀` be surjective with kernel `J` and let
`D` be a finitely presented `A₀`-algebra with a prime `𝔭`. There are polynomials
`g'', f''₁, …, f''ᵣ ∈ B'[x₁, …, xₙ]` and, with `M = B'[x][1/g'']`, `S₁ = M ⧸ (f'')` and
`X = S₁ ⧸ J S₁`, a ring map `λ : D → X` such that

* `λ` is compatible with `B'`;
* `X` is, through `λ`, the localization of `D` at an element outside `𝔭`;
* every relation `∑ aᵢ f''ᵢ = 0` in `M ⧸ J M` has all its coefficients in the prime of
  `M ⧸ J M` under `𝔭 X`. -/
theorem exists_liftedPresentation [Algebra A₀ D] [Algebra.FinitePresentation A₀ D]
    (𝔭 : Ideal D) [𝔭.IsPrime] :
    ∃ (n r : ℕ) (g'' : MvPolynomial (Fin n) B') (f'' : Fin r → MvPolynomial (Fin n) B')
      (lam : D →+* Reduced π g'' f''),
      (lam.comp (algebraMap A₀ D)).comp π = algebraMap B' (Reduced π g'' f'') ∧
      (∃ d ∉ 𝔭, @IsLocalization.Away D _ d (Reduced π g'' f'') _ lam.toAlgebra) ∧
      ∀ a : Fin r → AmbientReduced π g'',
        ∑ i, a i * Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') (f'' i)) = 0 →
        ∀ i, a i ∈ ((((𝔭.map lam).comap (Ideal.Quotient.mk _)).comap
          (algebraMap (Localization.Away g'') (Chart g'' f''))).map (Ideal.Quotient.mk _)) := by
  obtain ⟨n, σ, hσ, hfg⟩ := ‹Algebra.FinitePresentation A₀ D›
  obtain ⟨r, f₀, hf₀I, ⟨g, hg𝔮, hgI⟩, hrel⟩ :=
    Ideal.exists_minimal_generators_at_prime (RingHom.ker σ.toRingHom) hfg
      (𝔭.comap σ.toRingHom)
  choose f'' hf'' using fun i => MvPolynomial.map_surjective π hπ (f₀ i)
  obtain ⟨g'', rfl⟩ := MvPolynomial.map_surjective π hπ g
  have hf₀ : f₀ = fun i => map π (f'' i) := funext fun i => (hf'' i).symm
  subst hf₀
  have hfI : ∀ i, σ.toRingHom (map π (f'' i)) = 0 := fun i => RingHom.mem_ker.mp (hf₀I i)
  have hgI' : ∀ x, σ.toRingHom x = 0 →
      map π g'' * x ∈ Ideal.span (Set.range fun i => map π (f'' i)) :=
    fun x hx => hgI x (RingHom.mem_ker.mpr hx)
  let L := lam π hπ g'' f'' σ.toRingHom hσ hgI'
  refine ⟨n, r, g'', f'', L, ?_,
    ⟨σ (map π g''), hg𝔮, isLocalization_lam π hπ g'' f'' _ hσ hgI' hfI⟩, ?_⟩
  · ext b
    have : algebraMap A₀ D (π b) = σ.toRingHom (C (π b)) := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes]
    simp only [RingHom.comp_apply, this]
    exact lam_comp_C π hπ g'' f'' σ.toRingHom hσ hgI' b
  · intro a ha i
    have h := mem_map_reduction_of_relation π hπ g'' f'' (𝔭.comap σ.toRingHom) hg𝔮
      (fun a ha => hrel a ha) a ha i
    have hle : (𝔭.comap σ.toRingHom).map (reduction π hπ g'') ≤
        (𝔭.map L).comap (toReduced π g'' f'') := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap] at hx ⊢
      rw [← lam_apply π hπ g'' f'' σ.toRingHom hσ hgI']
      exact Ideal.mem_map_of_mem _ hx
    have heq : (𝔭.map L).comap (toReduced π g'' f'') =
        (((𝔭.map L).comap (Ideal.Quotient.mk _)).comap
          (algebraMap (Localization.Away g'') (Chart g'' f''))).map (Ideal.Quotient.mk _) := by
      rw [Ideal.comap_comap]
      have hc : (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap B' (Chart g'' f'')))).comp
          (algebraMap (Localization.Away g'') (Chart g'' f'')) =
          (toReduced π g'' f'').comp (Ideal.Quotient.mk _) := by
        ext m
        simp [toReduced_mk]
      rw [hc, ← Ideal.comap_comap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact heq ▸ hle h

end Algebra

end
