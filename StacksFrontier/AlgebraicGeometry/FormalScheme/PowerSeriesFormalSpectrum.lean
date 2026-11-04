module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Substitution
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit

/-!
# Power series with the `X`-adic topology and their formal spectra

For a commutative ring `R` the ring of power series `R⟦X⟧` with its `X`-adic topology is an
admissible topological ring, and its formal spectrum `Spf R⟦X⟧` has the points of `Spec R`.

## Main definitions

* `AlgebraicGeometry.PowerSeriesFormalSpectrum.ring`: `R⟦X⟧` with the `X`-adic topology.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.pointsEquiv`: the homeomorphism from the space of
  open primes of `R⟦X⟧` to `Spec R`, `p ↦ p ∩ R`.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.subst`: for a nilpotent `r : R`, the continuous
  ring automorphism `X ↦ X - r` of `R⟦X⟧`.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.aut`: the automorphism of `Spf R⟦X⟧` it induces.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.pointX`: the point `Spec (R⟦X⟧/(X)) → Spf R⟦X⟧`.

## Main results

* `AlgebraicGeometry.PowerSeriesFormalSpectrum.isIdealOfDefinition_span_X_pow` and
  `AlgebraicGeometry.PowerSeriesFormalSpectrum.isAdmissible`: every positive power of `(X)` is an
  ideal of definition, and `R⟦X⟧` is admissible, completeness being Mathlib's `X`-adic
  completeness of power series.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.pointsEquiv_mem_spfBasicOpen_C`: the basic open
  of `C r` corresponds to the basic open of `r`.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.aut_base`: the automorphism attached to a
  nilpotent `r` is the identity on points.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.aut_hom_c_app_top` and
  `AlgebraicGeometry.PowerSeriesFormalSpectrum.aut_hom_c_app_res`: on the sections coming from
  `R⟦X⟧`, over the whole space and restricted to any open, the automorphism is the substitution.
* `AlgebraicGeometry.PowerSeriesFormalSpectrum.pointX_c_app_spfBasicOpen_res_eq_zero_iff`: the
  image under `pointX` over `D(C f)` of the restriction of the section attached to `a` vanishes
  exactly when the constant coefficient of `a` vanishes in `R_f`.
* `AlgebraicGeometry.spfMapLTRS_comp_spfMapLTRS_eq_id`: for an admissible `A`, the morphisms of
  formal spectra attached to two continuous endomorphisms `φ`, `ψ` of `A` with `φ ∘ ψ = id`
  compose to the identity.

## Implementation notes

`ring R` is an instance-reducible definition. Instance search sees `(ring R).α` as the carrier
of a bundled topological ring, so it finds the `X`-adic topology there and never puts that
topology on `R⟦X⟧` itself; unification at instance transparency unfolds it to `R⟦X⟧`, so the
power series lemmas of Mathlib apply to its elements without any transport.

The substitution is Mathlib's `PowerSeries.substAlgHom`, with inverse the substitution
`X ↦ X + r`. The automorphism of `Spf R⟦X⟧` is `AlgebraicGeometry.spfMapLTRS` of the substitution
and of its inverse; that they are mutually inverse is checked on global sections, through the
identification `Γ(Spf A) = A` of Stacks 0AHY, and `AlgebraicGeometry.spfMap_eq_of_c_app_top_eq`
propagates it to all opens.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopologicalRing
open PowerSeries (X C constantCoeff coeff HasSubst substAlgHom)

universe u

namespace AlgebraicGeometry

/-! ### Functoriality of `Spf` for mutually inverse endomorphisms -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsAdmissible A)

/-- For an admissible topological ring `A` and continuous endomorphisms `φ`, `ψ` of `A` with
`φ ∘ ψ = id`, the morphism of formal spectra attached to `φ` followed by that attached to `ψ` is
the identity of `Spf A`.

Both composites agree with `Spf (id)` on points, which is `φ⁻¹ ∘ ψ⁻¹ = (φ ∘ ψ)⁻¹`, and on global
sections, where the maps of formal spectra are the ring maps read through the identification
`A = Γ(Spf A, 𝒪_{Spf A})`; `AlgebraicGeometry.spfMap_eq_of_c_app_top_eq` then identifies both with
`Spf (id)`. -/
theorem spfMapLTRS_comp_spfMapLTRS_eq_id (I₀ : IdealsOfDefinition A) {φ ψ : A →+* A}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : ∀ a, φ (ψ a) = a) :
    spfMapLTRS A A hφ hA.1 I₀ hA.1 ≫ spfMapLTRS A A hψ hA.1 I₀ hA.1 = 𝟙 _ := by
  have hid : Continuous (RingHom.id A) := continuous_id
  have hsurj := surjective_spfGammaHom A hA
  have hΓ : ∀ {χ : A →+* A} (hχ : Continuous χ) (a : A),
      ((spfMapC A A hχ I₀ hA.1).app (op ⊤)).1 ((spfGammaHom A).1 a) = (spfGammaHom A).1 (χ a) :=
    fun hχ a => congrArg (fun k : TopCommRingCat.of A ⟶ (spfPresheaf A).obj (op ⊤) => k.1 a)
      (spfGammaHom_comp_spfMapGammaHom A A hχ hA.1 I₀)
  refine LocallyTopologicallyRingedSpace.Hom.ext' ?_
  rw [LocallyTopologicallyRingedSpace.comp_toHom, LocallyTopologicallyRingedSpace.id_toHom]
  have e1 := spfMap_eq_of_c_app_top_eq A A hid hA.1 I₀ hA.1
    (spfMapLTRS A A hφ hA.1 I₀ hA.1 ≫ spfMapLTRS A A hψ hA.1 I₀ hA.1).toHom.base
    (spfMapLTRS A A hφ hA.1 I₀ hA.1 ≫ spfMapLTRS A A hψ hA.1 I₀ hA.1).toHom.c ?_ ?_
  · have e2 := spfMap_eq_of_c_app_top_eq A A hid hA.1 I₀ hA.1
      (𝟙 (spfLTRS A hA.1) : spfLTRS A hA.1 ⟶ spfLTRS A hA.1).toHom.base
      (𝟙 (spfLTRS A hA.1) : spfLTRS A hA.1 ⟶ spfLTRS A hA.1).toHom.c ?_ ?_
    · exact e1.symm.trans e2
    · ext p
      exact Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a => Iff.rfl))
    · refine Subtype.ext (RingHom.ext fun s => ?_)
      obtain ⟨a, rfl⟩ := hsurj s
      exact (hΓ hid a).symm
  · ext p
    exact Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a => by
      change a ∈ p.1.asIdeal ↔ φ (ψ a) ∈ p.1.asIdeal
      rw [h]))
  · refine Subtype.ext (RingHom.ext fun s => ?_)
    obtain ⟨a, rfl⟩ := hsurj s
    change ((spfMapC A A hφ I₀ hA.1).app (op ⊤)).1
        (((spfMapC A A hψ I₀ hA.1).app (op ⊤)).1 ((spfGammaHom A).1 a))
      = ((spfMapC A A hid I₀ hA.1).app (op ⊤)).1 ((spfGammaHom A).1 a)
    rw [hΓ hψ, hΓ hφ, hΓ hid, h]
    rfl

end

namespace PowerSeriesFormalSpectrum

/-! ### The ring `R⟦X⟧` with its `X`-adic topology -/

section Ring

variable (R : Type u) [CommRing R]

/-- The ring of power series `R⟦X⟧` with its `X`-adic topology, as a topological ring. -/
@[instance_reducible] noncomputable def ring : TopCommRingCat.{u} :=
  @TopCommRingCat.of (PowerSeries R) _ (Ideal.span {X}).adicTopology
    (Ideal.span {X}).ringFilterBasis.isTopologicalRing

/-- The `X`-adic topology of `R⟦X⟧` is linear: the powers of `(X)` form a basis of
neighbourhoods of zero. -/
instance isLinearTopology : IsLinearTopology (ring R).α (ring R).α :=
  Ideal.isLinearTopology (Ideal.span {X})

/-- The topology of `ring R` is the adic topology of the ideal `(X)`. -/
theorem isAdic_span_X : _root_.IsAdic (Ideal.span {X} : Ideal (ring R).α) := rfl

/-- Every positive power `(X)^(k+1)` of the ideal `(X)` is an ideal of definition of `R⟦X⟧`. -/
theorem isIdealOfDefinition_span_X_pow (k : ℕ) :
    IsIdealOfDefinition ((Ideal.span {X} : Ideal (ring R).α) ^ (k + 1)) :=
  have h := is_ideal_adic_pow (isAdic_span_X R) k.succ_pos
  ⟨by simpa only [pow_one] using (isAdic_iff.mp h).1 1, (isAdic_iff.mp h).2⟩

/-- The ideal `(X)` is an ideal of definition of `R⟦X⟧`. -/
theorem isIdealOfDefinition_span_X : IsIdealOfDefinition (Ideal.span {X} : Ideal (ring R).α) := by
  have h := isIdealOfDefinition_span_X_pow R 0
  rwa [zero_add, pow_one] at h

/-- `R⟦X⟧` with the `X`-adic topology is pre-admissible. -/
theorem isPreAdmissible : IsPreAdmissible (ring R).α :=
  ⟨_, isIdealOfDefinition_span_X R⟩

/-- **`R⟦X⟧` with the `X`-adic topology is admissible.** It is pre-admissible, `(X)` being an
ideal of definition, and complete and separated, which is Mathlib's `X`-adic completeness of
power series read through the adic topology. -/
theorem isAdmissible : IsAdmissible (ring R).α := by
  refine ⟨isPreAdmissible R, ?_⟩
  let : UniformSpace (ring R).α := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (ring R).α := isUniformAddGroup_of_addCommGroup
  have hc : IsAdicComplete (Ideal.span {X} : Ideal (PowerSeries R)) (PowerSeries R) :=
    inferInstance
  obtain ⟨hcomplete, hT2⟩ := (IsAdic.isAdicComplete_iff (isAdic_span_X R)).mp hc
  exact ⟨hT2, hcomplete⟩

/-- The ideal of definition `(X)` of `R⟦X⟧`, as a term of the index of the formal spectrum. -/
noncomputable def idealX : IdealsOfDefinition (ring R).α :=
  ⟨Ideal.span {X}, isIdealOfDefinition_span_X R⟩

end Ring

variable {R : Type u} [CommRing R]

/-- Two elements whose difference lies in an ideal lie in it simultaneously. -/
private theorem mem_iff_of_sub_mem {S : Type*} [CommRing S] {I : Ideal S} {a b : S}
    (h : a - b ∈ I) : a ∈ I ↔ b ∈ I :=
  ⟨fun ha => by simpa using I.sub_mem ha h, fun hb => by simpa using I.add_mem h hb⟩

/-- A power series lies in an ideal containing `X` exactly when its constant term does. -/
theorem mem_iff_C_constantCoeff_mem {I : Ideal (PowerSeries R)} (hX : X ∈ I)
    (a : PowerSeries R) : a ∈ I ↔ C (constantCoeff a) ∈ I := by
  have hd : a - C (constantCoeff a) ∈ I := by
    obtain ⟨b, hb⟩ := PowerSeries.X_dvd_iff.mpr (show constantCoeff (a - C (constantCoeff a)) = 0
      by simp)
    rw [hb]
    exact I.mul_mem_right b hX
  exact mem_iff_of_sub_mem hd

/-! ### The points of `Spf R⟦X⟧` -/

/-- Every open prime of `R⟦X⟧` contains `X`, because it contains the ideal of definition
`(X)`. -/
theorem X_mem_asIdeal (p : spfSpace (ring R).α) : (X : (ring R).α) ∈ p.1.asIdeal :=
  (mem_openPrimes_iff_le (ring R).α (isIdealOfDefinition_span_X R) p.1).1 p.2
    (Ideal.subset_span rfl)

/-- The preimage under the constant coefficient of a prime of `R` is an open prime of `R⟦X⟧`:
it contains `X`, hence the ideal of definition `(X)`. -/
theorem comap_constantCoeff_mem_openPrimes (q : PrimeSpectrum R) :
    PrimeSpectrum.comap (constantCoeff : (ring R).α →+* R) q ∈ openPrimes (ring R).α :=
  (mem_openPrimes_iff_le (ring R).α (isIdealOfDefinition_span_X R) _).2
    ((Ideal.span_le).2 fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      change constantCoeff X ∈ q.asIdeal
      rw [PowerSeries.constantCoeff_X]
      exact q.asIdeal.zero_mem)

/-- **The points of `Spf R⟦X⟧` are the points of `Spec R`.** An open prime `p` of `R⟦X⟧` contains
`X`, so it is the preimage of the prime `p ∩ R` of `R ≅ R⟦X⟧/(X)`; this is a homeomorphism from the
space of open primes onto `Spec R`. -/
noncomputable def pointsEquiv : spfSpace (ring R).α ≃ₜ PrimeSpectrum R where
  toFun p := PrimeSpectrum.comap (C : R →+* (ring R).α) p.1
  invFun q := ⟨PrimeSpectrum.comap (constantCoeff : (ring R).α →+* R) q,
    comap_constantCoeff_mem_openPrimes q⟩
  left_inv p := Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a =>
    ((mem_iff_C_constantCoeff_mem (X_mem_asIdeal p) a)).symm))
  right_inv q := PrimeSpectrum.ext (Ideal.ext fun r => by
    change constantCoeff (C r) ∈ q.asIdeal ↔ r ∈ q.asIdeal
    rw [PowerSeries.constantCoeff_C])
  continuous_toFun := (PrimeSpectrum.continuous_comap _).comp continuous_subtype_val
  continuous_invFun := (PrimeSpectrum.continuous_comap _).subtype_mk _

/-- The point of `Spec R` attached to an open prime `p` of `R⟦X⟧` is `p ∩ R`. -/
theorem pointsEquiv_apply (p : spfSpace (ring R).α) :
    pointsEquiv p = PrimeSpectrum.comap (C : R →+* (ring R).α) p.1 := rfl

/-- The open prime of `R⟦X⟧` attached to a prime `q` of `R` is its preimage under the constant
coefficient. -/
theorem pointsEquiv_symm_apply (q : PrimeSpectrum R) :
    (pointsEquiv.symm q).1 = PrimeSpectrum.comap (constantCoeff : (ring R).α →+* R) q := rfl

/-- Under `pointsEquiv` the basic open `D(C r) ∩ Spf R⟦X⟧` corresponds to the basic open `D(r)` of
`Spec R`. -/
theorem pointsEquiv_mem_spfBasicOpen_C (r : R) (p : spfSpace (ring R).α) :
    p ∈ spfBasicOpen (ring R).α (C r) ↔ pointsEquiv p ∈ PrimeSpectrum.basicOpen r :=
  Iff.rfl

/-! ### The substitution `X ↦ X - r` for a nilpotent `r` -/

/-- For a nilpotent `r`, the power series `X - r` can be substituted into power series: its
constant coefficient `-r` is nilpotent. -/
theorem hasSubst_X_sub_C {r : R} (hr : IsNilpotent r) : HasSubst (X - C r : PowerSeries R) := by
  unfold HasSubst
  rw [← PowerSeries.constantCoeff_eq]
  simpa using hr

/-- Substituting `X - r` into `X - s` gives `X - (r + s)`. -/
theorem subst_X_sub_C_X_sub_C {r : R} (hr : IsNilpotent r) (s : R) :
    PowerSeries.subst (X - C r : PowerSeries R) (X - C s : PowerSeries R) = X - C (r + s) := by
  rw [PowerSeries.subst_sub (hasSubst_X_sub_C hr), PowerSeries.subst_X (hasSubst_X_sub_C hr),
    PowerSeries.subst_C]
  change X - C r - C s = X - C (r + s)
  rw [map_add]
  ring

/-- Substituting `X - r` and then `X - s` into a power series is substituting `X - (r + s)`. -/
theorem substAlgHom_substAlgHom {r s : R} (hr : IsNilpotent r) (hs : IsNilpotent s)
    (f : PowerSeries R) :
    substAlgHom (hasSubst_X_sub_C hr) (substAlgHom (hasSubst_X_sub_C hs) f) =
      PowerSeries.subst (X - C (r + s) : PowerSeries R) f := by
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_comp_subst_apply (hasSubst_X_sub_C hs) (hasSubst_X_sub_C hr),
    subst_X_sub_C_X_sub_C hr]

/-- Substituting `X - r` and then `X - s` is the identity when `r + s = 0`. -/
private theorem substAlgHom_substAlgHom_of_add_eq_zero {r s : R} (hr : IsNilpotent r)
    (hs : IsNilpotent s) (h : r + s = 0) (f : PowerSeries R) :
    substAlgHom (hasSubst_X_sub_C hr) (substAlgHom (hasSubst_X_sub_C hs) f) = f := by
  rw [substAlgHom_substAlgHom hr hs, h, map_zero, sub_zero, PowerSeries.X_subst]

/-- The substitution `X ↦ X - r` of power series, for a nilpotent `r`, as an `R`-algebra
automorphism of `R⟦X⟧`, with inverse the substitution `X ↦ X + r`. -/
noncomputable def substAlgEquiv {r : R} (hr : IsNilpotent r) :
    PowerSeries R ≃ₐ[R] PowerSeries R :=
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_X_sub_C hr)) (substAlgHom (hasSubst_X_sub_C hr.neg))
    (AlgHom.ext fun f => by
      rw [AlgHom.comp_apply, substAlgHom_substAlgHom hr hr.neg, add_neg_cancel, map_zero, sub_zero,
        PowerSeries.X_subst, AlgHom.id_apply])
    (AlgHom.ext fun f => by
      rw [AlgHom.comp_apply, substAlgHom_substAlgHom hr.neg hr, neg_add_cancel, map_zero, sub_zero,
        PowerSeries.X_subst, AlgHom.id_apply])

/-- **The substitution `X ↦ X - r`** for a nilpotent `r : R`, as a ring automorphism of
`R⟦X⟧`. -/
noncomputable def subst (r : R) (hr : IsNilpotent r) : (ring R).α ≃+* (ring R).α :=
  (substAlgEquiv hr).toRingEquiv

/-- The substitution sends `X` to `X - r`. -/
theorem subst_X (r : R) (hr : IsNilpotent r) : subst r hr X = X - C r :=
  PowerSeries.substAlgHom_X (hasSubst_X_sub_C hr)

/-- The substitution fixes the constants. -/
theorem subst_C (r : R) (hr : IsNilpotent r) (a : R) : subst r hr (C a) = C a := by
  change substAlgHom (hasSubst_X_sub_C hr) (C a) = C a
  rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
  rfl

/-- The substitution `X ↦ X - r` undoes the substitution `X ↦ X + r`. -/
theorem subst_subst_neg (r : R) (hr : IsNilpotent r) (a : (ring R).α) :
    subst r hr (subst (-r) hr.neg a) = a := by
  exact substAlgHom_substAlgHom_of_add_eq_zero hr hr.neg (add_neg_cancel r) a

/-- The substitution `X ↦ X + r` undoes the substitution `X ↦ X - r`. -/
theorem subst_neg_subst (r : R) (hr : IsNilpotent r) (a : (ring R).α) :
    subst (-r) hr.neg (subst r hr a) = a := by
  exact substAlgHom_substAlgHom_of_add_eq_zero hr.neg hr (neg_add_cancel r) a

/-- The inverse of the substitution `X ↦ X - r` is the substitution `X ↦ X - (-r)`. -/
theorem subst_symm_apply (r : R) (hr : IsNilpotent r) (a : (ring R).α) :
    (subst r hr).symm a = subst (-r) hr.neg a :=
  (subst r hr).symm_apply_eq.2 (subst_subst_neg r hr a).symm

/-- The substitution `X ↦ X - r` is continuous for the `X`-adic topology: it sends
`(X)^(N+1)` into `(X)` as soon as `r^N = 0`, since `(X - r)^(N+1) ≡ (-r)^(N+1) = 0` modulo `X`. -/
theorem continuous_subst (r : R) (hr : IsNilpotent r) : Continuous (subst r hr) := by
  have ⟨N, hN⟩ := hr
  have hpow : r ^ (N + 1) = 0 := by rw [pow_succ, hN, zero_mul]
  refine (RingHom.continuous_adic_iff (subst r hr : (ring R).α →+* (ring R).α)
    (Ideal.span {X}) (Ideal.span {X})).2 ⟨N + 1, by omega, fun x hx => ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, RingEquiv.coe_toRingHom, subst_X, Ideal.mem_span_singleton]
  refine Dvd.dvd.mul_right (PowerSeries.X_dvd_iff.2 ?_) _
  rw [map_pow, map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub,
    neg_pow, hpow, mul_zero]

/-- The inverse of the substitution `X ↦ X - r` is continuous for the `X`-adic topology: it is
the substitution `X ↦ X + r`. -/
theorem continuous_subst_symm (r : R) (hr : IsNilpotent r) : Continuous (subst r hr).symm := by
  rw [show ⇑(subst r hr).symm = ⇑(subst (-r) hr.neg) from funext (subst_symm_apply r hr)]
  exact continuous_subst (-r) hr.neg

/-- The substitution `X ↦ X - r` as a homeomorphism of `R⟦X⟧` with its `X`-adic topology. -/
noncomputable def substHomeomorph (r : R) (hr : IsNilpotent r) : (ring R).α ≃ₜ (ring R).α where
  toEquiv := (subst r hr).toEquiv
  continuous_toFun := continuous_subst r hr
  continuous_invFun := continuous_subst_symm r hr

/-- The substitution `X ↦ X - r` differs from the identity by an element of every ideal containing
`X` and `r`. -/
theorem subst_sub_self_mem (r : R) (hr : IsNilpotent r) {I : Ideal (PowerSeries R)} (hX : X ∈ I)
    (hr' : C r ∈ I) (a : (ring R).α) : subst r hr a - a ∈ I := by
  obtain ⟨b, c, rfl⟩ : ∃ b c, a = X * b + C c :=
    ⟨_, _, PowerSeries.eq_X_mul_shift_add_const a⟩
  rw [map_add, map_mul, subst_X, subst_C]
  rw [show (X - C r) * subst r hr b + C c - (X * b + C c) =
      X * (subst r hr b - b) - C r * subst r hr b by ring]
  exact I.sub_mem (I.mul_mem_right _ hX) (I.mul_mem_right _ hr')

/-- The substitution `X ↦ X - r` maps every open prime of `R⟦X⟧` onto itself: an open prime
contains `X` and the nilpotent `r`, so it contains `subst r a - a` for every `a`. -/
theorem subst_mem_iff (r : R) (hr : IsNilpotent r) (p : spfSpace (ring R).α) (a : (ring R).α) :
    subst r hr a ∈ p.1.asIdeal ↔ a ∈ p.1.asIdeal := by
  have hr' : (C r : (ring R).α) ∈ p.1.asIdeal := by
    obtain ⟨n, hn⟩ := hr
    refine p.1.isPrime.mem_of_pow_mem n ?_
    rw [← map_pow, hn, map_zero]
    exact zero_mem _
  have hd := subst_sub_self_mem r hr (X_mem_asIdeal p) hr' a
  exact mem_iff_of_sub_mem hd

/-! ### The automorphism of `Spf R⟦X⟧` -/

/-- The morphism `Spf R⟦X⟧ → Spf R⟦X⟧` of locally topologically ringed spaces attached to the
continuous ring map `subst r : X ↦ X - r`. -/
noncomputable def autHom (r : R) (hr : IsNilpotent r) :
    spfLTRS (ring R).α (isPreAdmissible R) ⟶ spfLTRS (ring R).α (isPreAdmissible R) :=
  spfMapLTRS (ring R).α (ring R).α (φ := (subst r hr : (ring R).α →+* (ring R).α))
    (continuous_subst r hr) (isPreAdmissible R)
    (preAdmissibleSpfIndex _ (isPreAdmissible R)) (isPreAdmissible R)

/-- **The automorphism of `Spf R⟦X⟧` attached to a nilpotent `r : R`**, induced by the
substitution `X ↦ X - r`, with inverse induced by `X ↦ X + r`. -/
noncomputable def aut (r : R) (hr : IsNilpotent r) :
    spfLTRS (ring R).α (isPreAdmissible R) ≅ spfLTRS (ring R).α (isPreAdmissible R) where
  hom := autHom r hr
  inv := autHom (-r) hr.neg
  hom_inv_id := spfMapLTRS_comp_spfMapLTRS_eq_id (ring R).α (isAdmissible R) _
    (continuous_subst r hr) (continuous_subst (-r) hr.neg) (subst_subst_neg r hr)
  inv_hom_id := spfMapLTRS_comp_spfMapLTRS_eq_id (ring R).α (isAdmissible R) _
    (continuous_subst (-r) hr.neg) (continuous_subst r hr) (subst_neg_subst r hr)

/-- The automorphism of `Spf R⟦X⟧` is `Spf` of the substitution `X ↦ X - r`. -/
theorem aut_hom (r : R) (hr : IsNilpotent r) : (aut r hr).hom = autHom r hr := rfl

/-- The inverse of the automorphism of `Spf R⟦X⟧` is `Spf` of the substitution `X ↦ X + r`. -/
theorem aut_inv (r : R) (hr : IsNilpotent r) : (aut r hr).inv = autHom (-r) hr.neg := rfl

/-- **The automorphism of `Spf R⟦X⟧` attached to a nilpotent `r` is the identity on points**: the
substitution maps every open prime onto itself. -/
theorem aut_base (r : R) (hr : IsNilpotent r) (p : spfSpace (ring R).α) :
    (aut r hr).hom.toHom.base p = p :=
  Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a => subst_mem_iff r hr p a))

/-- The automorphism of `Spf R⟦X⟧` pulls every open back to itself. -/
theorem map_aut_base_obj (r : R) (hr : IsNilpotent r) (V : Opens (spfSpace (ring R).α)) :
    (Opens.map (aut r hr).hom.toHom.base).obj V = V :=
  Opens.ext (Set.ext fun p =>
    (congrArg (fun q : spfSpace (ring R).α => q ∈ V) (aut_base r hr p)).to_iff)

/-- **On global sections the automorphism of `Spf R⟦X⟧` is the substitution**: the section
attached to `a : R⟦X⟧` by the canonical map `A → Γ(Spf A, 𝒪_{Spf A})` (the hom of
`AlgebraicGeometry.spfGammaIso`, by `AlgebraicGeometry.spfGammaIso_hom`) goes to the section
attached to `subst r a`. -/
theorem aut_hom_c_app_top (r : R) (hr : IsNilpotent r) (a : (ring R).α) :
    ((aut r hr).hom.toHom.c.app (op ⊤)).1 ((spfGammaHom (ring R).α).1 a)
      = (spfGammaHom (ring R).α).1 (subst r hr a) :=
  congrArg (fun k : TopCommRingCat.of (ring R).α ⟶ (spfPresheaf (ring R).α).obj (op ⊤) => k.1 a)
    (spfGammaHom_comp_spfMapGammaHom (ring R).α (ring R).α (continuous_subst r hr)
      (isPreAdmissible R) (preAdmissibleSpfIndex _ (isPreAdmissible R)))

/-- **Over any open `V` the automorphism of `Spf R⟦X⟧` is the substitution on restrictions of
global sections**: the restriction to `V` of the section attached to `a` goes to the restriction,
to the preimage of `V` (which is `V` itself by `map_aut_base_obj`), of the section attached to
`subst r a`. -/
theorem aut_hom_c_app_res (r : R) (hr : IsNilpotent r) (V : Opens (spfSpace (ring R).α))
    (a : (ring R).α) :
    ((aut r hr).hom.toHom.c.app (op V)).1
        (((spfPresheaf (ring R).α).map (homOfLE (le_top : V ≤ ⊤)).op).1
          ((spfGammaHom (ring R).α).1 a))
      = ((spfPresheaf (ring R).α).map
          (homOfLE (le_top : (Opens.map (aut r hr).hom.toHom.base).obj V ≤ ⊤)).op).1
          ((spfGammaHom (ring R).α).1 (subst r hr a)) := by
  have hnat := congrArg (fun k => k.1 ((spfGammaHom (ring R).α).1 a))
    ((aut r hr).hom.toHom.c.naturality (homOfLE (le_top : V ≤ ⊤)).op)
  refine hnat.trans ?_
  change ((spfPresheaf (ring R).α).map
      (homOfLE (le_top : (Opens.map (aut r hr).hom.toHom.base).obj V ≤ ⊤)).op).1
      (((aut r hr).hom.toHom.c.app (op ⊤)).1 ((spfGammaHom (ring R).α).1 a)) = _
  rw [aut_hom_c_app_top]

/-- The form of `aut_hom_c_app_res` with target the sections over `V` itself: the image of the
restriction to `V` of the section attached to `a` is the restriction to `V` of the section
attached to `subst r a`, transported along the identification `map_aut_base_obj` of the preimage
of `V` with `V`. -/
theorem aut_hom_c_app_res_eqToHom (r : R) (hr : IsNilpotent r) (V : Opens (spfSpace (ring R).α))
    (a : (ring R).α) :
    ((aut r hr).hom.toHom.c.app (op V)).1
        (((spfPresheaf (ring R).α).map (homOfLE (le_top : V ≤ ⊤)).op).1
          ((spfGammaHom (ring R).α).1 a))
      = ((spfPresheaf (ring R).α).map (eqToHom (map_aut_base_obj r hr V)).op).1
          (((spfPresheaf (ring R).α).map (homOfLE (le_top : V ≤ ⊤)).op).1
            ((spfGammaHom (ring R).α).1 (subst r hr a))) := by
  rw [aut_hom_c_app_res]
  exact congrArg (fun k => k.1 ((spfGammaHom (ring R).α).1 (subst r hr a)))
    ((spfPresheaf (ring R).α).map_comp (homOfLE (le_top : V ≤ ⊤)).op
      (eqToHom (map_aut_base_obj r hr V)).op)

/-! ### The point at the ideal of definition `(X)` -/

variable (R) in
/-- The point `Spec (R⟦X⟧/(X)) → Spf R⟦X⟧` of the formal spectrum at the ideal of definition
`(X)`, a morphism of locally topologically ringed spaces. -/
noncomputable def pointX :
    schemeToLTRSObj (Spec (spfQuotient (ring R).α (idealX R))) ⟶
      spfLTRS (ring R).α (isPreAdmissible R) :=
  spfQuotientPoint (ring R).α (isPreAdmissible R) (idealX R)

/-- A power series vanishes modulo `X` exactly when its constant coefficient vanishes. -/
theorem mk_span_X_eq_zero_iff (b : (ring R).α) :
    Ideal.Quotient.mk (Ideal.span {X} : Ideal (ring R).α) b = 0 ↔ constantCoeff b = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- **The point `pointX` on the restrictions of global sections over `D(C f)`.** The image under
the comparison map of `pointX` over the basic open `D(C f) ∩ Spf R⟦X⟧` of the restriction of the
section attached to `a : R⟦X⟧` vanishes exactly when the constant coefficient of `a` vanishes in
the localization `R_f`.

Over `D(C f)` the comparison map of `pointX` is the projection of `𝒪_{Spf R⟦X⟧}` onto the sections
of the structure sheaf of `Spec (R⟦X⟧/(X))` over the basic open of `C f`, which is the
localization of `R⟦X⟧/(X) ≅ R` away from `f`, and the restriction of the section attached to `a`
goes to the image of `a` there. -/
theorem pointX_c_app_spfBasicOpen_res_eq_zero_iff (f : R) (a : (ring R).α) :
    ((pointX R).toHom.c.app (op (spfBasicOpen (ring R).α (C f)))).1
        (((spfPresheaf (ring R).α).map
          (homOfLE (le_top : spfBasicOpen (ring R).α (C f) ≤ ⊤)).op).1
            ((spfGammaHom (ring R).α).1 a)) = 0
      ↔ algebraMap R (Localization.Away f) (constantCoeff a) = 0 := by
  change spfAwayResidue (ring R).α (idealX R) (C f)
      (((spfPresheaf (ring R).α).map
        (homOfLE (le_top : spfBasicOpen (ring R).α (C f) ≤ ⊤)).op).1
          ((spfGammaHom (ring R).α).1 a)) = 0 ↔ _
  rw [spfAwayResidue_restrict_spfGammaHom,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk (idealX R).1 (C f))),
    IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f)]
  have key (n : ℕ) : Ideal.Quotient.mk (idealX R).1 (C f) ^ n * Ideal.Quotient.mk (idealX R).1 a =
      0 ↔ f ^ n * constantCoeff a = 0 := by
    rw [← map_pow, ← map_mul]
    exact (mk_span_X_eq_zero_iff _).trans (by rw [map_mul, map_pow, PowerSeries.constantCoeff_C])
  constructor
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    exact ⟨⟨f ^ n, n, rfl⟩, (key n).1 h⟩
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    exact ⟨⟨Ideal.Quotient.mk (idealX R).1 (C f) ^ n, n, rfl⟩, (key n).2 h⟩

/-- The case `a = (X - ε)^M` of `pointX_c_app_spfBasicOpen_res_eq_zero_iff`: the image under
`pointX` over `D(C f)` of the restriction of the section attached to `(X - ε)^M` is nonzero as
soon as `ε^M` is nonzero in `R_f`. -/
theorem pointX_c_app_spfBasicOpen_res_X_sub_C_pow_ne_zero (f ε : R) (M : ℕ)
    (h : algebraMap R (Localization.Away f) (ε ^ M) ≠ 0) :
    ((pointX R).toHom.c.app (op (spfBasicOpen (ring R).α (C f)))).1
        (((spfPresheaf (ring R).α).map
          (homOfLE (le_top : spfBasicOpen (ring R).α (C f) ≤ ⊤)).op).1
            ((spfGammaHom (ring R).α).1 ((X - C ε) ^ M))) ≠ 0 := by
  rwa [Ne, pointX_c_app_spfBasicOpen_res_eq_zero_iff, map_pow, map_sub,
    PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub, neg_pow, map_mul,
    IsUnit.mul_right_eq_zero (((isUnit_one.neg).pow M).map _)]

end PowerSeriesFormalSpectrum

end AlgebraicGeometry
