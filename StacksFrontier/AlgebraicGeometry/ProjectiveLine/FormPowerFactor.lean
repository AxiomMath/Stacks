module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.HomogeneousPrimes

/-!
# Binary forms divisible only by one irreducible form

Let `k` be a field and let `f ∈ k[T₀, T₁]` be a homogeneous irreducible form of degree `d ≥ 2`.
A form `h` dividing both `T₀ ^ m f ^ N` and `T₁ ^ m f ^ M` has every irreducible factor associated
to `f`: such a factor is associated to `T₀` or to `f`, and to `T₁` or to `f`, and the coordinates
are not associated to one another nor — the degree forbids it — to `f`. So `h` is a unit times a
power of `f`, and its degree is therefore divisible by `d`.

This is the arithmetic heart of the kernel computation of [Stacks, Tag 0CDP]: the degree of the
numerator of a generator of `Γ(D₊(f), 𝒪(m))` is `k d + m` for some `k`, and the two coordinates
give exactly the two divisibilities above, so `d ∣ m`.

## Main results

* `Stacks.ProjectiveLine.not_associated_X_zero_X_one`: the two coordinates are not associated.
* `Stacks.ProjectiveLine.isHomogeneous_zero_of_isUnit`: a unit of `k[T₀, T₁]` is homogeneous of
  degree zero.
* `Stacks.ProjectiveLine.eq_one_of_associated_X`: a homogeneous form associated to a coordinate
  has degree one.
* `Stacks.ProjectiveLine.exists_associated_pow_of_forall_prime_associated`: a nonzero form all
  of whose prime factors are associated to `f` is associated to a power of `f`.
* `Stacks.ProjectiveLine.dvd_of_isHomogeneous_dvd_mul_pow`: **the conclusion** — `d` divides the
  degree of `h`.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
-/

@[expose] public section

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k]

/-- **The two homogeneous coordinates of `k[T₀, T₁]` are not associated.** Evaluating at
`(0, 1)` turns an associatedness `T₀ · u = T₁` into `0 = 1`. -/
theorem not_associated_X_zero_X_one :
    ¬ Associated (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) := by
  rintro ⟨u, hu⟩
  have h := congrArg (MvPolynomial.eval (![(0 : k), 1])) hu
  simp at h

/-- A unit of `k[T₀, T₁]` is a nonzero constant, hence homogeneous of degree zero. -/
theorem isHomogeneous_zero_of_isUnit {w : MvPolynomial (Fin 2) k} (hw : IsUnit w) :
    w.IsHomogeneous 0 := by
  obtain ⟨r, -, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hw
  exact MvPolynomial.isHomogeneous_C _ _

/-- A form associated to a homogeneous form of degree `n` is homogeneous of degree `n`. -/
private theorem isHomogeneous_of_associated {n : ℕ} {g f : MvPolynomial (Fin 2) k}
    (hg : g.IsHomogeneous n) (h : Associated g f) : f.IsHomogeneous n := by
  obtain ⟨u, rfl⟩ := h
  simpa using hg.mul (isHomogeneous_zero_of_isUnit u.isUnit)

/-- **A nonzero homogeneous form associated to a coordinate has degree one.** -/
theorem eq_one_of_associated_X {d : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous d)
    (hf0 : f ≠ 0) (i : Fin 2) (ha : Associated f (MvPolynomial.X i)) : d = 1 := by
  exact hf.inj_right (isHomogeneous_of_associated (MvPolynomial.isHomogeneous_X k i) ha.symm) hf0

/-- **A nonzero element of `k[T₀, T₁]` all of whose prime factors are associated to `f` is
associated to a power of `f`**, by induction on the number of prime factors. -/
theorem exists_associated_pow_of_forall_prime_associated (f h : MvPolynomial (Fin 2) k)
    (hne : h ≠ 0)
    (hall : ∀ π : MvPolynomial (Fin 2) k, Prime π → π ∣ h → Associated π f) :
    ∃ r : ℕ, Associated h (f ^ r) := by
  have huf : UniqueFactorizationMonoid (MvPolynomial (Fin 2) k) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  revert hne hall
  refine UniqueFactorizationMonoid.induction_on_prime h ?_ ?_ ?_
  · exact fun h0 _ => absurd rfl h0
  · refine fun x hx _ _ => ⟨0, ?_⟩
    simpa using associated_one_iff_isUnit.mpr hx
  · refine fun a p ha hp ih _ hall => ?_
    obtain ⟨r, hr⟩ := ih ha fun π hπ hdvd => hall π hπ (hdvd.mul_left p)
    refine ⟨r + 1, ?_⟩
    have h2 := (hall p hp (dvd_mul_right p a)).mul_mul hr
    rwa [← pow_succ'] at h2

/-- **The arithmetic heart of the kernel computation of [Stacks, Tag 0CDP].** Let `f` be a
homogeneous irreducible form of degree `d ≥ 2` and let `h` be a nonzero homogeneous form of
degree `e` dividing both `T₀ ^ m f ^ N` and `T₁ ^ m f ^ M`. Then `d ∣ e`.

Every prime factor `π` of `h` divides `T₀ ^ m f ^ N`, so is associated to `T₀` or to `f`, and
divides `T₁ ^ m f ^ M`, so is associated to `T₁` or to `f`. The coordinates are not associated to
one another, and a form associated to a coordinate has degree one, which `2 ≤ d` forbids; so `π`
is associated to `f`. Hence `h` is a unit times `f ^ r`, and `e = d r`. -/
theorem dvd_of_isHomogeneous_dvd_mul_pow {d e m N M : ℕ} {f h : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) (hd : 2 ≤ d)
    (hh : h.IsHomogeneous e) (hhne : h ≠ 0)
    (h0 : h ∣ MvPolynomial.X (0 : Fin 2) ^ m * f ^ N)
    (h1 : h ∣ MvPolynomial.X (1 : Fin 2) ^ m * f ^ M) :
    d ∣ e := by
  have hall : ∀ π : MvPolynomial (Fin 2) k, Prime π → π ∣ h → Associated π f := by
    intro π hπ hdvd
    have hcase : ∀ (i : Fin 2) (P : ℕ), π ∣ MvPolynomial.X i ^ m * f ^ P →
        Associated π (MvPolynomial.X i) ∨ Associated π f := by
      intro i P hd2
      rcases hπ.dvd_mul.mp hd2 with hx | hfp
      · exact Or.inl (hπ.irreducible.associated_of_dvd (MvPolynomial.X_prime (i := i)).irreducible
          (hπ.dvd_of_dvd_pow hx))
      · exact Or.inr (hπ.irreducible.associated_of_dvd hirr (hπ.dvd_of_dvd_pow hfp))
    rcases hcase 0 N (hdvd.trans h0) with ha0 | hpf
    · rcases hcase 1 M (hdvd.trans h1) with ha1 | hpf
      · exact absurd (ha0.symm.trans ha1) not_associated_X_zero_X_one
      · exact absurd (eq_one_of_associated_X hf hirr.ne_zero 0 (hpf.symm.trans ha0)) (by omega)
    · exact hpf
  obtain ⟨r, hr⟩ := exists_associated_pow_of_forall_prime_associated f h hhne hall
  exact ⟨r, hh.inj_right (isHomogeneous_of_associated (hf.pow r) hr.symm) hhne⟩

end Stacks.ProjectiveLine

end
