module

public import StacksFrontier.LinearAlgebra.Basis.SemilinearTransport
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.SymmetricAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of a quasi-regular ideal are free on the monomials of their degree

Let `R` be a commutative ring and `f : Fin c → R` a quasi-regular sequence generating the ideal
`J`.  `Stacks.RingTheory.QuasiRegular.symPowEquivTcomp` identifies `J^n/J^{n+1}` with
`Symⁿ_{R/J}(J/J²)`, and `J/J²` is free on the classes of the `f i`; so `J^n/J^{n+1}` is a free
`R/J`-module on the monomials of degree `n` in `c` variables.  That is
`Stacks.RingTheory.QuasiRegular.basisTcomp`.

The rest of the file packages this for use where the quotient `J^n/J^{n+1}` is met not as a
quotient but through a *presentation*: an additive surjection `g : J^n ↠ N` onto a module over a
ring `S`, with kernel exactly `J^{n+1}` and semilinear over a surjection `ψ : R ↠ S` with kernel
`J`.  This is exactly the shape of the local associated-graded presentations of the conormal
algebra of an immersion (`Stacks.Conormal.ConormalAlgebraData`), and
`Stacks.RingTheory.QuasiRegular.GradedPresentation` is that data.

## Main definitions

* `Stacks.RingTheory.QuasiRegular.basisTcomp`: **`J^n/J^{n+1}` is free over `R/J` on the
  monomials of degree `n`**, for a quasi-regular sequence.
* `Stacks.RingTheory.QuasiRegular.isQuasiRegular_of_basisTcomp`: **its converse** — a sequence
  whose graded pieces are free on the degree-`n` monomials is quasi-regular.
* `Stacks.RingTheory.QuasiRegular.GradedPresentation`: a presentation of an `S`-module as
  the degree-`n` piece of the associated graded ring of an ideal with a chosen finite
  generating sequence.
* `Stacks.RingTheory.QuasiRegular.GradedPresentation.basis`: **the presented module is
  free over `S` on the monomials of degree `n`**, for a quasi-regular sequence.
* `Stacks.RingTheory.QuasiRegular.GradedPresentation.basisOne`: in degree one, the basis
  indexed by the sequence itself.
* `Stacks.RingTheory.QuasiRegular.GradedPresentation.basisTcompOfBasis`: the reverse
  transport, carrying a basis of the presented module back to one of `J^n/J^{n+1}`.

## Implementation notes

The presentation records the ideal `J` as data, with an equation `J = Ideal.span (Set.range f)`,
rather than using `Stacks.RingTheory.QuasiRegular.Jid` directly: a consumer meets `J` as the
kernel of a ring map and its powers `J ^ n` in the types of the data, so an equation of ideals
is all that may be assumed.  The two propositional identifications this costs — of `J ^ n` with
`Stacks.RingTheory.QuasiRegular.JpowM` and of `J ^ (n + 1)`-membership with membership in
`Stacks.RingTheory.QuasiRegular.Tsub` — are `GradedPresentation.jpow_eq` and
`GradedPresentation.gJ_ker`.

The crossing from the `R/J`-basis to an `S`-basis is
`Stacks.SemilinearTransport.basisOfAddEquiv`; the additive isomorphism it needs is
`GradedPresentation.tcompEquiv`, read off the presentation by
`Stacks.SemilinearTransport.quotientAddEquivOfSurjective`, and its semilinearity over `R/J`
comes from semilinearity over `R` together with the scalar tower `R → R/J → J^n/J^{n+1}`.

## References

* [Stacks Project, Tag 061P](https://stacks.math.columbia.edu/tag/061P)
* [Stacks Project, Tag 063B](https://stacks.math.columbia.edu/tag/063B)
-/

@[expose] public section

namespace Stacks.RingTheory.QuasiRegular

variable {R : Type*} [CommRing R] {c : ℕ}

/-- **The degree-`n` piece `J^n/J^{n+1}` of a quasi-regular ideal is free over `R/J` on the
monomials of degree `n` in the generators.**  It is the `n`-th symmetric power of `J/J²` by
`Stacks.RingTheory.QuasiRegular.symPowEquivTcomp`, and `J/J²` is free on the classes of the
generators by `Stacks.RingTheory.QuasiRegular.basisGeneratorClass`. -/
noncomputable def basisTcomp (f : Fin c → R)
    (h : Function.Bijective (associatedGradedMap f)) (n : ℕ) :
    Module.Basis {d : Fin c →₀ ℕ | d.degree = n} (qrRbar f) (Tcomp R f n) :=
  (SymPow.basisSymmetricPower (basisGeneratorClass f h.injective) n).map (symPowEquivTcomp f h n)

/-! ### The converse: freeness of the graded pieces forces quasi-regularity -/

/-- The degree-`n` part of the quasi-regularity map is injective as soon as `J^n/J^{n+1}` is
free over `R/J` on the monomials of degree `n`: the degree-`n` homogeneous polynomials are free
on the same index set, the degree-`n` part is surjective for *any* sequence, and a surjection
onto a finite module which admits an injection from its source is injective. -/
theorem injective_homogeneousToTcomp_of_basis (f : Fin c → R)
    (b : ∀ k : ℕ, Module.Basis {d : Fin c →₀ ℕ | d.degree = k} (qrRbar f) (Tcomp R f k))
    (n : ℕ) : Function.Injective (homogeneousToTcomp f n) := by
  have : Finite {d : Fin c →₀ ℕ | d.degree = n} := (Finsupp.finite_of_degree_eq n).to_subtype
  have : Module.Finite (qrRbar f) (Tcomp R f n) := Module.Finite.of_basis (b n)
  have e := (MvPolynomial.basisHomogeneousSubmodule (Fin c) (qrRbar f) n).equiv (b n)
    (Equiv.refl _)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
    (homogeneousToTcomp f n) e.injective
    (surjective_homogeneousToTcomp f (associatedGradedMap_surjective f) n)

/-- **A finite sequence generating `J` is quasi-regular as soon as every graded piece
`J^n/J^{n+1}` is free over `R/J` on the monomials of degree `n` in the generators.**  This is
the converse of `Stacks.RingTheory.QuasiRegular.basisTcomp`.

The quasi-regularity map is surjective for any sequence, so in each degree it is a surjection
between free modules on the same index set, hence injective; injectivity in each degree gives
injectivity, because the map carries a homogeneous polynomial of degree `k` into the degree-`k`
summand, so the degree-`n` component of the image of a polynomial sees only its degree-`n`
homogeneous component. -/
theorem isQuasiRegular_of_basisTcomp (f : Fin c → R)
    (b : ∀ k : ℕ, Module.Basis {d : Fin c →₀ ℕ | d.degree = k} (qrRbar f) (Tcomp R f k)) :
    _root_.RingTheory.Sequence.IsQuasiRegular R (List.ofFn f) := by
  have hcomp : ∀ (p : MvPolynomial (Fin c) (qrRbar f)), associatedGradedMap f p = 0 →
      ∀ k : ℕ, MvPolynomial.homogeneousComponent k p = 0 := by
    intro p hp k
    have hzero : ∀ j : ℕ, j ≠ k → targetComponent f k
        (associatedGradedMap f (MvPolynomial.homogeneousComponent j p)) = 0 := by
      intro j hj
      obtain ⟨t, ht⟩ :=
        associatedGradedMap_mem_range_lof f j (MvPolynomial.homogeneousComponent_mem j p)
      rw [← ht, DirectSum.component.of (qrRbar f) k j t]
      exact dite_eq_right_iff.mpr fun hcon => absurd hcon hj
    by_cases hk : k ∈ Finset.range (p.totalDegree + 1)
    · have hsum : targetComponent f k (associatedGradedMap f p) = 0 := by rw [hp, map_zero]
      rw [← MvPolynomial.sum_homogeneousComponent p, map_sum, map_sum,
        Finset.sum_eq_single_of_mem k hk fun j _ hj => hzero j hj] at hsum
      have hx : (⟨MvPolynomial.homogeneousComponent k p,
          MvPolynomial.homogeneousComponent_mem k p⟩ :
            MvPolynomial.homogeneousSubmodule (Fin c) (qrRbar f) k) = 0 := by
        refine injective_homogeneousToTcomp_of_basis f b k ?_
        rw [map_zero]
        exact hsum
      simpa using congrArg Subtype.val hx
    · exact MvPolynomial.homogeneousComponent_eq_zero k p (by simpa [Nat.lt_succ_iff] using hk)
  have hker : ∀ p : MvPolynomial (Fin c) (qrRbar f), associatedGradedMap f p = 0 → p = 0 := by
    intro p hp
    calc p = ∑ j ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent j p :=
          (MvPolynomial.sum_homogeneousComponent p).symm
      _ = 0 := Finset.sum_eq_zero fun j _ => hcomp p hp j
  refine (Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff f).mpr
    ⟨fun p q hpq => ?_, associatedGradedMap_surjective f⟩
  exact sub_eq_zero.mp (hker (p - q) (by rw [map_sub, hpq, sub_self]))

/-- A **presentation of an `S`-module `N` as the degree-`n` piece of the associated graded ring
of an ideal with a chosen finite generating sequence**: a surjection `ψ : R ↠ S` whose kernel is
an ideal `J` generated by `f`, together with an additive surjection `g : J^n ↠ N` which is
semilinear over `ψ` and whose kernel is exactly `J^{n+1}`.

Quasi-regularity of `f` is *not* part of the data: it is the hypothesis of
`Stacks.RingTheory.QuasiRegular.GradedPresentation.basis`, and its converse
`Stacks.RingTheory.QuasiRegular.GradedPresentation.basisTcompOfBasis` needs the presentation
without it. -/
structure GradedPresentation (R : Type*) [CommRing R] (S : Type*) [CommRing S] (c n : ℕ)
    (N : Type*) [AddCommGroup N] [Module S N] where
  /-- The generating sequence of the ideal. -/
  f : Fin c → R
  /-- The ring map presenting `S`. -/
  ψ : R →+* S
  /-- It is surjective. -/
  surjective_ψ : Function.Surjective ψ
  /-- The ideal. -/
  J : Ideal R
  /-- It is generated by the sequence. -/
  span_J : J = Ideal.span (Set.range f)
  /-- It is the kernel of the presenting ring map. -/
  ker_ψ : RingHom.ker ψ = J
  /-- The presentation of `N` by the `n`-th power of the ideal. -/
  g : ↥(J ^ n) →+ N
  /-- It is semilinear over the presenting ring map. -/
  smul_g : ∀ (r : R) (x : ↥(J ^ n)), g (r • x) = ψ r • g x
  /-- It is surjective. -/
  surjective_g : Function.Surjective g
  /-- Exactly `J^{n+1}` dies. -/
  ker_g : ∀ x : ↥(J ^ n), g x = 0 ↔ (x : R) ∈ J ^ (n + 1)

namespace GradedPresentation

variable {S : Type*} [CommRing S] {n : ℕ} {N : Type*} [AddCommGroup N] [Module S N]
  (P : GradedPresentation R S c n N)

/-- The ideal of the presentation is the ideal of its sequence. -/
theorem J_eq : P.J = Jid P.f := P.span_J

/-- The powers of the ideal of the presentation are the filtration steps of its sequence. -/
theorem jpow_eq (k : ℕ) : JpowM R P.f k = (P.J ^ k : Ideal R) := by
  rw [JpowM_self, ← P.J_eq]

/-- The filtration step `J^k` of the sequence, as the `k`-th power of the ideal. -/
noncomputable def powEquiv (k : ℕ) : ↥(JpowM R P.f k) ≃ₗ[R] ↥(P.J ^ k) :=
  LinearEquiv.ofEq _ _ (P.jpow_eq k)

/-- The identification `powEquiv` does not change the underlying element of `R`. -/
theorem coe_powEquiv (k : ℕ) (x : ↥(JpowM R P.f k)) : ((P.powEquiv k x : ↥(P.J ^ k)) : R) = x :=
  rfl

/-- The presentation read on the filtration step of the sequence. -/
noncomputable def gJ : ↥(JpowM R P.f n) →+ N :=
  P.g.comp (P.powEquiv n).toLinearMap.toAddMonoidHom

/-- `gJ` is `g` applied after `powEquiv`. -/
theorem gJ_apply (x : ↥(JpowM R P.f n)) : P.gJ x = P.g (P.powEquiv n x) := rfl

/-- `gJ` is semilinear over the presenting ring map `ψ`. -/
theorem gJ_smul (r : R) (x : ↥(JpowM R P.f n)) : P.gJ (r • x) = P.ψ r • P.gJ x := by
  rw [gJ_apply, gJ_apply, map_smul, P.smul_g]

/-- `gJ` is surjective. -/
theorem gJ_surjective : Function.Surjective P.gJ :=
  P.surjective_g.comp (P.powEquiv n).surjective

/-- An element of `J^n` is killed by `gJ` exactly when it lies in `J^{n+1}`. -/
theorem gJ_ker (x : ↥(JpowM R P.f n)) : P.gJ x = 0 ↔ x ∈ Tsub R P.f n := by
  rw [gJ_apply, P.ker_g, P.coe_powEquiv, Tsub, Submodule.mem_comap, Submodule.coe_subtype,
    P.jpow_eq (n + 1)]

/-- **The presented module is the degree-`n` piece `J^n/J^{n+1}`**, as additive groups. -/
noncomputable def tcompEquiv : Tcomp R P.f n ≃+ N :=
  Stacks.SemilinearTransport.quotientAddEquivOfSurjective (Tsub R P.f n) P.ψ P.gJ P.gJ_smul
    P.gJ_surjective P.gJ_ker

/-- The ring `S` of the presentation is `R/J`. -/
noncomputable def ringEquiv : qrRbar P.f ≃+* S :=
  (Ideal.quotEquivOfEq (show Jid P.f = RingHom.ker P.ψ by rw [P.ker_ψ, P.J_eq])).trans
    (RingHom.quotientKerEquivOfSurjective P.surjective_ψ)

/-- `ringEquiv` sends the class of `a` in `R/J` to `ψ a`. -/
theorem ringEquiv_mk (a : R) : P.ringEquiv (Ideal.Quotient.mk (Jid P.f) a) = P.ψ a := by
  rw [ringEquiv]
  simp only [RingEquiv.coe_trans, Function.comp_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective]
  exact RingHom.kerLift_mk P.ψ a

/-- The identification of the presented module with `J^n/J^{n+1}` is semilinear over the
identification of `S` with `R/J`. -/
theorem tcompEquiv_smul (r : qrRbar P.f) (x : Tcomp R P.f n) :
    P.tcompEquiv (r • x) = P.ringEquiv r • P.tcompEquiv x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk (Jid P.f) a) • x = a • x := by
    rw [show (Ideal.Quotient.mk (Jid P.f) a) = a • (1 : qrRbar P.f) by
      simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq], smul_assoc, one_smul]
  rw [h1, P.ringEquiv_mk]
  exact Stacks.SemilinearTransport.quotientAddEquivOfSurjective_smul _ _ _ _ _ _ a x

/-- **The presented module is free over `S` on the monomials of degree `n`** in the generators
of the ideal, for a quasi-regular generating sequence. -/
@[ega "IV 16.9.3" "(i)", sga "1 II 4.14" "(ii)"]
noncomputable def basis
    (hqr : _root_.RingTheory.Sequence.IsQuasiRegular R (List.ofFn P.f)) :
    Module.Basis {d : Fin c →₀ ℕ | d.degree = n} S N :=
  Stacks.SemilinearTransport.basisOfAddEquiv P.ringEquiv P.tcompEquiv P.tcompEquiv_smul
    (basisTcomp P.f (bijective_associatedGradedMap_of_isQuasiRegular P.f hqr) n)

/-- **A basis of the presented module is a basis of `J^n/J^{n+1}`**, on the same index set and
over `R/J`: the reverse transport of `Stacks.RingTheory.QuasiRegular.GradedPresentation.basis`,
which needs no quasi-regularity and is what feeds
`Stacks.RingTheory.QuasiRegular.isQuasiRegular_of_basisTcomp`. -/
noncomputable def basisTcompOfBasis {ι : Type*} (bN : Module.Basis ι S N) :
    Module.Basis ι (qrRbar P.f) (Tcomp R P.f n) :=
  Stacks.SemilinearTransport.basisOfAddEquiv P.ringEquiv.symm P.tcompEquiv.symm
    (fun s y => by
      have h := P.tcompEquiv_smul (P.ringEquiv.symm s) (P.tcompEquiv.symm y)
      rw [RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
      rw [← h, AddEquiv.symm_apply_apply]) bN

end GradedPresentation

namespace GradedPresentation

variable {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
  (P : GradedPresentation R S c 1 N)

/-- **In degree one the presented module is free over `S` on the classes of the generators**,
indexed by the generating sequence itself. -/
@[ega "IV 16.9.3" "(i), special case"]
noncomputable def basisOne
    (hqr : _root_.RingTheory.Sequence.IsQuasiRegular R (List.ofFn P.f)) :
    Module.Basis (Fin c) S N :=
  Stacks.SemilinearTransport.basisOfAddEquiv P.ringEquiv P.tcompEquiv P.tcompEquiv_smul
    (basisGeneratorClass P.f
      (bijective_associatedGradedMap_of_isQuasiRegular P.f hqr).injective)

include P in
/-- The degree-one piece of a presentation by a quasi-regular sequence is a finite
`S`-module. -/
theorem finite_of_presentationOne
    (hqr : _root_.RingTheory.Sequence.IsQuasiRegular R (List.ofFn P.f)) : Module.Finite S N :=
  Module.Finite.of_basis (basisOne P hqr)

end GradedPresentation

end Stacks.RingTheory.QuasiRegular

end
