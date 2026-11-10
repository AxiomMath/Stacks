module

public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs

/-!
# The two models of the canonical map of a quasi-regular sequence

Quasi-regularity of a finite family `f : Fin c → R` of elements of a commutative ring asks that
the canonical graded map
`Φ_M : (R/J)[X_1, …, X_c] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} J^n M / J^{n+1} M`, `J = (f_1, …, f_c)`,
be bijective. Two models of `Φ_M` are in use. `RingTheory.Sequence.quasiRegularCanonicalMap`
writes its source as a tensor product over `R/J` with the polynomial ring on the left, whereas
`Quasiregular.qregPhi` writes it as the free `M/JM`-module on the monomials. This file identifies
the two, so that the predicates `Quasiregular.IsMQuasiregularSeq` and
`RingTheory.Sequence.IsQuasiRegular` built on them agree.

## Main results

* `Quasiregular.isMQuasiregularSeq_iff_bijective_quasiRegularCanonicalMap`: the two models of the
  canonical map are bijective together.
* `Quasiregular.isQuasiregularSeq_iff_isQuasiRegular`: a finite family is a quasi-regular
  sequence in the sense of `Quasiregular.IsQuasiregularSeq` exactly when the list it spells out
  is quasi-regular in the sense of `RingTheory.Sequence.IsQuasiRegular`.

## Implementation notes

The identification is the monomial basis of the polynomial ring: tensoring with it turns the
tensor-product source into the finitely supported source,
`TensorProduct.equivFinsuppOfBasisLeft`, and under that equivalence the two maps agree monomial
by monomial, which is `RingTheory.Sequence.canonicalMap_srcMono`. The only further discrepancy is
bookkeeping: `Quasiregular.qregPhi` takes its monomial coefficients in
`M ⧸ Quasiregular.jpow (Ideal.span (Set.range f)) M 1` and
`RingTheory.Sequence.phiMonoR` in `RingTheory.Sequence.qrMbar M f`, two definitionally equal
quotients presented differently, and the degree of a monomial is spelled `Finsupp.sum` on one
side and `Finset.sum` on the other.

Comparing the predicates on a family `f : Fin c → R` with those on `List.ofFn f` is then a
reindexing: `List.equivSigmaTuple` identifies a list with the pair of its length and its entry
function, and `List.ofFn` is its inverse on that pair.

## References

* [Stacks Project, Definition 10.69.1 (Tag 061P)](https://stacks.math.columbia.edu/tag/061P)
* [Stacks Project, Equation 10.69.0.1 (Tag 061N)](https://stacks.math.columbia.edu/tag/061N)
-/

@[expose] public section

open RingTheory.Sequence

namespace Quasiregular

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {r : ℕ} {f : Fin r → R}

/-- **The two models of the canonical map of a quasi-regular sequence agree.** The map
`Quasiregular.qregPhi`, whose source is the free module on the monomials, is bijective exactly
when `RingTheory.Sequence.quasiRegularCanonicalMap`, whose source is the tensor product of the
polynomial ring with `M/JM`, is: the monomial basis of the polynomial ring is an isomorphism of
the two sources identifying the two maps. -/
theorem isMQuasiregularSeq_iff_bijective_quasiRegularCanonicalMap (f : Fin r → R) :
    IsMQuasiregularSeq M f ↔ Function.Bijective (quasiRegularCanonicalMap (M := M) f) := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := qrMbar M f)
    (MvPolynomial.basisMonomials (Fin r) (qrRbar f))
  have hmap :
      (Finsupp.lsum R fun d => phiMonoR (M := M) f d) =
        (quasiRegularCanonicalMap (M := M) f).restrictScalars R ∘ₗ
          e.symm.toLinearMap.restrictScalars R := by
    refine Finsupp.lhom_ext fun d m => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, Finsupp.lsum_single]
    change phiMonoR f d m = quasiRegularCanonicalMap f (e.symm (Finsupp.single d m))
    simp only [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_single_index,
      TensorProduct.tmul_zero]
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (Jid f • (⊤ : Submodule R M)) m
    exact (canonicalMap_srcMono f d m).symm
  let q : (M ⧸ jpow (Ideal.span (Set.range f)) M 1) ≃ₗ[R] qrMbar M f :=
    Submodule.quotEquivOfEq _ _ (by simp [jpow, Jid])
  let qf : ((Fin r →₀ ℕ) →₀ (M ⧸ jpow (Ideal.span (Set.range f)) M 1)) ≃ₗ[R]
      ((Fin r →₀ ℕ) →₀ qrMbar M f) := Finsupp.mapRange.linearEquiv q
  have hphi : qregPhi (M := M) f =
      (Finsupp.lsum R fun d => phiMonoR (M := M) f d) ∘ₗ qf.toLinearMap := by
    refine Finsupp.lhom_ext fun d m => ?_
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    change qregPhi f (Finsupp.single d (Submodule.Quotient.mk m)) =
      (Finsupp.lsum R fun d => phiMonoR f d)
        (qf (Finsupp.single d (Submodule.Quotient.mk m)))
    have hq : qf (Finsupp.single d (Submodule.Quotient.mk m)) =
        Finsupp.single d (Submodule.Quotient.mk m) := by
      simp only [qf, Finsupp.mapRange.linearEquiv_apply]
      exact Finsupp.mapRange_single
    rw [hq]
    simp only [qregPhi, Finsupp.lsum_single, LinearMap.comp_apply]
    change DirectSum.lof R ℕ (fun n => Tcomp M f n) (d.sum fun _ k => k)
      (Submodule.Quotient.mk ⟨(∏ i, f i ^ d i) • m, _⟩) = imgTargetLin f d m
    have hd : d.sum (fun _ k => k) = qrMdeg d := by
      simp [Finsupp.sum_fintype, qrMdeg]
    have hl : ∀ (n : ℕ) (hm : (∏ i, f i ^ d i) • m ∈ JpowM M f n),
        n = qrMdeg d →
        DirectSum.lof R ℕ (fun n => Tcomp M f n) n
          (Submodule.Quotient.mk ⟨(∏ i, f i ^ d i) • m, hm⟩) =
        imgTargetLin f d m := by
      rintro n hm rfl
      rfl
    exact hl _ _ hd
  change Function.Bijective (qregPhi (M := M) f) ↔ _
  rw [hphi, hmap]
  exact (qf.bijective.of_comp_iff _).trans (e.symm.bijective.of_comp_iff _)

/-- Reindexing a finite family as the list it spells out does not change the canonical map, so
the two spellings of quasi-regularity of a finite family agree. -/
theorem bijective_quasiRegularCanonicalMap_iff_isQuasiRegular (f : Fin r → R) :
    Function.Bijective (quasiRegularCanonicalMap (M := M) f) ↔
      IsQuasiRegular M (List.ofFn f) := by
  let P := fun s : Σ n, Fin n → R =>
    Function.Bijective (quasiRegularCanonicalMap (M := M) s.2)
  change P ⟨r, f⟩ ↔ P (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨r, f⟩))
  rw [Equiv.apply_symm_apply]

/-- **The two notions of quasi-regular sequence agree.** A finite family of elements of a
commutative ring is a quasi-regular sequence in the sense of
`Quasiregular.IsQuasiregularSeq` exactly when the list it spells out is quasi-regular in the
sense of `RingTheory.Sequence.IsQuasiRegular`. -/
theorem isQuasiregularSeq_iff_isQuasiRegular (f : Fin r → R) :
    IsQuasiregularSeq f ↔ IsQuasiRegular R (List.ofFn f) :=
  (isMQuasiregularSeq_iff_bijective_quasiRegularCanonicalMap f).trans
    (bijective_quasiRegularCanonicalMap_iff_isQuasiRegular f)

end Quasiregular

end
