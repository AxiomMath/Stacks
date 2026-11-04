module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseDecomposition

/-!
# The finite case of property (B) read on the idempotents of the local structure theorem

The finite case of property (B) for the étale topology, [Stacks, Tag 04DQ], was reduced in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseDecomposition` to the
ring-theoretic statement `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover`: for a
module-finite `A → B`, an étale `B`-algebra `C` surjective on spectra and a prime `p` of `A`, an
étale `A`-algebra `A₁` with a prime over `p` for which `B ⊗[A] A₁` is a finite product of
`C`-algebras.

That statement still mentions the base `A`, the tensor product `B ⊗[A] A₁` and the étale
neighbourhood `A₁` of the base, none of which the remaining argument touches: the only thing the
remaining argument does is *trim*, by inverting a single element of the étale neighbourhood
already produced, the pair of decompositions that the étale local structure theorem
[Stacks, Tag 00UL] supplies. This file performs that change of shape. It names the trimming
problem — `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents` — directly on the
output of `Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`,
and discharges everything around it: the production of the étale neighbourhood `A₁` as
`A'[1/a]`, its prime over `p`, the identification of `B ⊗[A] A₁` with `(A' ⊗[A] B)[1/a]` through
`Stacks.EtaleCohomology.tensorLocalizationAwayEquivLeft`, and the `C`-algebra structures with
their compatibility over `B`.

The statement is kept on the *whole* data of the local structure theorem — the two complete
orthogonal families of idempotents and all eight of their properties — and not on the bare triple
`A' → P → E`. Dropping the idempotents would make it false: for `A' = P = ℝ` and `E = ℂ`, which is
étale over `ℝ` and surjective on spectra, a decomposition of a localisation of `ℝ` into nonzero
`ℂ`-algebras cannot exist, since there is no ring homomorphism `ℂ → ℝ`. It is exactly the
idempotents, and the étaleness of `A'` over `A` that produced them, that make the trimming
possible.

## Main definitions

* `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents` is the trimming problem: given
  the two complete orthogonal families of idempotents of [Stacks, Tag 00UL] on a module-finite
  `A'`-algebra `P` and on an étale `P`-algebra `E` surjective on spectra, one localisation of `A'`
  outside the chosen prime turns `P` into a finite product of `E`-algebras.

## Main results

* `Stacks.EtaleCohomology.hasFiniteCaseDecompositionOfCover_of_idempotents`:
  `HasFiniteCaseDecompositionOfIdempotents` implies
  `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover`.
* `Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_idempotents` and
  `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_idempotents`: property (B) for a
  finite, respectively an integral, morphism of schemes, assuming
  `HasFiniteCaseDecompositionOfIdempotents`. These are [Stacks, Tag 04DQ] and
  [Stacks, Tag 04DR] with that single ring-theoretic statement as their only remaining input.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Algebra.TensorProduct.rightAlgebra awayTensorRightAlgebra

/-- **The trimming problem that the finite case of property (B) reduces to.** Let `A'` be a ring
with a prime `p'`, let `P` be a module-finite `A'`-algebra and `E` an étale `P`-algebra whose
spectrum surjects onto `Spec P`, and let `b` and `c` be the two complete orthogonal families of
idempotents that the étale local structure theorem [Stacks, Tag 00UL] attaches to `P` and to `E`
over `p'`: for each index other than the last the corresponding factor is module-finite over `A'`,
carries at most one prime over `p'`, and has purely inseparable residue field extension there,
while the last factor carries no prime over `p'` at which the algebra is quasi-finite over `A'`.

The statement asks for a single element `a` of `A'` outside `p'` after whose inversion `P` becomes
a finite product of rings, each of which is an algebra over `E` compatibly with `P` — that is, a
disjoint-union decomposition of the fibre product subordinate to the covering.

This is `Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover` with the base ring, the tensor
product and the étale neighbourhood removed;
`Stacks.EtaleCohomology.hasFiniteCaseDecompositionOfCover_of_idempotents` puts them back. It is the
one step of [Stacks, Tag 04DQ] that is not proved in this library. The route to it is the
per-index comparison
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair`, applied once for
each index of the `b`-family after the dead factors have been discarded by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_completeOrthogonalIdempotents_liesOver` and the
surviving idempotents turned into units by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_algebraMap_eq_one`, the matching index of the
`c`-family being supplied by `Stacks.EtaleCohomology.exists_liesOver_notMem_castSucc`; the
finitely many elements so produced are combined into one by
`Stacks.EtaleCohomology.exists_notMem_forall_dvd_of_forall_exists`, and the hypotheses are carried
across the intervening shrinking of the base by the lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.ShrunkStagePrime`. -/
def HasFiniteCaseDecompositionOfIdempotents : Prop :=
  ∀ (A' P E : Type u) [CommRing A'] [CommRing P] [CommRing E]
    [Algebra A' P] [Algebra A' E] [Algebra P E] [IsScalarTower A' P E]
    [Module.Finite A' P] [Algebra.Etale P E]
    (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap P E)))
    (p' : Ideal A') [p'.IsPrime] (n : ℕ) (b : Fin (n + 1) → P) (c : Fin (n + 1) → E)
    (_ : CompleteOrthogonalIdempotents b) (_ : CompleteOrthogonalIdempotents c)
    (_ : ∀ i : Fin n, Module.Finite A' (Localization.Away (b i.castSucc)))
    (_ : ∀ (i : Fin n) (q₁ q₂ : Ideal P), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
      q₁.LiesOver p' → q₂.LiesOver p' → b i.castSucc ∉ q₁ → b i.castSucc ∉ q₂ → q₁ = q₂)
    (_ : ∀ (i : Fin n) (q : Ideal P), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
      b i.castSucc ∉ q →
      letI := Localization.AtPrime.algebraOfLiesOver p' q
      IsPurelyInseparable p'.ResidueField q.ResidueField)
    (_ : ∀ q : Ideal P, ∀ _ : q.IsPrime, q.LiesOver p' → b (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q)
    (_ : ∀ i : Fin n, Module.Finite A' (Localization.Away (c i.castSucc)))
    (_ : ∀ (i : Fin n) (q₁ q₂ : Ideal E), ∀ _ : q₁.IsPrime, ∀ _ : q₂.IsPrime,
      q₁.LiesOver p' → q₂.LiesOver p' → c i.castSucc ∉ q₁ → c i.castSucc ∉ q₂ → q₁ = q₂)
    (_ : ∀ (i : Fin n) (q : Ideal E), ∀ _ : q.IsPrime, ∀ _ : q.LiesOver p',
      c i.castSucc ∉ q →
      letI := Localization.AtPrime.algebraOfLiesOver p' q
      IsPurelyInseparable p'.ResidueField q.ResidueField)
    (_ : ∀ q : Ideal E, ∀ _ : q.IsPrime, q.LiesOver p' → c (Fin.last n) ∉ q →
      ¬ Algebra.QuasiFiniteAt A' q),
    ∃ a ∉ p', ∃ (L : Type u) (_ : Finite L) (F : L → Type u) (_ : ∀ l, CommRing (F l))
      (_ : ∀ l, Algebra P (F l)) (_ : ∀ l, Algebra E (F l))
      (_ : ∀ l, IsScalarTower P E (F l)),
      Nonempty (Localization.Away (algebraMap A' P a) ≃ₐ[P] (∀ l, F l))

/-- **The covering form of the ring-theoretic statement follows from the idempotent form.**
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents` implies
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfCover`.

The étale local structure theorem is applied once, through
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`, to the pair
`(B, C)`, giving an étale `A`-algebra `A'` with a prime `p'` over `p` and the two families of
idempotents on `P = A' ⊗[A] B` and `E = P ⊗[B] C`; the covering side is surjective on spectra by
`Stacks.EtaleCohomology.surjective_comap_tensorBaseChange`. The hypothesis then supplies `a ∉ p'`
and the decomposition of `P[1/a]`, and the étale neighbourhood of the base asked for is `A'[1/a]`,
étale over `A` as a composite, with the prime `p'` cuts out there lying over `p` by
`Stacks.EtaleCohomology.liesOver_map_algebraMap_of_notMem`. What remains is bookkeeping:
`Stacks.EtaleCohomology.tensorLocalizationAwayEquivLeft` identifies `B ⊗[A] A'[1/a]` with
`P[1/a]` as `B`-algebras, each factor is an algebra over `C` through `E`, and the compatibility
over `B` holds because `(β ⊗ 1) ⊗ 1 = 1 ⊗ β` in `P ⊗[B] C`. -/
theorem hasFiniteCaseDecompositionOfCover_of_idempotents
    (h : HasFiniteCaseDecompositionOfIdempotents.{u}) :
    HasFiniteCaseDecompositionOfCover.{u} := by
  intro A B C _ _ _ _ _ _ _ _ _ hsurj p _
  obtain ⟨A', _, _, _, p', _, _, n, b, c, hb, hc, ⟨hbfin, hbuniq, hbres, hblast⟩,
    ⟨hcfin, hcuniq, hcres, hclast⟩⟩ :=
    exists_etale_completeOrthogonalIdempotents_tensorBaseChange (A := A) (B := B) (C := C) p
  obtain ⟨a, hap, L, hLfin, F, hFring, hFalgP, hFalgE, hFtower, ⟨ε⟩⟩ :=
    h A' (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] C) (surjective_comap_tensorBaseChange A' hsurj) p'
      n b c hb hc hbfin hbuniq hbres hblast hcfin hcuniq hcres hclast
  let _ := hFring
  let _ := hFalgP
  let _ := hFalgE
  let _ := hFtower
  let instB : ∀ l, Algebra B (F l) := fun l =>
    ((algebraMap (A' ⊗[A] B) (F l)).comp (algebraMap B (A' ⊗[A] B))).toAlgebra
  let instC : ∀ l, Algebra C (F l) := fun l =>
    ((algebraMap ((A' ⊗[A] B) ⊗[B] C) (F l)).comp
      (algebraMap C ((A' ⊗[A] B) ⊗[B] C))).toAlgebra
  have htow : ∀ l, IsScalarTower B C (F l) := by
    intro l
    refine .of_algebraMap_eq fun x => ?_
    change algebraMap ((A' ⊗[A] B)) (F l) (algebraMap B (A' ⊗[A] B) x) = _
    rw [(hFtower l).algebraMap_eq ((A' ⊗[A] B)) ((A' ⊗[A] B) ⊗[B] C) (F l)]
    have key : algebraMap (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] C) (algebraMap B (A' ⊗[A] B) x)
        = algebraMap C ((A' ⊗[A] B) ⊗[B] C) (algebraMap B C x) := by
      change (algebraMap B (A' ⊗[A] B) x) ⊗ₜ[B] (1 : C) =
        (1 : A' ⊗[A] B) ⊗ₜ[B] (algebraMap B C x)
      rw [Algebra.algebraMap_eq_smul_one x, Algebra.algebraMap_eq_smul_one x,
        TensorProduct.smul_tmul]
    rw [RingHom.comp_apply, key]
    rfl
  exact ⟨Localization.Away a, inferInstance, inferInstance,
    Algebra.Etale.comp A A' (Localization.Away a),
    p'.map (algebraMap A' (Localization.Away a)),
    isPrime_map_algebraMap_of_notMem a p' hap,
    liesOver_map_algebraMap_of_notMem a p p' hap, L, hLfin, F, hFring,
    instB, instC, htow, ⟨AlgEquiv.ofRingEquiv
      (f := (tensorLocalizationAwayEquivLeft A A' B a).toRingEquiv.trans ε.toRingEquiv)
      fun x => by
        change ε (tensorLocalizationAwayEquivLeft A A' B a (algebraMap B _ x)) = _
        rw [AlgEquiv.commutes]
        change ε (algebraMap (A' ⊗[A] B) _ (algebraMap B (A' ⊗[A] B) x)) = _
        rw [AlgEquiv.commutes]
        rfl⟩⟩

/-- **Property (B) for a finite morphism, from the idempotent form of the ring-theoretic
statement.** This is [Stacks, Tag 04DQ] modulo
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents`, obtained by composing
`Stacks.EtaleCohomology.hasFiniteCaseDecompositionOfCover_of_idempotents` with
`Stacks.EtaleCohomology.hasFiniteCaseDecomposition_of_cover` and
`Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition`. -/
theorem hasPropertyB_of_isFinite_of_idempotents
    (h : HasFiniteCaseDecompositionOfIdempotents.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    HasPropertyB f :=
  hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition
    (hasFiniteCaseDecomposition_of_cover (hasFiniteCaseDecompositionOfCover_of_idempotents h)) f

/-- **Property (B) for an integral morphism, from the idempotent form of the ring-theoretic
statement.** This is [Stacks, Tag 04DR] modulo
`Stacks.EtaleCohomology.HasFiniteCaseDecompositionOfIdempotents`: the integral case is the finite
case together with the limit argument
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite`, so the two tags have the same
single remaining input. -/
theorem hasPropertyB_of_isIntegralHom_of_idempotents
    (h : HasFiniteCaseDecompositionOfIdempotents.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] : HasPropertyB f :=
  hasPropertyB_of_isIntegralHom_of_hasFiniteCaseDecomposition
    (hasFiniteCaseDecomposition_of_cover (hasFiniteCaseDecompositionOfCover_of_idempotents h)) f

end Stacks.EtaleCohomology

end
