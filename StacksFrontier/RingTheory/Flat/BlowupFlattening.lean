module

public import StacksFrontier.RingTheory.Flat.BlowupGeometricallyIntegralFibres
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus

/-!
# Flattening a module by a blowup

Stacks 0810 says that a finite module `M` over a flat finitely presented algebra `S` of `R` with
geometrically integral fibres, which is finitely presented away from `f : R` and free of rank `r`
at the primes of `S` extended from the primes of `R` avoiding `f`, becomes free of rank `r` on
every affine chart of a blowup of `Spec R` in a finitely generated ideal cutting out `V(f)`.

`StacksFrontier.RingTheory.Flat.BlowupGeometricallyIntegralFibres` proves that from projectivity of
`S` as an `R`-module, which is Stacks 05FT, and proves it a second time from the two
generic-fibre statements that Stacks 05FT needed at the time. Stacks 05FT is now a theorem,
`Algebra.projective_of_geometricallyIntegral_fibres`, so **this file states Stacks 0810 with no
hypothesis beyond its own**, by supplying that projectivity.

## Main results

* `exists_fg_ideal_forall_blowup_chart_exists_away_basis`: **Stacks Project, Tag 0810.**

## Implementation notes

The fibre hypothesis of Stacks 0810 is stated with the fibre ring `Ideal.Fiber p S`, that of
Stacks 05FT with the base change `S ⊗[R] κ(p)` carrying `Algebra.TensorProduct.rightAlgebra`.
`Algebra.TensorProduct.comm` identifies the two as `κ(p)`-algebras, which is the only work here;
it is the same identification that
`exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_good_halves` performs, and it is done
with `Algebra.IsGeometricallyIntegral.of_algEquiv`.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open scoped TensorProduct

universe u v

/-- **Stacks Project, Tag 0810.** Let `R → S` be flat and of finite presentation with
geometrically integral fibres, let `f : R`, and let `M` be a finite `S`-module which is finitely
presented after inverting `f` and free of rank `r` at every extended prime `pS` with `f ∉ p`.
Then there is a finitely generated ideal `I ⊆ R` with `V(f) = V(I)` such that for every `a ∈ I`,
writing `R' = R[I/a]` and `S' = S ⊗[R] R'`, the quotient `M'` of `S' ⊗[S] M` by its `a`-power
torsion is free of rank `r` after inverting some `g : S'` outside `p'S'`, for every prime `p'` of
`R'`.

This is `exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective` with its hypothesis
`Module.Projective R S` supplied by Stacks 05FT,
`Algebra.projective_of_geometricallyIntegral_fibres`. -/
@[stacks 0810]
public theorem exists_fg_ideal_forall_blowup_chart_exists_away_basis
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (M : Type v) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (f : R) (r : ℕ)
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber S))
    (hfp : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule (Submonoid.powers (algebraMap R S f)) M))
    (hrank : ∀ (p : Ideal R) (hp : p.IsPrime), f ∉ p →
      letI := hp
      let q := Ideal.map (algebraMap R S) p
      ∀ hq : q.IsPrime,
        letI := hq
        Nonempty
          (LocalizedModule q.primeCompl M ≃ₗ[Localization q.primeCompl]
            (Fin r → Localization q.primeCompl))) :
    ∃ I : Ideal R, I.FG ∧
      (∀ (p : Ideal R), p.IsPrime → (f ∈ p ↔ I ≤ p)) ∧
      ∀ (a : R) (ha : a ∈ I),
        letI : Fact (a ∈ I) := ⟨ha⟩
        let R' := Blowup I a
        let S' := S ⊗[R] R'
        let N := S' ⊗[S] M
        let M' := N ⧸ Submodule.torsion' S' N
          (Submonoid.powers (algebraMap S S' (algebraMap R S a)))
        ∀ (p' : Ideal R') (_hp' : p'.IsPrime), ∃ g : S',
          g ∉ Ideal.map Algebra.TensorProduct.includeRight p' ∧
          Nonempty
            (LocalizedModule (Submonoid.powers g) M' ≃ₗ[Localization.Away g]
              (Fin r → Localization.Away g)) := by
  have _ : Module.Projective R S := by
    refine Algebra.projective_of_geometricallyIntegral_fibres ?_
    intro p hp
    let _ : Algebra p.ResidueField (S ⊗[R] p.ResidueField) := Algebra.TensorProduct.rightAlgebra
    refine Algebra.IsGeometricallyIntegral.of_algEquiv
      (AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv)
        (fun x ↦ by
          simp [Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.right_algebraMap_apply])) (hfibre p hp)
  exact exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective
    R S M f r hfibre hfp hrank

end
