module

public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension
public import StacksFrontier.RingTheory.Syntomic.ConormalRank
public import StacksFrontier.RingTheory.Syntomic.SpreadingOutFreeness

/-!
# A finite syntomic algebra is a relative global complete intersection locally on the base

Let `B` be a finite syntomic algebra over `A` and let `p` be a prime of `A`. Then there is
`g ∉ p` such that `B_g` is a relative global complete intersection over `A_g`, cut out of a
polynomial ring by as many equations as variables. This is the implication (1) ⟹ (4) of Stacks
0FKY in its algebraic form, over an arbitrary base.

## Main results

* `Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_away_of_finite_syntomic`: `B_g`
  is a relative global complete intersection over `A`.
* `Algebra.exists_notMem_forall_isRelativeGlobalCompleteIntersection_of_finite_syntomic`: the
  same over `A_g`, for any models of the localizations.

## Implementation notes

The conormal module `I/I²` of a finite polynomial presentation `B = A[x_1, …, x_n]/I` is finite
projective of rank `n` at every prime of `B`
(`Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic`). Over a base whose spectrum is
not semilocal it need not be free, so no square presentation of `B` itself is available; what is
available is a basis after inverting one element `g ∉ p` of the base, which is
`Stacks.RingTheory.SpreadFree.exists_mem_primeCompl_nonempty_basis_localizedModule`, the
spreading out of Lemma 02M9 over the semilocal ring `B ⊗_A A_p`.

Inverting `g` in `B` adjoins one variable and one relation to the presentation, and the conormal
module of the enlarged presentation is `(I/I²)_g ⊕ B_g` (Stacks 08JZ); it is therefore free of
rank `n + 1`, the number of variables. Lemma 07CF then adjoins a further variable and relation
and makes the relations a basis of the conormal module, so the enlarged presentation has `n + 2`
of each. Quasi-finiteness makes the dimension condition of Definition 00SP automatic for a square
presentation, which is all that is left.

Finally `B_g` is a relative global complete intersection over `A_g` rather than only over `A`
because `A → B_g` factors through `A_g`, which is Stacks 00SS (3).

## References

* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
* [Stacks Project, Tag 00SS](https://stacks.math.columbia.edu/tag/00SS)
* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
* [Stacks Project, Tag 07CF](https://stacks.math.columbia.edu/tag/07CF)
* [Stacks Project, Tag 08JZ](https://stacks.math.columbia.edu/tag/08JZ)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-- **A finite syntomic algebra becomes a relative global complete intersection after inverting
one element of the base.** For `B` finite syntomic over `A` and `p` a prime of `A` there is
`g ∉ p` such that `B_g = A[x_1, …, x_m]/(f_1, …, f_m)` for some `m`. -/
theorem Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_away_of_finite_syntomic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [Module.Finite A B] (p : Ideal A) [p.IsPrime] :
    ∃ g ∈ p.primeCompl, Algebra.IsRelativeGlobalCompleteIntersection A
      (Localization.Away (algebraMap A B g)) := by
  classical
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Algebra.Generators A B (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rw [heval]; exact hf)
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B) :=
    (NaiveCotangent.hasTorAmplitude_tfae_syntomic A B (Algebra.Syntomic A B) (by simp)
      (RingHom.IsLocalCompleteIntersection (algebraMap A B)) (by simp)).mp
      ‹Algebra.Syntomic A B›
  obtain ⟨hfin, hproj⟩ := P.cotangent_finite_projective_of_isLocalCompleteIntersection hlci
  have : Module.Finite B P.toExtension.Cotangent := hfin
  have : Module.Projective B P.toExtension.Cotangent := hproj
  obtain ⟨g, hgp, ⟨bM⟩⟩ :=
    Stacks.RingTheory.SpreadFree.exists_mem_primeCompl_nonempty_basis_localizedModule
      P.toExtension.Cotangent
      (fun q => Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic P q) p
  refine ⟨g, hgp, ?_⟩
  obtain ⟨e, -⟩ := Algebra.Generators.exists_cotangentComplex_comp_localizationAway_eq_prodMap
    (T := Localization.Away (algebraMap A B g)) (algebraMap A B g) P
  let b₀ : Module.Basis (Fin n ⊕ Unit) (Localization.Away (algebraMap A B g))
      ((Algebra.Generators.localizationAway (Localization.Away (algebraMap A B g))
        (algebraMap A B g)).comp P).toExtension.Cotangent :=
    ((bM.map (LocalizedModule.equivTensorProduct _ _)).prod
      (Algebra.Generators.basisCotangentAway (Localization.Away (algebraMap A B g))
        (algebraMap A B g))).map e.symm
  obtain ⟨P', -, -, -⟩ := Algebra.Generators.exists_presentation_of_basis_cotangent
    ((Algebra.Generators.localizationAway (Localization.Away (algebraMap A B g))
      (algebraMap A B g)).comp P) b₀
  have hP' : P'.IsRelativeGlobalCompleteIntersection := by
    refine ⟨fun q _ hnt => ?_⟩
    have := hnt
    rw [Algebra.QuasiFinite.ringKrullDim_fiber_eq_zero q]
    simp [Nat.card_eq_fintype_card, add_comm]
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_presentation P'

/-- **A finite syntomic algebra is a relative global complete intersection over a basic open of
the base.** For `B` finite syntomic over `A` and `p` a prime of `A` there is `g ∉ p` such that
`B_g = A_g[x_1, …, x_m]/(f_1, …, f_m)` for some `m`, for any models `A_g` and `B_g` of the two
localizations away from `g`. -/
theorem Algebra.exists_notMem_forall_isRelativeGlobalCompleteIntersection_of_finite_syntomic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [Module.Finite A B] (p : Ideal A) [p.IsPrime] :
    ∃ g ∈ p.primeCompl, ∀ (Ag Bg : Type u) [CommRing Ag] [CommRing Bg] [Algebra A Ag]
      [Algebra A Bg] [Algebra B Bg] [Algebra Ag Bg] [IsScalarTower A B Bg]
      [IsScalarTower A Ag Bg] [IsLocalization.Away g Ag]
      [IsLocalization.Away (algebraMap A B g) Bg],
      Algebra.IsRelativeGlobalCompleteIntersection Ag Bg := by
  obtain ⟨g, hgp, h⟩ :=
    Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_away_of_finite_syntomic
      (A := A) (B := B) p
  refine ⟨g, hgp, fun Ag Bg _ _ _ _ _ _ _ _ _ _ => ?_⟩
  have := h
  have : Algebra.IsRelativeGlobalCompleteIntersection A Bg :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv
      ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B g))
        (Localization.Away (algebraMap A B g)) Bg).restrictScalars A)
  exact Algebra.IsRelativeGlobalCompleteIntersection.localization_base (Submonoid.powers g)

end
