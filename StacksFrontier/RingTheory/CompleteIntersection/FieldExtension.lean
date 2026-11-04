module

import Mathlib.RingTheory.Finiteness.Descent

public import StacksFrontier.RingTheory.CompleteIntersection.BaseChange

/-!
# Being a local complete intersection is insensitive to a field extension

Let `k → K` be an extension of fields and let `S` be a `k`-algebra. Then `S` is a local complete
intersection over `k` (`Spec S` is covered by standard opens `D(g)` whose rings `S_g` are presented
as `k[x₁, …, xₙ] / (f₁, …, f_c)` with `dim S_g = n - c`) if and only if the base change `S ⊗_k K`
is a local complete intersection over `K`.

## Main results

* `Algebra.IsPushout.isLocalCompleteIntersection_iff`: for a field extension `k → K` and a base
  change `S' = S ⊗_k K`, `S'` is a local complete intersection over `K` if and only if `S` is one
  over `k`.

## Implementation notes

Both sides are translated by `IsLocalCompleteIntersection.tfae` into "the local ring at every
prime is a complete intersection over the base field", and these conditions are matched prime by
prime by `Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff`. Every prime of `S`
lies under a prime of `S'`, because `S → S'` is faithfully flat.

The base change is an arbitrary pushout square of rings, `Algebra.IsPushout k K S S'`, rather than
the chosen model `K ⊗[k] S`; the source's `S' = S ⊗_k K` is `inferInstance`. This covers a fibre
`κ(p') ⊗_{κ(p)} (κ(p) ⊗_R S)` of a ring map after a base change, which is a pushout of
`κ(p) ⊗_R S` along `κ(p) → κ(p')` without being that tensor product on the nose.

The source's finite type hypothesis on `S` is omitted: each side of the equivalence implies it, as
a local complete intersection over a field is of finite type and finite type descends along the
faithfully flat `k → K`.

## References

* [Stacks 00SJ](https://stacks.math.columbia.edu/tag/00SJ), Lemma 10.135.20
* [Stacks 00SH](https://stacks.math.columbia.edu/tag/00SH), Lemma 10.135.9
* [Stacks 00SI](https://stacks.math.columbia.edu/tag/00SI), Lemma 10.135.10
-/

@[expose] public section

namespace CompleteIntersection.FieldExtension

open TensorProduct
universe v w

/-- A global complete intersection over a field `k` is of finite type over `k`. -/
private theorem IsGlobalCompleteIntersection.finiteType {k : Type*} [Field k] {T : Type*}
    [CommRing T] [Algebra k T] (h : IsGlobalCompleteIntersection k T) :
    Algebra.FiniteType k T := by
  rcases h with hsub | ⟨n, c, f, e, -, -⟩
  · have := hsub
    infer_instance
  · have : Algebra.FiniteType k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
    exact this.equiv e.symm

/-- A local complete intersection over a field `k` is of finite type over `k`. -/
private theorem IsLocalCompleteIntersection.finiteType {k : Type*} [Field k] {S : Type*}
    [CommRing S] [Algebra k S] (h : IsLocalCompleteIntersection k S) : Algebra.FiniteType k S := by
  obtain ⟨s, hs, hg⟩ := h
  exact Algebra.FiniteType.of_span_eq_top_target s hs fun g hgs ↦
    IsGlobalCompleteIntersection.finiteType (hg g hgs)

/-- Being of finite type is insensitive to a faithfully flat base change: for a pushout square
`R → T`, `R → S`, `S' = S ⊗_R T` with `T` faithfully flat over `R`, the algebra `S'` is of finite
type over `T` if and only if `S` is of finite type over `R`. -/
private theorem finiteType_baseChange_iff (R T S S' : Type*) [CommRing R] [CommRing T] [CommRing S]
    [CommRing S'] [Algebra R T] [Algebra R S] [Algebra R S'] [Algebra T S'] [Algebra S S']
    [IsScalarTower R T S'] [IsScalarTower R S S'] [Algebra.IsPushout R T S S']
    [Module.FaithfullyFlat R T] : Algebra.FiniteType T S' ↔ Algebra.FiniteType R S := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Algebra.FiniteType T (T ⊗[R] S) := h.equiv (Algebra.IsPushout.equiv R T S S').symm
    exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat T
  · have h' : Algebra.FiniteType T (T ⊗[R] S) := inferInstance
    exact h'.equiv (Algebra.IsPushout.equiv R T S S')

/-- `Spec S' → Spec S` is surjective for a faithfully flat base change: for a pushout square
`R → T`, `R → S`, `S' = S ⊗_R T` with `T` faithfully flat over `R`, every prime `q` of `S` is the
contraction of a prime of `S'`. -/
private theorem exists_isPrime_liesOver (R T S S' : Type*) [CommRing R] [CommRing T] [CommRing S]
    [CommRing S'] [Algebra R T] [Algebra R S] [Algebra R S'] [Algebra T S'] [Algebra S S']
    [IsScalarTower R T S'] [IsScalarTower R S S'] [Algebra.IsPushout R T S S']
    [Module.FaithfullyFlat R T] (q : Ideal S) [q.IsPrime] :
    ∃ q' : Ideal S', q'.IsPrime ∧ q'.LiesOver q :=
  have : Algebra.IsPushout R S T S' := Algebra.IsPushout.symm inferInstance
  have : Module.FaithfullyFlat S S' :=
    Module.FaithfullyFlat.of_linearEquiv S (S ⊗[R] T)
      (Algebra.IsPushout.equiv R S T S').symm.toLinearEquiv
  Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S') q

/-- For a base change `S' = S ⊗_k K` along a field extension `k → K`, every local ring of `S'` is a
complete intersection over `K` if and only if every local ring of `S` is a complete intersection
over `k`. -/
private theorem forall_isCompleteIntersection_localization_iff (k : Type*) [Field k] (K : Type*)
    [Field K] [Algebra k K] (S : Type v) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (S' : Type w) [CommRing S'] [Algebra k S'] [Algebra K S'] [Algebra S S'] [IsScalarTower k K S']
    [IsScalarTower k S S'] [Algebra.IsPushout k K S S'] :
    (∀ (q' : Ideal S') [q'.IsPrime] (S'q' : Type w) [CommRing S'q'] [Algebra S' S'q']
        [IsLocalization.AtPrime S'q' q'] [Algebra K S'q'] [IsScalarTower K S' S'q'],
        IsCompleteIntersection K S'q') ↔
      ∀ (q : Ideal S) [q.IsPrime] (Sq : Type v) [CommRing Sq] [Algebra S Sq]
        [IsLocalization.AtPrime Sq q] [Algebra k Sq] [IsScalarTower k S Sq],
        IsCompleteIntersection k Sq := by
  constructor
  · intro h q _ Sq _ _ _ _ _
    obtain ⟨q', _, _⟩ := exists_isPrime_liesOver k K S S' q
    exact
      (Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff k K S S' q q' Sq
            (Localization.AtPrime q')).mp
        (h q' (Localization.AtPrime q'))
  · intro h q' _ S'q' _ _ _ _ _
    exact
      (Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff k K S S' (q'.under S) q'
            (Localization.AtPrime (q'.under S)) S'q').mpr
        (h (q'.under S) (Localization.AtPrime (q'.under S)))

/-- For a base change `S' = S ⊗_k K` along a field extension `k → K`, `S'` is a local complete
intersection over `K` if and only if `S` is a local complete intersection over `k`. -/
private theorem isLocalCompleteIntersection_iff (k K S S' : Type*) [Field k] [Field K] [CommRing S]
    [CommRing S'] [Algebra k K] [Algebra k S] [Algebra k S'] [Algebra K S'] [Algebra S S']
    [IsScalarTower k K S'] [IsScalarTower k S S'] [Algebra.IsPushout k K S S'] :
    IsLocalCompleteIntersection K S' ↔ IsLocalCompleteIntersection k S := by
  constructor
  · intro hS'
    have hft' : Algebra.FiniteType K S' := IsLocalCompleteIntersection.finiteType hS'
    have hft : Algebra.FiniteType k S := (finiteType_baseChange_iff k K S S').mp hft'
    exact
      ((IsLocalCompleteIntersection.tfae k S).out 2 1).mp
        ((forall_isCompleteIntersection_localization_iff k K S S').mp
          (((IsLocalCompleteIntersection.tfae K S').out 1 2).mp hS'))
  · intro hS
    have hft : Algebra.FiniteType k S := IsLocalCompleteIntersection.finiteType hS
    have hft' : Algebra.FiniteType K S' := (finiteType_baseChange_iff k K S S').mpr hft
    exact
      ((IsLocalCompleteIntersection.tfae K S').out 2 1).mp
        ((forall_isCompleteIntersection_localization_iff k K S S').mpr
          (((IsLocalCompleteIntersection.tfae k S).out 1 2).mp hS))

end CompleteIntersection.FieldExtension

/-- Let `k → K` be a field extension, let `S` be a `k`-algebra and let `S'` be
the base change of `S` along `k → K`, so `S' = S ⊗_k K`. Then `S'` is a local complete
intersection over `K` if and only if `S` is a local complete intersection over `k`. -/
@[stacks 00SJ "The base change `S' = S ⊗_k K` is an arbitrary pushout square
`Algebra.IsPushout k K S S'`, the orientation of the sibling 00SM; the source's literal form is
`inferInstance`. The source's finite type hypothesis on `S` is omitted: each side of the
equivalence implies it. A local complete intersection over a field (Definition 00S9 (2)) is
`IsLocalCompleteIntersection`. See the module docstring."]
public theorem Algebra.IsPushout.isLocalCompleteIntersection_iff (k K S S' : Type*) [Field k]
    [Field K] [CommRing S] [CommRing S'] [Algebra k K] [Algebra k S] [Algebra k S'] [Algebra K S']
    [Algebra S S'] [IsScalarTower k K S'] [IsScalarTower k S S'] [Algebra.IsPushout k K S S'] :
    IsLocalCompleteIntersection K S' ↔ IsLocalCompleteIntersection k S :=
  CompleteIntersection.FieldExtension.isLocalCompleteIntersection_iff k K S S'

end
