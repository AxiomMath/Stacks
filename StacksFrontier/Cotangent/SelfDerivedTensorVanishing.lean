module

public import StacksFrontier.Cotangent.FilteredColimitVanishing
public import StacksFrontier.Cotangent.PolynomialAlgebra
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChangeDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the cotangent complex when a ring is its own derived tensor square

Let `A ⟶ B` be a ring map with `B = B ⊗_A^𝐋 B`. Then `L_{B/A} = 0` in `D(B)`, which is
[Stacks, Tag 08R0].

The source's proof is two steps: `L_{B/A} = L_{B/B}` by [Stacks, Tag 08QZ] applied to the tower
`A ⟶ B ⟶ B`, and `L_{B/B} = 0`. Both are carried out here.

## Main results

* `CommAlgCat.isZero_cotangentComplex_self`: `L_{B/B} = 0`, because `B` is a polynomial algebra
  over itself on the empty set of variables and `Ω[B⁄B] = 0`.
* `CommAlgCat.isZero_cotangentComplex_of_derivedTensor_self`: **Stacks 08R0**.

## Implementation notes

`L_{B/B}` is written `cotangentComplex B (CommAlgCat.of B B)`. The second argument of
`CommAlgCat.cotangentComplex` is an algebra *object* rather than a bare type, so `B` has to
be presented as an algebra over itself; `CommAlgCat.of` is the constructor used for this elsewhere
in the directory.

That `B` is a polynomial algebra over itself is witnessed by the empty index set:
`CommAlgCat.IsPolynomialAlgebra` unfolds to the existence of some `ι` with
`MvPolynomial ι A ≃ₐ[A] P`, and `MvPolynomial.isEmptyAlgEquiv` supplies the equivalence for an
empty `ι`.

The hypothesis `B = B ⊗_A^𝐋 B` is written out as the two conditions it amounts to: the higher
Tor modules `Tor_i^A(B, B)` vanish, which is `RingTheory.TorIndependence.TorIndependent A B B`,
and the multiplication map `B ⊗_A B → B` is bijective. This is the spelling of the hypothesis
`B = B ⊗_A^𝐋 A'` of [Stacks, Tag 08QZ] in `CommAlgCat.midCotangentComplexHomologyIso`, at
`A' = B`. That isomorphism is degreewise, so the first step of the proof yields an isomorphism of
the cohomology of `L_{B/A}` with that of `L_{B/B}` in every degree `≤ 0`; since the cotangent
complex vanishes in positive degrees, `L_{B/A}` is acyclic, hence zero in `D(B)`.

## References

* [Stacks Project, Tag 08R0](https://stacks.math.columbia.edu/tag/08R0)
* [Stacks Project, Tag 08QZ](https://stacks.math.columbia.edu/tag/08QZ)
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

/-- `B` is a polynomial algebra over itself, on the empty set of variables. -/
theorem isPolynomialAlgebra_self (B : Type u) [CommRing B] :
    CommAlgCat.IsPolynomialAlgebra B (CommAlgCat.of B B) :=
  ⟨PEmpty.{u + 1}, ⟨MvPolynomial.isEmptyAlgEquiv B PEmpty.{u + 1}⟩⟩

/-- **The cotangent complex of a ring relative to itself vanishes.** `B` is a polynomial algebra
over itself, so [Stacks, Tag 08QH] identifies `L_{B/B}` with `Ω[B⁄B][0]`, and the module of Kähler
differentials of `B` over itself is zero. -/
theorem isZero_cotangentComplex_self (B : Type u) [CommRing B] :
    Limits.IsZero (DerivedCategory.Q.obj (cotangentComplex B (CommAlgCat.of B B))) := by
  have e := (cotangentComplex_iso_kaehlerDifferential B (CommAlgCat.of B B)
    (isPolynomialAlgebra_self B)).some
  refine Limits.IsZero.of_iso ?_ e
  refine (DerivedCategory.singleFunctor _ 0).map_isZero ?_
  have : Subsingleton (KaehlerDifferential B (CommAlgCat.of B B)) :=
    KaehlerDifferential.subsingleton_of_surjective _ _ Function.surjective_id
  exact ModuleCat.isZero_of_subsingleton _

/-- **Stacks Project, Tag 08R0.** Let `A → B` be a ring map such that `B = B ⊗_A^𝐋 B`, that is,
`Tor_i^A(B, B) = 0` for `i > 0` and the multiplication map `B ⊗_A B → B` is bijective. Then
`L_{B/A} = 0` in `D(B)`.

By [Stacks, Tag 08QZ] for the tower `A → B → B` (`CommAlgCat.midCotangentComplexHomologyIso`),
the cohomology of `L_{B/A}` in each degree `≤ 0` is that of `L_{B/B}`, which vanishes
(`CommAlgCat.isZero_cotangentComplex_self`); in positive degrees `L_{B/A}` is itself zero. -/
@[stacks 08R0]
theorem isZero_cotangentComplex_of_derivedTensor_self (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A)
    (hTor : RingTheory.TorIndependence.TorIndependent A B B)
    (hmul : Function.Bijective
      (Algebra.TensorProduct.lmul' (S := (B : Type u)) A)) :
    Limits.IsZero (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B)) := by
  have hφ : Function.Bijective
      (baseChangeUnit (B' := midAlgebra (B : Type u) B) (AlgHom.id A (B : Type u))) := by
    convert hmul using 1
    funext z
    induction z with
    | tmul a x => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have hneg : ∀ n : ℕ, (cotangentComplex.{u, u} A B).ExactAt (-(n : ℤ)) := fun n => by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (CochainComplex.exactAt_of_isZero_Q _ _ (isZero_cotangentComplex_self (B : Type u)))).of_iso
      (midCotangentComplexHomologyIso (A' := (B : Type u)) (B := B) hTor hφ n)
  refine CochainComplex.isZero_Q_obj_of_acyclic _ fun n => ?_
  rcases lt_or_ge 0 n with hn | hn
  · rw [HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (cotangentComplex_isZero_pos A B _ hn)
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact hneg m

end CommAlgCat

end
