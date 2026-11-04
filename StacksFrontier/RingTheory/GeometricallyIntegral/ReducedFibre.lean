module

public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-!
# The fibre loci, described by one field per point

`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus` defines `Algebra.fibreLocus A C P` by
quantifying over *every* field `K` over `A` whose structure map has kernel `p`: the fibre at `p`
has the property `P` when `P (C ⊗[A] K)` holds for all of them. That is Definition 030S of the
source and its analogue for irreducibility, transported to fibres.

A fibre property written that way cannot be handed to the library's theory of geometrically reduced
and geometrically irreducible algebras, which is stated for `Algebra.IsGeometricallyReduced` and
`Algebra.IsGeometricallyIrreducible` over a single field. **This file closes that gap.** The
quantifier over all fields over `A` with kernel `p` is exactly a quantifier over field extensions
of the residue field `κ(p)`, so the fibre at `p` is governed by the single `κ(p)`-algebra
`κ(p) ⊗[A] C`; and for reducedness the quantifier over field extensions of `κ(p)` collapses
further, to the single field `AlgebraicClosure κ(p)`.

The collapse for reducedness is the equivalence of Definition 030S with Mathlib's
`Algebra.IsGeometricallyReduced`, which tests an algebraic closure alone
(`Algebra.isGeometricallyReduced_field_iff`). It is items (5) and (6) of Stacks 030V,
`Algebra.isGeometricallyReduced_tfae`, whose substance is Lemma 034N,
`Algebra.IsGeometricallyReduced.isReduced_tensorProduct`; here it is stated as
`Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct`, an `Iff` with the tensor
factors in the order the fibre loci use. For irreducibility no collapse is needed:
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct` already
states the all-extensions form.

What has to be added in both cases is that the fields quantified over are precisely the field
extensions of `κ(p)`. A field `K` over `A` with `ker (A → K) = p` has its structure map factoring
through the injection `A ⧸ p ↪ K`, and `K` being a field that injection extends to the fraction
field `κ(p)` of `A ⧸ p` (`IsFractionRing.lift`); conversely a field extension of `κ(p)` is a field
over `A` with kernel `p`, because `κ(p) → K` is injective. The fibre `C ⊗[A] K` is then
`(κ(p) ⊗[A] C) ⊗[κ(p)] K` by `Algebra.TensorProduct.cancelBaseChange`.

## Main results

* `Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct`: over a field `k`, Mathlib's
  `Algebra.IsGeometricallyReduced k S` holds if and only if `S ⊗[k] K` is reduced for *every* field
  extension `K/k`, which is Definition 030S. This repackages items (5) and (6) of Stacks 030V
  with the tensor factors in the other order.
* `Algebra.mem_fibreLocus_iff_forall_residueFieldExtension`: for an iso-invariant property `P`, a
  prime `p` lies in `Algebra.fibreLocus A C P` if and only if
  `P ((κ(p) ⊗[A] C) ⊗[κ(p)] K)` holds for every field extension `K/κ(p)`.
* `Algebra.mem_geometricallyReducedFibreLocus_iff` and
  `Algebra.mem_geometricallyIrreducibleFibreLocus_iff`: the two loci of Stacks 05FT, described at
  each point by `Algebra.IsGeometricallyReduced` and `Algebra.IsGeometricallyIrreducible` of the
  single fibre algebra `κ(p) ⊗[A] C`. The first is the affine, fibrewise case of Stacks 0384.
* `Algebra.mem_geometricallyReducedFibreLocus_iff_isReduced_algebraicClosure`: membership in the
  geometrically reduced fibre locus as reducedness of the single ring
  `C ⊗[A] AlgebraicClosure κ(p)`.
* `Algebra.geometricallyReducedFibreLocus_eq_setOf` and
  `Algebra.geometricallyIrreducibleFibreLocus_eq_setOf`: those descriptions as equalities of
  subsets of `Spec A`, the form in which the two remaining gaps of Stacks 05FT can be attacked with
  the library's theory of geometrically reduced and geometrically irreducible algebras.

## Implementation notes

The quantifier in `Algebra.fibreLocus` ranges over fields in the universe of `A`, and `κ(p)` and
`AlgebraicClosure κ(p)` lie in that universe, so no universe change is involved; this is what makes
the collapse of the quantifier an honest `Iff` rather than an implication in one universe.

The residue field is Mathlib's `Ideal.ResidueField p`, which comes with
`IsFractionRing (A ⧸ p) p.ResidueField` and `Ideal.ker_algebraMap_residueField`. The extension of
`A ⧸ p ↪ K` to `κ(p) → K` is `Algebra.residueFieldLiftOfKerEq`; it is a ring homomorphism rather
than an instance, because the `κ(p)`-algebra structure it puts on `K` depends on the proof
`ker (A → K) = p` and so cannot be found by instance search. In the other direction
`Algebra.ker_algebraMap_of_isScalarTower_residueField` recovers the kernel, so the two sides of
`Algebra.mem_fibreLocus_iff_forall_residueFieldExtension` quantify over the same fields.

The two factors of a fibre are ordered as in `Algebra.fibreLocus`, with the field on the right of
`⊗[A]`, while `Algebra.IsGeometricallyReduced`, `Algebra.IsGeometricallyIrreducible` and Lemma 034N
put the tested algebra on the left of its base change; `Algebra.TensorProduct.comm` mediates, and
`Algebra.fibreResidueFieldEquiv` packages the whole comparison as one ring isomorphism. Nothing
here needs `C` to be of finite type over `A`, or `A` to be Noetherian: every statement is about one
point of `Spec A` at a time, which is why these are `Iff`s with no spreading-out content.

Nothing here carries a `@[stacks 0384]` attribute. Stacks 0384 is a statement about schemes over a
field and about geometric reducedness at a point; what is proved here is the consequence for the
affine fibre of an algebra map, which is the instance of it that Stacks 0579 uses. Likewise
`Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct` is not tagged 030S, which is a
definition rather than a lemma, nor 030V, whose other items are not proved here.

## References

* [Stacks Project, Tag 0384](https://stacks.math.columbia.edu/tag/0384)
* [Stacks Project, Tag 030S](https://stacks.math.columbia.edu/tag/030S)
* [Stacks Project, Tag 030V](https://stacks.math.columbia.edu/tag/030V)
* [Stacks Project, Tag 034N](https://stacks.math.columbia.edu/tag/034N)
* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-- Reducedness of a tensor product does not depend on the order of the factors. -/
private theorem isReduced_tensorProduct_comm {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (h : IsReduced (S ⊗[R] T)) : IsReduced (T ⊗[R] S) :=
  isReduced_of_injective (TensorProduct.comm R T S).toRingEquiv (RingEquiv.injective _)

/-- **Definition 030S is Mathlib's `Algebra.IsGeometricallyReduced`.** A `k`-algebra `S` over a
field `k` is geometrically reduced in Mathlib's sense — `AlgebraicClosure k ⊗[k] S` is reduced — if
and only if `S ⊗[k] K` is reduced for *every* field extension `K/k`, which is the source's
definition. -/
theorem isGeometricallyReduced_iff_forall_isReduced_tensorProduct (k S : Type u) [Field k]
    [CommRing S] [Algebra k S] :
    IsGeometricallyReduced k S ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsReduced (S ⊗[k] K) := by
  refine ⟨fun _ K _ _ => ?_, fun h => ?_⟩
  · exact isReduced_tensorProduct_comm (inferInstance : IsReduced (K ⊗[k] S))
  · rw [isGeometricallyReduced_field_iff]
    exact isReduced_tensorProduct_comm (h _)

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

section ResidueField

variable {p : Ideal A} [p.IsPrime]

/-- **A field over `A` with kernel `p` is a field extension of `κ(p)`.** The structure map of a
field `K` over `A` whose kernel is `p` factors through the injection `A ⧸ p ↪ K`, and `K` being a
field that injection extends to the fraction field `κ(p)` of `A ⧸ p`. -/
noncomputable def residueFieldLiftOfKerEq {K : Type u} [Field K] [Algebra A K]
    (hker : RingHom.ker (algebraMap A K) = p) : p.ResidueField →+* K :=
  IsFractionRing.lift (A := A ⧸ p) (K := p.ResidueField) (L := K)
    (g := Ideal.Quotient.lift p (algebraMap A K) fun _ ha => hker.ge ha)
    (by rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, hker,
      Ideal.map_quotient_self])

/-- `Algebra.residueFieldLiftOfKerEq` is a map of algebras over `A`: it sends the image of `a : A`
in `κ(p)` to the image of `a` in `K`. -/
theorem residueFieldLiftOfKerEq_algebraMap {K : Type u} [Field K] [Algebra A K]
    (hker : RingHom.ker (algebraMap A K) = p) (a : A) :
    residueFieldLiftOfKerEq hker (algebraMap A p.ResidueField a) = algebraMap A K a := by
  rw [← Ideal.algebraMap_quotient_residueField_mk, residueFieldLiftOfKerEq,
    IsFractionRing.lift_algebraMap]
  exact Ideal.Quotient.lift_mk _ _ _

/-- **A field extension of `κ(p)` is a field over `A` with kernel `p`.** The converse direction to
`Algebra.residueFieldLiftOfKerEq`: if the structure map of a field `K` over `A` factors through
`κ(p)`, its kernel is `p`, because `κ(p) → K` is injective and `A → κ(p)` has kernel `p`. -/
theorem ker_algebraMap_of_isScalarTower_residueField (K : Type u) [Field K] [Algebra A K]
    [Algebra p.ResidueField K] [IsScalarTower A p.ResidueField K] :
    RingHom.ker (algebraMap A K) = p := by
  have hinj : RingHom.ker (algebraMap p.ResidueField K) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective (algebraMap p.ResidueField K))
  rw [IsScalarTower.algebraMap_eq A p.ResidueField K, ← RingHom.comap_ker, hinj,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- An algebraic closure of `κ(p)` is a field over `A` whose structure map has kernel `p`, so it is
one of the fields quantified over in `Algebra.fibreLocus` at `p`. -/
theorem ker_algebraMap_algebraicClosure_residueField :
    RingHom.ker (algebraMap A (AlgebraicClosure p.ResidueField)) = p :=
  ker_algebraMap_of_isScalarTower_residueField _

/-- **The fibre at `p` is a base change of the fibre at `κ(p)`.** For a field `K` over `A` whose
structure map factors through `κ(p)`, the ring `C ⊗[A] K` is the base change of the single
`κ(p)`-algebra `κ(p) ⊗[A] C` along `κ(p) → K`. -/
noncomputable def fibreResidueFieldEquiv (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (p : Ideal A) [p.IsPrime] (K : Type u) [Field K] [Algebra A K] [Algebra p.ResidueField K]
    [IsScalarTower A p.ResidueField K] :
    C ⊗[A] K ≃+* (p.ResidueField ⊗[A] C) ⊗[p.ResidueField] K :=
  ((TensorProduct.comm A C K).toRingEquiv.trans
      (TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K C).symm.toRingEquiv).trans
    (TensorProduct.comm p.ResidueField K (p.ResidueField ⊗[A] C)).toRingEquiv

end ResidueField

/-- **A fibre locus is governed by one algebra per point.** Let `P` be a property of rings
invariant under ring isomorphism. A prime `p` of `A` lies in `Algebra.fibreLocus A C P` if and
only if `P ((κ(p) ⊗[A] C) ⊗[κ(p)] K)` holds for every field extension `K/κ(p)`. -/
theorem mem_fibreLocus_iff_forall_residueFieldExtension
    {P : ∀ (R : Type u) [CommRing R], Prop}
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (p : PrimeSpectrum A) :
    p ∈ fibreLocus A C P ↔
      ∀ (K : Type u) [Field K] [Algebra p.asIdeal.ResidueField K],
        P ((p.asIdeal.ResidueField ⊗[A] C) ⊗[p.asIdeal.ResidueField] K) := by
  have := p.isPrime
  refine ⟨fun h K _ _ => ?_, fun h K _ _ hker => ?_⟩
  · let _ : Algebra A K := ((algebraMap p.asIdeal.ResidueField K).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
    have : IsScalarTower A p.asIdeal.ResidueField K := .of_algebraMap_eq' rfl
    exact (hP _ _ (fibreResidueFieldEquiv A C p.asIdeal K)).mp
      (h K (ker_algebraMap_of_isScalarTower_residueField K))
  · let _ : Algebra p.asIdeal.ResidueField K := (residueFieldLiftOfKerEq hker).toAlgebra
    have : IsScalarTower A p.asIdeal.ResidueField K :=
      .of_algebraMap_eq fun a => (residueFieldLiftOfKerEq_algebraMap hker a).symm
    exact (hP _ _ (fibreResidueFieldEquiv A C p.asIdeal K)).mpr (h K)

/-- **The affine, fibrewise case of Stacks 0384.** A prime `p` lies in the geometrically reduced
fibre locus of `C` — that is, `C ⊗[A] K` is reduced for every field `K` over `A` with
`ker (A → K) = p` — if and only if the single fibre `κ(p) ⊗[A] C` is geometrically reduced over
`κ(p)` in Mathlib's sense. -/
theorem mem_geometricallyReducedFibreLocus_iff (p : PrimeSpectrum A) :
    p ∈ geometricallyReducedFibreLocus A C ↔
      IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] C) := by
  have := p.isPrime
  rw [geometricallyReducedFibreLocus_eq_fibreLocus,
    isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  exact mem_fibreLocus_iff_forall_residueFieldExtension (fun _ _ _ _ e => isReduced_congr e) p

/-- **The geometrically reduced fibre locus is cut out by one ring per point.** A prime `p` lies in
the geometrically reduced fibre locus of `C` if and only if `C ⊗[A] AlgebraicClosure κ(p)` is
reduced. -/
theorem mem_geometricallyReducedFibreLocus_iff_isReduced_algebraicClosure (p : PrimeSpectrum A) :
    p ∈ geometricallyReducedFibreLocus A C ↔
      IsReduced (C ⊗[A] AlgebraicClosure p.asIdeal.ResidueField) := by
  have := p.isPrime
  refine ⟨fun h => h _ ker_algebraMap_algebraicClosure_residueField, fun h => ?_⟩
  rw [mem_geometricallyReducedFibreLocus_iff, isGeometricallyReduced_field_iff]
  exact isReduced_tensorProduct_comm
    ((isReduced_congr (fibreResidueFieldEquiv A C p.asIdeal _)).mp h)

/-- **The affine, fibrewise collapse of the quantifier for geometric irreducibility.** A prime `p`
lies in the geometrically irreducible fibre locus of `C` — that is, `Spec (C ⊗[A] K)` is
irreducible for every field `K` over `A` with `ker (A → K) = p` — if and only if the single fibre
`κ(p) ⊗[A] C` is geometrically irreducible over `κ(p)`. -/
theorem mem_geometricallyIrreducibleFibreLocus_iff (p : PrimeSpectrum A) :
    p ∈ geometricallyIrreducibleFibreLocus A C ↔
      IsGeometricallyIrreducible p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] C) := by
  have := p.isPrime
  rw [geometricallyIrreducibleFibreLocus_eq_fibreLocus,
    isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  exact mem_fibreLocus_iff_forall_residueFieldExtension
    (fun _ _ _ _ e => irreducibleSpace_primeSpectrum_congr e) p

/-- `Algebra.mem_geometricallyReducedFibreLocus_iff_isReduced_algebraicClosure` as an equality of
subsets of `Spec A`: the geometrically reduced fibre locus is the set of primes `p` at which
`C ⊗[A] AlgebraicClosure κ(p)` is reduced. -/
theorem geometricallyReducedFibreLocus_eq_setOf (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] :
    geometricallyReducedFibreLocus A C =
      {p : PrimeSpectrum A | IsReduced (C ⊗[A] AlgebraicClosure p.asIdeal.ResidueField)} :=
  Set.ext fun p => mem_geometricallyReducedFibreLocus_iff_isReduced_algebraicClosure p

/-- `Algebra.mem_geometricallyIrreducibleFibreLocus_iff` as an equality of subsets of `Spec A`: the
geometrically irreducible fibre locus is the set of primes `p` at which `κ(p) ⊗[A] C` is
geometrically irreducible over `κ(p)`. -/
theorem geometricallyIrreducibleFibreLocus_eq_setOf (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] :
    geometricallyIrreducibleFibreLocus A C =
      {p : PrimeSpectrum A |
        IsGeometricallyIrreducible p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] C)} :=
  Set.ext fun p => mem_geometricallyIrreducibleFibreLocus_iff p

end Algebra

end
