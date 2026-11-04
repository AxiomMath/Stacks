module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyIrreducibleModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IntegralModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelOverField

/-!
# The affine model of Stacks Tag 0559 as a scheme over a domain

The output of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IntegralModel`, packaged as the
input of `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel`, which is Steps D,
E and F of Tag 0559 assembled over a domain base. That consumer asks for a domain `S` with an
injective ring map from the base, locally of finite type and geometrically irreducible as a
morphism of spectra, whose fraction field is the function field; the hypersurface
`MvPolynomial (Fin (n + 1)) A' ⧸ (P)` has all four properties once `P` is monic in the last
variable and stays irreducible under every specialization of `A'` to a field.

The base is a domain `A'` between the original domain `A` and its fraction field `K`: Step F only
gives geometric irreducibility after shrinking `Spec A` to a principal open, and the model has to
be base changed to the corresponding localization. All four conclusions are stable under that
base change — monicity because `Polynomial.Monic.map` and
`MvPolynomial.map_finLastEquiv` commute with it, and the kernel over `K` because it does not move
at all — so the statement is formulated for an arbitrary such `A'` and `A` is only the ring the
polynomial is defined over.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_specMap_mvPolynomialQuotient_fin`: Step F of
  Tag 0559 with the variables indexed by a type of `Type 0`, in particular by `Fin n`, over a
  coefficient ring in an arbitrary universe.
* `AlgebraicGeometry.specModel_of_monic`: **the four properties of the affine model**, over a
  domain `A'` with fraction field `K`.
* `Algebra.exists_away_monic_model_of_isDomain_tensor`: the model, with the element of `A` whose
  principal open the base has to be shrunk to for Step F.

## Implementation notes

`AlgebraicGeometry.geometricallyIrreducible_specMap_mvPolynomialQuotient` is stated for a ring
and an index type in the same universe, which `Fin n` cannot satisfy over a coefficient ring
outside `Type 0`; the variant here is its statement at an index type in `Type 0`, with the same
three-line proof, and it exists only to make the universes fit.

Injectivity of the structure map of the model, which the consumer asks for separately, is read
off the embedding into `L`: the model embeds in `L` and the composite is the inclusion of `A'`
into its fraction field followed by `K ⟶ L`.

No Stacks tag is attached: Steps D, E and F are not themselves tags of the source, and Tag 0557
is carried by `MvPolynomial.exists_away_irreducible_map`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps D, E and F of the
  first proof
* [Stacks Project, Tag 0557](https://stacks.math.columbia.edu/tag/0557)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

open MvPolynomial

universe u v w

namespace AlgebraicGeometry

/-- An ideal spanned by the image of `P` in `K[xᵢ]` is also spanned by its image through `A'`. -/
private theorem eq_span_map_map_of_eq_span_map {A K : Type*} [CommRing A] [CommRing K]
    (A' : Type*) [CommRing A'] [Algebra A A'] [Algebra A K] [Algebra A' K]
    [IsScalarTower A A' K] {σ : Type*} {P : MvPolynomial σ A} {I : Ideal (MvPolynomial σ K)}
    (h : I = Ideal.span {P.map (algebraMap A K)}) :
    I = Ideal.span {(P.map (algebraMap A A')).map (algebraMap A' K)} := by
  rw [h, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Step F of Stacks Tag 0559** for variables indexed by a type in `Type 0`. If the
coefficientwise image of `P : MvPolynomial ι R` in `κ[xᵢ]` is irreducible for every homomorphism
from `R` to a field `κ`, then the hypersurface `Spec (R[xᵢ] ⧸ (P))` is geometrically irreducible
over `Spec R`.

This is `AlgebraicGeometry.geometricallyIrreducible_specMap_mvPolynomialQuotient`, whose index
type is required to lie in the same universe as the coefficient ring; `Fin n` lies in `Type 0`,
and `MvPolynomial (Fin n) R` still lies in the universe of `R`. -/
theorem geometricallyIrreducible_specMap_mvPolynomialQuotient_fin {R : Type u} [CommRing R]
    {ι : Type} (P : MvPolynomial ι R)
    (hP : ∀ (κ : Type u) [Field κ] (φ : R →+* κ), Irreducible (P.map φ)) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial ι R ⧸ Ideal.span {P})))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun κ _ _ ↦ ?_⟩
  have : IsDomain ((MvPolynomial ι R ⧸ Ideal.span {P}) ⊗[R] κ) :=
    MvPolynomial.isDomain_quotientSpan_tensor R ι P (hP κ (algebraMap R κ))
  exact (pullbackSpecIso R (MvPolynomial ι R ⧸ Ideal.span {P}) κ).hom.homeomorph
    |>.irreducibleSpace_iff.mpr inferInstance

/-- **The affine model of Stacks Tag 0559 over a domain base.** Let `A'` be a domain with
fraction field `K`, let `L` be a field extension of `K` generated by a family
`v : Fin (n + 1) → L`, let `A` be a domain with the same fraction field mapping to `A'`, and let
`P : MvPolynomial (Fin (n + 1)) A` be monic in the last variable, with image in `K[xᵢ]`
generating the kernel of evaluation at `v`, and remaining irreducible under every specialization
of `A'` to a field. Then the base change `B'` of the hypersurface `A[xᵢ] ⧸ (P)` to `A'` is a
domain, the structure map `A' ⟶ B'` is injective, and `Spec B' ⟶ Spec A'` is locally of finite
type and geometrically irreducible; and `L` is a field of fractions of `B'`.

These are exactly the hypotheses on the model in
`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel`. -/
theorem specModel_of_monic {A : Type u} [CommRing A] [IsDomain A] {K : Type u} [Field K]
    [Algebra A K] [IsFractionRing A K] {L : Type v} [Field L] [Algebra K L] (A' : Type u)
    [CommRing A'] [IsDomain A'] [Algebra A A'] [Algebra A' K] [IsScalarTower A A' K]
    [IsFractionRing A' K] {n : ℕ} (v : Fin (n + 1) → L)
    (hv : IntermediateField.adjoin K (Set.range v) = ⊤)
    {P : MvPolynomial (Fin (n + 1)) A} (hmonic : (finLastEquiv A n P).Monic)
    (hker : RingHom.ker (aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom =
      Ideal.span {P.map (algebraMap A K)})
    (hirr : ∀ (κ : Type u) [Field κ] (φ : A' →+* κ),
      Irreducible ((P.map (algebraMap A A')).map φ)) :
    IsDomain (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')}) ∧
      Function.Injective (algebraMap A'
        (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')})) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A'
        (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')})))) ∧
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap A'
        (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')})))) ∧
      ∀ ψ : (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')}) →+* L,
        ψ.comp (Ideal.Quotient.mk (Ideal.span {P.map (algebraMap A A')})) =
            (aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom.comp
              (MvPolynomial.map (algebraMap A' K)) →
          letI := ψ.toAlgebra
          IsFractionRing
            (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')}) L := by
  -- Monicity and the kernel over `K` survive the base change to `A'`.
  have hmonic' : (finLastEquiv A' n (P.map (algebraMap A A'))).Monic := by
    rw [MvPolynomial.map_finLastEquiv]
    exact hmonic.map _
  have hker' := eq_span_map_map_of_eq_span_map A' hker
  obtain ⟨hdom, hfrac⟩ :=
    MvPolynomial.isDomain_and_isFractionRing_quotient_of_monic v hv hmonic' hker'
  refine ⟨hdom, ?_, locallyOfFiniteType_specMap_mvPolynomialQuotient A' (n + 1) _,
    geometricallyIrreducible_specMap_mvPolynomialQuotient_fin _ hirr, hfrac⟩
  -- Injectivity of the structure map, read off the embedding of the model into `L`.
  have hkerA : RingHom.ker ((aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom.comp
      (MvPolynomial.map (algebraMap A' K))) =
      Ideal.span {P.map (algebraMap A A')} :=
    MvPolynomial.ker_comp_map_eq_span_of_monic (algebraMap A' K)
      (IsFractionRing.injective A' K) _ hmonic' hker'
  set ψ₀ : (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')}) →+* L :=
    Ideal.Quotient.lift (Ideal.span {P.map (algebraMap A A')})
      ((aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom.comp
        (MvPolynomial.map (algebraMap A' K)))
      (fun x hx ↦ by rw [← hkerA, RingHom.mem_ker] at hx; exact hx) with hψ₀
  have hψ₀inj : Function.Injective ψ₀ :=
    MvPolynomial.injective_of_comp_quotientMk_eq ψ₀ _ (RingHom.ext fun _ ↦ rfl) hkerA.symm
  have hcomp : ∀ x : A', ψ₀ (algebraMap A'
      (MvPolynomial (Fin (n + 1)) A' ⧸ Ideal.span {P.map (algebraMap A A')}) x) =
      algebraMap K L (algebraMap A' K x) := by
    intro x
    show ψ₀ (Ideal.Quotient.mk _ (C x)) = _
    simp [hψ₀]
  intro x y hxy
  refine IsFractionRing.injective A' K ((algebraMap K L).injective ?_)
  rw [← hcomp, ← hcomp, hxy]

end AlgebraicGeometry

namespace Algebra

/-- **The monic integral model of Stacks Tag 0559, with the shrinking element.** Let `A` be a
domain with fraction field `K`, let `L` be a finitely generated field extension of `K` which is
geometrically reduced over `K`, and let `K̄` be an algebraically closed field extension of `K`
such that `L ⊗[K] K̄` is a domain. Then there is a nonzero `a : A`, a family
`v : Fin (n + 1) → L` generating `L` over `K` and a `P : MvPolynomial (Fin (n + 1)) A`, monic in
the last variable, whose image in `K[xᵢ]` generates the kernel of evaluation at `v` and which
stays irreducible under every specialization of `A_a` to a field.

Combined with `AlgebraicGeometry.specModel_of_monic` over any domain between `A_a` and `K`, this
produces the affine model that Steps D, E and F of Tag 0559 consume. -/
theorem exists_away_monic_model_of_isDomain_tensor (A : Type u) [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type v) [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] [Algebra.IsGeometricallyReduced K L]
    (Kbar : Type w) [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar]
    (hL : IsDomain (L ⊗[K] Kbar)) :
    ∃ (a : A) (n : ℕ) (v : Fin (n + 1) → L) (P : MvPolynomial (Fin (n + 1)) A),
      a ≠ 0 ∧
      IntermediateField.adjoin K (Set.range v) = ⊤ ∧
      (finLastEquiv A n P).Monic ∧
      RingHom.ker (aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom =
          Ideal.span {P.map (algebraMap A K)} ∧
      ∀ (κ : Type u) [Field κ] (φ : Localization.Away a →+* κ),
        Irreducible ((P.map (algebraMap A (Localization.Away a))).map φ) := by
  obtain ⟨n, v, P, hadj, hmonic, hirr, hker, -, -⟩ :=
    Algebra.exists_integral_model_of_isDomain_tensor A K L Kbar hL
  obtain ⟨a, ha, haway⟩ := MvPolynomial.exists_away_irreducible_map A K Kbar (Fin (n + 1)) P hirr
  refine ⟨a, n, v, P, ha, hadj, hmonic, hker, fun κ _ φ ↦ ?_⟩
  rw [MvPolynomial.map_map]
  exact haway κ φ

end Algebra

namespace AlgebraicGeometry

/-- **The affine model of Stacks Tag 0559 over a principal open of the base.** Let `A` be a
domain with fraction field `K`, let `L` be a finitely generated field extension of `K` which is
geometrically reduced over `K`, and let `K̄` be an algebraically closed field extension of `K`
such that `L ⊗[K] K̄` is a domain. Then there are a nonzero `a : A`, a family
`v : Fin (n + 1) → L` generating `L` over `K`, the inclusion `ι` of `A_a` into `K`, and a
`P : MvPolynomial (Fin (n + 1)) A_a` whose image in `K[xᵢ]` generates the kernel of evaluation at
`v`, such that `B' = MvPolynomial (Fin (n + 1)) A_a ⧸ (P)` is a domain, receives `A_a`
injectively, and `Spec B' ⟶ Spec A_a` is locally of finite type and geometrically irreducible,
while `L` is a field of fractions of `B'`.

This is the model with all of the properties
`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel` asks of it; the base is the
principal open `D(a) ⊆ Spec A` to which Step F of the source shrinks. -/
theorem exists_away_specModel (A : Type u) [CommRing A] [IsDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] (L : Type v) [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] [Algebra.IsGeometricallyReduced K L] (Kbar : Type w) [Field Kbar]
    [Algebra K Kbar] [IsAlgClosed Kbar] (hL : IsDomain (L ⊗[K] Kbar)) :
    ∃ (a : A) (n : ℕ) (v : Fin (n + 1) → L) (ι : Localization.Away a →+* K)
      (P : MvPolynomial (Fin (n + 1)) (Localization.Away a)),
      a ≠ 0 ∧
      ι.comp (algebraMap A (Localization.Away a)) = algebraMap A K ∧
      IntermediateField.adjoin K (Set.range v) = ⊤ ∧
      RingHom.ker (aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom =
          Ideal.span {P.map ι} ∧
      IsDomain (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P}) ∧
      Function.Injective (algebraMap (Localization.Away a)
        (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P})) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away a)
        (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P})))) ∧
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away a)
        (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P})))) ∧
      ∀ ψ : (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P}) →+* L,
        ψ.comp (Ideal.Quotient.mk (Ideal.span {P})) =
            (aeval v : MvPolynomial (Fin (n + 1)) K →ₐ[K] L).toRingHom.comp
              (MvPolynomial.map ι) →
          letI := ψ.toAlgebra
          IsFractionRing
            (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P}) L := by
  obtain ⟨a, n, v, P, ha, hadj, hmonic, hker, hirr⟩ :=
    Algebra.exists_away_monic_model_of_isDomain_tensor A K L Kbar hL
  have hunit : IsUnit (algebraMap A K a) := by
    refine isUnit_iff_ne_zero.mpr ?_
    simpa [IsFractionRing.to_map_eq_zero_iff] using ha
  have : IsDomain (Localization.Away a) :=
    IsLocalization.Away.isDomain (S := Localization.Away a) (x := a) ha
  let : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a hunit).toAlgebra
  have : IsScalarTower A (Localization.Away a) K :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp a hunit).symm
  have : IsFractionRing (Localization.Away a) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers a)
      (Localization.Away a) K
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ :=
    specModel_of_monic (A := A) (K := K) (L := L) (Localization.Away a) v hadj hmonic hker hirr
  exact ⟨a, n, v, algebraMap (Localization.Away a) K,
    P.map (algebraMap A (Localization.Away a)), ha, IsLocalization.Away.lift_comp a hunit, hadj,
    eq_span_map_map_of_eq_span_map _ hker, h₁, h₂, h₃, h₄, h₅⟩

end AlgebraicGeometry

end
