module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.AffineCoverOfOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Affine charts over a ring, presented by a polynomial algebra

Let `R` be a ring, write `S = Spec R`, and let `f : X ⟶ S` be a morphism of schemes. An open `U`
of `X` has a ring of sections `Γ(X, U)`, and `f` makes it an `R`-algebra: the structure map is
`AlgebraicGeometry.Scheme.Hom.chartHom`, the composite of the comparison `R ≅ Γ(S, ⊤)` with
`f.appLE ⊤ U`.

This module proves that for `U` affine the structure map inherits the three properties of `f` that
the fibrewise criterion of Stacks 0DJH consumes — finite type, finite presentation and flatness —
and that, `f` being locally of finite type, `Γ(X, U)` is then a quotient of a polynomial algebra
`R[x_1, …, x_d]`. Combined with quasi-compactness of `X`, which universal closedness of `f`
supplies, this is the covering step of the proof of Stacks 0DJZ: *choose a finite affine open
covering `X = U_1 ∪ … ∪ U_n`, with each `U_i` closed in an affine space `𝐀^{d_i}_S`*.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.chartHom`: the structure map `R ⟶ Γ(X, U)` induced by `f`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finiteType_chartHom`,
  `AlgebraicGeometry.Scheme.Hom.finitePresentation_chartHom`,
  `AlgebraicGeometry.Scheme.Hom.flat_chartHom`: the structure map of an affine chart is of finite
  type, of finite presentation, and flat, when `f` is.
* `AlgebraicGeometry.Scheme.Hom.exists_mvPolynomial_surjective_chartHom`: an affine chart of a
  morphism locally of finite type is a quotient of `R[x_1, …, x_d]`, compatibly with the structure
  map.
* `AlgebraicGeometry.Scheme.Hom.exists_finset_affineOpens_mvPolynomial_surjective_chartHom`:
  finitely many affine opens cover a quasi-compact `X`, and the sections over each are a quotient
  of a polynomial algebra over `R` in finitely many variables.
* `exists_finset_affineOpens_mvPolynomial_surjective_chartHom_of_universallyClosed`, in the same
  namespace: **the covering step of Stacks 0DJZ**, the previous statement with quasi-compactness
  of `X` supplied by universal closedness of `f`.

## Implementation notes

The presentation is exported as a **ring** homomorphism `MvPolynomial (Fin d) R →+* Γ(X, U)`
together with the equation `ψ.comp MvPolynomial.C = chartHom f U`, rather than as an
`R`-algebra homomorphism. The two carry the same information, and the ring form needs no `Algebra`
instance on `Γ(X, U)` to be stated: a consumer that has already chosen one — the fibrewise
criterion `StacksDraft.PseudoCoherence.hasTorAmplitude_localization_of_isZero_homology_fibre`
asks for an `AlgHom` over an `[Algebra R A]` instance it does not fix — recovers the algebra form
from the equation, for whichever instance it is using. The companion
`AlgebraicGeometry.Scheme.Hom.exists_mvPolynomial_surjective_chartHom_algHom` does exactly that,
taking the instance and its identification with `chartHom f U` as hypotheses.

Quasi-compactness of `X` is deduced from universal closedness of `f` rather than from `IsProper f`
for two reasons. Mathlib's `AlgebraicGeometry.IsProper` is `IsSeparated ⊓ UniversallyClosed ⊓
LocallyOfFiniteType` and does **not** carry `QuasiCompact` as a field, so properness reaches
quasi-compactness through the universally-closed instance anyway; and universal closedness
together with local finite type is all the source's proof of this step uses, which is also the
hypothesis the sibling module
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonSpecialization` takes for the
specialization step.

Nothing here mentions a derived category, an object of `D(𝒪_X)`, a Tor amplitude, or relative
perfectness; see the References for where those enter.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Lemma 15.85.9 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 29.21.2 (01T8)](https://stacks.math.columbia.edu/tag/01T8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- **The structure map of a chart.** For `f : X ⟶ Spec R` and an open `U` of `X`, the ring
homomorphism `R ⟶ Γ(X, U)` obtained by composing the comparison `R ≅ Γ(Spec R, ⊤)` with the map
`Γ(Spec R, ⊤) ⟶ Γ(X, U)` that `f` induces. -/
public def chartHom (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- A property of ring homomorphisms respecting isomorphisms holds for `chartHom f U` as soon as it
holds for `f.appLE ⊤ U`. -/
private theorem chartHom_of_respectsIso {P : ∀ {A B : Type u} [CommRing A] [CommRing B],
    (A →+* B) → Prop} (hP : RingHom.RespectsIso P) {U : X.Opens}
    (h : P (f.appLE ⊤ U le_top).hom) : P (chartHom f U) :=
  (hP.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv (f.appLE ⊤ U le_top)).mpr h

/-- **An affine chart of a morphism locally of finite type is of finite type over the base.** -/
public theorem finiteType_chartHom [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    (chartHom f U).FiniteType :=
  chartHom_of_respectsIso f RingHom.finiteType_respectsIso
    (f.finiteType_appLE (isAffineOpen_top _) hU le_top)

/-- **An affine chart of a morphism locally of finite presentation is of finite presentation over
the base.** -/
public theorem finitePresentation_chartHom [LocallyOfFinitePresentation f] {U : X.Opens}
    (hU : IsAffineOpen U) : (chartHom f U).FinitePresentation :=
  chartHom_of_respectsIso f RingHom.finitePresentation_respectsIso
    (f.finitePresentation_appLE (isAffineOpen_top _) hU le_top)

/-- **An affine chart of a flat morphism is flat over the base.** -/
public theorem flat_chartHom [Flat f] {U : X.Opens} (hU : IsAffineOpen U) :
    (chartHom f U).Flat :=
  chartHom_of_respectsIso f RingHom.Flat.respectsIso (f.flat_appLE (isAffineOpen_top _) hU le_top)

/-- **An affine chart of a morphism locally of finite type is a quotient of a polynomial algebra.**
For `f : X ⟶ Spec R` locally of finite type and `U` an affine open of `X`, there are a number `d`
of variables and a surjection `R[x_1, …, x_d] ⟶ Γ(X, U)` of rings carrying the constants to the
structure map `chartHom f U`.

This is the `(d, presentation, hpresentation)` triple that the fibrewise criterion of Stacks 0DJH,
`StacksDraft.PseudoCoherence.hasTorAmplitude_localization_of_isZero_homology_fibre`, consumes. -/
@[ega "IV 1.5.7" "more general"]
public theorem exists_mvPolynomial_surjective_chartHom [LocallyOfFiniteType f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) R →+* Γ(X, U)),
      Function.Surjective ψ ∧ ψ.comp MvPolynomial.C = chartHom f U := by
  let : Algebra R Γ(X, U) := (chartHom f U).toAlgebra
  have hft : Algebra.FiniteType R Γ(X, U) := finiteType_chartHom f hU
  obtain ⟨d, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  refine ⟨d, ψ.toRingHom, hψ, RingHom.ext fun r => ?_⟩
  simp [RingHom.algebraMap_toAlgebra]

/-- **The polynomial presentation of an affine chart, as an algebra homomorphism.** The previous
statement for a consumer that has already chosen the `R`-algebra structure on `Γ(X, U)`, and knows
it to be the one `f` induces. -/
public theorem exists_mvPolynomial_surjective_chartHom_algHom [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) [Algebra R Γ(X, U)]
    (halg : algebraMap R Γ(X, U) = chartHom f U) :
    ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) R →ₐ[R] Γ(X, U)), Function.Surjective ψ := by
  obtain ⟨d, ψ, hsurj, hcomp⟩ := exists_mvPolynomial_surjective_chartHom f hU
  refine ⟨d, ⟨ψ, fun r => ?_⟩, hsurj⟩
  rw [halg, ← hcomp]
  simp [MvPolynomial.algebraMap_eq]

/-- **A finite affine covering whose members are presented by polynomial algebras.** Let `R` be a
ring and let `f : X ⟶ Spec R` be locally of finite type with `X` quasi-compact. Then finitely many
affine opens cover `X`, and over each the sections are a quotient of a polynomial algebra
`R[x_1, …, x_d]` in finitely many variables, compatibly with the structure map that `f` induces. -/
public theorem exists_finset_affineOpens_mvPolynomial_surjective_chartHom
    [LocallyOfFiniteType f] [CompactSpace X] :
    ∃ s : Finset X.affineOpens, (⨆ V ∈ s, (V : X.Opens)) = ⊤ ∧
      ∀ V ∈ s, ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) R →+* Γ(X, V.1)),
        Function.Surjective ψ ∧ ψ.comp MvPolynomial.C = chartHom f V.1 := by
  obtain ⟨s, hs⟩ := exists_finset_affineOpens_sup_eq_top (X := X) ⊥
  exact ⟨s, by simpa using hs, fun V _ => exists_mvPolynomial_surjective_chartHom f V.2⟩

/-- **The covering step of Stacks 0DJZ.** Let `R` be a ring and let `f : X ⟶ Spec R` be
universally closed and locally of finite type. Then finitely many affine opens cover `X`, and over
each the sections are a quotient of a polynomial algebra `R[x_1, …, x_d]` in finitely many
variables, compatibly with the structure map that `f` induces.

The source's proof of Stacks 0DJZ opens with this: *choose a finite affine open covering
`X = U_1 ∪ … ∪ U_n`; for each `i` we can choose a closed immersion `U_i → 𝐀^{d_i}_S`*. For an
affine `U_i`, giving a closed immersion into `𝐀^{d_i}_S` over `S` is the same as giving a
surjection `R[x_1, …, x_{d_i}] ⟶ Γ(X, U_i)` of `R`-algebras, and the surjection is the form the
fibrewise criterion of Stacks 0DJH consumes, so it is the form exported here.

Quasi-compactness of `X` comes from universal closedness of `f`: the import
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed` carries an instance making a universally
closed morphism quasi-compact, and `Spec R` is quasi-compact, so
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` applies. Properness is not asked
for; universal closedness and local finite type are all the source's proof of this step uses, and
they are also the hypotheses under which the sibling module
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonSpecialization` proves the
specialization step. -/
@[stacks 0DJZ "the covering step with which the proof opens: for `f : X ⟶ Spec R` \
universally closed and locally of finite type, finitely many affine opens cover `X` and the \
sections over each are a quotient of a polynomial algebra over `R` in finitely many variables",
  ega "I 6.6.3" "special case",
  ega "IV 1.5.1" "(a) ⇒ (c), special case"]
public theorem exists_finset_affineOpens_mvPolynomial_surjective_chartHom_of_universallyClosed
    [LocallyOfFiniteType f] [UniversallyClosed f] :
    ∃ s : Finset X.affineOpens, (⨆ V ∈ s, (V : X.Opens)) = ⊤ ∧
      ∀ V ∈ s, ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) R →+* Γ(X, V.1)),
        Function.Surjective ψ ∧ ψ.comp MvPolynomial.C = chartHom f V.1 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact exists_finset_affineOpens_mvPolynomial_surjective_chartHom f

end AlgebraicGeometry.Scheme.Hom

end
