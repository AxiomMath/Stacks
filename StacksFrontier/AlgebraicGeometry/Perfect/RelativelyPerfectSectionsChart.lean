module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsUnbounded
public import StacksFrontier.Homology.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative perfectness of the derived sections on an affine chart

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation, let
`U ⊆ X` and `V ⊆ S` be affine opens with `U ⊆ f⁻¹(V)`, and let `E` be an object of `D(𝒪_X)`.
Clauses (2) and (3) of Stacks 0DI2 assert that the complex of `Γ(X, U)`-modules `RΓ(U, E)` is
`Γ(S, V)`-perfect in the sense of Stacks 0DHS.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`: the module-side condition of clauses
  (2) and (3) of Stacks 0DI2 — the complex `RΓ(U, E)` is `Γ(S, V)`-perfect, read at the canonical
  derived tensoring datum of Stacks 0BYI.

## Main results

* `AlgebraicGeometry.Scheme.Hom.moduleFlat_appLE` and
  `AlgebraicGeometry.Scheme.Hom.algebraFinitePresentation_appLE`: the chart ring map of a flat
  morphism locally of finite presentation is flat and of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.exists_affineCovering_sectionsRelativelyPerfect`: the implication
  (2) ⟹ (3) of Stacks 0DI2, at the full module-side condition.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_of_forall_sectionsRelativelyPerfect`: clause (2)
  of Stacks 0DI2 implies the pseudo-coherence conjunct of clause (1).

## Implementation notes

`PseudoCoherence.IsRelativelyPerfect` takes `Module.Flat` and `Algebra.FinitePresentation` as
instance arguments, so `Γ(S, V)`-perfectness of a complex of `Γ(X, U)`-modules is stated for a
`Γ(S, V)`-algebra structure on `Γ(X, U)` which is flat and of finite presentation. The chart ring
map `f.appLE V U e` of a flat morphism locally of finite presentation has both properties.

Finite Tor dimension is measured against `PseudoCoherence.canonicalDerivedTensoringDatum`, the
canonical derived tensor product of Stacks 0BYI, against which it agrees with the finite Tor
dimension of Stacks 0652 by
`PseudoCoherence.hasFiniteTorDimension_canonicalDerivedTensoringDatum_iff`.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [The Stacks Project, Definition 15.85.1 (0DHS)](https://stacks.math.columbia.edu/tag/0DHS)
* [The Stacks Project, Lemma 36.10.4 (0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The chart ring map of a flat morphism is flat.** For `f : X ⟶ S` flat, an affine open `V ⊆ S`
and an affine open `U ⊆ f⁻¹(V)`, the sections `Γ(X, U)` form a flat `Γ(S, V)`-module, for any
algebra structure whose structure map is `f.appLE V U e`. -/
@[ega "III 1.4.15.5" "partial"]
public theorem moduleFlat_appLE [Flat f] {V : S.Opens} {U : X.Opens} (hV : IsAffineOpen V)
    (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(X, U)]
    (h : algebraMap Γ(S, V) Γ(X, U) = (f.appLE V U e).hom) :
    Module.Flat Γ(S, V) Γ(X, U) := by
  rw [← RingHom.flat_algebraMap_iff, h]
  exact AlgebraicGeometry.Flat.flat_appLE f hV hU e

/-- **The chart ring map of a morphism locally of finite presentation is of finite presentation.**
For `f : X ⟶ S` locally of finite presentation, an affine open `V ⊆ S` and an affine open
`U ⊆ f⁻¹(V)`, the algebra `Γ(X, U)` is of finite presentation over `Γ(S, V)`, for any algebra
structure whose structure map is `f.appLE V U e`. -/
public theorem algebraFinitePresentation_appLE [LocallyOfFinitePresentation f] {V : S.Opens}
    {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    [Algebra Γ(S, V) Γ(X, U)] (h : algebraMap Γ(S, V) Γ(X, U) = (f.appLE V U e).hom) :
    Algebra.FinitePresentation Γ(S, V) Γ(X, U) := by
  rw [← RingHom.finitePresentation_algebraMap, h]
  exact AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE f hV hU e

/-- **The module-side condition of clauses (2) and (3) of Stacks 0DI2.** For `f : X ⟶ S` flat and
locally of finite presentation, an affine open `V ⊆ S`, an affine open `U ⊆ f⁻¹(V)` and an object
`E` of `D(𝒪_X)`, this is the assertion that the complex of `Γ(X, U)`-modules `RΓ(U, E)` is
`Γ(S, V)`-perfect in the sense of Stacks 0DHS: pseudo-coherent over `Γ(X, U)` and, read over
`Γ(S, V)`, of finite Tor dimension.

The `Γ(S, V)`-algebra structure on `Γ(X, U)` is the one given by the chart ring map
`f.appLE V U e`, and finite Tor dimension is measured against the canonical derived tensor product
of Stacks 0BYI. -/
public def SectionsRelativelyPerfect [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules) {V : S.Opens} {U : X.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU e rfl
  letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hU e rfl
  PseudoCoherence.IsRelativelyPerfect.{u, u, u}
    (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).tensor
    (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).comparison
    (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).isLeftDerived
    ((derivedSectionsUnbounded X U).obj E)

/-- The pseudo-coherence conjunct of `Γ(S, V)`-perfectness of `RΓ(U, E)`. -/
public theorem SectionsRelativelyPerfect.isPseudoCoherent [Flat f]
    [LocallyOfFinitePresentation f] {E : DerivedCategory X.Modules} {V : S.Opens} {U : X.Opens}
    {hV : IsAffineOpen V} {hU : IsAffineOpen U} {e : U ≤ f ⁻¹ᵁ V}
    (h : SectionsRelativelyPerfect f E hV hU e) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj E) := h.1

/-- **Clause (2) of Stacks 0DI2 implies the pseudo-coherence conjunct of clause (1).** If
`RΓ(U, E)` is `Γ(S, V)`-perfect for every affine open `U ⊆ X` mapping into an affine open `V ⊆ S`,
then `E` is a pseudo-coherent object of `D(𝒪_X)`. -/
public theorem isPseudoCoherent_of_forall_sectionsRelativelyPerfect [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), SectionsRelativelyPerfect f E hV hU e) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E := by
  have h2 : ∀ (U : X.Opens), IsAffineOpen U → ∀ (V : S.Opens), IsAffineOpen V → U ≤ f ⁻¹ᵁ V →
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj E) :=
    fun U hU V hV e => (h U hU V hV e).isPseudoCoherent
  exact (pseudoCoherent_derivedSections_tfae f E hE _ (by simp) _ (by simp)).mp h2

/-- **Stacks 0DI2**, the implication (2) ⟹ (3): if `RΓ(U, E)` is `Γ(S, V)`-perfect for every affine
open `U ⊆ X` mapping into an affine open `V ⊆ S`, then there are an affine open covering of `S`
and, over each of its members `V`, an affine open covering of `f⁻¹(V)` on whose members the
condition holds. -/
@[stacks 0DI2 "the implication (2) implies (3), at the source's own module-side condition and \
for BOTH of its conjuncts at once: if the complex of sections over every affine open U of X \
mapping into an affine open V of S is O_S(V)-perfect, then there are an affine open covering of \
S and, over each member V, an affine open covering of the preimage of V on whose members the \
same condition holds. The whole three-way equivalence is \
AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae"]
public theorem exists_affineCovering_sectionsRelativelyPerfect [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), SectionsRelativelyPerfect f E hV hU e) :
    ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens) (hle : ∀ j, (U j).1 ≤ f ⁻¹ᵁ (V i).1),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, SectionsRelativelyPerfect f E (V i).2 (U j).2 (hle j) :=
  ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V =>
    ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U => U.1, fun U => U.2,
      iSup_affineOpens_subtype_eq _, fun U => h _ U.1.2 _ V.2 U.2⟩⟩

end AlgebraicGeometry.Scheme.Hom

end
