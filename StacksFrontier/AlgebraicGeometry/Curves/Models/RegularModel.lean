module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular models of smooth curves

A *model* of a smooth curve `C` over the fraction field `K` of a discrete valuation ring `R` is
a flat finite-type scheme `X ⟶ Spec(R)` whose generic fibre `X_K` is `C`. The model is *regular*
when `X` is a regular scheme. This file packages that standing data as a structure and names its
two fibres: the generic fibre `X_K` over `K` and the special fibre `X_k` over the residue field.

Everything the chapter says about the geometry of a regular model — that the special fibre and
each of its irreducible components are effective Cartier divisors, the decomposition
`X_k = ∑ mᵢ Cᵢ`, and the intersection pairing — is stated relative to this one context.

## Main definitions

* `Stacks.Models.RegularModelSituation` — the standing data of a regular model.
* `Stacks.Models.RegularModelSituation.genericFiber` and
  `Stacks.Models.RegularModelSituation.specialFiber` — its two fibres, as the pullbacks of the
  model along `Spec(K) ⟶ Spec(R)` and `Spec(k) ⟶ Spec(R)`.

## Main results

There are no propositional results beyond the bundled situation: this file fixes the context
the chapter works in.

## Implementation notes

The residue field is allowed to be any chosen field identified, as an `R`-algebra, with the
canonical residue field `IsLocalRing.ResidueField R`; the identification is part of the data.
Likewise the generic fibre is identified with `C` by an isomorphism recorded *over* `Spec(K)`,
i.e. together with the equation `genericFiberIso_over_K` saying that it respects the two
structure morphisms, rather than by a bare isomorphism of schemes. Following Mathlib's
convention, "finite type" is represented by `LocallyOfFiniteType` together with `QuasiCompact`
rather than by a bundled predicate (Tag 01T1).

## References

* [Stacks Project, Chapter 55, Models](https://stacks.math.columbia.edu/chapter/models)
* [Stacks Project, Tag 0C5Y](https://stacks.math.columbia.edu/tag/0C5Y)
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace Stacks.Models

/-- The standing data of a regular model of a smooth curve over the fraction field of a
discrete valuation ring: the ring `R` with a chosen fraction field `K` and residue field `k`,
a smooth curve `C` over `K`, and a flat finite-type regular scheme `X` over `R` whose generic
fibre is identified with `C` over `K`. -/
public structure RegularModelSituation where
  /-- The discrete valuation ring. -/
  R : Type u
  /-- The ring structure on `R`. -/
  [commRingR : CommRing R]
  /-- The ring `R` is a domain. -/
  [isDomainR : IsDomain R]
  /-- The discrete valuation ring hypothesis. -/
  [isDiscreteValuationRingR : IsDiscreteValuationRing R]
  /-- A chosen fraction field of `R`. -/
  K : Type u
  /-- The field structure on `K`. -/
  [fieldK : Field K]
  /-- The inclusion of `R` into its fraction field. -/
  [algebraRK : Algebra R K]
  /-- The assertion that `K` is the fraction field of `R`. -/
  [isFractionRingRK : IsFractionRing R K]
  /-- A chosen residue field of `R`. -/
  k : Type u
  /-- The field structure on `k`. -/
  [fieldk : Field k]
  /-- The quotient map from `R` to its residue field. -/
  [algebraRk : Algebra R k]
  /-- Identification of the chosen residue field with the canonical residue field of `R`. -/
  residueEquiv : IsLocalRing.ResidueField R ≃ₐ[R] k
  /-- The smooth curve over `K`. -/
  C : Scheme.{u}
  /-- The structure morphism of the curve. -/
  C_to_K : C ⟶ Spec (.of K)
  /-- The curve has dimension one and is a variety over `K`. -/
  [isCurve : IsCurve K C_to_K]
  /-- The curve is smooth over `K`. -/
  [smooth : Smooth C_to_K]
  /-- The total space of the model. -/
  X : Scheme.{u}
  /-- The model morphism. -/
  X_to_R : X ⟶ Spec (.of R)
  /-- The model is flat over `R`. -/
  [flat : Flat X_to_R]
  /-- The model morphism is locally of finite type. -/
  [locallyOfFiniteType : LocallyOfFiniteType X_to_R]
  /-- The model morphism is quasi-compact, completing the finite type hypothesis. -/
  [quasiCompact : QuasiCompact X_to_R]
  /-- The total space is regular. -/
  regular : IsRegular X
  /-- The given curve is the generic fibre of the model. -/
  genericFiberIso : C ≅ pullback X_to_R (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  /-- The generic-fibre isomorphism respects the structure morphisms to `Spec(K)`. -/
  genericFiberIso_over_K :
    genericFiberIso.hom ≫ pullback.snd X_to_R
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C_to_K

attribute [instance]
  RegularModelSituation.commRingR
  RegularModelSituation.isDomainR
  RegularModelSituation.isDiscreteValuationRingR
  RegularModelSituation.fieldK
  RegularModelSituation.algebraRK
  RegularModelSituation.isFractionRingRK
  RegularModelSituation.fieldk
  RegularModelSituation.algebraRk
  RegularModelSituation.isCurve
  RegularModelSituation.smooth
  RegularModelSituation.flat
  RegularModelSituation.locallyOfFiniteType
  RegularModelSituation.quasiCompact

namespace RegularModelSituation

/-- The generic fibre `X_K` of a regular model. -/
public noncomputable abbrev genericFiber (S : RegularModelSituation) : Scheme.{u} :=
  pullback S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))

/-- The special fibre `X_k` of a regular model. -/
public noncomputable abbrev specialFiber (S : RegularModelSituation) : Scheme.{u} :=
  pullback S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))

end RegularModelSituation

end Stacks.Models

end
