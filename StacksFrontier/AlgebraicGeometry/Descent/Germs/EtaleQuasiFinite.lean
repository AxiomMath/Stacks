module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Étale morphisms are locally quasi-finite

An étale morphism of schemes is locally of finite type and has discrete fibres, which together
are the Stacks Project's local quasi-finiteness. It is moreover flat, so generalizations lift
along it, and when it is in addition quasi-compact its fibres are finite.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_of_etale` states that an étale morphism of schemes is
  locally quasi-finite.
* `AlgebraicGeometry.flat_and_generalizingMap_of_etale` states that an étale morphism is flat
  and that generalizations lift along it.
* `AlgebraicGeometry.finite_preimage_singleton_of_etale_of_quasiCompact` states that a
  quasi-compact étale morphism has finite fibres.

## Implementation notes

Étaleness is the morphism property `AlgebraicGeometry.Etale`. Local quasi-finiteness is the
conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, the latter being the fibre-isolation condition. The
discreteness half is obtained by observing that an étale morphism is unramified, which follows
pointwise from the characterisation of étaleness at a point as smoothness together with
unramifiedness.

There is no morphism property for quasi-finiteness in Mathlib: a quasi-finite morphism is a
locally quasi-finite one that is in addition quasi-compact, so quasi-finiteness of a
quasi-compact étale morphism is `AlgebraicGeometry.locallyQuasiFinite_of_etale` together with
the hypothesis, and the finiteness of the fibres is what is recorded separately below.

## References

* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An étale morphism of schemes is locally quasi-finite. -/
@[stacks 03WS, stacks 03II "etale_locally_quasi_finite"]
theorem locallyQuasiFinite_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f := by
  have hu : Unramified f :=
    ⟨fun x ↦ ((etaleAt_iff_smoothAt_and_unramifiedAt f x).mp
      ((etale_iff_forall_etaleAt f).mp ‹Etale f› x)).2⟩
  exact ⟨inferInstance, @locallyQuasiFinite_of_unramified _ _ f hu⟩

/-- An étale morphism of schemes is flat, and hence generalizations lift along it. -/
@[stacks 03II "etale_flat_generalizing", ega "IV 2.3.4" "(i), special case"]
theorem flat_and_generalizingMap_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    Flat f ∧ GeneralizingMap f.base :=
  ⟨inferInstance, Flat.generalizingMap f⟩

/-- A quasi-compact étale morphism of schemes has finite fibres.

It is locally quasi-finite, hence quasi-finite as it is quasi-compact. -/
@[stacks 03II "etale_quasi_compact_finite_fibres"]
theorem finite_preimage_singleton_of_etale_of_quasiCompact {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] [QuasiCompact f] (s : S) : (f.base ⁻¹' {s}).Finite :=
  have : LocallyQuasiFinite f := (locallyQuasiFinite_of_etale f).2
  f.finite_preimage_singleton s

end AlgebraicGeometry
