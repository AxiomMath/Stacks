module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import StacksFrontier.RingTheory.Flat.CompleteDevissage

/-!
# The complete dévissage of the zero module

Stacks 05HX puts no condition on the dimensions of the fibres of `Spec Bᵢ → Spec R`, and that is
what makes the zero module cheap on the algebraic side: a complete dévissage of `0/S/R` over a
prime `r` of `R` exists outright, with one stage, `A₁` the zero ring, `B₁ = R`, `M₁ = 0` and
`r₁ = 0`. Every condition of Stacks 05HX holds: `S → A₁` is surjective and of finite
presentation, being the quotient by the unit ideal; `B₁ → A₁` is finite; `R → B₁` is the
identity, which is smooth with geometrically irreducible fibres; the map
`α₁ : B₁^{⊕ 0} → M₁` out of the empty direct sum is surjective onto the zero module and becomes
an isomorphism over the residue field of `rB₁`; and its cokernel vanishes.

This is the one place where the geometric and the algebraic notions come apart, and the source
says so: on the scheme side Stacks 05H4 (5) asks the fibres of `Y → S` to have dimension
`dim (Supp(ℱ_s))`, which for `ℱ = 0` is `-∞`, so *no* smooth morphism with geometrically
irreducible — in particular nonempty — fibres can satisfy it, and the zero sheaf has only the
empty dévissage of Stacks 05HH. Stacks 05I0 (1) is an implication for exactly this reason, and
`AlgebraicGeometry.CompleteDevissage.empty` is sent to the dévissage built here.

## Main definitions

* `Module.CompleteDevissage.ofSubsingleton`: **the one-stage complete dévissage of the zero
  module over any prime of the base**, with the zero ring upstairs and the base ring itself as
  the smooth algebra.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_id` and
  `AlgebraicGeometry.geometricallyIrreducible_specMap_algebraMap_self`: an identity morphism of
  schemes has geometrically irreducible fibres, since its base change along a field-valued point
  is the spectrum of that field.
* `Module.nonempty_completeDevissage_of_subsingleton`: the zero module has a complete dévissage
  over every prime of the base.

## Implementation notes

The stage algebra `A₁` is `PUnit`, the zero ring in the universe of `R`, and the stage module is
`PUnit` in the universe of `N`; the maps out of `S` and out of `B₁` are the unique algebra maps
to a trivial algebra, `default`. Finiteness of `B₁ → A₁` and of `M₁` over `A₁` is
`Module.Finite.of_finite`, which needs only that the target is a finite type, so it applies
whatever module structure the dévissage puts on it. The residue-field condition is bijectivity
of a map between two trivial modules: a tensor product with a trivial factor is trivial, which
instance synthesis sees through `Unique.instSubsingleton`, so `Subsingleton.elim` applies to the
base-changed source and target without either being named.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u v w

/-- **An identity morphism of schemes has geometrically irreducible fibres.** Its base change
along a point `Spec K ⟶ X` with `K` a field is `Spec K` itself, whose space is irreducible. -/
public theorem AlgebraicGeometry.geometricallyIrreducible_id (X : Scheme.{u}) :
    GeometricallyIrreducible (𝟙 X) :=
  ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun _ _ x =>
    (asIso (Limits.pullback.snd (𝟙 X) x)).hom.homeomorph.irreducibleSpace_iff.mpr
      inferInstance⟩

/-- **The spectrum of a ring has geometrically irreducible fibres over itself.** The structure
map of `R` as an `R`-algebra is the identity. -/
public theorem AlgebraicGeometry.geometricallyIrreducible_specMap_algebraMap_self (R : Type u)
    [CommRing R] : GeometricallyIrreducible (Spec.map (ofHom (algebraMap R R))) := by
  rw [show ofHom (algebraMap R R) = 𝟙 (CommRingCat.of R) from (hom_ext rfl).symm, Spec.map_id]
  exact geometricallyIrreducible_id _

namespace Module

/-- **The complete dévissage of the zero module over a prime `r` of `R`** (Stacks 05HX): one
stage, with the zero ring `A₁ = PUnit` as the algebra upstairs, the base ring itself as the
smooth algebra `B₁ = R`, the zero module `M₁ = PUnit`, and the empty direct sum
`B₁^{⊕ 0} → M₁` as `α₁`. -/
public def CompleteDevissage.ofSubsingleton (R : Type u) (S : Type v) (N : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] [Subsingleton N] (r : Ideal R) [r.IsPrime] :
    CompleteDevissage R S N r where
  stepCount := 0
  A := fun _ => PUnit.{u + 1}
  B := fun _ => R
  M := fun _ => PUnit.{w + 1}
  toA₀ := default
  toLeft := fun _ => default
  toRight := fun i => i.elim0
  multiplicity := fun _ => 0
  alpha := fun _ => 0
  finiteM := fun _ => inferInstance
  initial_surjective := fun _ => ⟨0, Subsingleton.elim _ _⟩
  initial_finitePresentation := by
    have : Algebra.FinitePresentation S PUnit.{u + 1} := inferInstance
    exact this
  transition_surjective := fun i => i.elim0
  transition_finitePresentation := fun i => i.elim0
  left_finite := fun _ => by exact Module.Finite.of_finite
  smooth := fun _ => inferInstance
  geometricallyIrreducibleFibers := fun _ =>
    AlgebraicGeometry.geometricallyIrreducible_specMap_algebraMap_self R
  initialEquiv :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _
      map_smul' := fun _ _ => Subsingleton.elim _ _ }
  cokerEquiv := fun i => i.elim0
  map_isPrime := fun _ => by rw [Algebra.algebraMap_self, Ideal.map_id]; infer_instance
  fiber_bijective := fun _ => by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  final_surjective := fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- **The zero module has a complete dévissage over every prime of the base**, namely
`Module.CompleteDevissage.ofSubsingleton`. -/
public theorem nonempty_completeDevissage_of_subsingleton {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] [Subsingleton N] (r : Ideal R) [r.IsPrime] :
    Nonempty (CompleteDevissage R S N r) :=
  ⟨CompleteDevissage.ofSubsingleton R S N r⟩

end Module

end
