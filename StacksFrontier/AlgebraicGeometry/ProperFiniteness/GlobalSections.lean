module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the global sections of a proper scheme over a Noetherian affine base

[Stacks, Tag 02O6] says that for a Noetherian ring `A`, a proper morphism `f : X ⟶ Spec A` and a
coherent `𝒪_X`-module `ℱ`, every cohomology module `Hⁱ(X, ℱ)` is finite over `A`. Its degree-zero
case for `ℱ = 𝒪_X` is the assertion that `Γ(X, ⊤)` is a finite `A`-module, and that case is what
the finiteness of normalization in [Stacks, Tag 0BGG] consumes.

That assertion is **proved in this development**, with no hypothesis, by
`AlgebraicGeometry.finiteGlobalSectionsOfProper` in
`StacksFrontier/AlgebraicGeometry/ProperFiniteness/GlobalSectionsFinite.lean`: it reads off the
coherence of the direct image `f_* 𝒪_X`, which is the hypothesis-free [Stacks, Tag 02O5] of
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean`. It is named *here*, and
proved there, because this file imports nothing but Mathlib while that one sits on top of the
whole coherence development. What this file provides is the name, together with what is provable
about the assertion with no coherence machinery at all:

* the reduction of finiteness to finite generation as an algebra, which is the whole remaining
  content of the degree-zero case;
* the bridge from the ring-map form to the module form over the base ring;
* the affine case, where properness already gives finiteness of the morphism.

Two further cases are theorems of Mathlib rather than of this file:
`AlgebraicGeometry.Scheme.Hom.finite_appTop` for a finite morphism, and
`AlgebraicGeometry.finite_appTop_of_universallyClosed` for a morphism from an integral scheme to
the spectrum of a field.

## Main definitions

* `AlgebraicGeometry.FiniteGlobalSectionsOfProper` is the degree-zero case of
  [Stacks, Tag 02O6] for the structure sheaf, as a proposition.

## Main results

* `AlgebraicGeometry.finite_appTop_iff_finiteType`: for a universally closed morphism to an
  affine scheme, the map on global sections is finite if and only if it is of finite type.
* `AlgebraicGeometry.finite_appTop_of_isAffineHom`: an affine proper morphism to an affine
  scheme has finite map on global sections.
* `AlgebraicGeometry.module_finite_globalSections`: the module form of the conclusion over the
  base ring.

## Implementation notes

The statement is phrased with `Scheme.Hom.appTop` rather than with an `Algebra` instance on
`Γ(X, ⊤)`, matching Mathlib's `AlgebraicGeometry.finite_appTop_of_universallyClosed`;
`module_finite_globalSections` converts to the module form along `Scheme.ΓSpecIso`.

The Noetherian hypothesis on the base and properness of the morphism are carried as explicit
arguments of `FiniteGlobalSectionsOfProper` rather than as instance arguments, so that a consumer
can apply it without arranging instances for a ring it has built by hand.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- **The degree-zero case of [Stacks, Tag 02O6] for the structure sheaf**: for every Noetherian
ring `A` and every proper morphism `g : V ⟶ Spec A`, the ring map `Γ(Spec A, ⊤) ⟶ Γ(V, ⊤)` is
finite, i.e. `Γ(V, ⊤)` is a finite `A`-module.

This holds, and is proved with no hypothesis by
`AlgebraicGeometry.finiteGlobalSectionsOfProper` in
`StacksFrontier/AlgebraicGeometry/ProperFiniteness/GlobalSectionsFinite.lean`. It is stated here
rather than there so that the consumers of [Stacks, Tag 02O6] name this input in one place; see
the module documentation. -/
def FiniteGlobalSectionsOfProper : Prop :=
  ∀ (A : Type u) [CommRing A], IsNoetherianRing A →
    ∀ {V : Scheme.{u}} (g : V ⟶ Spec (.of A)), IsProper g → g.appTop.hom.Finite

/-- **For a universally closed morphism to an affine scheme, finiteness of the map on global
sections is finite generation as an algebra.** That map is always integral
(`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`), and an integral ring map of finite
type is finite. -/
theorem finite_appTop_iff_finiteType (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] :
    f.appTop.hom.Finite ↔ f.appTop.hom.FiniteType := by
  refine ⟨RingHom.FiniteType.of_finite, fun h => ?_⟩
  have hint := isIntegral_appTop_of_universallyClosed f
  algebraize [f.appTop.hom]
  exact Algebra.IsIntegral.finite

/-- An affine proper morphism is finite, so its map on global sections is finite. -/
theorem finite_appTop_of_isAffineHom (f : X ⟶ Y) [IsAffine Y] [IsAffineHom f] [IsProper f] :
    f.appTop.hom.Finite :=
  have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨‹_›, ‹_›⟩
  f.finite_appTop

/-- The module form of finiteness of the global sections over the base ring: if the ring map
`Γ(Spec A, ⊤) ⟶ Γ(V, ⊤)` is finite then `Γ(V, ⊤)` is a finite `A`-module for the algebra
structure induced by that map through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem module_finite_globalSections {A : Type u} [CommRing A] {V : Scheme.{u}}
    (g : V ⟶ Spec (.of A)) (hg : g.appTop.hom.Finite) :
    letI := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom.toAlgebra
    Module.Finite A Γ(V, ⊤) := by
  let := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom.toAlgebra
  rw [← RingHom.finite_algebraMap]
  exact hg.comp (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of A)).inv.hom)
    (fun x => ⟨(Scheme.ΓSpecIso (.of A)).hom.hom x, by simp⟩))

end AlgebraicGeometry

end
