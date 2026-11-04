module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFPBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The critère de platitude par fibres at a point of a thickening

Let `R → T → A` be local homomorphisms of local rings, with `A` essentially of finite
presentation and flat over `R` and `T` essentially of finite type over `R`. The critère de
platitude par fibres (Stacks Tag 05UV) says that if the fibre `A/𝔪_R A` is flat over `T/𝔪_R T`,
then `T` is flat and essentially of finite presentation over `R` and `A` is flat over `T`.

In the geometric situation of a morphism of thickenings
`(X ⊆ X') → (Y ⊆ Y')` over `(S ⊆ S')` with `X = S ×_{S'} X'` and `Y = S ×_{S'} Y'`, the fibre
hypothesis arrives not over the maximal ideal of `O_{S', s'}` but over the smaller ideal
`I = ker(O_{S', s'} → O_{S, s})` cutting out the thickening: flatness of `f : X → Y` at a point
says exactly that `A/IA` is flat over `T/IT`. Since the kernel of a local homomorphism is
contained in the maximal ideal, the fibre over `I` dominates the fibre over `𝔪_R`, and the
criterion applies. That is the content of
`Stacks.Flatness.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient`, the local
engine of Stacks Tag 0CF3.

## Main results

* `Stacks.Flatness.ker_stalkMap_le_maximalIdeal`: the kernel of a stalk map of a morphism of
  schemes lies in the maximal ideal of the stalk of the target.
* `Stacks.Flatness.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient`: the
  critère de platitude par fibres with the fibre taken over an arbitrary ideal contained in the
  maximal ideal of the base.

## Implementation notes

`𝔪_R T` is `(IsLocalRing.maximalIdeal R).map (algebraMap R T)` and `𝔪_R A` is the submodule
`𝔪_R T • ⊤`, so that the fibre `A/𝔪_R A` is a module over the fibre ring `T/𝔪_R T`; this is the
spelling used by
`Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal`, and the
same spelling is used here for a general ideal `I`. The passage from `I` to the maximal
ideal is `Module.Flat.quotient_smul_top_of_le`, which identifies `A/𝔪_R A` as the base change of
`A/IA` along `T/IT → T/𝔪_R T`.

Essential finite presentation is `RingHom.EssentiallyOfFinitePresentation`, Mathlib having no
such predicate; essential finite type is Mathlib's `Algebra.EssFiniteType`.

## References

* [Stacks Project, Tag 05UV](https://stacks.math.columbia.edu/tag/05UV)
* [Stacks Project, Tag 0CEL](https://stacks.math.columbia.edu/tag/0CEL)
* [Stacks Project, Tag 0CF3](https://stacks.math.columbia.edu/tag/0CF3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Flatness

/-- The kernel of a stalk map of a morphism of schemes is contained in the maximal ideal of the
stalk at the image point: the stalk map is a local homomorphism into a nonzero local ring, so no
unit can be in its kernel. -/
theorem ker_stalkMap_le_maximalIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    RingHom.ker (f.stalkMap x).hom ≤ maximalIdeal (Y.presheaf.stalk (f x)) := by
  intro a ha
  by_contra h
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (notMem_maximalIdeal.mp h)
  have : (1 : X.presheaf.stalk x) = 0 := by
    rw [← map_one (f.stalkMap x).hom, ← hb, map_mul, RingHom.mem_ker.mp ha, zero_mul]
  exact one_ne_zero this

/-- **Critère de platitude par fibres at a point of a thickening.** Let `R → T → A` be local
homomorphisms of local rings with `R → A` essentially of finite presentation, `R → T` essentially
of finite type and `A` flat over `R`. If `I ⊆ R` is an ideal contained in the maximal ideal and
the fibre `A/IA` is flat over `T/IT`, then `R → T` is essentially of finite presentation, `T` is
flat over `R` and `A` is flat over `T`.

This is the form in which Stacks Tag 05UV is applied at a point of a thickening: there `I` is the
kernel of the surjection of the base local ring onto the local ring of the closed subscheme, and
the fibre hypothesis is flatness of the morphism of closed subschemes. -/
@[ega "IV 11.3.10" "special case",
  sga "1 I 5.9" "partial",
  sga "1 IV 5.9" "(ii) ⇒ (i) for M = C",
  sga "3 VIB 1.3.0" "special case",
  sga "3 X 3.5" "partial"]
theorem essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient
    {R T A : Type u} [CommRing R] [CommRing T] [CommRing A]
    [IsLocalRing R] [IsLocalRing T] [IsLocalRing A]
    [Algebra R T] [Algebra T A] [Algebra R A] [IsScalarTower R T A]
    [IsLocalHom (algebraMap R T)] [IsLocalHom (algebraMap T A)]
    [Algebra.EssFiniteType R T] [Module.Flat R A]
    (hA : (algebraMap R A).EssentiallyOfFinitePresentation)
    {I : Ideal R} (hI : I ≤ maximalIdeal R)
    (hfibre : Module.Flat (T ⧸ I.map (algebraMap R T))
      (A ⧸ (I.map (algebraMap R T) • (⊤ : Submodule T A)))) :
    (algebraMap R T).EssentiallyOfFinitePresentation ∧ Module.Flat R T ∧ Module.Flat T A := by
  have := hfibre
  have : Module.Flat (T ⧸ (maximalIdeal R).map (algebraMap R T))
      (A ⧸ ((maximalIdeal R).map (algebraMap R T) • (⊤ : Submodule T A))) :=
    Module.Flat.quotient_smul_top_of_le (Ideal.map_mono hI)
  exact Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal hA

end Stacks.Flatness

end
