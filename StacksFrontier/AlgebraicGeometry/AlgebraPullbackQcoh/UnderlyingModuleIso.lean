module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible

/-!
# The module underlying an algebra pullback, as an isomorphism

Let `g : T ⟶ S` be a morphism of schemes and `A` a sheaf of commutative `𝒪_S`-algebras.
`Stacks.AlgebraPullbackQcoh.isIso_comparison` proves that the canonical comparison
`Stacks.ModuleStalkTensor.comparison g A : g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of underlying
`𝒪_T`-modules is invertible, for an arbitrary `g` and an arbitrary `A`.  That result is
stated as an `IsIso`, and `AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own
`Category` instance, so the `IsIso` is not found by instance search and `CategoryTheory.asIso`
cannot be applied to the comparison without handing it over positionally.

This file does that once and exports the resulting isomorphism in both directions, so that
the consumers which take the identification of the module underlying `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`
as a hypothesis can be supplied with it rather than repeating the `asIso` incantation.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.underlyingModulePullbackIso`: the identification
  `g^*A ≅ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of `𝒪_T`-modules, for an arbitrary morphism of schemes and an
  arbitrary sheaf of commutative `𝒪_S`-algebras.
* `Stacks.AlgebraPullbackQcoh.algebraPullbackUnderlyingModuleIso`: the same isomorphism in the
  direction in which
  `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso`
  takes it as a hypothesis.

## Main results

* `Stacks.AlgebraPullbackQcoh.isQuasicoherent_algebraPullback`: the hypothesis of
  `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` is
  derivable, so that reduction is unconditional.  This is the same conclusion as
  `Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`, reached through the stated
  reduction rather than through `isQuasicoherent_of_isIso_comparison`, and it is recorded here
  to witness that the hypothesis the reduction names is not an open assumption.

## Implementation notes

The invertibility is handed to `CategoryTheory.asIso` positionally, as
`Stacks.ModuleStalkTensor.isQuasicoherent_of_isIso_comparison` does and for the same reason:
instance search looks for `IsIso` in the `SheafOfModules` category rather than in the
`AlgebraicGeometry.Scheme.Modules` wrapper, and so does not find it.

No project tag attribute is attached.  The clause of [Stacks, Tag 01SA] these statements serve
is `algebraPullback_isQuasicoherent`, which is registered nowhere in this repository: Tag
01SA carries a single unqualified tag on a nine-field structure several of whose fields are
still open, so a tag here would make the whole tag render as formalized.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraPullbackQcoh

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.ModuleStalkTensor

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : AlgebraSheaf S)

/-- **The module underlying the pullback of an algebra sheaf is the pullback of its underlying
module.**  For an arbitrary morphism of schemes `g : T ⟶ S` and an arbitrary sheaf of
commutative `𝒪_S`-algebras `A`, the canonical comparison
`g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is an isomorphism of `𝒪_T`-modules.  This is
`Stacks.AlgebraPullbackQcoh.isIso_comparison` packaged as an isomorphism. -/
noncomputable def underlyingModulePullbackIso :
    (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A) ≅
      AlgebraSheaf.underlyingModule ((algebraPullback g).obj A) :=
  @asIso _ _ _ _ (comparison g A) (isIso_comparison g A)

/-- The forward map of `underlyingModulePullbackIso` is the canonical comparison map. -/
@[simp] theorem underlyingModulePullbackIso_hom :
    (underlyingModulePullbackIso g A).hom = comparison g A :=
  rfl

/-- The identification of the module underlying `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` with the pullback of the
module underlying `A`, in the direction in which
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` takes
it as a hypothesis. -/
noncomputable def algebraPullbackUnderlyingModuleIso :
    AlgebraSheaf.underlyingModule ((algebraPullback g).obj A) ≅
      (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A) :=
  (underlyingModulePullbackIso g A).symm

/-- **The hypothesis of the first reduction of the quasi-coherence clause of [Stacks, Tag 01SA]
is derivable.**  Feeding `algebraPullbackUnderlyingModuleIso` to
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` makes
that reduction unconditional: the pullback of a quasi-coherent sheaf of commutative
`𝒪_S`-algebras along an arbitrary morphism of schemes is quasi-coherent.

The conclusion is that of `Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`; what
this records is that the identification the reduction names as its hypothesis is supplied by
`isIso_comparison` and is not an open assumption. -/
theorem isQuasicoherent_algebraPullback [A.IsQuasicoherent] :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  isQuasicoherent_algebraPullback_of_underlyingModuleIso g A
    (algebraPullbackUnderlyingModuleIso g A)

end Stacks.AlgebraPullbackQcoh

end
