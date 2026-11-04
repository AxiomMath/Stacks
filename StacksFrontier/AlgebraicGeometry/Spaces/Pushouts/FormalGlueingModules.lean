module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The formal glueing situation for quasi-coherent modules

Formal glueing of quasi-coherent modules takes place in a fixed situation: a quasi-compact and
quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`, a closed subspace
`Z` of `X` which is of finite presentation, such that `f` is an isomorphism over `Z` and is
flat at every point of `f⁻¹(Z)`. The two open parts of the picture are then `U = X \ Z` and
`V = Y \ f⁻¹(Z)`, and the glueing statement compares modules on `X` with pairs of modules on
`U` and on `Y` agreeing on `V`.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation`: the standing data and hypotheses.
* `AlgebraicGeometry.Space.FormalGlueingSituation.U`: the open complement of `Z` in `X`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.V`: its inverse image in `Y`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplement_preimage`: `V` is the
  open complement of `f⁻¹(Z)` in `Y`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isOpenSubspace_U` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.isOpenSubspace_V`: both are open subspaces.

## Implementation notes

The closed part is a subfunctor `Z` of `X`, so its inverse image is `Subfunctor.preimage` and
"`f` is an isomorphism over `Z`" is invertibility of `Subfunctor.fromPreimage`, the projection
`f⁻¹(Z) ⟶ Z`. The complements are `AlgebraicGeometry.Space.openComplement`, which is defined
for an arbitrary subfunctor; that `V` as defined — the inverse image of `U` — agrees with the
complement of `f⁻¹(Z)` is `V_eq_openComplement_preimage`, proved by unfolding both
complements, and it is what makes the openness of `V` a case of the openness of a complement.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AEV.** The standing situation for formal glueing of quasi-coherent modules: a
quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over `S`, a finitely
presented closed subspace `Z` of `X` over which `f` is an isomorphism, with `f` flat at every
point of the inverse image of `Z`. -/
@[stacks 0AEV "standing data and hypotheses"]
structure FormalGlueingSituation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The ambient algebraic space. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The algebraic space mapping to `X`. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X` is an algebraic space. -/
  algebraicSpace_X : IsAlgebraicSpace B S hS X
  /-- `Y` is an algebraic space. -/
  algebraicSpace_Y : IsAlgebraicSpace B S hS Y
  /-- The morphism being glued along. -/
  f : Y ⟶ X
  /-- The morphism is quasi-compact. -/
  quasiCompact_f : IsQuasiCompact B S hS f
  /-- The morphism is quasi-separated. -/
  quasiSeparated_f : IsQuasiSeparated B S hS f
  /-- The closed part of `X`. -/
  Z : Subfunctor X
  /-- `Z` is a closed subspace of `X`. -/
  closed_Z : IsClosedSubspace B S hS Z
  /-- The inclusion of `Z` is of finite presentation. -/
  finitePresentation_Z : IsFinitePresentation B S hS Z.ι
  /-- The morphism is an isomorphism over `Z`. -/
  iso_over_Z : IsIso (Z.fromPreimage f)
  /-- The morphism is flat at every point of the inverse image of `Z`. -/
  flat_at_preimage_Z :
    ∀ x : points B S hS (Z.preimage f).toFunctor,
      IsFlatAt B S hS f
        (pointsMap B S hS (Z.preimage f).toFunctor
          (Z.preimage f).ι x)

namespace FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The open complement of `Z` in `X`. -/
abbrev U (D : FormalGlueingSituation B S hS) : Subfunctor D.X :=
  openComplement B S hS D.Z

/-- The inverse image of `U` in `Y`; equivalently the complement of `f⁻¹(Z)`. -/
abbrev V (D : FormalGlueingSituation B S hS) : Subfunctor D.Y :=
  D.U.preimage D.f

/-- **Stacks 0AEV.** The inverse image of the open complement of `Z` is the open complement
of the inverse image of `Z`. -/
@[stacks 0AEV "V = Y minus the inverse image of Z"]
theorem V_eq_openComplement_preimage (D : FormalGlueingSituation B S hS) :
    D.V = openComplement B S hS (D.Z.preimage D.f) := by
  ext A x
  simp only [FormalGlueingSituation.V, FormalGlueingSituation.U,
    openComplement, Subfunctor.preimage_obj, Set.mem_preimage]
  constructor <;> intro hx A' a ha <;> apply hx A' a <;>
    simpa only [NatTrans.naturality_apply] using ha

/-- **Stacks 0AEV.** The complement of `Z` is an open subspace of `X`. -/
@[stacks 0AEV "openness of U"]
theorem isOpenSubspace_U (D : FormalGlueingSituation B S hS) :
    IsOpenSubspace B S hS D.U :=
  isOpenSubspace_openComplement B S hS D.algebraicSpace_X D.Z D.closed_Z

/-- **Stacks 0AEV.** The complement of the inverse image of `Z` is an open subspace of `Y`. -/
@[stacks 0AEV "openness of V"]
theorem isOpenSubspace_V (D : FormalGlueingSituation B S hS) :
    IsOpenSubspace B S hS D.V := by
  simpa only [V_eq_openComplement_preimage] using
    isOpenSubspace_openComplement B S hS D.algebraicSpace_Y _
      (isClosedSubspace_preimage B S hS D.f D.Z
        D.algebraicSpace_X D.algebraicSpace_Y D.closed_Z)

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
