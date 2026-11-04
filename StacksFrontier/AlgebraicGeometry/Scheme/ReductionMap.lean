module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism of reductions induced by a morphism of schemes

A morphism of schemes `f : X ⟶ Y` carries the reduction of `X` to the reduction of `Y`: the
composite `X_red ⟶ X ⟶ Y` has reduced source, so it kills the nilradical of `Y` and therefore
factors uniquely through the closed subscheme `Y_red ⟶ Y` that the nilradical cuts out. For an
isomorphism the induced morphism is an isomorphism, its inverse being the morphism induced by
the inverse.

## Main definitions

* `AlgebraicGeometry.reductionMap` is the induced morphism `X_red ⟶ Y_red`.
* `AlgebraicGeometry.reductionIso` is the induced isomorphism `X_red ≅ Y_red` of the reductions
  of two isomorphic schemes.

## Main results

* `AlgebraicGeometry.reductionMap_comp_subschemeι` is the defining square of `reductionMap`, and
  determines it, `Y_red ⟶ Y` being a monomorphism.
* `AlgebraicGeometry.reductionMap_comp`: the construction is functorial.

## Implementation notes

The reduction of `X` is written as `X.nilradical.subscheme`, the closed subscheme cut out by
Mathlib's nilradical ideal sheaf, rather than through a wrapper, so that the statements here are
immediately available to the lemmas about closed subschemes they are used with.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism out of a reduced scheme kills the nilradical of its target: a nilpotent section
of the target is carried to a nilpotent section of a reduced scheme, hence to zero. -/
theorem nilradical_le_ker_of_isReduced {X Y : Scheme.{u}}
    [IsReduced X] (f : X ⟶ Y) : Y.nilradical ≤ f.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U x hx
  change x ∈ nilradical Γ(Y, U) at hx
  exact (IsNilpotent.map (mem_nilradical.mp hx) (f.app U).hom).eq_zero

/-- The morphism `X_red ⟶ Y_red` of reductions induced by `f : X ⟶ Y`: the composite
`X_red ⟶ X ⟶ Y` has reduced source, so it kills `Y.nilradical` and factors through the closed
subscheme that the nilradical cuts out. -/
@[ega "I 5.1.5"]
def reductionMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.nilradical.subscheme ⟶ Y.nilradical.subscheme :=
  have : IsReduced X.nilradical.subscheme := by
    rw [Scheme.nilradical]; infer_instance
  IsClosedImmersion.lift Y.nilradical.subschemeι (X.nilradical.subschemeι ≫ f)
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact nilradical_le_ker_of_isReduced _)

/-- The defining square of `AlgebraicGeometry.reductionMap`. Since `Y_red ⟶ Y` is a
monomorphism, this determines the morphism of reductions. -/
theorem reductionMap_comp_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    reductionMap f ≫ Y.nilradical.subschemeι = X.nilradical.subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- Taking reductions is functorial. -/
theorem reductionMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    reductionMap f ≫ reductionMap g = reductionMap (f ≫ g) := by
  apply (cancel_mono Z.nilradical.subschemeι).mp
  simp only [Category.assoc, reductionMap_comp_subschemeι]
  rw [← Category.assoc, reductionMap_comp_subschemeι, Category.assoc]

/-- The reduction of a closed immersion is a closed immersion. -/
theorem isClosedImmersion_reductionMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] : IsClosedImmersion (reductionMap f) := by
  have : IsClosedImmersion (reductionMap f ≫ Y.nilradical.subschemeι) := by
    rw [reductionMap_comp_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ Y.nilradical.subschemeι

/-- A section of `f` induces a section of the morphism of reductions. -/
theorem reductionMap_section {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    reductionMap s ≫ reductionMap f = 𝟙 Y.nilradical.subscheme := by
  rw [reductionMap_comp, hs]
  apply (cancel_mono Y.nilradical.subschemeι).mp
  rw [reductionMap_comp_subschemeι, Category.id_comp, Category.comp_id]

/-- Isomorphic schemes have isomorphic reductions: the morphisms of reductions induced by an
isomorphism and by its inverse are mutually inverse. -/
def reductionIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.nilradical.subscheme ≅ Y.nilradical.subscheme where
  hom := reductionMap e.hom
  inv := reductionMap e.inv
  hom_inv_id := reductionMap_section e.inv e.hom e.hom_inv_id
  inv_hom_id := reductionMap_section e.hom e.inv e.inv_hom_id

/-- The forward map of `AlgebraicGeometry.reductionIso` is the morphism of reductions induced
by the forward map of the isomorphism. -/
theorem reductionIso_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (reductionIso e).hom = reductionMap e.hom :=
  rfl

/-- The inverse map of `AlgebraicGeometry.reductionIso` is the morphism of reductions induced
by the inverse of the isomorphism. -/
theorem reductionIso_inv {X Y : Scheme.{u}} (e : X ≅ Y) :
    (reductionIso e).inv = reductionMap e.inv :=
  rfl

/-- The defining square of `AlgebraicGeometry.reductionIso`: it is compatible with the closed
immersions of the two reductions into the two schemes. -/
theorem reductionIso_hom_comp_subschemeι {X Y : Scheme.{u}} (e : X ≅ Y) :
    (reductionIso e).hom ≫ Y.nilradical.subschemeι =
      X.nilradical.subschemeι ≫ e.hom :=
  reductionMap_comp_subschemeι e.hom

end AlgebraicGeometry
