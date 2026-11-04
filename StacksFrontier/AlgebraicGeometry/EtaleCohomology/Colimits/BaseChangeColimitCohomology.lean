module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# Étale cohomology of a limit of base changes: the canonical maps

Let `T = Spec A` be affine, let `Z : Iᵒᵖ ⥤ Over T` be a diagram of affine schemes `Z_i = Spec B_i`
over `T` indexed by a directed set `I`, let `X` be a scheme over `T` and let `F` be an abelian
sheaf on the small étale site of `X`. Write `Y_i = Z_i ×_T X`, with projection `π_i : Y_i ⟶ X`,
and `G_i = π_i⁻¹ F`; let `cY` be a limit cone of the `Y_i` with apex `Y`, and `p : Y ⟶ X` the
common composite of the legs with the projections, `G = p⁻¹ F`.

This file defines the canonical maps that Stacks 03Q6 is a statement about, in Mathlib's model
`AlgebraicGeometry.Scheme.smallEtaleTopology` of the small étale site, with inverse image
`Stacks.EtaleCohomology.smallEtalePullbackAb`:

* `levelProj` — the projection `π_i : Y_i ⟶ X`, and `levelProj_transition`, its compatibility
  with the transitions;
* `levelSheaf` — the sheaf `G_i = π_i⁻¹ F` on `Y_i`;
* `gammaTransition` — for `f : i ⟶ j` in `Iᵒᵖ`, i.e. `j ≤ i` in `I`, the map
  `Γ(Y_j, G_j) ⟶ Γ(Y_i, G_i)`: restriction of global sections along `Y_i ⟶ Y_j`
  (`Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb`) followed by the comparison
  `(Y_i ⟶ Y_j)⁻¹ π_j⁻¹ F ≅ π_i⁻¹ F` of `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'`;
* `gammaLeg` — the map `Γ(Y_i, G_i) ⟶ Γ(Y, G)`, restriction along the leg `Y ⟶ Y_i` read through
  the same comparison.

The comparisons carry the composite as a named morphism together with the equation naming it, so
no `eqToIso` of an equality of functors appears.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.ColimitBaseChange

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

variable {I : Type u} [Preorder I] (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  (F : Sheaf X.left.smallEtaleTopology Ab.{u + 1})

/-- The projection `π_i : Y_i = Z_i ×_T X ⟶ X`. -/
def levelProj (i : Iᵒᵖ) : (baseChange T X Z).obj i ⟶ X.left :=
  Limits.pullback.snd (Z.obj i).hom X.hom

/-- The projections are compatible with the transitions of the system. -/
theorem levelProj_transition {i j : Iᵒᵖ} (f : i ⟶ j) :
    levelProj T X Z i = (baseChange T X Z).map f ≫ levelProj T X Z j :=
  (Over.w ((Z ⋙ Over.pullback X.hom).map f)).symm

/-- The sheaf `G_i = π_i⁻¹ F` on the small étale site of `Y_i`. -/
abbrev levelSheaf (i : Iᵒᵖ) : Sheaf ((baseChange T X Z).obj i).smallEtaleTopology Ab.{u + 1} :=
  (smallEtalePullbackAb (levelProj T X Z i)).obj F

/-- **The transition map `Γ(Y_j, G_j) ⟶ Γ(Y_i, G_i)` of the degree-zero diagram**, for
`f : i ⟶ j` in `Iᵒᵖ`: restriction of global sections along `Y_i ⟶ Y_j`, read through the
comparison `(Y_i ⟶ Y_j)⁻¹ π_j⁻¹ F ≅ π_i⁻¹ F`. -/
def gammaTransition {i j : Iᵒᵖ} (f : i ⟶ j) :
    (Sheaf.Γ ((baseChange T X Z).obj j).smallEtaleTopology Ab.{u + 1}).obj (levelSheaf T X Z F j) ⟶
      (Sheaf.Γ ((baseChange T X Z).obj i).smallEtaleTopology Ab.{u + 1}).obj
        (levelSheaf T X Z F i) :=
  (smallEtaleGlobalSectionsRestrictionAb ((baseChange T X Z).map f)).app (levelSheaf T X Z F j) ≫
    (Sheaf.Γ _ Ab.{u + 1}).map
      ((smallEtalePullbackAbCompIso' ((baseChange T X Z).map f) (levelProj T X Z j)
        (levelProj T X Z i) (levelProj_transition T X Z f)).hom.app F)

variable {T X Z} (cY : Cone (baseChange T X Z)) (p : cY.pt ⟶ X.left)
  (hp : ∀ i, p = cY.π.app i ≫ levelProj T X Z i)

/-- **The leg `Γ(Y_i, G_i) ⟶ Γ(Y, G)` of the degree-zero cocone**: restriction of global sections
along the leg `Y ⟶ Y_i` of the limit cone, read through the comparison
`(Y ⟶ Y_i)⁻¹ π_i⁻¹ F ≅ p⁻¹ F`. -/
def gammaLeg (i : Iᵒᵖ) :
    (Sheaf.Γ ((baseChange T X Z).obj i).smallEtaleTopology Ab.{u + 1}).obj (levelSheaf T X Z F i) ⟶
      (Sheaf.Γ cY.pt.smallEtaleTopology Ab.{u + 1}).obj ((smallEtalePullbackAb p).obj F) :=
  (smallEtaleGlobalSectionsRestrictionAb (cY.π.app i)).app (levelSheaf T X Z F i) ≫
    (Sheaf.Γ _ Ab.{u + 1}).map
      ((smallEtalePullbackAbCompIso' (cY.π.app i) (levelProj T X Z i) p (hp i)).hom.app F)

end Stacks.EtaleCohomology.ColimitBaseChange

end
