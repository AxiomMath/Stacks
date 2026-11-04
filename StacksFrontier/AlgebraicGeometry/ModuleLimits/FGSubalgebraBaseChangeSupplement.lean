module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.Algebra.Module.Adequate.FiniteTypeSubalgebras
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FGSubalgebraBaseChange

/-!
# Invertible modules on a base change descend to a finitely generated subalgebra

Let `X` be a quasi-compact quasi-separated scheme over a commutative ring `k` and let `A` be a
`k`-algebra. Writing `A` as the filtered colimit of its finitely generated `k`-subalgebras, the
base change `X_A = Spec A ×_{Spec k} X` is the cofiltered limit of the base changes `X_{A'}`, with
affine transition morphisms; so by [Stacks, Tag 0B8W] (2) every invertible module on `X_A` is the
pullback of an invertible module on some `X_{A'}`.

## Main definitions

* `Stacks.FGSubalgebraLimit.baseChangeLimitCone`: the presentation of `X_A` as that limit, built
  on the filtered colimit `Stacks.Adequate.isColimit_fgSubalgebraCocone` of the finitely generated
  subalgebras.

## Implementation notes

`StacksFrontier/AlgebraicGeometry/Variety/Geometrically/QuasiCompactOpenSubalgebra.lean` carries the
same limit presentation, but keeps it private to that file (its declarations live in the root
`AlgebraicGeometry` namespace under names that other public modules of this library already use,
so they cannot be exported). The presentation here is therefore assembled from the public
colimit API `Stacks.Adequate.FgSubalgebras` / `Stacks.Adequate.fgSubalgebraCocone` rather than
from a second copy of that colimit.

## Main results

* `Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.FGSubalgebraLimit

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

open Stacks.Adequate (FgSubalgebras fgSubalgebraDiagram fgSubalgebraCocone)

/-- The cofiltered diagram of the spectra of the finitely generated `k`-subalgebras of `A`, as
schemes over `Spec k`. -/
noncomputable def specDiagram : (FgSubalgebras k A)ᵒᵖ ⥤ Over (Spec (.of k)) :=
  (fgSubalgebraDiagram k A).op ⋙ algSpec (CommRingCat.of k)

/-- `Spec A` is the limit of the spectra of the finitely generated `k`-subalgebras of `A`, over
`Spec k`, because `Spec` on algebras preserves limits. -/
noncomputable def specLimitCone : LimitCone (specDiagram k A) where
  cone := (algSpec (CommRingCat.of k)).mapCone (fgSubalgebraCocone k A).op
  isLimit :=
    haveI : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of k)) :=
      preservesLimitsOfSize_algSpec
    isLimitOfPreserves _ (Stacks.Adequate.isColimit_fgSubalgebraCocone k A).op

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The diagram of base changes `i ↦ Spec Aᵢ ×_{Spec k} X` of `X` to the finitely generated
`k`-subalgebras of `A`. -/
noncomputable def baseChangeDiagram : (FgSubalgebras k A)ᵒᵖ ⥤ Scheme.{u} :=
  specDiagram k A ⋙ Over.pullback f ⋙ Over.forget X

/-- `X_A` is the limit of the base changes of `X` to the finitely generated `k`-subalgebras of
`A`: base change along `f` is a right adjoint and the forgetful functor from the slice category
preserves cofiltered limits. The apex is `X_A` on the nose. -/
noncomputable def baseChangeLimitCone : LimitCone (baseChangeDiagram k A f) where
  cone := (Over.forget X).mapCone ((Over.pullback f).mapCone (specLimitCone k A).cone)
  isLimit :=
    haveI : PreservesLimitsOfShape (FgSubalgebras k A)ᵒᵖ (Over.forget X) := inferInstance
    isLimitOfPreserves _ (isLimitOfPreserves _ (specLimitCone k A).isLimit)

/-- The transition morphisms of the diagram of base changes are affine, being base changes of
the morphisms of spectra induced by the inclusions of subalgebras. -/
instance isAffineHom_baseChangeDiagram_map {i j : (FgSubalgebras k A)ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom ((baseChangeDiagram k A f).map g) := by
  refine MorphismProperty.overPullbackMap (P := @IsAffineHom) f ((specDiagram k A).map g) ?_
  change IsAffineHom (Spec.map _)
  infer_instance

/-- A leg of the limit cone covers the morphism `Spec A ⟶ Spec Aᵢ` induced by the inclusion of
the subalgebra. -/
theorem baseChangeLimitCone_π_comp_fst (i : (FgSubalgebras k A)ᵒᵖ) :
    (baseChangeLimitCone k A f).cone.π.app i ≫
        pullback.fst ((specDiagram k A).obj i).hom f =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.val (i.unop : Subalgebra k A)).toRingHom) := by
  show pullback.lift (pullback.fst _ f ≫ _) (pullback.snd _ f) _ ≫ _ = _
  rw [pullback.lift_fst]
  rfl

/-- A leg of the limit cone commutes with the projection to `X`. -/
theorem baseChangeLimitCone_π_comp_snd (i : (FgSubalgebras k A)ᵒᵖ) :
    (baseChangeLimitCone k A f).cone.π.app i ≫
        pullback.snd ((specDiagram k A).obj i).hom f =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f := by
  show pullback.lift (pullback.fst _ f ≫ _) (pullback.snd _ f) _ ≫ _ = _
  rw [pullback.lift_snd]
  rfl

end Stacks.FGSubalgebraLimit

end
