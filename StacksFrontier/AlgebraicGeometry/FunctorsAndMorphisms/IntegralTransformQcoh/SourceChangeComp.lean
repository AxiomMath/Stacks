module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Change of source along a composite

Let `R` be a commutative ring and let `U`, `U'`, `U''` and `Y` be schemes over `R`.  A composite
`U'' ⟶ U' ⟶ U` of morphisms over `R` induces `U'' ×_R Y ⟶ U ×_R Y`, and the inverse image of a
quasi-coherent kernel on `U ×_R Y` along it is the iterated inverse image.  This file records
that comparison together with the two facts about direct images along a composite of affine
morphisms that it is used with.

## Main definitions

* `AlgebraicGeometry.sourceChangeKernelCompIso`: change of source along a composite is the
  composite of the two changes of source.

## Main results

* `AlgebraicGeometry.isAffineHom_left_comp`: a composite of affine morphisms of schemes over a
  base is affine.
* `AlgebraicGeometry.quasicoherentPushforward_eq_comp`: the direct image on quasi-coherent
  modules along a composite of affine morphisms is the composite of the direct images.

## Implementation notes

The direct image on quasi-coherent modules along a composite is *equal*, not merely isomorphic,
to the composite of the direct images; the equality is isolated in
`AlgebraicGeometry.quasicoherentPushforward_eq_comp` because the elaborator does not see it
through a whiskering.

## References

* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A composite of affine morphisms of schemes over a base is affine, in the form in which the
composite of two charts is a chart. -/
@[ega "II 1.3.5", ega "II 1.3.6" "partial"]
instance isAffineHom_left_comp {S : Scheme.{u}} {X U U' : Over S} (j : U ⟶ X) (j' : U' ⟶ U)
    [IsAffineHom j.left] [IsAffineHom j'.left] : IsAffineHom (j' ≫ j).left :=
  inferInstanceAs (IsAffineHom (j'.left ≫ j.left))

/-- The direct image on quasi-coherent modules along a composite of affine morphisms of schemes
over a base is the composite of the direct images. -/
theorem quasicoherentPushforward_eq_comp {S : Scheme.{u}} {X U U' : Over S} (j : U ⟶ X)
    (j' : U' ⟶ U) {k : U' ⟶ X} (hk : j' ≫ j = k) [IsAffineHom j.left] [IsAffineHom j'.left]
    [IsAffineHom k.left] :
    quasicoherentPushforward k.left =
      quasicoherentPushforward j'.left ⋙ quasicoherentPushforward j.left := by
  subst hk; rfl

/-- Change of source along a composite `U'' ⟶ U' ⟶ U` is the composite of the two changes of
source. -/
def sourceChangeKernelCompIso (R : Type u) [CommRing R] (U U' U'' Y : Over (Spec (.of R)))
    (j' : U' ⟶ U) (j'' : U'' ⟶ U')
    (K : Scheme.QuasicoherentModules (pullback U.hom Y.hom)) :
    sourceChangeKernel R U U'' Y (j'' ≫ j') K ≅
      sourceChangeKernel R U' U'' Y j'' (sourceChangeKernel R U U' Y j' K) :=
  ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackCongr (sourceChangeMap_comp R U U' U'' Y j' j'').symm).app K.obj ≪≫
      ((Scheme.Modules.pullbackComp (sourceChangeMap R U' U'' Y j'')
        (sourceChangeMap R U U' Y j')).app K.obj).symm)

end AlgebraicGeometry

end
