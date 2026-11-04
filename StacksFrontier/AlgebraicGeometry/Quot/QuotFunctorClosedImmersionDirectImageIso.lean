module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionPushforwardUnconditional

/-!
# The direct image along a closed immersion is an isomorphism of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be a closed immersion of algebraic spaces which
are separated and of finite presentation over `B`, and let `F` be a quasi-coherent `𝒪_X`-module.
Then the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of Stacks 0DP1 is an isomorphism.

Over a test scheme `T` the morphism sends the quotient of `F_T` with kernel `K` to the kernel of
`G_T ⟶ π_{T,*}F_T ⟶ π_{T,*}(F_T/K)`, the first map being the base change map, an isomorphism by
Stacks 07U8.  That is the shape
`AlgebraicGeometry.Space.QuotPushforwardSituation.isIso_of_app_eq_kernelSubobject` treats.

## Main results

All in the namespace `AlgebraicGeometry.Space.QuotPushforwardSituation`:

* `isIso_directImageQuotFunctorMap_of_isClosedImmersion`: the morphism of Stacks 0DP1 is an
  isomorphism when `π` is a closed immersion.
* `isIso_pushforwardQuotFunctorMap_ofIsClosedImmersion`: the morphism `pushforwardQuotFunctorMap`
  of Stacks 0DP1 is an isomorphism for a closed immersion of algebraic spaces separated and of
  finite presentation over `B`.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- These two global instances leave universe constraints stuck against the modules of an
algebraic space. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

namespace QuotPushforwardSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotPushforwardSituation B S hS)

/-- The base change map `G_T ⟶ π_{T,*}F_T` is an isomorphism (Stacks 07U8). -/
theorem isIso_moduleBaseChangeMap_app_baseChangeOfMap (T : SchemesOver D.base) :
    IsIso ((moduleBaseChangeMap D.π (baseChangeProjection D.structureY T)
      (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
      (D.isPullback_baseChangeOfMap T).flip.w).app D.F) :=
  isIso_moduleBaseChangeMap_app_of_isAffineHom (D.isPullback_baseChangeOfMap T).flip
    D.affine D.F D.quasicoherent

/-- The base change map of the situation is the base change map of the cartesian square of
`π_T` over `π`. -/
theorem directImageBaseChange_eq (T : SchemesOver D.base) :
    D.directImageBaseChange T = moduleBaseChangeMap D.π (baseChangeProjection D.structureY T)
      (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
      (D.isPullback_baseChangeOfMap T).flip.w :=
  rfl

/-- Over a test scheme the morphism of Stacks 0DP1 sends a quotient to the kernel of the
projection of `G_T` onto its direct image. -/
theorem directImageQuotFunctorMap_app (H : D.PushforwardIsCoherent) (T : SchemesOver D.base)
    (K : D.sourceSituation.properlySupportedQuotients T) :
    ((D.directImageQuotFunctorMap H).app (Opposite.op T) K).1 =
      kernelSubobject ((moduleBaseChangeMap D.π (baseChangeProjection D.structureY T)
        (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
        (D.isPullback_baseChangeOfMap T).flip.w).app D.F ≫
          (modulePushforward B S hS (D.baseChangeOfMap T)).map
            (D.sourceSituation.quotientProjection T K.1)) := by
  change D.directImageQuotient T K.1 = _
  unfold directImageQuotient Functor.conjSubobjectOfHom Functor.conjQuotientProjectionOfHom
  rw [directImageBaseChange_eq]
  rfl

/-- The morphism of Stacks 0DP1 is an isomorphism when `π` is a closed immersion, for every proof
`H` that the direct image is coherent. -/
theorem isIso_directImageQuotFunctorMap_of_isClosedImmersion (H : D.PushforwardIsCoherent)
    (hπ : IsClosedImmersion B S hS D.π.hom) :
    IsIso (D.directImageQuotFunctorMap H) :=
  D.isIso_of_app_eq_kernelSubobject _ hπ _ _ D.isIso_moduleBaseChangeMap_app_baseChangeOfMap
    (D.directImageQuotFunctorMap_app H)

/-- Let `B` be an algebraic space, let `π : X ⟶ Y` be a closed immersion of algebraic spaces
which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module. Then the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of Stacks 0DP1 is an
isomorphism. -/
@[stacks 0DP4]
theorem isIso_pushforwardQuotFunctorMap_ofIsClosedImmersion (base X Y : AlgebraicSpaces B S hS)
    (π : X ⟶ Y) (hπ : IsClosedImmersion B S hS π.hom) (structureX : X ⟶ base)
    (structureY : Y ⟶ base) (comp : π ≫ structureY = structureX)
    (F : Modules.{u, u} B S hS X.1 X.2) (quasicoherent : F.IsQuasicoherentOnSite)
    (separatedX : IsSeparated B S hS structureX.hom)
    (separatedY : IsSeparated B S hS structureY.hom)
    (finitePresentationX : IsFinitePresentation B S hS structureX.hom)
    (finitePresentationY : IsFinitePresentation B S hS structureY.hom) :
    IsIso (ofIsClosedImmersion base X Y π hπ structureX structureY comp F quasicoherent
      separatedX separatedY finitePresentationX finitePresentationY).pushforwardQuotFunctorMap :=
  isIso_directImageQuotFunctorMap_of_isClosedImmersion _ _ hπ

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
