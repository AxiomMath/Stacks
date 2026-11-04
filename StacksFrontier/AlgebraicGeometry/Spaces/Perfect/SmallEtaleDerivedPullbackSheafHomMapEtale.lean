module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMapStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackChartConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackProjectionBaseChange

/-!
# The map of Stacks 08I3 along an étale morphism of algebraic spaces, out of a perfect object

Let `u : U ⟶ Z` be an étale morphism of algebraic spaces, so that the derived pullback `Lu^*`
has the left adjoint `u_!` of extension by zero
(`AlgebraicGeometry.Space.etaleDerivedLowerShriekAdjunction`). For `W ∈ D(𝒪_U)` and
`A ∈ D(𝒪_Z)` the **projection map**

`π(W, A) : u_!(W ⊗^L Lu^*A) ⟶ u_!W ⊗^L A`

is the transpose of the unit followed by the comparison of Stacks 07A4
(`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.projectionMap`). This file proves the
**derived projection formula** for `u` at perfect `A`: `π(W, A)` is an isomorphism for every `W`.
Consequently the canonical map of Stacks 08I3 along `u`,

`Lu^*R𝓗om(K, L) ⟶ R𝓗om(Lu^*K, Lu^*L)`,

is an isomorphism for every perfect `K` and every `L`.

The proof is local on `Z`. Isomorphisms of `D(𝒪_Z)` are detected on the étale charts
`t : T ⟶ Z` of a covering
(`Space.isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace`), and a
perfect `A` has a strictly perfect model on the charts of a covering
(`AlgebraicGeometry.Space.exists_hasStrictlyPerfectModel_chart_of_isPerfect`). For such a chart,
base change to the fibre product `T' = T ×_Z U` carries `Lt^*π(W, A)` to the projection map of
the étale `u' : T' ⟶ T` at `(Lt'^*W, Lt^*A)`
(`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.isIso_map_projectionMap_of_baseChange`):
the base change map for extension by zero is invertible
(`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`) and the
comparisons of Stacks 07A4 around the square are compatible
(`AlgebraicGeometry.Space.tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso`). Since
`Lt^*A` has a strictly perfect model, the map of Stacks 08I3 along `u'` is invertible at it
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel`),
and so are the projection maps of `u'` there
(`DerivedInternalHomPullback.Transpose.isIso_projectionMap_of_isIso_homComparison`).

## Main results

* `AlgebraicGeometry.Space.squareIso_canonical_eq_squareCompositeIso`: the identification of the
  two composites around a commutative square used by the base change map for extension by zero
  is the one the compatibility of Stacks 07A4 around the square is stated for.
* `AlgebraicGeometry.Space.isMateOf_extensionByZeroBaseChange`: the base change map for extension
  by zero is the mate of that identification.
* `AlgebraicGeometry.Space.isIso_map_projectionMap_of_isPullback`: base change of the projection
  map along a cartesian square.
* `AlgebraicGeometry.Space.isIso_projectionMap_of_isEtale_of_isPerfect`: **the derived projection
  formula for an étale morphism of algebraic spaces**, at a perfect object.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale_of_isPerfect`:
  **the map of Stacks 08I3 along an étale morphism is invertible out of a perfect object.**

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U)
  (u : U ⟶ Z) (h : u' ≫ t = t' ≫ u)

/-- The identification of the two composites around a commutative square, for any
pseudofunctoriality datum, through the common composite `t' ≫ u` rather than `u' ≫ t`. -/
theorem DerivedPullbackComposition.squareIso_eq_iso_trans_iso_symm
    (P : DerivedPullbackComposition B S hS) :
    P.squareIso u' t t' u h = P.iso t' u (t' ≫ u) rfl ≪≫ (P.iso u' t (t' ≫ u) h).symm := by
  have key : ∀ (k : T' ⟶ Z) (hk : u' ≫ t = k),
      P.iso t' u (u' ≫ t) h.symm ≪≫ (P.iso u' t (u' ≫ t) rfl).symm =
        P.iso t' u k (h.symm.trans hk) ≪≫ (P.iso u' t k hk).symm := by
    intro k hk
    subst hk
    rfl
  exact key (t' ≫ u) h

/-- **The identification of the two composites around a commutative square used by the base
change map for extension by zero** (`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso`
for the canonical pseudofunctoriality datum) is the comparison
`Stacks.AffineProjectionFormula.squareCompositeIso` of the composition and square isomorphisms
of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModuleAdjunction.lean`, at which the
compatibility of Stacks 07A4 around the square is stated. -/
theorem squareIso_canonical_eq_squareCompositeIso :
    (DerivedPullbackComposition.canonical B S hS).squareIso u' t t' u h =
      Stacks.AffineProjectionFormula.squareCompositeIso
        (smallEtaleDerivedModulePullbackCompIso B S hS t' u)
        (smallEtaleDerivedModulePullbackSquareIso B S hS t u t' u' h) := by
  rw [DerivedPullbackComposition.squareIso_eq_iso_trans_iso_symm,
    smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso,
    smallEtaleDerivedModulePullbackSquareIso_eq_canonical_iso]
  rfl

/-- **The base change map for extension by zero is the mate of the identification of the two
composites around the square**, in the form
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.IsMateOf` consumes. -/
theorem isMateOf_extensionByZeroBaseChange (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) :
    Transpose.IsMateOf (etaleDerivedLowerShriekAdjunction B S hS u hu)
      (etaleDerivedLowerShriekAdjunction B S hS u' hu')
      (smallEtaleDerivedModulePullback B S hS t) (smallEtaleDerivedModulePullback B S hS t')
      ((DerivedPullbackComposition.canonical B S hS).squareIso u' t t' u h)
      ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu'
        h) :=
  fun W => (DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange_app
    u' t t' u hu hu' h W

/-- **Base change of the projection map along a cartesian square.** For a cartesian square
`u' ≫ t = t' ≫ u` with `u` étale, if the projection map of the étale `u'` at
`(Lt'^*W, Lt^*A)` is invertible, then `Lt^*` carries the projection map of `u` at `(W, A)` to
an isomorphism. -/
theorem isIso_map_projectionMap_of_isPullback (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom)
    (W : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U)))
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hπ : IsIso (Transpose.projectionMap (smallEtaleDerivedModulePullback B S hS u')
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS T))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS T'))
      (smallEtaleDerivedPullbackTensorIso u') (etaleDerivedLowerShriekAdjunction B S hS u' hu')
      ((smallEtaleDerivedModulePullback B S hS t').obj W)
      ((smallEtaleDerivedModulePullback B S hS t).obj A))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS t).map
      (Transpose.projectionMap (smallEtaleDerivedModulePullback B S hS u)
        (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
        (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U))
        (smallEtaleDerivedPullbackTensorIso u) (etaleDerivedLowerShriekAdjunction B S hS u hu)
        W A)) :=
  Transpose.isIso_map_projectionMap_of_baseChange_of_tensorComparisonCompatible
    (etaleDerivedLowerShriekAdjunction B S hS u hu)
    (etaleDerivedLowerShriekAdjunction B S hS u' hu')
    (smallEtaleDerivedModulePullback B S hS t) (smallEtaleDerivedModulePullback B S hS t')
    ((DerivedPullbackComposition.canonical B S hS).squareIso u' t t' u sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS T))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS T'))
    (smallEtaleDerivedPullbackTensorIso u) (smallEtaleDerivedPullbackTensorIso u')
    (smallEtaleDerivedPullbackTensorIso t) (smallEtaleDerivedPullbackTensorIso t')
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu' sq.w)
    (smallEtaleDerivedModulePullbackCompIso B S hS t' u)
    (smallEtaleDerivedModulePullbackSquareIso B S hS t u t' u' sq.w)
    (squareIso_canonical_eq_squareCompositeIso u' t t' u sq.w)
    (isMateOf_extensionByZeroBaseChange u' t t' u sq.w hu hu')
    (fun M N => tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso t u t' u' sq.w M N)
    W A (isIso_extensionByZeroBaseChange_canonical_app_of_isPullback u' t t' u sq hu hu' W)
    (isIso_extensionByZeroBaseChange_canonical_app_of_isPullback u' t t' u sq hu hu' _) hπ

end Square

section Etale

variable {U Z : AlgebraicSpaces B S hS} (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)

/-- **The derived projection formula for an étale morphism of algebraic spaces, at a perfect
object.** For `u : U ⟶ Z` étale and `A ∈ D(𝒪_Z)` perfect, the projection map
`u_!(W ⊗^L Lu^*A) ⟶ u_!W ⊗^L A` is an isomorphism for every `W ∈ D(𝒪_U)`. -/
theorem isIso_projectionMap_of_isEtale_of_isPerfect
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hA : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Z.1 Z.2) A)
    (W : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))) :
    IsIso (Transpose.projectionMap (smallEtaleDerivedModulePullback B S hS u)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U))
      (smallEtaleDerivedPullbackTensorIso u) (etaleDerivedLowerShriekAdjunction B S hS u hu)
      W A) := by
  refine isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace _
    fun V₀ => ?_
  obtain ⟨R, hR, hSP⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect A hA V₀
  refine ⟨R, hR, fun V g hg => ?_⟩
  have sq := IsPullback.of_hasPullback (chartToSpace B S hS Z V) u
  have hu' : IsEtale B S hS (pullback.fst (chartToSpace B S hS Z V) u).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sq.flip hu
  refine isIso_map_projectionMap_of_isPullback _ _ _ u sq hu hu' W A ?_
  refine Transpose.isIso_projectionMap_of_isIso_homComparison _
    (smallEtaleDerivedSheafHom B S hS _) (smallEtaleDerivedSheafHom B S hS _) _ _
    (smallEtaleTensorHomEquiv B S hS _) (smallEtaleTensorHomEquiv B S hS _) _ _
    (tensorHomEquivNaturalLeft_smallEtale B S hS _) (tensorHomEquivNaturalLeft_smallEtale B S hS _)
    _ (fun L => ?_) _
  exact isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel _ (hSP g hg) L

include hu in
/-- **The map of Stacks 08I3 along an étale morphism of algebraic spaces is invertible out of a
perfect object.** For `u : U ⟶ Z` étale, `K ∈ D(𝒪_Z)` perfect and `L ∈ D(𝒪_Z)`, the canonical
map `Lu^*R𝓗om(K, L) ⟶ R𝓗om(Lu^*K, Lu^*L)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale_of_isPerfect
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Z.1 Z.2) K)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap u K L) :=
  Transpose.isIso_homComparison_of_isIso_projectionMap (smallEtaleDerivedModulePullback B S hS u)
    (smallEtaleDerivedSheafHom B S hS Z) (smallEtaleDerivedSheafHom B S hS U)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Z))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS U))
    (smallEtaleTensorHomEquiv B S hS Z) (smallEtaleTensorHomEquiv B S hS U)
    (smallEtaleDerivedPullbackTensorIso u) (etaleDerivedLowerShriekAdjunction B S hS u hu)
    (tensorHomEquivNaturalLeft_smallEtale B S hS Z) (tensorHomEquivNaturalLeft_smallEtale B S hS U)
    K L (isIso_projectionMap_of_isEtale_of_isPerfect u hu K hK)

end Etale

end AlgebraicGeometry.Space

end
