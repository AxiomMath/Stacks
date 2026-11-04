module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic

/-!
# The fibres of a morphism of `Coh_{X/B}` over a point

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, and let
`m : (T, 𝓕) ⟶ (T', 𝓕')` be a morphism of `Coh_{X/B}`: a morphism `h : T ⟶ T'` of schemes over `B`
together with an isomorphism `(X_h)^*𝓕' ≅ 𝓕`.  For a point `t ∈ T` with image `t' = h(t)`, the
residue field map `κ(t') ⟶ κ(t)` gives a morphism `Spec κ(t) ⟶ Spec κ(t')` of schemes over
`B`, lying over `h`.  This file records what that morphism does to the fibres that enter the
twisted Euler characteristics of Stacks 0DNF:

* the fibre `X_t` is the base change `X_{t'} ×_{Spec κ(t')} Spec κ(t)`;
* the pullback `𝓕_t` of `𝓕` to `X_t` is the pullback of `𝓕'_{t'}` along `X_t ⟶ X_{t'}`;
* the twist `(L^{⊗ n})_t` is the pullback of `(L^{⊗ n})_{t'}`, and so is the twisted module
  `𝓕_t ⊗ (L^{⊗ n})_t` whose cohomology is the twisted Euler characteristic.

These are the identifications by which the twisted Euler characteristic of `(T, 𝓕)` at `t` is
compared with that of `(T', 𝓕')` at `t'`: the comparison is flat base change of cohomology along
the field extension `κ(t') ⟶ κ(t)` (Stacks 073K, part (2)).

## Main definitions

* `AlgebraicGeometry.Space.CoherentHom.pointTestMap`: the morphism `Spec κ(t) ⟶ Spec κ(h(t))` of
  test schemes over `B` induced by a morphism of `Coh_{X/B}` at a point `t`.
* `AlgebraicGeometry.Space.CoherentHom.fibreMap`: the induced morphism of fibres
  `X_t ⟶ X_{h(t)}`.
* `AlgebraicGeometry.Space.CoherentHom.fibreModuleIso`: `𝓕_t ≅ (X_t ⟶ X_{h(t)})^* 𝓕'_{h(t)}`.
* `AlgebraicGeometry.Space.CoherentHom.fibreTwistIso`: the same for the pulled-back twists
  `(L^{⊗ n})_t`.
* `AlgebraicGeometry.Space.CoherentHom.fibreTwistedModuleIso`: the same for the twisted modules
  `𝓕_t ⊗ (L^{⊗ n})_t`.

## Main results

* `AlgebraicGeometry.Space.CoherentHom.pointTestMap_comp_pointTestHom`: the morphism of point
  test schemes lies over the morphism of test schemes.
* `AlgebraicGeometry.Space.CoherentHom.isPullback_fibreMap`: **the fibre `X_t` is
  `X_{h(t)} ×_{Spec κ(h(t))} Spec κ(t)`**, a cartesian square of algebraic spaces.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace CoherentHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {A A' : CoherentObject D}

/-- The morphism of schemes `Spec κ(t) ⟶ Spec κ(h(t))` induced by the residue field map of the
morphism `h` of test schemes underlying a morphism of `Coh_{X/B}`. -/
def pointSchemeMap (m : CoherentHom A A') (t : A.testScheme) :
    A.pointScheme t ⟶ A'.pointScheme (m.baseScheme t) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (m.baseScheme.residueFieldMap t))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (m.baseScheme.residueFieldMap t) ≫
        (A'.testScheme.fromSpecResidueField (m.baseScheme t) ≫ B.inclusion.map A'.T.left.hom) =
      A.testScheme.fromSpecResidueField t ≫ B.inclusion.map A.T.left.hom
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    change A.testScheme.fromSpecResidueField t ≫ B.inclusion.map m.base.left.left ≫
        B.inclusion.map A'.T.left.hom = _
    rw [← Functor.map_comp]
    exact congrArg (fun k => A.testScheme.fromSpecResidueField t ≫ B.inclusion.map k)
      (Over.w m.base.left))

/-- The morphism of point schemes lies over the morphism of test schemes:
`Spec κ(t) ⟶ Spec κ(h(t)) ⟶ T'` is `Spec κ(t) ⟶ T ⟶ T'`. -/
theorem pointSchemeMap_comp_pointSchemeHom (m : CoherentHom A A') (t : A.testScheme) :
    m.pointSchemeMap t ≫ A'.pointSchemeHom (m.baseScheme t) =
      A.pointSchemeHom t ≫ m.base.left :=
  Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <|
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField m.baseScheme t

/-- **The morphism `Spec κ(t) ⟶ Spec κ(h(t))` of test schemes over `B`** induced by a morphism of
`Coh_{X/B}` at a point `t` of the source test scheme. -/
def pointTestMap (m : CoherentHom A A') (t : A.testScheme) :
    A.pointTest t ⟶ A'.pointTest (m.baseScheme t) :=
  CostructuredArrow.homMk (m.pointSchemeMap t) (by
    change (schemeSpaceFunctor B S hS).map (m.pointSchemeMap t) ≫
        (schemeSpaceFunctor B S hS).map (A'.pointSchemeHom (m.baseScheme t)) ≫ A'.T.hom =
      (schemeSpaceFunctor B S hS).map (A.pointSchemeHom t) ≫ A.T.hom
    rw [← Category.assoc, ← Functor.map_comp, pointSchemeMap_comp_pointSchemeHom,
      Functor.map_comp, Category.assoc]
    congr 1
    exact CostructuredArrow.w m.base)

/-- **The morphism of point test schemes lies over the morphism of test schemes.** -/
theorem pointTestMap_comp_pointTestHom (m : CoherentHom A A') (t : A.testScheme) :
    m.pointTestMap t ≫ A'.pointTestHom (m.baseScheme t) = A.pointTestHom t ≫ m.base :=
  CostructuredArrow.hom_ext _ _ (pointSchemeMap_comp_pointSchemeHom m t)

/-- The morphism of fibres `X_t ⟶ X_{h(t)}` induced by a morphism of `Coh_{X/B}`. -/
abbrev fibreMap (m : CoherentHom A A') (t : A.testScheme) :
    A.fibreSpace t ⟶ A'.fibreSpace (m.baseScheme t) :=
  D.relativeMap (m.pointTestMap t)

/-- **The fibre over `t` is the base change of the fibre over `h(t)` along
`Spec κ(t) ⟶ Spec κ(h(t))`**: the square formed by `X_t ⟶ X_{h(t)}` and the two projections to
the point schemes is cartesian. -/
theorem isPullback_fibreMap (m : CoherentHom A A') (t : A.testScheme) :
    IsPullback (m.fibreMap t) (D.projection (A.pointTest t))
      (D.projection (A'.pointTest (m.baseScheme t)))
      ((schemeSpaceFunctor B S hS).map (m.pointSchemeMap t)) :=
  isPullback_baseChangeMap D.f (m.pointTestMap t)

/-- **The pullback of `𝓕` to the fibre over `t` is the pullback of `𝓕'_{h(t)}`** along
`X_t ⟶ X_{h(t)}`: both are pullbacks of `𝓕'` along `X_t ⟶ X_{T'}`, through the comparison
`(X_h)^*𝓕' ≅ 𝓕` of the morphism and the composition law of Stacks 03LU. -/
def fibreModuleIso (m : CoherentHom A A') (t : A.testScheme) :
    A.fibreModule t ≅
      (modulePullback B S hS (m.fibreMap t)).obj (A'.fibreModule (m.baseScheme t)) :=
  (modulePullback B S hS (D.relativeMap (A.pointTestHom t))).mapIso (asIso m.fibre).symm ≪≫
    (D.compComparison (A.pointTestHom t) m.base).symm.app A'.F ≪≫
    (D.relativeMapComparison (m.pointTestMap_comp_pointTestHom t).symm).app A'.F ≪≫
    (D.compComparison (m.pointTestMap t) (A'.pointTestHom (m.baseScheme t))).app A'.F

/-- **The twist pulled back to the fibre over `t` is the pullback of the twist pulled back to
the fibre over `h(t)`**: `X_t ⟶ X_{h(t)} ⟶ X` is the projection `X_t ⟶ X`. -/
def fibreTwistIso (m : CoherentHom A A') (t : A.testScheme)
    (M : Modules.{u, u} B S hS D.X.1 D.X.2) :
    (modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj M ≅
      (modulePullback B S hS (m.fibreMap t)).obj
        ((modulePullback B S hS (baseChangeProjection D.f (A'.pointTest (m.baseScheme t)))).obj
          M) :=
  (modulePullbackTriangle B S hS
    (baseChangeMap_comp_projection D.f (m.pointTestMap t))).app M

/-- **The twisted module on the fibre over `t` is the pullback of the twisted module on the
fibre over `h(t)`**: `𝓕_t ⊗ (L^{⊗ n})_t ≅ (X_t ⟶ X_{h(t)})^*(𝓕'_{h(t)} ⊗ (L^{⊗ n})_{h(t)})`,
by `fibreModuleIso`, `fibreTwistIso` and the compatibility of pullback with tensor products
(Stacks 03EL). -/
def fibreTwistedModuleIso (m : CoherentHom A A') (t : A.testScheme)
    (M : Modules.{u, u} B S hS D.X.1 D.X.2) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).obj
      ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj M) ≅
    (modulePullback B S hS (m.fibreMap t)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS (A'.fibreSpace (m.baseScheme t)).1
          (A'.fibreSpace (m.baseScheme t)).2).O).obj
          (A'.fibreModule (m.baseScheme t))).obj
        ((modulePullback B S hS
          (baseChangeProjection D.f (A'.pointTest (m.baseScheme t)))).obj M)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).mapIso
        (m.fibreModuleIso t)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj _).mapIso
        (m.fibreTwistIso t M) ≪≫
    (modulePullbackSheafTensorIso B S hS (m.fibreMap t) _ _).symm

end CoherentHom

end AlgebraicGeometry.Space

end
