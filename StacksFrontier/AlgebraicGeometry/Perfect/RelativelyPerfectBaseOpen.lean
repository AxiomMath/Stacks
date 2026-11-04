module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso

/-!
# Relative perfectness over an open of the base

Let `j : W ⟶ S` be an open immersion of schemes and `g : X ⟶ W` a morphism, so that
`f = g ≫ j : X ⟶ S` factors through `W`. The inverse-image ringed spaces `(X, g⁻¹𝒪_W)` and
`(X, f⁻¹𝒪_S)` are isomorphic, by the morphism the functor
`AlgebraicGeometry.RingedSpace.inverseImageArrow` attaches to the square `(𝟙 X, j)`, and the
naturality of `AlgebraicGeometry.RingedSpace.inverseImageArrowUnit` identifies derived
restriction of scalars along `f` with derived restriction of scalars along `g` followed by the
derived pullback along that isomorphism. Consequently the Tor-dimension clause of Stacks 0DI0,
and relative perfectness itself, are the same over `S` and over `W`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.baseOpenInverseImageIso`: the isomorphism
  `(X, (g ≫ j)⁻¹𝒪_S) ≅ (X, g⁻¹𝒪_W)` for an open immersion `j`.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionBaseOpenIso`: derived restriction of
  scalars along `g ≫ j` is derived pullback along that isomorphism of derived restriction of
  scalars along `g`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_baseOpen_iff`: the Tor-dimension
  clause of Stacks 0DI0, at the canonical certificate family, over `S` and over `W`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_baseOpen_iff`: relative perfectness over `S`
  and over `W`.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

variable (S : RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ S.carrier)

/-- Lifts of morphisms agree when their underlying maps and the lifted morphisms agree. -/
theorem inverseImageLiftOfHom_congr₂ {V : RingedSpace.{u, u}} {g g' : V.carrier ⟶ Z}
    (hg : g = g') {q q' : V ⟶ S} (hqq : q = q') (hq : q.hom.base = g ≫ i)
    (hq' : q'.hom.base = g' ≫ i) :
    inverseImageLiftOfHom S i V g q hq = inverseImageLiftOfHom S i V g' q' hq' := by
  subst hg hqq
  rfl

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X W S : Scheme.{u}} (g : X ⟶ W) (j : W ⟶ S) [IsOpenImmersion j]

/-- An open immersion of schemes, read as a morphism of ringed spaces. -/
def ringedOpenImmersion : W.toRingedSpace ⟶ S.toRingedSpace :=
  Scheme.forgetToRingedSpace.map j

/-- The open immersion `j`, read as a morphism of ringed spaces, is an open immersion. -/
instance : SheafedSpace.IsOpenImmersion (ringedOpenImmersion j) :=
  show LocallyRingedSpace.IsOpenImmersion j.toLRSHom from inferInstance

/-- The square `(𝟙 X, j)` from `g` to `g ≫ j` in the arrow category of ringed spaces. -/
def baseOpenArrowHom : ringedArrow g ⟶ ringedArrow (g ≫ j) :=
  Arrow.homMk (𝟙 _) (Scheme.forgetToRingedSpace.map j)
    (by rw [Category.id_comp]; exact Scheme.forgetToRingedSpace.map_comp g j)

/-- The comparison `(X, g⁻¹𝒪_W) ⟶ (X, (g ≫ j)⁻¹𝒪_S)` of inverse-image ringed spaces. -/
def baseOpenInverseImageMap :
    RingedSpace.inverseImage W.toRingedSpace g.base ⟶
      RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base :=
  inverseImageArrow.map (baseOpenArrowHom g j)

omit [IsOpenImmersion j] in
/-- The comparison `baseOpenInverseImageMap g j` is the lift to `(X, (g ≫ j)⁻¹𝒪_S)` of the
projection of `(X, g⁻¹𝒪_W)` followed by `j`. -/
theorem baseOpenInverseImageMap_eq :
    baseOpenInverseImageMap g j =
      inverseImageLiftOfHom S.toRingedSpace (g ≫ j).base
        (RingedSpace.inverseImage W.toRingedSpace g.base) (𝟙 _)
        (inverseImageProjection W.toRingedSpace g.base ≫ ringedOpenImmersion j)
        (arrow_base_comm (baseOpenArrowHom g j)) :=
  rfl

omit [IsOpenImmersion j] in
/-- The comparison `baseOpenInverseImageMap g j`, followed by the projection of
`(X, (g ≫ j)⁻¹𝒪_S)`, is the projection of `(X, g⁻¹𝒪_W)` followed by `j`. -/
theorem baseOpenInverseImageMap_comp_projection :
    baseOpenInverseImageMap g j ≫ inverseImageProjection S.toRingedSpace (g ≫ j).base =
      inverseImageProjection W.toRingedSpace g.base ≫ ringedOpenImmersion j :=
  inverseImageArrowMap_comp_projection (baseOpenArrowHom g j)

omit [IsOpenImmersion j] in
/-- The range of the projection of `(X, (g ≫ j)⁻¹𝒪_S)` lies in the range of `j`. -/
theorem range_projection_subset :
    Set.range (inverseImageProjection S.toRingedSpace (g ≫ j).base).hom.base ⊆
      Set.range (ringedOpenImmersion j).hom.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨g.base x, ?_⟩
  show j.base (g.base x) = (g ≫ j).base x
  rw [Scheme.Hom.comp_base]
  rfl

/-- The projection of `(X, (g ≫ j)⁻¹𝒪_S)` factored through the open immersion `j`. -/
def baseOpenProjectionLift :
    RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base ⟶ W.toRingedSpace :=
  InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift (ringedOpenImmersion j).hom
    (inverseImageProjection S.toRingedSpace (g ≫ j).base).hom (range_projection_subset g j))

/-- The lift `baseOpenProjectionLift g j`, followed by `j`, is the projection of
`(X, (g ≫ j)⁻¹𝒪_S)`. -/
theorem baseOpenProjectionLift_comp :
    baseOpenProjectionLift g j ≫ ringedOpenImmersion j =
      inverseImageProjection S.toRingedSpace (g ≫ j).base :=
  InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac (ringedOpenImmersion j).hom
    (inverseImageProjection S.toRingedSpace (g ≫ j).base).hom (range_projection_subset g j))

/-- The underlying map of `baseOpenProjectionLift g j` is that of `g`. -/
theorem baseOpenProjectionLift_base :
    (baseOpenProjectionLift g j).hom.base = g.base := by
  have : Mono j.base := (TopCat.mono_iff_injective _).2 j.isOpenEmbedding.injective
  refine (cancel_mono j.base).1 ?_
  exact (congrArg (fun t => t.hom.base) (baseOpenProjectionLift_comp g j)).trans
    (Scheme.Hom.comp_base g j)

/-- The inverse of `baseOpenInverseImageMap`. -/
def baseOpenInverseImageInv :
    RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base ⟶
      RingedSpace.inverseImage W.toRingedSpace g.base :=
  inverseImageLiftOfHom W.toRingedSpace g.base _ (𝟙 _) (baseOpenProjectionLift g j)
    ((baseOpenProjectionLift_base g j).trans (Category.id_comp _).symm)

/-- The morphism `baseOpenInverseImageInv g j`, followed by the projection of `(X, g⁻¹𝒪_W)`, is
`baseOpenProjectionLift g j`. -/
theorem baseOpenInverseImageInv_comp_projection :
    baseOpenInverseImageInv g j ≫ inverseImageProjection W.toRingedSpace g.base =
      baseOpenProjectionLift g j :=
  inverseImageLiftOfHom_comp_projection _ _ _ _ _ _

/-- The morphism `baseOpenInverseImageInv g j`, followed by the projection of `(X, g⁻¹𝒪_W)` and by
`j`, is the projection of `(X, (g ≫ j)⁻¹𝒪_S)`. -/
theorem baseOpenInverseImageInv_comp_projection_comp :
    baseOpenInverseImageInv g j ≫ inverseImageProjection W.toRingedSpace g.base ≫
        ringedOpenImmersion j =
      inverseImageProjection S.toRingedSpace (g ≫ j).base := by
  rw [← Category.assoc, baseOpenInverseImageInv_comp_projection, baseOpenProjectionLift_comp]

/-- The comparison `baseOpenInverseImageMap g j`, followed by `baseOpenProjectionLift g j`, is the
projection of `(X, g⁻¹𝒪_W)`. -/
theorem baseOpenInverseImageMap_comp_lift :
    baseOpenInverseImageMap g j ≫ baseOpenProjectionLift g j =
      inverseImageProjection W.toRingedSpace g.base := by
  rw [← cancel_mono (ringedOpenImmersion j), Category.assoc, baseOpenProjectionLift_comp,
    baseOpenInverseImageMap_comp_projection]

/-- A morphism `γ` out of `(Z, i⁻¹𝒪_S)` whose composite with `q` is the projection, followed by
the lift of `q` along the identity of `Z`, is the identity. -/
private theorem comp_inverseImageLiftOfHom_eq_id {S T : RingedSpace.{u, u}} {Z : TopCat.{u}}
    (i : Z ⟶ S.carrier) (k : Z ⟶ T.carrier) (γ : RingedSpace.inverseImage S i ⟶
      RingedSpace.inverseImage T k) (q : RingedSpace.inverseImage T k ⟶ S)
    (hq : q.hom.base = 𝟙 Z ≫ i) (hγ : γ.hom.base = 𝟙 Z) (h : γ ≫ q = inverseImageProjection S i) :
    γ ≫ inverseImageLiftOfHom S i (RingedSpace.inverseImage T k) (𝟙 _) q hq = 𝟙 _ := by
  refine (comp_inverseImageLiftOfHom _ _ _ _ γ _ _
    ((congrArg (fun t => t.hom.base) h).trans (by simp [hγ]))).trans ?_
  refine (inverseImageLiftOfHom_congr₂ S i ((Category.comp_id _).trans hγ) h _ rfl).trans ?_
  exact inverseImageLiftOfHom_projection_eq_id _ _ rfl

/-- The morphism `baseOpenInverseImageInv g j`, followed by `baseOpenInverseImageMap g j`, is the
identity. -/
theorem baseOpenInverseImageInv_comp_map :
    baseOpenInverseImageInv g j ≫ baseOpenInverseImageMap g j = 𝟙 _ := by
  rw [baseOpenInverseImageMap_eq]
  exact comp_inverseImageLiftOfHom_eq_id _ _ _ _ _ rfl
    (baseOpenInverseImageInv_comp_projection_comp g j)

/-- The comparison `baseOpenInverseImageMap g j`, followed by `baseOpenInverseImageInv g j`, is the
identity. -/
theorem baseOpenInverseImageMap_comp_inv :
    baseOpenInverseImageMap g j ≫ baseOpenInverseImageInv g j = 𝟙 _ :=
  comp_inverseImageLiftOfHom_eq_id _ _ _ _ _ rfl (baseOpenInverseImageMap_comp_lift g j)

/-- **The inverse-image ringed spaces over `S` and over an open `W` through which the morphism
factors agree**: `(X, (g ≫ j)⁻¹𝒪_S) ≅ (X, g⁻¹𝒪_W)` for an open immersion `j`. -/
def baseOpenInverseImageIso :
    RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base ≅
      RingedSpace.inverseImage W.toRingedSpace g.base where
  hom := baseOpenInverseImageInv g j
  inv := baseOpenInverseImageMap g j
  hom_inv_id := baseOpenInverseImageInv_comp_map g j
  inv_hom_id := baseOpenInverseImageMap_comp_inv g j

/-- The unit of `g ≫ j` is the unit of `g` followed by the comparison of inverse-image ringed
spaces. -/
theorem arrowUnit_comp_eq :
    arrowUnit (g ≫ j) = arrowUnit g ≫ (baseOpenInverseImageIso g j).inv :=
  (Category.id_comp _).symm.trans (inverseImageArrowUnit.naturality (baseOpenArrowHom g j))

/-- **Restriction of scalars along `g ≫ j` is restriction of scalars along `g` followed by
pullback along the comparison of inverse-image ringed spaces.** -/
def scalarRestrictionBaseOpenIso :
    modulePushforward (arrowUnit (g ≫ j)) ≅
      modulePushforward (arrowUnit g) ⋙ modulePullback (baseOpenInverseImageIso g j).hom :=
  eqToIso (congrArg modulePushforward (arrowUnit_comp_eq g j)) ≪≫
    (Stacks.RingedSpace.modulePushforwardComp (arrowUnit g)
      (baseOpenInverseImageIso g j).inv).symm ≪≫
    Functor.isoWhiskerLeft _
      (modulePullbackIsoPushforwardInv (baseOpenInverseImageIso g j)).symm

/-- **Derived restriction of scalars over an open of the base**, in the pushforward spelling. -/
def derivedScalarRestrictionBaseOpenIso'
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (modulePushforward (arrowUnit (g ≫ j))).mapDerivedCategory.obj E ≅
      (derivedPullback (baseOpenInverseImageIso g j).hom).obj
        ((modulePushforward (arrowUnit g)).mapDerivedCategory.obj E) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (scalarRestrictionBaseOpenIso g j)).app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).app E ≪≫
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategory
      (baseOpenInverseImageIso g j)).symm.app _

/-- **Derived restriction of scalars along `g ≫ j` is derived pullback along the comparison of
inverse-image ringed spaces of derived restriction of scalars along `g`.** -/
def derivedScalarRestrictionBaseOpenIso (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (derivedScalarRestriction (g ≫ j)).obj E ≅
      (derivedPullback (baseOpenInverseImageIso g j).hom).obj
        ((derivedScalarRestriction g).obj E) := by
  rw [derivedScalarRestriction_eq_mapDerivedCategory (g ≫ j),
    derivedScalarRestriction_eq_mapDerivedCategory g]
  exact derivedScalarRestrictionBaseOpenIso' g j E

/-- **The Tor-dimension clause of Stacks 0DI0 over an open of the base.** For an open immersion
`j : W ⟶ S`, `g : X ⟶ W` with `X` quasi-compact, and `E` in `D(𝒪_X)`, derived restriction of
scalars along `g ≫ j` locally has finite Tor dimension on `(X, (g ≫ j)⁻¹𝒪_S)` exactly when
derived restriction of scalars along `g` does on `(X, g⁻¹𝒪_W)`, at the canonical certificate
families. -/
theorem locallyHasFiniteTorDimension_baseOpen_comp_iff [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    RingedSpace.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage S.toRingedSpace (g ≫ j).base)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedScalarRestriction (g ≫ j)).obj E) ↔
      RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage W.toRingedSpace g.base)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedScalarRestriction g).obj E) :=
  ⟨fun h => (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff
      (baseOpenInverseImageIso g j) _).1
      (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso
        (derivedScalarRestrictionBaseOpenIso g j E) h),
    fun h => RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso
      (derivedScalarRestrictionBaseOpenIso g j E).symm
      ((RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff
        (baseOpenInverseImageIso g j) _).2 h)⟩

/-- **The Tor-dimension clause of Stacks 0DI0 over an open of the base**, for a morphism
`f = g ≫ j` factoring through the open immersion `j`. -/
theorem locallyHasFiniteTorDimension_baseOpen_iff [CompactSpace X.carrier] {f : X ⟶ S}
    (hf : g ≫ j = f) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage S.toRingedSpace f.base)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedScalarRestriction f).obj E) ↔
      RingedSpace.LocallyHasFiniteTorDimension (RingedSpace.inverseImage W.toRingedSpace g.base)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedScalarRestriction g).obj E) := by
  subst hf
  exact locallyHasFiniteTorDimension_baseOpen_comp_iff g j E

/-- **Relative perfectness over an open of the base.** For an open immersion `j : W ⟶ S` and a
flat morphism `g : X ⟶ W` locally of finite presentation with `X` quasi-compact, an object of
`D(𝒪_X)` is perfect relative to `S` along `f = g ≫ j` exactly when it is perfect relative to `W`
along `g`, at the canonical certificate families. -/
theorem isPerfectRelativeTo_baseOpen_iff [CompactSpace X.carrier] {f : X ⟶ S} (hf : g ≫ j = f)
    [Flat f] [LocallyOfFinitePresentation f] [Flat g] [LocallyOfFinitePresentation g]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E ↔
      g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  and_congr Iff.rfl (locallyHasFiniteTorDimension_baseOpen_iff g j hf E)

end AlgebraicGeometry.Scheme.Hom

end
