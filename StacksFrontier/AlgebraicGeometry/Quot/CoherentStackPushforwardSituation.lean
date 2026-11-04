module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange

/-!
# The standing data of the direct image on stacks of coherent sheaves

Let `B` be an algebraic space and let `π : X ⟶ Y` be a quasi-finite morphism of algebraic spaces
which are separated and of finite presentation over `B`. This file defines the standing data of
the stacks `Coh_{X/B}` and `Coh_{Y/B}` of coherent sheaves with proper support, and for every test
scheme `T` over `B` the base change `π_T : X_T ⟶ Y_T` of `π`. For a morphism `h : T ⟶ T'` of test
schemes the square formed by `π_T`, `π_{T'}` and the two induced morphisms of base changes is
cartesian.

## Main definitions

* `AlgebraicGeometry.Space.CoherentPushforwardSituation`: a quasi-finite morphism `π : X ⟶ Y`
  of algebraic spaces separated and of finite presentation over `B`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.source` and
  `AlgebraicGeometry.Space.CoherentPushforwardSituation.target`: the coherent situations
  `X ⟶ B` and `Y ⟶ B`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.mapAt`: the base change
  `π_T : X_T ⟶ Y_T`.

## Main results

* `AlgebraicGeometry.Space.CoherentPushforwardSituation.relativeMap_comp_mapAt`: the
  base changes of `π` commute with the morphisms of base changes induced by a morphism of test
  schemes, and `AlgebraicGeometry.Space.CoherentPushforwardSituation.isPullback_relativeMap`: the
  resulting square is cartesian.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.isLocallyQuasiFinite_mapAt` and
  `AlgebraicGeometry.Space.CoherentPushforwardSituation.isSeparated_targetProjection`: `π_T` is
  locally quasi-finite and `Y_T ⟶ T` is separated.

## References

* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A quasi-finite morphism `π : X ⟶ Y` of algebraic spaces over `S` which are separated and of
finite presentation over an algebraic space `base`. The structure morphism of `X` is the
composite `π ≫ f`. -/
structure CoherentPushforwardSituation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- The base algebraic space `B`. -/
  base : AlgebraicSpaces B S hS
  /-- The source of the morphism. -/
  X : AlgebraicSpaces B S hS
  /-- The target of the morphism. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism `π : X ⟶ Y`. -/
  π : X ⟶ Y
  /-- The structure morphism `Y ⟶ B`. -/
  f : Y ⟶ base
  /-- `π` is quasi-finite. -/
  quasiFinite : IsQuasiFinite B S hS π.hom
  /-- `X` is separated over `B`. -/
  separated_source : IsSeparated B S hS (π ≫ f).hom
  /-- `X` is of finite presentation over `B`. -/
  finitePresentation_source : IsFinitePresentation B S hS (π ≫ f).hom
  /-- `Y` is separated over `B`. -/
  separated_target : IsSeparated B S hS f.hom
  /-- `Y` is of finite presentation over `B`. -/
  finitePresentation_target : IsFinitePresentation B S hS f.hom

namespace CoherentPushforwardSituation

variable (D : CoherentPushforwardSituation B S hS)

/-- The coherent situation `X ⟶ B`, whose category is `Coh_{X/B}`. -/
abbrev source : CoherentSituation B S hS :=
  ⟨D.X, D.base, D.π ≫ D.f, D.finitePresentation_source⟩

/-- The coherent situation `Y ⟶ B`, whose category is `Coh_{Y/B}`. -/
abbrev target : CoherentSituation B S hS :=
  ⟨D.Y, D.base, D.f, D.finitePresentation_target⟩

/-- The base change `π_T : X_T ⟶ Y_T` of `π` to a test scheme `T` over `B`. -/
def mapAt (T : SchemesOver D.base) : D.source.space T ⟶ D.target.space T :=
  D.target.baseChangeOfMap (π := D.π) (bX := D.π ≫ D.f) rfl T

/-- `π_T` lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem mapAt_comp_inclusion (T : SchemesOver D.base) :
    D.mapAt T ≫ baseChangeInclusion D.f T = baseChangeInclusion (D.π ≫ D.f) T :=
  D.target.baseChangeOfMap_comp_inclusion rfl T

/-- `π_T` lies over `T`: it commutes with the projections of `X_T` and `Y_T` to `T`. -/
theorem mapAt_comp_projection (T : SchemesOver D.base) :
    D.mapAt T ≫ D.target.projection T = D.source.projection T :=
  D.mapAt_comp_inclusion T

/-- `π_T` lies over `π`. -/
@[reassoc (attr := simp)]
theorem mapAt_comp_baseChangeProjection (T : SchemesOver D.base) :
    D.mapAt T ≫ baseChangeProjection D.f T = baseChangeProjection (D.π ≫ D.f) T ≫ D.π :=
  D.target.baseChangeOfMap_comp_projection rfl T

/-- For a morphism `h : T ⟶ T'` of test schemes over `B`, `X_h ≫ π_{T'} = π_T ≫ Y_h`. -/
@[reassoc]
theorem relativeMap_comp_mapAt {T T' : SchemesOver D.base} (h : T ⟶ T') :
    D.source.relativeMap h ≫ D.mapAt T' = D.mapAt T ≫ D.target.relativeMap h := by
  refine baseChange_hom_ext D.f ?_ ?_
  · simp only [Category.assoc, mapAt_comp_baseChangeProjection,
      Space.baseChangeMap_comp_projection, Space.baseChangeMap_comp_projection_assoc]
  · simp only [Category.assoc, mapAt_comp_inclusion, Space.baseChangeMap_comp_inclusion,
      mapAt_comp_inclusion_assoc]

/-- `X_T` is the fibre product of `Y_T` and `X` over `Y`. -/
theorem isPullback_mapAt (T : SchemesOver D.base) :
    IsPullback (D.mapAt T).hom (baseChangeProjection (D.π ≫ D.f) T).hom
      (baseChangeProjection D.f T).hom D.π.hom :=
  D.target.isPullback_baseChangeOfMap rfl T

/-- For a morphism `h : T ⟶ T'` of test schemes over `B`, `X_T` is the fibre product of `X_{T'}`
and `Y_T` over `Y_{T'}`. -/
theorem isPullback_relativeMap {T T' : SchemesOver D.base} (h : T ⟶ T') :
    IsPullback (D.source.relativeMap h) (D.mapAt T) (D.mapAt T')
      (D.target.relativeMap h) := by
  refine IsPullback.of_bot ?_ (D.relativeMap_comp_mapAt h)
    (Space.isPullback_baseChangeMap D.f h)
  rw [mapAt_comp_inclusion, mapAt_comp_inclusion]
  exact Space.isPullback_baseChangeMap (D.π ≫ D.f) h

/-- `π_T` is locally quasi-finite. -/
theorem isLocallyQuasiFinite_mapAt (T : SchemesOver D.base) :
    IsLocallyQuasiFinite B S hS (D.mapAt T).hom :=
  IsLocallyQuasiFinite.of_isPullback B S hS (D.isPullback_mapAt T) D.X.2 D.Y.2 D.quasiFinite.1

/-- `Y_T ⟶ T` is separated. -/
theorem isSeparated_targetProjection (T : SchemesOver D.base) :
    IsSeparated B S hS (D.target.projection T).hom :=
  isSeparated_pullbackSnd B S hS T.hom.hom D.separated_target

end CoherentPushforwardSituation

end AlgebraicGeometry.Space

end
