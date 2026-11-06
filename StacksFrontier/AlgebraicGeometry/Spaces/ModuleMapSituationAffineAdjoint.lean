module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs

/-!
# Stacks 0CW7, unconditionally

In Situation Stacks 083F, let `i : Z ⟶ X` be an affine morphism of algebraic spaces, `H` a
quasi-coherent `𝒪_Z`-module with `G = i_*H`, and `v : i^*F ⟶ H` the adjoint of `u : F ⟶ G`.
Stacks 0CW7 asserts `F_{v,zero} = F_{u,zero}`, and `F_{v,surj} = F_{u,surj}` when `i` is a closed
immersion.

`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffine` proves both parts from two
inputs at each test scheme `T`:
`AlgebraicGeometry.Space.AffineAdjointData.AdjointAfterBaseChange` (the source's "`u_T` and `v_T`
are adjoint maps as well") and, for part (2),
`AlgebraicGeometry.Space.AffineAdjointData.ClosedImmersionSurjectivityInput`.  This file proves
both inputs, and so both parts with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.Space.homEquiv_comp_moduleBaseChangeMap`: for any commutative square, the
  inverse image of an adjoint `u` followed by the base change map `g^*f_* ⟶ f'_*(g')^*` is the
  adjoint of the inverse image of `v`, read through the comparison of composite inverse images.
* `AlgebraicGeometry.Space.exists_iso_comp_eq_homEquiv_of_isAffineHom`: for a cartesian square
  with `f` affine, the same with the base change map invertible (Stacks 07U8,
  `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineHom`).
* `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_affinePushforwardBaseChange`: the square
  of `g` and its base change `g_T` is cartesian.
* `AlgebraicGeometry.Space.AffineAdjointData.adjointAfterBaseChange` and
  `AlgebraicGeometry.Space.AffineAdjointData.closedImmersionSurjectivityInput`: the two inputs.
* `AlgebraicGeometry.Space.AffineAdjointData.zeroFunctor_adjointSituation_eq_of_isAffineHom` and
  `AlgebraicGeometry.Space.AffineAdjointData.surjFunctor_adjointSituation_eq_of_isClosedImmersion`:
  **Stacks 0CW7, parts (1) and (2)**.

## Implementation notes

The quasi-coherence of `i^*F` and `i_*H`, which the two situations carry as fields, is not
assumed: it is Stacks 03GA and Stacks 03M9, an affine morphism being quasi-compact and
quasi-separated.

The cartesian square of `i` and `i_T` is stated with its four objects written out
(`AlgebraicGeometry.Space.AffineAdjointData.isPullback_baseChangeImmersion`).  Left implicit,
they elaborate as fields of the two situations rather than as `Z` and `X`, and matching those
against the statement of `AdjointAfterBaseChange` exhausts the unifier.

## References

* [Stacks Project, Tag 0CW7](https://stacks.math.columbia.edu/tag/0CW7)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ModuleMapSituationAffineAdjoint :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ModuleMapSituationAffineAdjoint
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_ModuleMapSituationAffineAdjoint.has_limit _

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)

/-- **The base change map turns adjoints into adjoints.**  For a commutative square and a map
`v : f^*F ⟶ H` with adjoint `u : F ⟶ f_*H`, the inverse image `g^*u` followed by the base change
map `g^*f_*H ⟶ f'_*(g')^*H` is the adjoint, under `(f')^* ⊣ f'_*`, of `(g')^*v` precomposed with
the comparison `(f')^*g^*F ≅ (g')^*f^*F` of the two composite inverse images. -/
theorem homEquiv_comp_moduleBaseChangeMap {F : Modules.{u, u} B S hS Y.1 Y.2}
    {H : Modules.{u, u} B S hS X.1 X.2} (v : (modulePullback B S hS f).obj F ⟶ H) :
    (modulePullback B S hS g).map ((modulePullbackAdjunction B S hS f).homEquiv F H v) ≫
        (moduleBaseChangeMap f g f' g' comm).app H =
      (modulePullbackAdjunction B S hS f').homEquiv _ _
        ((modulePullbackSquareComparison f g f' g' comm).inv.app F ≫
          (modulePullback B S hS g').map v) := by
  apply ((modulePullbackAdjunction B S hS f').homEquiv _ _).symm.injective
  have hsplit := moduleBaseChangeMap_adjoint_split f g f' g' comm H
  dsimp only [Functor.comp_obj] at hsplit
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm, hsplit]
  have hnat := (modulePullbackSquareComparison f g f' g' comm).inv.naturality
    ((modulePullbackAdjunction B S hS f).homEquiv F H v)
  dsimp only [Functor.comp_map] at hnat
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp]
  congr 2
  simp [Adjunction.homEquiv_unit]

/-- **Affine base change turns adjoints into adjoints.**  For a cartesian square with `f`
affine, a quasi-coherent `H` and a map `v : f^*F ⟶ H` with adjoint `u : F ⟶ f_*H`, the
inverse image `g^*u`, read through the base change isomorphism `g^*f_*H ≅ f'_*(g')^*H` of
Stacks 07U8, is the adjoint of `(g')^*v`, read through the comparison
`(f')^*g^*F ≅ (g')^*f^*F` of the two composite inverse images. -/
theorem exists_iso_comp_eq_homEquiv_of_isAffineHom (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) {F : Modules.{u, u} B S hS Y.1 Y.2}
    {H : Modules.{u, u} B S hS X.1 X.2} (hH : H.IsQuasicoherentOnSite)
    (v : (modulePullback B S hS f).obj F ⟶ H) :
    ∃ (a : (modulePullback B S hS f').obj ((modulePullback B S hS g).obj F) ≅
        (modulePullback B S hS g').obj ((modulePullback B S hS f).obj F))
      (b : (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj H) ≅
        (modulePushforward B S hS f').obj ((modulePullback B S hS g').obj H)),
      (modulePullback B S hS g).map ((modulePullbackAdjunction B S hS f).homEquiv F H v) ≫
          b.hom =
        (modulePullbackAdjunction B S hS f').homEquiv _ _
          (a.hom ≫ (modulePullback B S hS g').map v) :=
  have := isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf H hH
  ⟨(modulePullbackSquareComparison f g f' g' sq.w).symm.app F,
    asIso ((moduleBaseChangeMap f g f' g' sq.w).app H),
    homEquiv_comp_moduleBaseChangeMap f g f' g' sq.w v⟩

end Square

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : D.X ⟶ X')
  (f' : X' ⟶ D.Y) (comm : g ≫ f' = D.f) (T : D.SchemesOver)

/-- The morphism `g_T` lies over `g`. -/
theorem affinePushforwardBaseChange_comp_fst :
    D.affinePushforwardBaseChange g f' comm T ≫
        ObjectProperty.homMk (pullback.fst f'.hom T.hom.hom) =
      D.baseChangeProjection T ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f' T.hom).lift_fst _ _ _

/-- The square formed by `g_T : X ×_Y T ⟶ X' ×_Y T` over `g : X ⟶ X'` is cartesian. -/
theorem isPullback_affinePushforwardBaseChange :
    IsPullback (D.baseChangeProjection T) (D.affinePushforwardBaseChange g f' comm T) g
      (ObjectProperty.homMk (pullback.fst f'.hom T.hom.hom)) := by
  have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS f' T.hom
  have hsnd : D.affinePushforwardBaseChange g f' comm T ≫
      ObjectProperty.homMk (pullback.snd f'.hom T.hom.hom) = D.baseChangeInclusion T :=
    hp.lift_snd _ _ _
  have houter : IsPullback (D.affinePushforwardBaseChange g f' comm T ≫
      ObjectProperty.homMk (pullback.snd f'.hom T.hom.hom)) (D.baseChangeProjection T)
      T.hom (g ≫ f') := by
    rw [hsnd, comm]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).flip
  exact (IsPullback.of_right houter
    (D.affinePushforwardBaseChange_comp_fst g f' comm T)
    hp.flip).flip

end ModuleMapSituation

namespace AffineAdjointData

variable (A : AffineAdjointData.{u} B S hS)
  (hqcF : ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite)
  (hqcH : ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite)
  (T : (A.sourceSituation hqcH).SchemesOver)

/-- The base change `i_T : Z ×_Y T ⟶ X ×_Y T` of `i`. -/
abbrev baseChangeImmersion :
    (A.adjointSituation hqcF).baseChangeSpace T ⟶ (A.sourceSituation hqcH).baseChangeSpace T :=
  (A.adjointSituation hqcF).affinePushforwardBaseChange A.i A.f rfl T

/-- The square of `i` and its base change `i_T` is cartesian. -/
theorem isPullback_baseChangeImmersion :
    @IsPullback (AlgebraicSpaces B S hS) _ ((A.adjointSituation hqcF).baseChangeSpace T) A.Z
      ((A.sourceSituation hqcH).baseChangeSpace T) A.X
      ((A.adjointSituation hqcF).baseChangeProjection T)
      (A.baseChangeImmersion hqcF hqcH T) A.i ((A.sourceSituation hqcH).baseChangeProjection T) :=
  (A.adjointSituation hqcF).isPullback_affinePushforwardBaseChange A.i A.f rfl T

/-- **`u_T` and `v_T` are adjoint**, for an affine `i`: the base change `i_T` exhibits `u_T` as
the adjoint of `v_T`, through the comparison of the two composite inverse images and the affine
base change isomorphism `p^*(i_*H) ≅ i_{T,*}(q^*H)` of Stacks 07U8. -/
theorem isAdjointAfterBaseChange (hi : IsAffineHom B S hS A.i.hom) :
    A.IsAdjointAfterBaseChange hqcF hqcH T (A.baseChangeImmersion hqcF hqcH T) :=
  exists_iso_comp_eq_homEquiv_of_isAffineHom _ _ _ _
    (A.isPullback_baseChangeImmersion hqcF hqcH T) hi A.quasicoherent_H A.v

/-- **The input `AlgebraicGeometry.Space.AffineAdjointData.AdjointAfterBaseChange` of Stacks 0CW7,
proved**, for an affine `i`. -/
theorem adjointAfterBaseChange (hi : IsAffineHom B S hS A.i.hom) :
    A.AdjointAfterBaseChange hqcF hqcH T :=
  ⟨_, A.isAdjointAfterBaseChange hqcF hqcH T hi⟩

/-- **The input `AlgebraicGeometry.Space.AffineAdjointData.ClosedImmersionSurjectivityInput` of
Stacks 0CW7, proved**, for a closed immersion `i`, at the base change `i_T`.  The base change
`i_T` is a closed immersion (Stacks 03WI for closed immersions); the unit of `i_T^* ⊣ i_{T,*}` is
an epimorphism, because every `𝒪`-module annihilated by the ideal of `i_T` is a direct image
(the essential-image clause of Stacks 04CJ, part (3)); and `i_{T,*}` preserves epimorphisms. -/
theorem closedImmersionSurjectivityInput (hci : IsClosedImmersion B S hS A.i.hom) :
    A.ClosedImmersionSurjectivityInput hqcF hqcH T (A.baseChangeImmersion hqcF hqcH T) := by
  have hT : IsClosedImmersion B S hS (A.baseChangeImmersion hqcF hqcH T).hom :=
    isClosedImmersion_of_isPullback B S hS (A.isPullback_baseChangeImmersion hqcF hqcH T) hci
  exact ⟨hT, epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS _ hT
      (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS _ hT M hM) _,
    preservesEpimorphisms_modulePushforward_of_isClosedImmersion B S hS _ hT⟩

end AffineAdjointData

namespace AffineAdjointData

variable (A : AffineAdjointData.{u} B S hS)

/-- The pullback `i^*F` is quasi-coherent (Stacks 03GA). -/
theorem quasicoherent_modulePullback :
    ((modulePullback B S hS A.i).obj A.F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS A.i A.F A.quasicoherent_F

/-- For an affine `i`, the direct image `i_*H` is quasi-coherent (Stacks 03M9, an affine morphism
being quasi-compact and quasi-separated). -/
theorem quasicoherent_modulePushforward (hi : IsAffineHom B S hS A.i.hom) :
    ((modulePushforward B S hS A.i).obj A.H).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS A.i
    (isQuasiCompact_of_isAffineHom' B S hS A.i.hom A.Z.2 A.X.2 hi)
    (isQuasiSeparated_of_isAffineHom B S hS A.i.hom A.Z.2 A.X.2 hi) A.H A.quasicoherent_H

/-- **Stacks 0CW7, part (1), unconditionally**: for an affine `i : Z ⟶ X`, a quasi-coherent
`𝒪_Z`-module `H` and a map `u : F ⟶ i_*H` with adjoint `v : i^*F ⟶ H`,
`F_{v,zero} = F_{u,zero}`. -/
@[stacks 0CW7 "part (1)"]
theorem zeroFunctor_adjointSituation_eq_of_isAffineHom (hi : IsAffineHom B S hS A.i.hom) :
    (A.adjointSituation A.quasicoherent_modulePullback).zeroFunctor
        (modulePullbackSystem B S hS) =
      (A.sourceSituation (A.quasicoherent_modulePushforward hi)).zeroFunctor
        (modulePullbackSystem B S hS) :=
  A.zeroFunctor_adjointSituation_eq _ _ fun T => A.adjointAfterBaseChange _ _ T hi

/-- **Stacks 0CW7, part (2), unconditionally**: if moreover `i` is a closed immersion,
`F_{v,surj} = F_{u,surj}`. -/
@[stacks 0CW7 "part (2)"]
theorem surjFunctor_adjointSituation_eq_of_isClosedImmersion (hi : IsAffineHom B S hS A.i.hom)
    (hci : IsClosedImmersion B S hS A.i.hom) :
    (A.adjointSituation A.quasicoherent_modulePullback).surjFunctor
        (modulePullbackSystem B S hS) =
      (A.sourceSituation (A.quasicoherent_modulePushforward hi)).surjFunctor
        (modulePullbackSystem B S hS) :=
  A.surjFunctor_adjointSituation_eq _ _ fun T =>
    ⟨_, A.isAdjointAfterBaseChange _ _ T hi, A.closedImmersionSurjectivityInput _ _ T hci⟩

end AffineAdjointData

end AlgebraicGeometry.Space

end
