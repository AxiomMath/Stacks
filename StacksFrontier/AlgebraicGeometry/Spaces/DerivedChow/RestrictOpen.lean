module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Restriction

/-!
# Restricting a datum of the derived Chow lemma to a smaller open

Let `(n, Z, V, E)` be a datum of Stacks 0CTR on `X` and `j : V' ⟶ V` an open immersion. Then
`(n, Z, V', E)` is again a datum, at every point of `W' = c⁻¹(V')`: `W' ⟶ V'` is the base change
of the closed immersion `W ⟶ V` along `j`, `W' ⟶ W` is an open immersion, and clause (4) on
`X ×_S V'` is the restriction of clause (4) on `X ×_S V`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedChowDatum.restrictOpen`: the restricted datum.

## Main results

* `AlgebraicGeometry.Space.DerivedChowDatum.isPullback_restrictOpenMap`: `W'` is the part of `W`
  over `V'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

/-- For `j : D ⟶ B` and `v : B ⟶ C`, the pullback of `a` along `j ≫ v` is the pullback along
`j` of the pullback of `a` along `v`. -/
theorem _root_.CategoryTheory.Limits.isPullback_pullbackLift_comp {𝒞 : Type*} [Category 𝒞]
    [HasPullbacks 𝒞] {A B' C D' : 𝒞} (a : A ⟶ C) (v : B' ⟶ C) (j : D' ⟶ B') :
    IsPullback (pullback.lift (pullback.fst a (j ≫ v)) (pullback.snd a (j ≫ v) ≫ j)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.snd a (j ≫ v)) (pullback.snd a v) j :=
  IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback _ _)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

namespace DerivedChowDatum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {x : points B S hS X.1} (D : DerivedChowDatum X x) {V' : AlgebraicSpaces B S hS} (j : V' ⟶ D.V)

/-- The inclusion `W' ⟶ W` of the part of `Z` over a smaller open `V' ⊂ V`. -/
abbrev restrictOpenMap : overOpen D.i (j ≫ D.v) ⟶ overOpen D.i D.v :=
  ObjectProperty.homMk (show pullback (D.i ≫ productSnd X D.n D.contains).hom (j ≫ D.v).hom ⟶
      pullback (D.i ≫ productSnd X D.n D.contains).hom D.v.hom from
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.hom)
      (by rw [Category.assoc]; exact pullback.condition))

/-- The part of `Z` over `V' ⊂ V` is the part of `W` over `V'`. -/
theorem isPullback_restrictOpenMap :
    IsPullback (restrictOpenMap D j).hom (overOpenToOpen D.i (j ≫ D.v)).hom
      (overOpenToOpen D.i D.v).hom j.hom :=
  isPullback_pullbackLift_comp _ _ _

/-- The inclusion `X ×_S V' ⟶ X ×_S V`. -/
abbrev restrictOpenProductMap :
    productOver X D.n D.contains (j ≫ D.v) ⟶ productOver X D.n D.contains D.v :=
  ObjectProperty.homMk (show pullback (productSnd X D.n D.contains).hom (j ≫ D.v).hom ⟶
      pullback (productSnd X D.n D.contains).hom D.v.hom from
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.hom)
      (by rw [Category.assoc]; exact pullback.condition))

/-- The inclusion `X ×_S V' ⟶ X ×_S V` commutes with the inclusions of both into `X ×_S ℙⁿ_S`. -/
theorem restrictOpenProductMap_comp_ι :
    restrictOpenProductMap D j ≫ productOverι X D.n D.contains D.v =
      productOverι X D.n D.contains (j ≫ D.v) := by
  ext1
  exact pullback.lift_fst (pullback.fst (productSnd X D.n D.contains).hom (j ≫ D.v).hom) _ _

variable (hj : IsOpenImmersion B S hS j.hom)

/-- Clause (4) of the restriction of a datum to a smaller open. -/
def restrictOpenIso :
    (smallEtaleDerivedModulePullback B S hS (productOverι X D.n D.contains (j ≫ D.v))).obj D.E ≅
      (smallEtaleDerivedModulePullback B S hS (productOverι X D.n D.contains (j ≫ D.v))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureSheafPushforward B S hS D.i)) :=
  (smallEtaleDerivedModulePullbackCongr B S hS (restrictOpenProductMap_comp_ι D j)).symm.app _ ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS (restrictOpenProductMap D j)).mapIso
      D.restrictIso.some ≪≫
    (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _ ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS (restrictOpenProductMap_comp_ι D j)).app _

include hj in
/-- If `j : V' ⟶ V` is an open immersion, then so is the inclusion `W' ⟶ W`. -/
theorem isOpenImmersion_restrictOpenMap : IsOpenImmersion B S hS (restrictOpenMap D j).hom :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_restrictOpenMap D j).flip hj

/-- **The restriction of a datum of the derived Chow lemma to a smaller open.** For an open
immersion `j : V' ⟶ V` and a point `w'` of `W' = c⁻¹(V')`, the same `n`, `Z` and `E` with
the open `V'` form a datum of the derived Chow lemma at the image of `w'`. -/
def restrictOpen (w' : points B S hS (overOpen D.i (j ≫ D.v)).1) :
    DerivedChowDatum X (pointsMap B S hS _
      (overOpenι D.i (j ≫ D.v) ≫ D.i ≫ productFst X D.n D.contains).hom w') where
  n := D.n
  contains := D.contains
  Z := D.Z
  i := D.i
  isClosedImmersion_i := D.isClosedImmersion_i
  isFinitePresentation_i := D.isFinitePresentation_i
  V := V'
  v := j ≫ D.v
  isOpenImmersion_v := isOpenImmersion_comp B S hS _ _ hj D.isOpenImmersion_v
  isClosedImmersion_overOpenToOpen :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_restrictOpenMap D j) D.isClosedImmersion_overOpenToOpen
  isEtale_overOpen := by
    have h : (overOpenι D.i (j ≫ D.v) ≫ D.i ≫ productFst X D.n D.contains).hom =
        (restrictOpenMap D j).hom ≫
          (overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains).hom := by
      change pullback.fst _ _ ≫ _ = pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _
      rw [pullback.lift_fst_assoc]
    rw [h]
    exact isEtale_comp B S hS
      (isEtale_of_isOpenImmersion B S hS (isOpenImmersion_restrictOpenMap D j hj))
      D.isEtale_overOpen
  w := w'
  pointsMap_w := rfl
  E := D.E
  restrictIso := ⟨restrictOpenIso D j⟩
  isPseudoCoherent_E := D.isPseudoCoherent_E
  cohomologySupportedOn_E := D.cohomologySupportedOn_E

end DerivedChowDatum

end AlgebraicGeometry.Space

end
