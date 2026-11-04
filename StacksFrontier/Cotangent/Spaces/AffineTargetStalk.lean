module

public import StacksFrontier.Cotangent.Spaces.AffineTargetStructureMap

/-!
# The structure map of an affine scheme at a geometric point

Let `T` be an object of the big fppf site with affine underlying scheme, `Λ = Γ(T, 𝒪_T)`, and
regard `T` as an algebraic space. Its structure map `Λ̲ ⟶ 𝒪_T` from the constant sheaf on the
small étale site (`AlgebraicGeometry.Space.chartBaseStructureMap` of the identity of `T`) has, at
a geometric point `ȳ` of `T`, the stalk map `Λ → 𝒪_{T, ȳ}`: this file identifies the stalk of `Λ̲`
with `Λ` (`AlgebraicGeometry.Space.chartBaseConstantFiberEquiv`) and the stalk map with the germ
map to the étale local ring (`AlgebraicGeometry.Space.pointStalkRingEquiv_schemeSpaceStalkMap`),
and proves that the ring-level cotangent complex of `Λ → 𝒪_{T, ȳ}` is acyclic
(`AlgebraicGeometry.Space.acyclic_cotangentComplex_schemeSpaceStalkMap`).

The last statement is the source's computation of the stalks of `L_q` for
`q : Spec(Λ)_étale ⟶ (*, Λ)` in the proof of Tag 08VG: the stalk `𝒪_{T, ȳ}` is a strict
henselization of the local ring `Λ_𝔭` of `T` at the image point (Stacks 04KF), so items (3), (7)
and (8) of Tag 08R2 apply to the tower `Λ → Λ_𝔭 → 𝒪_{T, ȳ}`. It is the form of
`AlgebraicGeometry.Space.isZero_cotangentComplexDerived_specStalkMap` for an arbitrary affine `T`
over an arbitrary base scheme, with the stalk taken in the universe of the sections of `𝒪_T`, as
the point fibres of the small étale site are.

## Main definitions

* `AlgebraicGeometry.Space.schemeSpaceNeighborhood`: the identity chart of `T`, as a small étale
  neighbourhood of a geometric point.
* `AlgebraicGeometry.Space.chartBaseConstantFiberEquiv`: the stalk of `Λ̲` is `Λ`.
* `AlgebraicGeometry.Space.schemeSpaceStalkMap`: the stalk map `Λ → 𝒪_{T, ȳ}` of the structure
  map.

## Main results

* `AlgebraicGeometry.Space.pointStalkRingEquiv_schemeSpaceStalkMap`
* `AlgebraicGeometry.Space.acyclic_cotangentComplex_schemeSpaceStalkMap`

## References

* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  (y : GeometricPoint B S hS (schemeSpace T).1)

/-- The identity chart of `T`, with the geometric point itself as the lift: a small étale
neighbourhood of every geometric point of `T`. -/
def schemeSpaceNeighborhood : SmallEtaleNeighborhood y where
  chart := schemeSpaceIdChart T
  point := y.val.value
  point_comp := rfl

/-- The point of the small étale site of `T` attached to a geometric point. -/
abbrev schemeSpaceEtalePoint : (SmallEtale.topology B S hS (schemeSpace T).1).Point.{u} :=
  etaleSitePoint B S hS (schemeSpace T).1 y (schemeSpace T).2

/-- The lift of the geometric point to the identity chart. -/
abbrev schemeSpaceLift :
    (schemeSpaceEtalePoint y).fiber.obj (schemeSpaceNeighborhood y).chart :=
  ⟨y.val.value, rfl⟩

/-- The germ map `Λ → Λ̲_ȳ` of the constant sheaf at a geometric point, at the identity chart. -/
def chartBaseConstantGerm : CommRingCat.of (baseRing B S hS T) ⟶
    ((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).obj
      (chartBaseConstantRing (X := schemeSpace T) (T := T)).obj :=
  (toSheafify (SmallEtale.topology B S hS (schemeSpace T).1)
      ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
        (CommRingCat.of (baseRing B S hS T)))).app (op (schemeSpaceNeighborhood y).chart) ≫
    (schemeSpaceEtalePoint y).toPresheafFiber (schemeSpaceNeighborhood y).chart
      (schemeSpaceLift y) (chartBaseConstantRing (X := schemeSpace T) (T := T)).obj

/-- **The stalk of the constant sheaf `Λ̲` at a geometric point is `Λ`.** -/
theorem bijective_chartBaseConstantGerm : Function.Bijective (chartBaseConstantGerm y) := by
  have h : chartBaseConstantGerm y = (schemeSpaceEtalePoint y).toPresheafFiber
      (schemeSpaceNeighborhood y).chart (schemeSpaceLift y)
        ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
          (CommRingCat.of (baseRing B S hS T))) ≫
      ((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).map
        (toSheafify (SmallEtale.topology B S hS (schemeSpace T).1)
          ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
            (CommRingCat.of (baseRing B S hS T)))) :=
    ((schemeSpaceEtalePoint y).toPresheafFiber_naturality _ _ _).symm
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso
      (((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).map
        (toSheafify (SmallEtale.topology B S hS (schemeSpace T).1)
          ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
            (CommRingCat.of (baseRing B S hS T)))))).comp
    ((schemeSpaceEtalePoint y).bijective_toPresheafFiber_const (CommRingCat.of (baseRing B S hS T))
      (schemeSpaceNeighborhood y).chart (schemeSpaceLift y))

/-- The stalk of the constant sheaf `Λ̲` at a geometric point of `T`, identified with `Λ`. -/
def chartBaseConstantFiberEquiv :
    ((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).obj
      (chartBaseConstantRing (X := schemeSpace T) (T := T)).obj ≃+* baseRing B S hS T :=
  (RingEquiv.ofBijective (chartBaseConstantGerm y).hom (bijective_chartBaseConstantGerm y)).symm

/-- The stalk of the structure sheaf of `T` at a geometric point. -/
abbrev schemeSpaceStalk : Type u :=
  ((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).obj
    (smallEtaleRingedTopos B S hS (schemeSpace T)).O.obj

/-- **The stalk map `Λ → 𝒪_{T, ȳ}` of the structure map of `T`** at a geometric point. -/
def schemeSpaceStalkMap : baseRing B S hS T →+* schemeSpaceStalk y :=
  (((schemeSpaceEtalePoint y).presheafFiber (A := CommRingCat.{u})).map
      (chartBaseStructureMap (𝟙 (schemeSpace T))).hom).hom.comp (chartBaseConstantGerm y).hom

/-- **The stalk map of the structure map of `T` is the germ map** `Λ → 𝒪_{T, ȳ}` at the identity
chart, through the identification of the stalk of `𝒪_T` with the étale local ring. -/
theorem pointStalkRingEquiv_schemeSpaceStalkMap (a : baseRing B S hS T) :
    pointStalkRingEquiv B S hS (schemeSpace T) y (schemeSpaceStalkMap y a) =
      etaleLocalRingGerm B S hS (schemeSpace T).1 y (op (schemeSpaceNeighborhood y)) a := by
  have hκ : (chartBaseStructureMap (𝟙 (schemeSpace T))).hom.app
        (op (schemeSpaceNeighborhood y).chart)
        ((toSheafify (SmallEtale.topology B S hS (schemeSpace T).1)
          ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
            (CommRingCat.of (baseRing B S hS T)))).app (op (schemeSpaceNeighborhood y).chart) a) =
      a :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => φ.app (op (schemeSpaceNeighborhood y).chart))
      (toSheafify_comp_chartBaseStructureMap (𝟙 (schemeSpace T)))) a).trans
      (chartBaseStructurePresheafMap_app_schemeSpaceIdChart_apply T a)
  have hn := (schemeSpaceEtalePoint y).toPresheafFiber_naturality_apply
    (chartBaseStructureMap (𝟙 (schemeSpace T))).hom (schemeSpaceNeighborhood y).chart
    (schemeSpaceLift y)
    ((toSheafify (SmallEtale.topology B S hS (schemeSpace T).1)
      ((Functor.const (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ).obj
        (CommRingCat.of (baseRing B S hS T)))).app (op (schemeSpaceNeighborhood y).chart) a)
  refine (congrArg (pointStalkRingEquiv B S hS (schemeSpace T) y) hn).trans ?_
  refine (congrArg (fun z => pointStalkRingEquiv B S hS (schemeSpace T) y
    ((schemeSpaceEtalePoint y).toPresheafFiber (schemeSpaceNeighborhood y).chart (schemeSpaceLift y)
      (smallEtaleRingedTopos B S hS (schemeSpace T)).O.obj z)) hκ).trans ?_
  exact pointStalkRingEquiv_germ_neighborhood B S hS (schemeSpace T) y
    (schemeSpaceNeighborhood y) a

/-- The stalk of the structure sheaf of `T` at a geometric point is a local ring. -/
theorem isLocalRing_schemeSpaceStalk : IsLocalRing (schemeSpaceStalk y) :=
  have := isLocalRing_etaleLocalRing B S hS (schemeSpace T).1 (schemeSpace T).2 y
  have : Nontrivial (schemeSpaceStalk y) :=
    (pointStalkRingEquiv B S hS (schemeSpace T) y).toEquiv.nontrivial
  IsLocalRing.of_surjective' (pointStalkRingEquiv B S hS (schemeSpace T) y).symm.toRingHom
    (pointStalkRingEquiv B S hS (schemeSpace T) y).symm.surjective

attribute [local instance] HasDerivedCategory.standard in
/-- **The cotangent complex of the stalk map `Λ → 𝒪_{T, ȳ}` of an affine `T` is acyclic.** The
stalk `𝒪_{T, ȳ}` is a strict henselization of the local ring `Λ_𝔭` of `T` at the image point
(Stacks 04KF, at the identity chart), and `Λ_𝔭` is a localization of `Λ` since `T` is affine; so
items (3), (7) and (8) of Stacks 08R2 apply to the tower `Λ → Λ_𝔭 → 𝒪_{T, ȳ}`. -/
theorem acyclic_cotangentComplex_schemeSpaceStalkMap
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    letI : Algebra (baseRing B S hS T) (schemeSpaceStalk y) := (schemeSpaceStalkMap y).toAlgebra
    (CommAlgCat.cotangentComplex.{u, u} (baseRing B S hS T)
      (CommAlgCat.of (baseRing B S hS T) (schemeSpaceStalk y))).Acyclic := by
  let V := schemeSpaceNeighborhood y
  let X := chartScheme V.chart
  have : IsAffine X := hT
  let p : X := chartPoint B S hS (schemeSpace T).1 V
  let C := schemeSpaceStalk y
  let Ψ := pointStalkRingEquiv B S hS (schemeSpace T) y
  have := isLocalRing_etaleLocalRing B S hS (schemeSpace T).1 (schemeSpace T).2 y
  have : IsLocalRing C := isLocalRing_schemeSpaceStalk y
  let algE : Algebra ↥(chartLocalRing B S hS (schemeSpace T).1 V)
      (etaleLocalRing B S hS (schemeSpace T).1 y) :=
    (chartLocalRingToEtaleLocalRing B S hS _ (schemeSpace T).2 V).toAlgebra
  have : IsHenselization ↥(chartLocalRing B S hS (schemeSpace T).1 V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS (schemeSpace T).1 V))
        (chartGeometricPoint V).residueField)
      (etaleLocalRing B S hS (schemeSpace T).1 y) :=
    IsHenselization.of_ringEquiv
      (chartStrictHenselizationEquiv B S hS _ (schemeSpace T).2 V) fun _ ↦ rfl
  let algC : Algebra ↥(chartLocalRing B S hS (schemeSpace T).1 V) C :=
    (Ψ.symm.toRingHom.comp (chartLocalRingToEtaleLocalRing B S hS _ (schemeSpace T).2 V)).toAlgebra
  have : IsHenselization ↥(chartLocalRing B S hS (schemeSpace T).1 V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS (schemeSpace T).1 V))
        (chartGeometricPoint V).residueField) C :=
    IsHenselization.of_ringEquiv Ψ.symm fun _ ↦ rfl
  let algL : Algebra Γ(X, ⊤) ↥(chartLocalRing B S hS (schemeSpace T).1 V) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := ⊤) ⟨p, trivial⟩
  have : IsLocalization ((isAffineOpen_top X).primeIdealOf ⟨p, trivial⟩).asIdeal.primeCompl
      ↥(chartLocalRing B S hS (schemeSpace T).1 V) :=
    (isAffineOpen_top X).isLocalization_stalk ⟨p, trivial⟩
  let algΛ : Algebra Γ(X, ⊤) C := (schemeSpaceStalkMap y).toAlgebra
  have : IsScalarTower Γ(X, ⊤) ↥(chartLocalRing B S hS (schemeSpace T).1 V) C := by
    refine IsScalarTower.of_algebraMap_eq fun a => Ψ.injective ?_
    refine (pointStalkRingEquiv_schemeSpaceStalkMap y a).trans ?_
    refine Eq.trans ?_ (Ψ.apply_symm_apply _).symm
    exact (chartLocalRingToEtaleLocalRing_germ B S hS _ (schemeSpace T).2 V a).symm
  have key := CommAlgCat.isZero_cotangentComplexDerived_henselization_localization
    Γ(X, ⊤) ((isAffineOpen_top X).primeIdealOf ⟨p, trivial⟩).asIdeal.primeCompl
    ↥(chartLocalRing B S hS (schemeSpace T).1 V)
    (separableClosure (ResidueField ↥(chartLocalRing B S hS (schemeSpace T).1 V))
      (chartGeometricPoint V).residueField) C
  exact fun n => CochainComplex.exactAt_of_isZero_Q _ n key

end AlgebraicGeometry.Space

end
