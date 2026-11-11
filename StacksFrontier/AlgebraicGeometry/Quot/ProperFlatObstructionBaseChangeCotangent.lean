module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeCotangentModel
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeGeometryModel
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.RingTheory.Koszul.TorIndependence

/-!
# The cotangent complex of a deformation restricted to its special fibre

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over a field and
`x = (X ⟶ Spec A)` a deformation of `x₀` over an object `A` of `𝒞_Λ`, with `j : X₀ ⟶ X` the map of
total spaces. The square `X₀ = X ×_{Spec A} Spec k` is cartesian
(`AlgebraicGeometry.ProperFlatSpaceDeformation.isPullback_specialFibreMap`) and `X ⟶ Spec A` is
flat, so `X` and `Spec k` are Tor independent over `Spec A`. By Tor independent base change of
the cotangent complex (Stacks 09DL, Stacks 08QQ), read on the `Type u` models
(`AlgebraicGeometry.Space.modelCotangentBaseChangeIso`), the canonical map

`Lj_m^* L_{X/A} ⟶ L_{X₀/k}`

is an isomorphism in the derived category of `𝒪_{X₀}`-modules on the model of the small étale site
of `X₀` (`AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreCotangentIso`), where `j_m` is
the model morphism `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelHom`. This is
the base change input of the comparison of the obstruction groups `T²_{X/A}(I)` and `T²_{X₀/k}(I)`
of [Stacks, Remark 0D1P].

## Main results

* `AlgebraicGeometry.Space.torIndependent_of_isFlat_right`: an algebraic space flat over `Z` is
  Tor independent over `Z` from every algebraic space over `Z`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreCotangentIso`.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 09DL](https://stacks.math.columbia.edu/tag/09DL)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **A flat algebraic space is Tor independent from every other one** (Stacks 08IP): for
`f : X ⟶ Z` flat and `g : Y ⟶ Z`, at compatible geometric points the étale local ring of `X` is
flat over that of `Z`, hence Tor independent from that of `Y`. -/
theorem torIndependent_of_isFlat_right (g : Y ⟶ Z) (f : X ⟶ Z) (hf : IsFlat B S hS f.hom) :
    TorIndependent Y.2 X.2 Z.2 g.hom f.hom := by
  intro y x h
  refine ⟨etaleLocalRingMap Y.2 g.hom y, etaleLocalRingMap X.2 f.hom x,
    etaleLocalRingMap_isEtaleLocalRingMap Y.2 g.hom y,
    etaleLocalRingMap_isEtaleLocalRingMap X.2 f.hom x, ?_⟩
  let : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom y))
      (etaleLocalRing B S hS Y.1 y) := (etaleLocalRingMap Y.2 g.hom y).toAlgebra
  let : Algebra (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom y))
      (etaleLocalRing B S hS X.1 x) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS Z.1) h) ≫
      CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom x)).hom).toAlgebra
  have hflat : ((eqToHom (congrArg (etaleLocalRing B S hS Z.1) h) ≫
      CommRingCat.ofHom (etaleLocalRingMap X.2 f.hom x)).hom).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg (etaleLocalRing B S hS Z.1) h))))
      ((isFlat_iff_forall_etaleLocalRingMap_flat B S hS f).1 hf x)
  have : Module.Flat (etaleLocalRing B S hS Z.1 (geometricPointMap g.hom y))
      (etaleLocalRing B S hS X.1 x) := hflat
  exact (CommAlgCat.torIndependent_of_flat _ _ _).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
    hx₀)

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The cotangent complex of a deformation restricted to its special fibre** (Stacks 08QQ,
Stacks 09DL): for a deformation `x = (X ⟶ Spec A)` of `x₀ = (X₀ ⟶ Spec k)` with `j : X₀ ⟶ X` the
map of total spaces, the canonical map `Lj_m^* L_{X/A} ⟶ L_{X₀/k}` is an isomorphism in the
derived category of `𝒪_{X₀}`-modules on the `Type u` model of the small étale site of `X₀`, where
`j_m` is `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreModelHom`, `L_{X/A}` is
formed on the model of `X` and `L_{X₀/k}` on the model of `X₀`. -/
def specialFibreCotangentIso :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback (specialFibreModelHom a)).obj
        (Space.modelRingedToposHom
          (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)).cotangentComplexDerived ≅
      (Space.modelRingedToposHom (Space.ProperFlatLift.chartStructureMap x₀
        (obj_eq_specialFibre x₀ hx₀))).cotangentComplexDerived :=
  Space.modelCotangentBaseChangeIso (isPullback_specialFibreMap a)
    (Space.torIndependent_of_isFlat_right _ _
      (Space.ProperFlatLift.isFlat_chartStructureMap a.point a.obj_eq))

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
