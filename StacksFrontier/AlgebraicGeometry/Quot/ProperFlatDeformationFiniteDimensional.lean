module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceDeformationComparison
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.LocalizedTangentOfAutomorphismGroup
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceFinite
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransportEquivalence
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.Artin.Infinitesimal.FunctorDataComparison

/-!
# The deformation category of a point of `Spaces'_{fp, flat, proper}` is finite dimensional

Let `x₀ = (X ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over the spectrum of a
field `k`, the stack being formed over the big fppf site of `Spec ℤ`. The predeformation category
`𝓕_{𝒳,k,x₀}` over `𝒞_ℤ` is equivalent, over `𝒞_ℤ`, to the deformation category `𝓓_X` of the
algebraic space `X` over `k`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.toSpaceDeformationFunctor`). Hence it is a
deformation category (Stacks 0E40), and its tangent space and its infinitesimal automorphisms embed
in those of `𝓓_X`, which are `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` and
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` and finite dimensional because `X` is proper over `k` (Stacks 0E41,
0E42; the finiteness is Stacks 0D0Z with Stacks 0D0T, the argument of the proof of Stacks 0D1K).

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.isDeformationCategory_predeformation`
* `AlgebraicGeometry.ProperFlatSpaceDeformation.finiteDimensional_tangentSpace`
* `AlgebraicGeometry.ProperFlatSpaceDeformation.finiteDimensional_infinitesimalAutomorphisms`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0E40](https://stacks.math.columbia.edu/tag/0E40)
* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Examples

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {k : Type u} [Field k]
  [Algebra (ULift.{u} ℤ) k] (x₀ : CartesianProperFlatSpaces B integerBase hZ)
  (hx₀ : (projection B hZ).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) ≫ 𝟙 integerBase))

/-- The deformation category `𝓓_X` of the algebraic space `X` of `x₀` is a deformation category
(Stacks 0E40). -/
theorem isDeformationCategory_spaceProjection :
    IsDeformationCategory.{u, u, u} (spaceProjection x₀ hx₀) :=
  isDeformationCategory_spaceDeformationProjection B hZ (contains_spec x₀ hx₀) (space x₀)
    x₀.obj.obj.left.property (toResidueField x₀ hx₀)

/-- **The predeformation category `𝓕_{𝒳,k,x₀}` is a deformation category**: it is equivalent over
`𝒞_ℤ` to the deformation category of the algebraic space `X`, which satisfies (RS) by
Stacks 0E40. -/
theorem isDeformationCategory_predeformation :
    letI := (predeformation x₀ hx₀).category
    IsDeformationCategory.{u, u, u} (predeformation x₀ hx₀).projection := by
  let := (predeformation x₀ hx₀).category
  have := toSpaceDeformationFunctor_full x₀ hx₀
  have := toSpaceDeformationFunctor_faithful x₀ hx₀
  have := toSpaceDeformationFunctor_essSurj x₀ hx₀
  have hpre := Artin.predeformationCategory_isPredeformationCategory B hZ (𝟙 integerBase)
    (cartesianProperFlatProjection B integerBase hZ) x₀ hx₀
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)
  obtain ⟨E⟩ := hpre.specialFiber
  exact isDeformationCategory_comp_of_essSurj (toSpaceDeformationFunctor x₀ hx₀)
    (spaceProjection x₀ hx₀) hpre.cofibered ⟨E.inverse.obj ⟨PUnit.unit⟩⟩
    (isDeformationCategory_spaceProjection x₀ hx₀)

/-- The algebraic space `X` of `x₀` is proper over `k`. -/
theorem isProper_toResidueField : Space.IsProper B integerBase hZ (toResidueField x₀ hx₀) :=
  (isFinitePresentation_and_isProper_toResidueField x₀ hx₀).2

/-- **The tangent space of `𝓕_{𝒳,k,x₀}` is finite dimensional.** -/
theorem finiteDimensional_tangentSpace :
    letI := (predeformation x₀ hx₀).category
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (predeformation x₀ hx₀).projection).p) :=
      ⟨(isDeformationCategory_predeformation x₀ hx₀).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
        (isomorphismClasses (BasedCategory.ofFunctor (predeformation x₀ hx₀).projection)
          (isDeformationCategory_predeformation x₀ hx₀).predeformation.cofibered))) :=
      ⟨tangentConditionS2.{u, u, u} (isDeformationCategory_predeformation x₀ hx₀)⟩
    FiniteDimensional k (artinianTangentSpace (ULift.{u} ℤ) k
      (isomorphismClasses (BasedCategory.ofFunctor (predeformation x₀ hx₀).projection)
        (isDeformationCategory_predeformation x₀ hx₀).predeformation.cofibered)) := by
  let := (predeformation x₀ hx₀).category
  have hD := isDeformationCategory_predeformation x₀ hx₀
  have hDef := isDeformationCategory_spaceProjection x₀ hx₀
  let Φ : BasedCategory.ofFunctor (predeformation x₀ hx₀).projection ⥤ᵇ
      BasedCategory.ofFunctor (spaceProjection x₀ hx₀) :=
    { toFunctor := toSpaceDeformationFunctor x₀ hx₀
      w := rfl }
  have : Φ.toFunctor.Full := toSpaceDeformationFunctor_full x₀ hx₀
  have : Φ.toFunctor.Faithful := toSpaceDeformationFunctor_faithful x₀ hx₀
  have hfin := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hDef).mp
    (spaceTangentSpace_finiteDimensional B hZ (contains_spec x₀ hx₀) (space x₀)
      x₀.obj.obj.left.property (toResidueField x₀ hx₀) (isProper_toResidueField x₀ hx₀))
  exact (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mpr
    (finiteDimensional_tangentModuleAt_of_fullyFaithful hD hDef Φ _ hfin)

attribute [local instance] Artin.PredeformationConstruction.category in
/-- **The infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` are finite dimensional**, at every object
of its special fibre and every choice of its pushforwards. -/
theorem finiteDimensional_infinitesimalAutomorphisms
    (y : (predeformation x₀ hx₀).carrier)
    (hy : (predeformation x₀ hx₀).projection.obj y = residueFieldObject.{u, u, u} (ULift.{u} ℤ) k)
    (PF : ChosenPushforwardsAt (predeformation x₀ hx₀).projection y) :
    FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} PF
      (isDeformationCategory_predeformation x₀ hx₀).satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{u} k))) := by
  let := (predeformation x₀ hx₀).category
  have := toSpaceDeformationFunctor_faithful x₀ hx₀
  have hD := isDeformationCategory_predeformation x₀ hx₀
  have hDef := isDeformationCategory_spaceProjection x₀ hx₀
  let y' : (spaceProjection x₀ hx₀).Fiber (residueFieldObject.{u, u, u} (ULift.{u} ℤ) k) :=
    ⟨(toSpaceDeformationFunctor x₀ hx₀).obj y, hy⟩
  let Q := chosenPushforwardsAtOfCofiberedInGroupoids hDef.predeformation.cofibered y'.1
  refine finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hD.satisfiesRS PF ?_
  refine finiteDimensional_localizedAutomorphismFunctorTangent_of_faithful
    (p := (predeformation x₀ hx₀).projection) (q := spaceProjection x₀ hx₀)
    (toSpaceDeformationFunctor x₀ hx₀) rfl hD.satisfiesRS hDef.satisfiesRS PF Q ?_
  exact finiteDimensional_localizedAutomorphismFunctorTangent_of_infinitesimalAutomorphismGroup y'
    hDef.predeformation hDef.satisfiesRS Q
    (spaceInfinitesimalAutomorphisms_finiteDimensional B hZ (contains_spec x₀ hx₀) (space x₀)
      x₀.obj.obj.left.property (toResidueField x₀ hx₀) (isProper_toResidueField x₀ hx₀))

/-! ### The functors `T_x` and `Inf_x` of Stacks 07Y9 -/

section Functors

variable {k : Type u} [Field k] (toS : Spec (.of k) ⟶ integerBase) (hk : B.Contains (Spec (.of k)))
  (x : CartesianProperFlatSpaces B integerBase hZ)
  (hx : (cartesianProperFlatProjection B integerBase hZ).obj x =
    Deformation.Artin.algebraOver k B integerBase hZ toS hk)

include hx in
/-- A point of `𝒳` over `Spec k`, read in schemes over `Spec ℤ`, lies over `Spec k ⟶ Spec ℤ`
presented through the unique ring map `ℤ ⟶ k`. -/
theorem projection_obj_eq_of_eq_algebraOver :
    letI : Algebra (ULift.{u} ℤ) k := ULift.algebra' ℤ k
    (projection B hZ).obj x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) ≫ 𝟙 integerBase) := by
  change (Over.post B.inclusion).obj ((cartesianProperFlatProjection B integerBase hZ).obj x) = _
  rw [hx]
  change Over.mk (B.inclusion.map (ObjectProperty.homMk toS : B.obj hk ⟶ B.obj hZ)) = _
  congr 1
  exact specULiftZIsTerminal.hom_ext _ _

/-- **The tangent space `T_x(k)` of Stacks 07Y9 is finite dimensional**, for every `k`-linear
tangent functor of `x` and every field `k`. -/
theorem finiteDimensional_tangentFunctorData_obj
    (T : Deformation.Artin.TangentFunctorData k B integerBase hZ toS hk
      (cartesianProperFlatProjection B integerBase hZ) x hx) :
    FiniteDimensional k (T.functor.obj ((Deformation.Artin.fgSiteModule B hk).obj
      (FGModuleCat.of k k))) := by
  let : Algebra (ULift.{u} ℤ) k := ULift.algebra' ℤ k
  have hx₀ := projection_obj_eq_of_eq_algebraOver toS hk x hx
  exact Deformation.Artin.finiteDimensional_tangentFunctorData_of_artinianTangentSpace B
    integerBase hZ (𝟙 integerBase) toS hk (cartesianProperFlatProjection B integerBase hZ)
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ) x hx₀ hx T
    (isDeformationCategory_predeformation x hx₀) (finiteDimensional_tangentSpace x hx₀)

/-- **The infinitesimal automorphisms `Inf_x(k)` of Stacks 07Y9 are finite dimensional**, for
every `k`-linear functor of infinitesimal automorphisms of `x` and every field `k`. -/
theorem finiteDimensional_infinitesimalAutomorphismFunctorData_obj
    (I : Deformation.Artin.InfinitesimalAutomorphismFunctorData k B integerBase hZ toS hk
      (cartesianProperFlatProjection B integerBase hZ) x hx
      (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ)) :
    FiniteDimensional k (I.functor.obj ((Deformation.Artin.fgSiteModule B hk).obj
      (FGModuleCat.of k k))) := by
  let : Algebra (ULift.{u} ℤ) k := ULift.algebra' ℤ k
  have hx₀ := projection_obj_eq_of_eq_algebraOver toS hk x hx
  exact Deformation.Artin.finiteDimensional_infinitesimalAutomorphismFunctorData B integerBase hZ
    (𝟙 integerBase) toS hk (cartesianProperFlatProjection B integerBase hZ)
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ) x hx₀ hx I
    (isDeformationCategory_predeformation x hx₀)
    (finiteDimensional_infinitesimalAutomorphisms x hx₀)

end Functors

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
