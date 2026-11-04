module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectIffStalkTorDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkAmplitude
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor independent base change of a perfect morphism

Consider a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `f` perfect and `f`, `g` Tor independent. At a point `x'` of `X'` lying over `x ∈ X`, the
local ring `𝒪_{X', x'}` is, over `𝒪_{S', f' x'}`, the base change of `𝒪_{X, x}` over
`𝒪_{S, f x}`, and Tor independence makes this base change preserve Tor amplitude
(`AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_stalk_of_cartesian`, the
ring-level core of [Stacks, Tag 0C0V]). So `𝒪_{X', x'}` has finite Tor dimension over
`𝒪_{S', f' x'}`, and if `f'` is pseudo-coherent it is perfect by the stalkwise criterion of
[Stacks, Tag 069C].

## Main results

* `AlgebraicGeometry.perfect_of_isPullback_of_torIndependent` — a Tor independent base change of
  a perfect morphism is perfect as soon as it is pseudo-coherent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- The restriction of scalars of a ring, viewed as a module over itself, along a ring map
`φ : R ⟶ A` is `A` with the module structure of the algebra `φ.toAlgebra`. -/
private def restrictScalarsSelfIso {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    letI := φ.hom.toAlgebra
    (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A) ≅ ModuleCat.of R A :=
  letI := φ.hom.toAlgebra
  (StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv R A).toModuleIso

/-- An additive functor `F` carries a complex concentrated in degree zero on `M` to the complex
concentrated in degree zero on `N`, given an isomorphism `F M ≅ N`. -/
private def mapSingleIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive] {M : C} {N : D} (e : F.obj M ≅ N) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ≅
      (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj N :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M ≪≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso e

/-- The derived image of the ring `A`, placed in degree zero, under restriction of scalars along
`φ : R ⟶ A` is `A` placed in degree zero as an `R`-module. -/
private def restrictScalarsSingleSelfIso {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    letI := φ.hom.toAlgebra
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A) :=
  letI := φ.hom.toAlgebra
  (ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (mapSingleIso _ (restrictScalarsSelfIso φ)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app _).symm

/-- **A Tor independent base change of a perfect morphism is perfect, once it is
pseudo-coherent.** In a cartesian square `X' = X ×_S S'` with `f : X ⟶ S` perfect and `f`, `g`
Tor independent, the base change `f' : X' ⟶ S'` is perfect provided it is pseudo-coherent (for
instance when `S'` is locally Noetherian, `f'` being locally of finite type). -/
@[sga "6 X 7.10" "more general"]
theorem perfect_of_isPullback_of_torIndependent {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g) [Perfect f]
    [PseudoCoherent f'] (htor : TorIndependent f g) : Perfect f' := by
  refine perfect_of_forall_hasFiniteTorDimensionCanonical_stalk f' fun x' => ?_
  obtain ⟨a, b, hab⟩ := (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).1
    (Perfect.hasFiniteTorDimensionCanonical_stalk f (g'.base x'))
  let A := X.presheaf.stalk (g'.base x')
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have hK : K.KFlat := CochainComplex.DerivedTensor.kFlat_single_of_flat (ModuleCat.of A A)
  have hup := BaseChangeTorAmplitude.hasTorAmplitudeCanonical_stalk_of_cartesian g' f' f g sq
    htor x' K hK a b (BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (restrictScalarsSingleSelfIso (f.stalkMap (g'.base x'))).symm a b hab)
  let := (f'.stalkMap x').hom.toAlgebra
  refine (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).2
    ⟨a, b, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b hup⟩
  exact DerivedCategory.Q.mapIso
      ((((ModuleCat.restrictScalars (f'.stalkMap x').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
        (mapSingleIso _ (ModuleCat.ExtendScalars.objSelfIso (g'.stalkMap x').hom))) ≪≫
        mapSingleIso _ (restrictScalarsSelfIso (f'.stalkMap x'))) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

end AlgebraicGeometry
