module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsTensorFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafifyLocallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureModuleStalkFunctorAtPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedTensorPullbackSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback

/-!
# Tensoring the inverse image with a module flat over the target is exact

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢` an `𝒪_X`-module whose geometric stalks
are flat over the étale local rings of `Y` (Stacks 05VU (2)). Then the functor
`𝒩 ↦ 𝒢 ⊗_{𝒪_X} f^*𝒩` from `𝒪_Y`-modules to `𝒪_X`-modules is exact.

Exactness is checked at the geometric points `x̄` of `X`. There the functor is the stalk at
`ȳ = f ∘ x̄` followed by `N ↦ 𝒢_{x̄} ⊗_{𝒪_{X,x̄}} (𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} N)`
(Stacks 03EL at a point and Stacks 05V5), which is `N ↦ 𝒢_{x̄} ⊗_{𝒪_{Y,ȳ}} N` and so exact.

## Main definitions

* `AlgebraicGeometry.Space.tensorPullbackFunctor`: the functor `𝒩 ↦ 𝒢 ⊗ f^*𝒩`.
* `AlgebraicGeometry.Space.tensorPullbackStalkIso`: its composite with the stalk functor at a
  geometric point.

## Main results

* `AlgebraicGeometry.Space.flat_geometricStalk_of_isFlatOverAtGeometricPoint`
* `AlgebraicGeometry.Space.preservesFiniteLimits_tensorPullbackFunctor_comp_stalk` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_tensorPullbackFunctor_comp_stalk`: the
  functor followed by the stalk at a geometric point is exact.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))

/-- The functor `𝒩 ↦ 𝒢 ⊗_{𝒪_X} f^*𝒩` from `𝒪_Y`-modules to `𝒪_X`-modules. -/
def tensorPullbackFunctor :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) G

/-- The stalk functor at a geometric point `x̄` of `X` after `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is the stalk functor
at `f ∘ x̄` followed by `N ↦ 𝒢_{x̄} ⊗ (𝒪_{X,x̄} ⊗ N)`. -/
def tensorPullbackStalkIso (x : GeometricPoint B S hS X.1) :
    tensorPullbackFunctor f G ⋙ structureModuleStalkFunctorAtPoint B S hS X x ≅
      structureModuleStalkFunctorAtPoint B S hS Y (geometricPointMap f.hom x) ⋙
        (ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS f x) ⋙
          (curriedTensor _).obj ((structureModuleStalkFunctorAtPoint B S hS X x).obj G)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
      (Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorNatIso
        (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O G) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackStalkFunctorIso f x) _ ≪≫
    Functor.associator _ _ _

/-- **The stalk of a module flat over `Y` at `x̄` is flat over the stalk of `𝒪_Y` at `f ∘ x̄`**,
through the homomorphism of structure-sheaf stalks along which Stacks 05V5 extends scalars. -/
theorem flat_geometricStalk_of_isFlatOverAtGeometricPoint (x : GeometricPoint B S hS X.1)
    (hG : IsFlatOverAtGeometricPoint B S hS f G x) :
    letI : Module (Stacks.ringFiber (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O.obj)
        ((structureModuleStalkFunctorAtPoint B S hS X x).obj G) :=
      Module.compHom _ (smallEtaleStalkPullbackRingMap B S hS f x)
    Module.Flat (Stacks.ringFiber (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleRingedTopos B S hS Y).O.obj)
        ((structureModuleStalkFunctorAtPoint B S hS X x).obj G) := by
  let R₀ := Stacks.ringFiber (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
    (smallEtaleRingedTopos B S hS Y).O.obj
  let φ := smallEtaleStalkPullbackRingMap B S hS f x
  let N := geometricModuleStalk B S hS X x G
  let Ret := etaleLocalRing B S hS Y.1 (geometricPointMap f.hom x)
  let eR := pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)
  let γ := etaleLocalRingMap X.2 f.hom x
  let : Module Ret N := Module.compHom N γ
  have : Module.Flat Ret N := hG
  let : Algebra R₀ Ret := eR.toRingHom.toAlgebra
  let : Module R₀ N := Module.compHom N (γ.comp eR.toRingHom)
  have : IsScalarTower R₀ Ret N :=
    ⟨fun r s n => by
      change (γ (eR r * s)) • n = (γ (eR r)) • ((γ s) • n)
      rw [map_mul, mul_smul]⟩
  have : Module.Flat R₀ Ret := RingHom.Flat.of_bijective (f := eR.toRingHom) eR.bijective
  have : Module.Flat R₀ N := Module.Flat.trans _ Ret N
  let : Module R₀ ((structureModuleStalkFunctorAtPoint B S hS X x).obj G) := Module.compHom _ φ
  let L := Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O G
  let ε := geometricModuleStalkAddEquiv B S hS X x G
  let e : ((structureModuleStalkFunctorAtPoint B S hS X x).obj G : Type u) ≃+ N :=
    L.symm.toAddEquiv.trans ε
  have he : ∀ (r : R₀) (m : ((structureModuleStalkFunctorAtPoint B S hS X x).obj G : Type u)),
      e (r • m) = γ (eR r) • e m := by
    intro r m
    have h : pointStalkRingEquiv B S hS X x (φ r) = γ (eR r) :=
      congrArg (fun k : R₀ →+* _ => k r)
        (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f x)
    exact ((congrArg ε (L.symm.map_smul (φ r) m)).trans
      (geometricModuleStalkAddEquiv_smul B S hS X x G (φ r) (L.symm m))).trans
      (congrArg (· • ε (L.symm m)) h)
  exact Module.Flat.of_linearEquiv (AddEquiv.toLinearEquiv e he)

/-- `𝒩 ↦ 𝒢 ⊗ f^*𝒩` followed by the stalk at a geometric point of `X` preserves finite limits when
`𝒢` is flat over `Y` at that point. -/
theorem preservesFiniteLimits_tensorPullbackFunctor_comp_stalk (x : GeometricPoint B S hS X.1)
    (hG : IsFlatOverAtGeometricPoint B S hS f G x) :
    PreservesFiniteLimits
      (tensorPullbackFunctor f G ⋙ structureModuleStalkFunctorAtPoint B S hS X x) := by
  have : PreservesFiniteLimits
      (structureModuleStalkFunctorAtPoint B S hS Y (geometricPointMap f.hom x)) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleRingedTopos B S hS Y).O
  have := ModuleCat.preservesFiniteLimits_extendScalars_comp_tensorLeft
    (smallEtaleStalkPullbackRingMap B S hS f x)
    ((structureModuleStalkFunctorAtPoint B S hS X x).obj G)
    (flat_geometricStalk_of_isFlatOverAtGeometricPoint f G x hG)
  exact preservesFiniteLimits_of_natIso (tensorPullbackStalkIso f G x).symm

/-- `𝒩 ↦ 𝒢 ⊗ f^*𝒩` followed by the stalk at a geometric point of `X` preserves finite
colimits. -/
theorem preservesFiniteColimits_tensorPullbackFunctor_comp_stalk (x : GeometricPoint B S hS X.1) :
    PreservesFiniteColimits
      (tensorPullbackFunctor f G ⋙ structureModuleStalkFunctorAtPoint B S hS X x) := by
  have : PreservesFiniteColimits
      (structureModuleStalkFunctorAtPoint B S hS Y (geometricPointMap f.hom x)) :=
    ((exactFunctor_iff _).mp (Stacks.exactFunctor_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleRingedTopos B S hS Y).O)).2
  have := ModuleCat.preservesFiniteColimits_extendScalars_comp_tensorLeft
    (smallEtaleStalkPullbackRingMap B S hS f x)
    ((structureModuleStalkFunctorAtPoint B S hS X x).obj G)
  exact preservesFiniteColimits_of_natIso (tensorPullbackStalkIso f G x).symm

/-- `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is right exact: `f^*` is a left adjoint and `𝒢 ⊗ -` is right exact. -/
theorem preservesFiniteColimits_tensorPullbackFunctor :
    PreservesFiniteColimits (tensorPullbackFunctor f G) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.preservesFiniteColimits_tensorPullback
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y) _ G

/-- `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is additive, being right exact. -/
instance additive_tensorPullbackFunctor : (tensorPullbackFunctor f G).Additive := by
  have := preservesFiniteColimits_tensorPullbackFunctor f G
  have : PreservesBinaryBiproducts (tensorPullbackFunctor f G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **`𝒩 ↦ 𝒢 ⊗ f^*𝒩` is left exact when `𝒢` is flat over `Y`** at every geometric point of `X`:
exactness of a short complex and injectivity of a map are read at the geometric points, where
the functor is exact. -/
theorem preservesFiniteLimits_tensorPullbackFunctor
    (hG : ∀ x, IsFlatOverAtGeometricPoint B S hS f G x) :
    PreservesFiniteLimits (tensorPullbackFunctor f G) := by
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
    fun σ hσ => ⟨?_, ?_⟩
  · refine (Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
      (smallEtaleRingedTopos B S hS X).O
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2)).2 ?_
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
    have h₁ := preservesFiniteLimits_tensorPullbackFunctor_comp_stalk f G x (hG x)
    have h₂ := preservesFiniteColimits_tensorPullbackFunctor_comp_stalk f G x
    exact hσ.exact.map (tensorPullbackFunctor f G ⋙ structureModuleStalkFunctorAtPoint B S hS X x)
  · have := hσ.mono_f
    let T : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
      ShortComplex.mk (0 : (tensorPullbackFunctor f G).obj σ.X₁ ⟶
          (tensorPullbackFunctor f G).obj σ.X₁)
        ((tensorPullbackFunctor f G).map σ.f) zero_comp
    refine (T.exact_iff_mono rfl).1 ?_
    refine (Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
      (smallEtaleRingedTopos B S hS X).O
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2)).2 ?_
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
    have h₁ := preservesFiniteLimits_tensorPullbackFunctor_comp_stalk f G x (hG x)
    have hz : (structureModuleStalkFunctorAtPoint B S hS X x).PreservesZeroMorphisms :=
      Stacks.preservesZeroMorphisms_sheafModuleFiberOfCommRing
        (smallEtaleRingedTopos B S hS X).O (etaleSitePoint B S hS X.1 x X.2)
    refine ((T.map (structureModuleStalkFunctorAtPoint B S hS X x)).exact_iff_mono
      ((structureModuleStalkFunctorAtPoint B S hS X x).map_zero _ _)).2 ?_
    exact inferInstanceAs (Mono
      ((tensorPullbackFunctor f G ⋙ structureModuleStalkFunctorAtPoint B S hS X x).map σ.f))

end AlgebraicGeometry.Space

end
