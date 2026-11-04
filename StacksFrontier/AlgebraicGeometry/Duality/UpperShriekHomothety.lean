module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingHomothety
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSliceSelfUnit
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfection
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.Devissage.DerivedHomCoproductsLargeUniverse
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyLocal
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfectionPerfect

/-!
# The homothety of the relative dualizing complex

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a perfect morphism of
`AlgebraicGeometry.FTS S` (for instance a flat one).
If `ω` is an object of `D(𝒪_X)` with the affine-chart description of `f^!𝒪_Y`, then the homothety
`𝒪_X ⟶ R𝓗om_{𝒪_X}(ω, ω)` is an isomorphism. This is the second assertion of
[Stacks, Tag 0E9T] for an object described chart by chart.

## Main results

* `Stacks.Duality.isIso_derivedHomothety_upperShriekFunctor_structureModel` — over a chart, the
  derived homothety of `φ^!Γ(Y, V)` is invertible ([Stacks, Tag 0BZW] (1)(c)).
* `Stacks.Duality.exists_iso_overFunctor_of_isShriekOfStructureSheafOnCharts` — the chart
  description read behind the slice-site restriction, at the standard model.
* `Stacks.Duality.isIso_derivedSheafHomothety_of_isShriekOfStructureSheafOnCharts` — the
  homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(ω, ω)` is an isomorphism.

## References

* [Stacks Project, Tag 0E9T](https://stacks.math.columbia.edu/tag/0E9T)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open StacksDraft.TorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- **The derived homothety of the chart model of `f^!𝒪_Y` is invertible.** For `f` perfect, an
affine open `U ⊆ X` over an affine open `V ⊆ Y` and a polynomial presentation `p` of `f.appLE V U`,
the derived homothety `Γ(X, U) ⟶ R𝐻om(φ^!Γ(Y, V), φ^!Γ(Y, V))` is an isomorphism.

This is [Stacks, Tag 0BZW] (1)(c), the chart ring map being perfect by
`AlgebraicGeometry.Perfect.perfect_appLE`; it is read at the chain level, so at the tensor--Hom
adjunction the comparison of [Stacks, Tag 0A6H] is stated with. -/
theorem isIso_derivedHomothety_upperShriekFunctor_structureModel [Perfect f.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    IsIso (Dualizing.derivedHomothety
      (StacksDraft.DerivedHom.derivedHomAdjunction
        (R := (Γ(X.left, U) : Type u))).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (Γ(X.left, U) : Type u))))
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (Γ(X.left, U) : Type u))).tensorUnitLeft
      (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) := by
  have hVn : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let D : CertifiedDerivedTensoring.{u, u} Γ(Y.left, V) :=
    canonicalCertifiedDerivedTensoring Γ(Y.left, V)
  let : Module p.Poly Γ(X.left, U) := Module.compHom Γ(X.left, U) p.toRingHom
  have hperf₀ : StacksDraft.Perfect.IsPerfectModule (R := p.Poly) Γ(X.left, U) := by
    let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
    exact RingHom.isPerfectModule_of_isPerfectRingMap D.tensor D.comparison D.isLeftDerived
      (AlgebraicGeometry.Perfect.perfect_appLE f.left U hU V hV hUV D) p.variableCount
      (AlgHom.mk p.toRingHom fun r ↦ congrArg (· r) p.commutes) p.surjective
  obtain ⟨J, b, hJge, hJinj, ⟨eJ⟩, hJ⟩ :=
    Dualizing.upperShriekFunctor_unit_exists_quasiIso_homothety.{u, u} p
      (StacksDraft.Perfect.isPerfectModule_ulift.{u, u} Γ(X.left, U) hperf₀)
  have := hJge
  have := hJinj
  exact Dualizing.isIso_derivedHomothety_of_injectiveRepresentative _ _ J b
    (eJ.symm ≪≫ p.upperShriekFunctor.{u, u}.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).mapIso
        (LinearEquiv.toModuleIso
          (ULift.moduleEquiv (R := Γ(Y.left, V)) (M := Γ(Y.left, V)) :
            ULift.{u} Γ(Y.left, V) ≃ₗ[Γ(Y.left, V)] Γ(Y.left, V))))) hJ

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The chart description of `f^!𝒪_Y`, read behind the slice-site restriction.** If `ω` has the
affine-chart description `Stacks.Duality.IsShriekOfStructureSheafOnCharts`, then every point of
`X` lies in an affine open `U` over an affine open `V` of `Y` such that the restriction of `ω` to
the slice site `Opens(X)/U`, read in the open-subscheme model, is the complex associated to the
algebraic upper shriek of `Γ(Y, V)` along a presentation of `f.appLE V U`. -/
theorem exists_iso_overFunctor_of_isShriekOfStructureSheafOnCharts
    (ω : DerivedCategory X.left.Modules) (hw : IsShriekOfStructureSheafOnCharts f ω)
    (x : X.left) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens) (_hV : IsAffineOpen V)
      (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty (((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u} X.left.ringCatSheaf U).mapDerivedCategory.obj ω) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V))) := by
  obtain ⟨U, hU, V, hV, hUV, hx, p, ⟨e⟩⟩ := hw x
  exact ⟨U, hU, V, hV, hUV, hx, p, ⟨(Stacks.SheafOfModules.derivedOverFunctorEquiv U).app ω ≪≫
    Stacks.Injectives.isoOfTargetModelIso.{u} U.toScheme.Modules
      (Scheme.Modules.restrictFunctor U.ι)
      (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ω _ e⟩⟩

/-- Sheafification on the site of opens of a scheme, supplied directly. -/
private local instance hasSheafifyOpensScheme (W : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology W) AddCommGrpCat.{u} := inferInstance

/-- Sheafification on a slice of the site of opens of a scheme, supplied directly. -/
private local instance hasSheafifyOverOpens (W : Scheme.{u}) (U : W.Opens) :
    HasSheafify ((Opens.grothendieckTopology W).over U) AddCommGrpCat.{u} := inferInstance

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive

/-- `M ⊗_{𝒪_W} -` is additive. -/
private local instance sheafTensor_obj_additive' (W : Scheme.{u})
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj M).Additive :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive W.sheaf M

/-- The total tensor complex of two complexes of `𝒪_W`-modules exists. -/
private local instance hasMapBifunctor_sheafTensor' (W : Scheme.{u})
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf) (ComplexShape.up ℤ) :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor W.sheaf K L

/-- **The homothety of an object with the chart description of `f^!𝒪_Y` is an isomorphism.**
Let `f : X ⟶ Y` be a perfect morphism of `FTS S` and let `ω` be an object of `D(𝒪_X)` which over
affine charts `U → V` is the complex associated to `φ^!Γ(Y, V)` for a presentation of the chart
ring map `φ = f.appLE V U`. Then `𝒪_X ⟶ R𝓗om_{𝒪_X}(ω, ω)` is an isomorphism.

Over a chart, [Stacks, Tag 0BZW] (1)(c) makes `R𝐻om(φ^!Γ(Y, V), φ^!Γ(Y, V))` the ring in degree
zero, the comparison of [Stacks, Tag 0A6H] carries this to `R𝓗om(ω|_U, ω|_U) ≅ 𝒪_U`, and the
homothety is an isomorphism as soon as this holds over the members of an open covering. -/
theorem isIso_derivedSheafHomothety_of_isShriekOfStructureSheafOnCharts [Perfect f.left]
    (ω : DerivedCategory X.left.Modules) (hw : IsShriekOfStructureSheafOnCharts f ω) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.left.sheaf ω) := by
  choose U hU V hV hUV hx p e using
    exists_iso_overFunctor_of_isShriekOfStructureSheafOnCharts f ω hw
  have hY : (Opens.grothendieckTopology X.left).CoversTop U :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩))
  refine Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_iso_unit X.left.sheaf ω hY
    fun x => ?_
  have hB := derivedCategoryBBounded_upperShriekFunctor_structureModel_of_perfect f (hU x) (hV x)
    (hUV x) (p x)
  have : IsNoetherianRing Γ(X.left, U x) :=
    IsLocallyNoetherian.component_noetherian ⟨U x, hU x⟩
  obtain ⟨n, hn⟩ := hB.1.1
  exact Stacks.Duality.nonempty_derivedSheafHom_restrictD_self_iso_unit (U x) (hU x)
    (Dualizing.isPseudoCoherent_of_derivedCategoryBMinus.{u, u} ⟨hB.1.2, hB.2⟩)
    ⟨n, (DerivedCategory.isGE_iff _ n).2 hn⟩
    (isIso_derivedHomothety_upperShriekFunctor_structureModel f (hU x) (hV x) (hUV x) (p x))
    ω (e x).some

end Stacks.Duality

end
