module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianIsomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModelNaiveCotangentHomologyNegOneCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.Cotangent.FiniteHomology
public import StacksFrontier.Cotangent.Spaces.ModelCotangentAffineSections

/-!
# The cohomology sheaves of the cotangent complex of a morphism to an affine scheme

Let `f : X ⟶ T` be a morphism from an algebraic space to an object `T` of the big fppf site with
affine underlying scheme, and let `L_{X/T}` be its cotangent complex (Stacks 08SU), formed on the
model of the small étale site of `X` (`AlgebraicGeometry.Space.modelRingedToposHom`). This file
reads the cohomology sheaves `H^i(L_{X/T})`, carried back to `X` by the Comparison Lemma, on the
affine étale charts of `X`, and proves that they are cartesian there
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_modelCotangentHomology`): along a morphism
`V ⟶ U` of affine étale charts, `𝒪(V) ⊗_{𝒪(U)} H^i(U) ⟶ H^i(V)` is bijective. By Descent,
Proposition 03DX (2) in the form of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse`, the
cohomology sheaves are quasi-coherent.

The cohomology sheaves are the sheafifications of `W ↦ H^i(L_{𝒪(W)/Λ})`, `Λ = Γ(T, 𝒪_T)`
(`AlgebraicGeometry.Space.modelCotangentHomologyIso`, from Tag 08VG on the model and the presheaf
base form of Tag 08SX), whose sections over the affine charts are unchanged by sheafification and
whose restriction maps along morphisms of affine charts are étale base changes
(`StacksFrontier/Cotangent/Spaces/ModelCotangentAffineSections.lean`). Being cartesian along a
morphism is unchanged by isomorphisms of presheaves of modules, by morphisms bijective at the two
ends, and by replacing the morphism by an isomorphic arrow, which is how it is carried from the
model to `X`.

## Main definitions

* `AlgebraicGeometry.Space.modelCotangentHomologyIso`: `H^i(L_{X/T})` is the sheafification of
  `W ↦ H^i(L_{𝒪(W)/Λ})`.

## Main results

* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_modelCotangentHomology`
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_modelCotangentHomology`
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modelCotangentHomology`

## References

* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **`H^i(L_{X/T})` is the sheafification of `W ↦ H^i(L_{𝒪(W)/Λ})`** on the model, `Λ = Γ(T, 𝒪_T)`
and `T` affine: the change of base `L_{𝒪_X/f⁻¹Λ̲} ⟶ L_{X/T}` is a quasi-isomorphism (Tag 08VG),
and `L_{𝒪_X/f⁻¹Λ̲}` is the sheafification of `W ↦ L_{𝒪(W)/Λ}` (Tag 08SX over the constant
presheaf), sheafification commuting with cohomology. -/
def modelCotangentHomologyIso (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : ℤ) :
    (modelRingedToposHom f).cotangentComplex.homology i ≅
      (CategoryTheory.Sheaf.moduleSheafification.{u, u, u} (modelTopos X).J
        (B := (modelTopos X).O)).obj (modelPresheafBaseHomology f i) :=
  haveI := quasiIso_modelTowerChangeOfBase f hT
  (asIso (HomologicalComplex.homologyMap (CategoryTheory.Sheaf.towerCotangentChangeOfBase.{u, u, u}
    (modelTopos X).J (modelTowerLower f) (modelRingedToposHom f).fSharpInverseImage) i)).symm ≪≫
    (CategoryTheory.Sheaf.presheafBaseCohomologySheafIso.{u, u, u} (modelTopos X).J
      (modelTowerMap f) (modelConstantBaseMap f) (W_modelConstantBaseMap f) i).symm

/-- The unit of the sheafification of `W ↦ H^i(L_{𝒪(W)/Λ})` is bijective over the affine étale
charts. -/
theorem bijective_modelPresheafBaseHomology_unit_app (i : ℤ) (U : AffineEtale B S hS X.1) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj)).unit.app
        (modelPresheafBaseHomology f i)).app (op ((modelAffineChartFunctor X).obj U))) := by
  have := isIso_toSheafify_modelPresheafBaseHomology_app f i U
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify (modelTopos X).J (modelPresheafBaseHomology f i).presheaf).app
      (op ((modelAffineChartFunctor X).obj U)))

/-- **Along a morphism of affine étale charts, `H^i(L_{X/T})` is a base change** on the model. -/
theorem isIso_restrictionBaseChange_modelCotangentHomology
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : ℤ)
    {U V : AffineEtale B S hS X.1} (g : U ⟶ V) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u, u, u, u}
      (R := (modelTopos X).O.obj) ((modelRingedToposHom f).cotangentComplex.homology i).val
        ((modelAffineChartFunctor X).map g).op) := by
  have h0 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u, u, u, u}
      (R := (modelTopos X).O.obj) (modelPresheafBaseHomology f i)
        ((modelAffineChartFunctor X).map g).op) :=
    isIso_restrictionAdjoint_modelPresheafBaseHomology f i g
  have h1 := (Stacks.PresheafOfModules.isIso_restrictionBaseChange_iff_of_bijective_app
    ((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj)).unit.app
        (modelPresheafBaseHomology f i)) ((modelAffineChartFunctor X).map g).op
    (bijective_modelPresheafBaseHomology_unit_app f i V)
    (bijective_modelPresheafBaseHomology_unit_app f i U)).1 h0
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
    ((SheafOfModules.forget _).mapIso (modelCotangentHomologyIso f hT i).symm) _ _ _ h1

/-- **The cohomology sheaves of `L_{X/T}`, carried back to `X`, are cartesian on the affine étale
charts**, for `T` affine. -/
theorem isCartesianOnAffineCharts_modelCotangentHomology
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : ℤ) :
    IsCartesianOnAffineCharts ((smallEtaleModelModulesEquiv B S hS X).inverse.obj
      ((modelRingedToposHom f).cotangentComplex.homology i)) := by
  intro U V hU hV f₀
  let e := smallEtaleModelEquiv B S hS X
  let E := smallEtaleModelModulesEquiv B S hS X
  let N := (modelRingedToposHom f).cotangentComplex.homology i
  have h1 := isIso_restrictionBaseChange_modelCotangentHomology f hT i
    (show (⟨V, hV⟩ : AffineEtale B S hS X.1) ⟶ ⟨U, hU⟩ from ObjectProperty.homMk f₀)
  have h2 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u, u, u, u}
      (R := (modelTopos X).O.obj) (E.functor.obj (E.inverse.obj N)).val (e.functor.map f₀).op) :=
    @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
      ((SheafOfModules.forget _).mapIso (E.counitIso.app N).symm) _ _ _ h1
  have h3 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS X.1) (E.inverse.obj N).val
        (e.inverse.map (e.functor.map f₀)).op) := h2
  have h4 := @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_arrow_iso _ _ _
    (E.inverse.obj N).val _ _ _ _ f₀.op (e.inverse.map (e.functor.map f₀)).op
    (e.unitInv.app U).op (e.unitInv.app V).op ((e.unitIso.app U).symm.op).isIso_hom
    ((e.unitIso.app V).symm.op).isIso_hom
    (op_comp.symm.trans ((congrArg Quiver.Hom.op (e.unitInv.naturality f₀).symm).trans
      op_comp)) h3
  exact (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS X.1 X.2
    (E.inverse.obj N) f₀).2 h4

/-- **The cohomology sheaves of `L_{X/T}`, carried back to `X`, are quasi-coherent**, for `T`
affine (Descent, Proposition 03DX (2)). -/
theorem isQuasicoherentOnSite_modelCotangentHomology
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : ℤ) :
    ((smallEtaleModelModulesEquiv B S hS X).inverse.obj
      ((modelRingedToposHom f).cotangentComplex.homology i)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse _
    (isCartesianOnAffineCharts_modelCotangentHomology f hT i)

/-! ### Finiteness of the sections over the affine charts -/

/-- On an object `W` of the model, the composite `Λ ⟶ f⁻¹Λ̲ ⟶ 𝒪_X` of the presheaf base is the
ring map `Γ(U ⟶ T)` of the étale chart `U` of `X` underlying `W`. -/
theorem modelSectionsAlgebraMap_eq (W : (modelTopos X).C) :
    (modelConstantBaseMap f ≫ (modelTowerMap f).hom).app (op W) =
      (chartBaseStructurePresheafMap f).app
        (op ((smallEtaleModelEquiv B S hS X).inverse.obj W)) :=
  congrArg (fun φ => φ.app (op W)) (modelConstantBaseMap_comp f)

/-- **Over an object of the model lying over an affine étale chart, the sections of `𝒪_X` are of
finite type over `Λ = Γ(T, 𝒪_T)`**, for `f` locally of finite type and `T` affine. -/
theorem finiteType_modelSectionsAlgebraMap (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (W : (modelTopos X).C)
    (hW : IsAffine (chartScheme ((smallEtaleModelEquiv B S hS X).inverse.obj W))) :
    ((modelConstantBaseMap f ≫ (modelTowerMap f).hom).app (op W)).hom.FiniteType := by
  rw [modelSectionsAlgebraMap_eq]
  exact algebraFiniteType_chartDiagram B S hS f hf
    (affineTargetChartDiagram f ((smallEtaleModelEquiv B S hS X).inverse.obj W)) hW hT

/-- **Over an object of the model lying over an affine étale chart, the sections of `H^i(L_{X/T})`
form a finite module**, for `f` locally of finite type, `T` affine and `Γ(T, 𝒪_T)` Noetherian:
they are `H^i(L_{𝒪(W)/Λ})` (sheafification not changing them), finite by Tag 08PZ. -/
theorem moduleFinite_modelCotangentHomology_obj (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)]
    (i : ℤ) (U : AffineEtale B S hS X.1) :
    Module.Finite ((Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj.obj
        (op ((modelAffineChartFunctor X).obj U)))
      (((modelRingedToposHom f).cotangentComplex.homology i).val.obj
        (op ((modelAffineChartFunctor X).obj U))) := by
  let W := (modelAffineChartFunctor X).obj U
  have hW : IsAffine (chartScheme ((smallEtaleModelEquiv B S hS X).inverse.obj W)) :=
    (IsAffineChart B S hS X.1).prop_of_iso ((smallEtaleModelEquiv B S hS X).unitIso.app U.obj)
      U.property
  let : Algebra (baseRing B S hS T) ((modelTopos X).O.obj.obj (op W)) :=
    ((modelConstantBaseMap f ≫ (modelTowerMap f).hom).app (op W)).hom.toAlgebra
  have : Algebra.FiniteType (baseRing B S hS T) ((modelTopos X).O.obj.obj (op W)) :=
    finiteType_modelSectionsAlgebraMap f hf hT W hW
  have : Module.Finite ((Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj.obj (op W))
      ((CommAlgCat.cotangentComplex.{u, u} ((modelConstantPresheaf (X := X) (T := T)).obj (op W))
        (CategoryTheory.Sheaf.sectionsAlgebra ⊥ (CategoryTheory.Sheaf.presheafBaseHom.{u, u, u}
          (modelTopos X).J (modelTowerMap f) (modelConstantBaseMap f)) (op W))).homology i) :=
    CommAlgCat.finite_homology_cotangentComplex (baseRing B S hS T)
      ((modelTopos X).O.obj.obj (op W)) i
  have : Module.Finite ((Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj.obj
      (op W)) (((𝟭 (PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
        (modelTopos X).O).obj)).obj (modelPresheafBaseHomology f i)).obj (op W)) :=
    Module.Finite.equiv (CategoryTheory.Sheaf.presheafBaseHomologyObjIso.{u, u, u}
      (modelTopos X).J (modelTowerMap f) (modelConstantBaseMap f) i (op W)).toLinearEquiv
  have : Module.Finite ((Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj.obj (op W))
      ((PresheafOfModules.evaluation _ (op W)).obj ((SheafOfModules.forget _).obj
        ((CategoryTheory.Sheaf.moduleSheafification.{u, u, u} (modelTopos X).J
          (B := (modelTopos X).O)).obj (modelPresheafBaseHomology f i)))) :=
    Module.Finite.of_surjective
      (((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (modelTopos X).O).obj)).unit.app
          (modelPresheafBaseHomology f i)).app (op W)).hom
      (bijective_modelPresheafBaseHomology_unit_app f i U).2
  exact Module.Finite.equiv ((PresheafOfModules.evaluation _ (op W)).mapIso
    ((SheafOfModules.forget _).mapIso (modelCotangentHomologyIso f hT i).symm)).toLinearEquiv

/-- **Over an affine étale chart, the sections of the cohomology sheaves of `L_{X/T}`, carried back
to `X`, form a finite module**, for `f` locally of finite type, `T` affine and `Γ(T, 𝒪_T)`
Noetherian: over the chart lying over the corresponding object of the model they are finite, and
the given chart is isomorphic to it, the sections over it being the base change. -/
theorem moduleFinite_sections_modelCotangentHomology (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)]
    (i : ℤ) (C : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (hC : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj C)) :
    Module.Finite (chartRing B S hS X.1 X.2 C)
      (((smallEtaleModelModulesEquiv B S hS X).inverse.obj
        ((modelRingedToposHom f).cotangentComplex.homology i)).val.obj (op C)) := by
  let e := smallEtaleModelEquiv B S hS X
  let E := smallEtaleModelModulesEquiv B S hS X
  let N := (modelRingedToposHom f).cotangentComplex.homology i
  let U' := e.inverse.obj (e.functor.obj C)
  have hU' : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U') :=
    (IsAffineChart B S hS X.1).prop_of_iso (e.unitIso.app C) hC
  let ε := (PresheafOfModules.evaluation _ (op (e.functor.obj C))).mapIso
    ((SheafOfModules.forget _).mapIso (E.counitIso.app N).symm)
  have : Module.Finite (chartRing B S hS X.1 X.2 ((e.functor ⋙ e.inverse).obj C))
      ((E.inverse.obj N).val.obj (op ((e.functor ⋙ e.inverse).obj C))) :=
    Module.Finite.of_surjective (hM := moduleFinite_modelCotangentHomology_obj f hf hT i ⟨C, hC⟩)
      ε.toLinearEquiv.toLinearMap ε.toLinearEquiv.surjective
  have hbc := isCartesianOnAffineCharts_modelCotangentHomology f hT i U' C hU' hC (e.unit.app C)
  let := chartAlgebra (hF := X.2) (e.unit.app C)
  exact Module.Finite.of_surjective (sectionsBaseChange (E.inverse.obj N) (e.unit.app C)) hbc.2

/-- **An algebraic space locally of finite type over a Noetherian affine scheme is locally
Noetherian**: every étale scheme over it is locally of finite type over the base. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_locallyOfFiniteType
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)] :
    HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V) := by
  refine (exists_atlas_iff_forall_etale B S hS X.1 _ X.2).2 fun V g hg => ?_
  let Uc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk g, hg⟩
  let d := affineTargetChartDiagram f Uc
  let Ts := (BigFppfOver.toScheme B S hS).obj T
  have : IsNoetherianRing Γ(Ts, ⊤) := ‹IsNoetherianRing (baseRing B S hS T)›
  have : IsLocallyNoetherian Ts := LocallyOfFiniteType.isLocallyNoetherian Ts.isoSpec.hom
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  exact @LocallyOfFiniteType.isLocallyNoetherian _ _ ((BigFppfOver.toScheme B S hS).map d.g)
    hlft ‹IsLocallyNoetherian Ts›

/-- **The cohomology sheaves of `L_{X/T}` are coherent**, for `f : X ⟶ T` locally of finite type
with `T` affine and `Γ(T, 𝒪_T)` Noetherian: they are quasi-coherent, and of finite type, their
sections over the affine étale charts being finite (Tag 08PZ), on the locally Noetherian `X`
(Stacks 07UB). -/
theorem isCoherent_modelCotangentHomology (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)]
    (i : ℤ) :
    IsCoherent B S hS X.1 X.2 ((smallEtaleModelModulesEquiv B S hS X).inverse.obj
      ((modelRingedToposHom f).cotangentComplex.homology i)) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_locallyOfFiniteType f hf hT⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 _).2
    ⟨isQuasicoherentOnSite_modelCotangentHomology f hT i,
      Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
        (isFiniteTypeOnSite_of_forall_affine_moduleFinite B S hS X.1 X.2 _
          (isCartesianOnAffineCharts_modelCotangentHomology f hT i)
          (moduleFinite_sections_modelCotangentHomology f hf hT i))⟩

end AlgebraicGeometry.Space

end
