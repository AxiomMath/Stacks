module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTrace
import StacksCore.Tactic.StacksAttribute

/-!
# The trace map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` for algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces and let `a`
be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `L` in `D_QCoh(𝒪_X)` and `K` in
`D_QCoh(𝒪_Y)` there is the canonical map

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

the canonical map `Rf_*R𝓗om(L, M) ⟶ R𝓗om(Rf_*L, Rf_*M)` followed by the counit `Rf_*a(K) ⟶ K`.
It becomes an isomorphism after applying a right adjoint `DQ_Y` of the inclusion
`D_QCoh(𝒪_Y) ⟶ D(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomPushforwardMap`: the canonical map
  `Rf_*R𝓗om(L, M) ⟶ R𝓗om(Rf_*L, Rf_*M)`.
* `AlgebraicGeometry.Space.smallEtalePushforwardTrace`: the trace map
  `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)`.

## Main results

* `AlgebraicGeometry.Space.isIso_coherator_map_smallEtalePushforwardTrace`: the trace map becomes
  an isomorphism after applying a right adjoint of the inclusion `D_QCoh(𝒪_Y) ⟶ D(𝒪_Y)`.

## References

* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
* [Stacks Project, Tag 0E58](https://stacks.math.columbia.edu/tag/0E58)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- For a morphism `f` of algebraic spaces, the canonical map
`Rf_*R𝓗om(L, M) ⟶ R𝓗om(Rf_*L, Rf_*M)`, adjoint to the relative cup product followed by `Rf_*`
of the evaluation `R𝓗om(L, M) ⊗^L L ⟶ M`. -/
def smallEtaleDerivedSheafHomPushforwardMap (f : X ⟶ Y)
    (L M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op L)).obj M) ⟶
      ((smallEtaleDerivedSheafHom B S hS Y).obj
        (op ((derivedModulePushforward B S hS f).obj L))).obj
          ((derivedModulePushforward B S hS f).obj M) :=
  InternalHomTrace.pushforwardInternalHomMap (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS Y)
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y) L M

variable (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1)
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- For a morphism `f : X ⟶ Y` of quasi-compact and quasi-separated algebraic spaces with right
adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and `L` in `D_QCoh(𝒪_X)`, `K` in
`D_QCoh(𝒪_Y)`, the canonical map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)`: the map
`smallEtaleDerivedSheafHomPushforwardMap` followed by `R𝓗om(Rf_*L, -)` of the counit
`Rf_*a(K) ⟶ K`. -/
def smallEtalePushforwardTrace (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) ⟶
      ((smallEtaleDerivedSheafHom B S hS Y).obj
        (op ((derivedModulePushforward B S hS f).obj L.obj))).obj K.obj :=
  InternalHomTrace.pushforwardTrace (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS Y)
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y) L.obj
    ((quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)).counit.app
        K).hom

/-- The trace map is `smallEtaleDerivedSheafHomPushforwardMap` followed by `R𝓗om(Rf_*L, -)` of
the counit. -/
theorem smallEtalePushforwardTrace_eq (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K =
      smallEtaleDerivedSheafHomPushforwardMap f L.obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj ≫
        ((smallEtaleDerivedSheafHom B S hS Y).obj
          (op ((derivedModulePushforward B S hS f).obj L.obj))).map
          ((quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs
              f.hom)).counit.app K).hom :=
  rfl

/-- Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces, `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `L` in `D_QCoh(𝒪_X)` and `K` in
`D_QCoh(𝒪_Y)`. Then the trace map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` becomes an isomorphism
after applying any right adjoint `DQ_Y` of the inclusion `D_QCoh(𝒪_Y) ⟶ D(𝒪_Y)`. -/
@[stacks 0E58]
theorem isIso_coherator_map_smallEtalePushforwardTrace
    {DQ : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjQ : (QcohDerived B S hS Y).ι ⊣ DQ)
    (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (DQ.map (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K)) := by
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  refine InternalHomTrace.isIso_map_of_bijective_comp adjQ _ fun M => ?_
  let adj := quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs hfqc hfqs
  let E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨((smallEtaleDerivedTensor B S hS X).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj M.obj)).obj L.obj,
      qcohDerived_smallEtaleDerivedTensor X _ _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f M.obj M.property) L.property⟩
  refine InternalHomTrace.bijective_comp_pushforwardTrace _ _ _ _ _ _ _ _ L.obj _ M.obj
    (isIso_smallEtaleProjectionFormulaMapSnd B S hS f hfqc hfqs M.obj M.property L.obj
      L.property) ?_
  have key : (fun v : E.obj ⟶ ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj =>
      (derivedModulePushforward B S hS f).map v ≫ (adj.counit.app K).hom) =
      (fun w => w.hom) ∘ (adj.homEquiv E K).symm ∘
        ((ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv (X := E)
          (Y := (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K)).symm := by
    funext v
    simp only [Function.comp_apply, Adjunction.homEquiv_counit]
    rfl
  exact key ▸ ((ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y)).homEquiv.bijective.comp
    ((adj.homEquiv E K).symm.bijective.comp
      (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv.symm.bijective))

end AlgebraicGeometry.Space

end
