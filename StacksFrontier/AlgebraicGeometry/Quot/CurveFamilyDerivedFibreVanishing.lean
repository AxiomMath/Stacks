module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPushforwardOverPointIsLE
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.FibreCycleLift

/-!
# The derived fibres of `Rf_*𝒪_X` of a family of curves vanish above degree one

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) for which the base change map
`Lh^*Rf_*𝒪_X ⟶ Rf'_*𝒪_{X'}` of Stacks 0CTM, part (1), is an isomorphism for every morphism of
families (`AlgebraicGeometry.CurveFamily.HasDerivedStructureSheafBaseChange`). Let `V = Spec A` be
an affine étale chart of `S` on which `(Rf_*𝒪_X)|_V ≅ 𝒪_V ⊕ P` with `P` strictly perfect (Stacks
0E6B, part (b)), and let `P = M^~` for a complex `M` of `A`-modules. Then for every prime `𝔭` of
`A` the derived fibre `M ⊗^L_A κ(𝔭)` has no cohomology in degrees `≥ 2`.

This is the step "`H^i(P ⊗^L κ(s)) = H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2`" of the proof of Stacks
0E1J: the restriction of the base change isomorphism to `Spec κ(𝔭) ⟶ V ⟶ S` identifies
`𝒪 ⊕ (M ⊗^L_A κ(𝔭))^~` with `Rf'_*𝒪_{X'}` for the fibre `X' = X ×_S Spec κ(𝔭)`, a family of curves
over a one-point base, whose derived direct image has no cohomology above degree one
(`AlgebraicGeometry.CurveFamily.hasDerivedStructureSheafPushforwardIsLEOne_of_subsingleton`).

## Main definitions

* `AlgebraicGeometry.Space.primeResidueObject`, `AlgebraicGeometry.Space.primeResidueMap`: the
  point `Spec κ(𝔭) ⟶ U` of an affine object `U` of the big fppf site at a prime `𝔭` of `Γ(U)`.
* `AlgebraicGeometry.Space.primeResidueRingEquiv`: `Γ(Spec κ(𝔭)) ≅ κ(𝔭)`, compatibly with
  `Γ(U) ⟶ κ(𝔭)` (`AlgebraicGeometry.Space.primeResidueRingEquiv_comp`).

## Main results

* `AlgebraicGeometry.CurveFamily.isZero_homology_derivedExtension_primeResidueMap_of_splitting`.
* `StacksDraft.Perfect.isZero_homology_fibreComplex_comp_ringEquiv`: vanishing of the homology of
  a termwise base change is unchanged by composing with a ring isomorphism.

## Implementation notes

No declaration here carries a `stacks` attribute: these are steps of the proof of Stacks 0E1J.
The derived categories are those of the standard model, fixed by `letI` inside the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Vanishing of the homology of a termwise base change along a ring isomorphism -/

namespace StacksDraft.Perfect

/-- **Composing a base change with a ring isomorphism keeps homology zero.** If the termwise base
change `A' ⊗_A F` of a complex of `A`-modules has zero homology in degree `j`, so has
`K ⊗_A F` for any ring isomorphism `e : A' ≅ K`: the second is the base change of the first along
`e`, an exact functor. -/
theorem isZero_homology_fibreComplex_comp_ringEquiv {A A' K : Type u} [CommRing A] [CommRing A']
    [CommRing K] (φ : A →+* A') (e : A' ≃+* K) (F : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
    (h : IsZero ((FibreCycleLift.fibreComplex φ F).homology j)) :
    IsZero ((FibreCycleLift.fibreComplex ((e : A' →+* K).comp φ) F).homology j) := by
  let G := ModuleCat.extendScalars.{u, u, u} (e : A' →+* K)
  have : PreservesFiniteLimits G :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.Flat.of_bijective e.bijective)
  have : G.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj (e : A' →+* K)).isLeftAdjoint
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ _ j).mapIso
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ (e : A' →+* K))
      (ComplexShape.up ℤ)).app F))
  exact IsZero.of_iso (G.map_isZero h)
    (((FibreCycleLift.fibreComplex φ F).sc j).mapHomologyIso G)

end StacksDraft.Perfect

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-! ### The residue field point of an affine object at a prime -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [p.IsPrime]

/-- `U ⟶ S` read through `U ≅ Spec Γ(U)`, as a scheme over `S`. -/
abbrev primeSpecOver : Over S :=
  Over.mk (((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv ≫ B.inclusion.map U.hom)

/-- The prime `𝔭` as a point of `Spec Γ(U)`. -/
abbrev primeSpecPoint : (primeSpecOver B S hS U).left := ⟨p, inferInstance⟩

/-- The spectrum of the residue field of `Spec Γ(U)` at `𝔭` lies in the big fppf site. -/
theorem contains_spec_residueField_primeSpecPoint :
    B.Contains (Spec ((primeSpecOver B S hS U).left.residueField (primeSpecPoint B S hS U p))) := by
  have hT : ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff := U.left.property
  rw [Scheme.size_congr ((BigFppfOver.toScheme B S hS).obj U).isoSpec] at hT
  exact B.residueField_spec_contains hT _

/-- **The residue field point `Spec κ(𝔭)` of an affine object `U` at a prime `𝔭` of `Γ(U)`**, as
an object of the big fppf site. -/
abbrev primeResidueObject : BigFppfOver B S hS :=
  schemeSiteObject B hS (X := Over.mk ((primeSpecOver B S hS U).left.fromSpecResidueField
    (primeSpecPoint B S hS U p) ≫ (primeSpecOver B S hS U).hom))
    (contains_spec_residueField_primeSpecPoint B S hS U p)

/-- The residue field point `Spec κ(𝔭)` is an affine scheme. -/
instance isAffine_toScheme_primeResidueObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (primeResidueObject B S hS U p)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- **The map `Spec κ(𝔭) ⟶ U`** of the big fppf site, for a prime `𝔭` of `Γ(U)`. -/
def primeResidueMap : primeResidueObject B S hS U p ⟶ U :=
  Over.homMk ⟨(primeSpecOver B S hS U).left.fromSpecResidueField (primeSpecPoint B S hS U p) ≫
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv⟩ rfl

/-- **The global functions of `Spec κ(𝔭)` are `κ(𝔭)`.** -/
def primeResidueRingEquiv :
    Γ((BigFppfOver.toScheme B S hS).obj (primeResidueObject B S hS U p), ⊤) ≃+* p.ResidueField :=
  (Scheme.ΓSpecIso _ ≪≫ Scheme.Spec.residueFieldIso _ _).commRingCatIsoToRingEquiv

/-- The composite `Γ(U) ⟶ Γ(Spec κ(𝔭)) ≅ κ(𝔭)` of the map induced by `Spec κ(𝔭) ⟶ U` with
`primeResidueRingEquiv` is the residue map `Γ(U) ⟶ κ(𝔭)`. -/
theorem primeResidueRingEquiv_comp :
    ((primeResidueRingEquiv B S hS U p : _ ≃+* p.ResidueField) : _ →+* _).comp
        (representedAffineCommRingCatHom B S hS (primeResidueMap B S hS U p)).hom =
      algebraMap _ p.ResidueField := by
  have h : representedAffineCommRingCatHom B S hS (primeResidueMap B S hS U p) ≫
      (Scheme.ΓSpecIso _ ≪≫ Scheme.Spec.residueFieldIso _ _).hom =
        CommRingCat.ofHom (algebraMap _ p.ResidueField) := by
    have hrw := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (primeSpecPoint B S hS U p)
    show ((Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).fromSpecResidueField
      (primeSpecPoint B S hS U p) ≫
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso _ ≪≫
        Scheme.Spec.residueFieldIso _ (primeSpecPoint B S hS U p)).hom = _
    rw [← hrw, ← Spec.map_comp,
      Scheme.Hom.comp_appTop, Stacks.Modules.isoSpec_inv_appTop, Category.assoc, Iso.trans_hom,
      Scheme.ΓSpecIso_naturality_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Iso.inv_hom_id_assoc (Scheme.ΓSpecIso _) _
  exact congrArg CommRingCat.Hom.hom h

end Space

/-! ### The derived fibres of `Rf_*𝒪_X` above degree one -/

attribute [local instance] Space.etaleModulePullback_additive
  Space.preservesFiniteLimits_etaleModulePullback Space.preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The object of the big fppf site underlying an étale chart of the base of a family. -/
abbrev chartObject (X : CurveFamily B hZ)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1) : BigFppfOver B integerBase hZ :=
  (Space.SmallEtale.toOver B integerBase hZ (schemeSpace X.base).1).obj V

/-- **The derived fibres of the perfect summand of `Rf_*𝒪_X` vanish above degree one.** Let
`X` be a family of curves for which the base change map of Stacks 0CTM, part (1), at `𝒪_X` is an
isomorphism, `V` an étale chart of the base with affine scheme `Spec A`, on which
`(Rf_*𝒪_X)|_V ≅ 𝒪|_V ⊕ P`, and `M ∈ D(A)` with `M^~ ≅ P`. Then for every prime `𝔭` of `A`,
`H^n(M ⊗^L_A κ(𝔭)) = 0` for `n ≥ 2`, where `κ(𝔭)` is read as the ring of functions of the point
`Spec κ(𝔭) ⟶ V`. -/
theorem isZero_homology_derivedExtension_primeResidueMap_of_splitting {X : CurveFamily B hZ}
    (hbc : X.HasDerivedStructureSheafBaseChange)
    (V : Space.SmallEtale B integerBase hZ (schemeSpace X.base).1)
    [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj
      (X.chartObject V))]
    (P : CochainComplex (Space.Modules.{u, u} B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2) ℤ)
    (e :
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
              (Space.structureSheafModule B integerBase hZ X.total))) ≅
        (Space.etaleModulePullback.{u, u} B integerBase hZ
          (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
          (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base)
              V)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
              0).obj (Space.structureSheafModule B integerBase hZ (schemeSpace X.base))) ⊞
          DerivedCategory.Q.obj P)
    (M :
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase hZ).obj
        (X.chartObject V), ⊤)))
    (eM :
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (X.chartObject V))
          (isAlgebraicSpace_yoneda B integerBase hZ (X.chartObject V)))
      (Space.representedAffineDerivedAssociated B integerBase hZ
        (X.chartObject V)).obj M ≅
        DerivedCategory.Q.obj P)
    (p : Ideal Γ((BigFppfOver.toScheme B integerBase hZ).obj
      (X.chartObject V), ⊤)) [p.IsPrime]
    (n : ℤ) (hn : 2 ≤ n) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (X.chartObject V), ⊤))
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (Space.primeResidueObject B integerBase hZ
          (X.chartObject V) p), ⊤))
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((Space.representedAffineDerivedExtension B integerBase hZ
        (Space.primeResidueMap B integerBase hZ
          (X.chartObject V) p)).functor.obj
        M)) := by
  let g := Space.primeResidueMap B integerBase hZ (X.chartObject V) p
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
    hZ).obj (X.chartObject V), ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
    hZ).obj (Space.primeResidueObject B integerBase hZ (X.chartObject V) p), ⊤))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ X.total))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (X.total).1 (X.total).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace X.base)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (Space.chartSpace B
        integerBase hZ (schemeSpace X.base) V)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (Space.chartSpace B integerBase hZ (schemeSpace X.base)
        V).1 (Space.chartSpace B integerBase hZ (schemeSpace X.base) V).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace (X.chartObject V) : AlgebraicSpaces B integerBase hZ)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ
      ((schemeSpace (X.chartObject V) : AlgebraicSpaces B integerBase hZ)).1
      ((schemeSpace (X.chartObject V) : AlgebraicSpaces B integerBase hZ)).2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace (Space.primeResidueObject B integerBase hZ (X.chartObject V) p) :
        AlgebraicSpaces B integerBase hZ)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ
      ((schemeSpace (Space.primeResidueObject B integerBase hZ (X.chartObject V) p) :
        AlgebraicSpaces B integerBase hZ)).1
      ((schemeSpace (Space.primeResidueObject B integerBase hZ (X.chartObject V) p) :
        AlgebraicSpaces B integerBase hZ)).2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (X.chartObject V))
      (isAlgebraicSpace_yoneda B integerBase hZ (X.chartObject V)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (yoneda.obj (Space.primeResidueObject B integerBase hZ
        (X.chartObject V) p))
      (isAlgebraicSpace_yoneda B integerBase hZ (Space.primeResidueObject B integerBase hZ
          (X.chartObject V) p)))
  -- the field point of the base through the chart
  let jV : (X.chartObject V) ⟶ X.base := yoneda.preimage V.obj.hom
  let h : (Space.primeResidueObject B integerBase hZ (X.chartObject V) p) ⟶ X.base := g ≫ jV
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (X.baseChange h).total.1 (X.baseChange h).total.2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (X.baseChange
        h).total))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ (schemeSpace
        (X.baseChange h).base)))
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace (X.baseChange h).base).1 (schemeSpace
        (X.baseChange h).base).2)
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj (X.baseChange h).base) :=
    inferInstanceAs (Subsingleton (Spec ((Space.primeSpecOver B integerBase hZ
      (X.chartObject V)).left.residueField (Space.primeSpecPoint B integerBase hZ
        (X.chartObject V) p))))
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (X.baseChange h).base) :=
    inferInstanceAs (IsAffine (Spec _))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj (X.baseChange h).base) :=
    inferInstanceAs (IsLocallyNoetherian (Spec ((Space.primeSpecOver B integerBase hZ
      (X.chartObject V)).left.residueField (Space.primeSpecPoint B integerBase hZ
        (X.chartObject V) p))))
  have : ((Space.smallEtaleDerivedModulePushforward B integerBase hZ (X.baseChange h).toBase).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ (X.baseChange h).total)) 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ
          (X.baseChange h).total)))).IsLE 1 :=
    (X.baseChange h).hasDerivedStructureSheafPushforwardIsLEOne_of_subsingleton
  -- the composite of the point and the chart is the point of the base
  let gY := schemeSpaceMap g
  have hw : gY ≫ Space.chartToSpace B integerBase hZ (schemeSpace X.base) V =
      schemeSpaceMap (X.baseChangeHom h).baseMap := by
    refine InducedCategory.hom_ext ?_
    show yoneda.map g ≫ V.obj.hom = yoneda.map (g ≫ jV)
    rw [Functor.map_comp]
    congr 1
    exact (Functor.map_preimage yoneda
      (V.obj.hom : yoneda.obj (X.chartObject V) ⟶ yoneda.obj X.base)).symm
  let R := (Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
    ((DerivedCategory.singleFunctor
      (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
      (Space.structureSheafModule B integerBase hZ X.total))
  let Lg := Space.smallEtaleDerivedModulePullback B integerBase hZ gY
  let c₁ : Lg.obj ((Space.etaleModulePullback.{u, u} B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).mapDerivedCategory.obj
        R) ≅ (Space.smallEtaleDerivedModulePullback B integerBase hZ
          (schemeSpaceMap (X.baseChangeHom h).baseMap)).obj R :=
    Lg.mapIso ((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
        (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).app R).symm ≪≫
      (Space.smallEtaleDerivedModulePullbackCompIso B integerBase hZ gY
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)).app R ≪≫
      (Space.smallEtaleDerivedModulePullbackCongr B integerBase hZ hw).app R
  let c₂ := @asIso _ _ _ _ _ (hbc (X.baseChange h) (X.baseChangeHom h)) ≪≫
    (Space.smallEtaleDerivedModulePushforward B integerBase hZ (X.baseChange h).toBase).mapIso
      (Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := integerBase) (hS := hZ)
        (X.baseChangeHom h).totalMap)
  have hZR : IsZero ((DerivedCategory.homologyFunctor _ n).obj (Lg.obj
      ((Space.etaleModulePullback.{u, u} B integerBase hZ
        (Space.chartToSpace B integerBase hZ (schemeSpace X.base) V)
        (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) V)).mapDerivedCategory.obj
          R))) :=
    (DerivedCategory.isZero_of_isLE ((Space.smallEtaleDerivedModulePushforward B integerBase hZ
      (X.baseChange h).toBase).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ (X.baseChange h).total)) 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ
          (X.baseChange h).total)))) 1 n (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf
        B integerBase hZ (schemeSpace (X.baseChange h).base))) n).mapIso (c₁ ≪≫ c₂))
  -- `Lg^*P` is a retract of `Lg^*((Rf_*𝒪_X)|_V)`
  have hZP : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      (Lg.obj (DerivedCategory.Q.obj P))) := by
    let H := Lg ⋙ DerivedCategory.homologyFunctor _ n
    let i := biprod.inr ≫ e.inv
    let r := e.hom ≫ biprod.snd
    have hir0 : i ≫ r = 𝟙 _ := by simp [i, r]
    have hir : H.map i ≫ H.map r = 𝟙 _ :=
      (H.map_comp i r).symm.trans ((congrArg H.map hir0).trans (H.map_id _))
    exact (IsZero.iff_id_eq_zero _).2 (hir.symm.trans
      ((congrArg (· ≫ H.map r) (hZR.eq_of_tgt (H.map i) 0)).trans zero_comp))
  -- read through the affine base change of the associated module
  let β := Space.representedAffineDerivedBaseChangeIso B integerBase hZ g
  have hZΦ : IsZero ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} B integerBase hZ
      (yoneda.obj (Space.primeResidueObject B integerBase hZ (X.chartObject V) p))
          (isAlgebraicSpace_yoneda B integerBase hZ (Space.primeResidueObject B integerBase hZ
              (X.chartObject V) p))) n).obj
      ((Space.representedAffineDerivedAssociated B integerBase hZ (Space.primeResidueObject B
          integerBase hZ (X.chartObject V) p)).obj
        ((Space.representedAffineDerivedExtension B integerBase hZ g).functor.obj M))) :=
    hZP.of_iso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ
          (schemeSpace (Space.primeResidueObject B integerBase hZ (X.chartObject V) p) :
            AlgebraicSpaces B integerBase hZ))) n).mapIso
                        ((β.app M).symm ≪≫ Lg.mapIso eM))
  have hZa : IsZero ((Space.representedAffineAssociated B integerBase hZ (Space.primeResidueObject
      B integerBase hZ (X.chartObject V) p)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B integerBase
        hZ).obj (Space.primeResidueObject B integerBase hZ (X.chartObject V) p), ⊤)) n).obj
        ((Space.representedAffineDerivedExtension B integerBase hZ g).functor.obj M))) :=
    hZΦ.of_iso (((Space.representedAffineAssociated B integerBase hZ (Space.primeResidueObject B
        integerBase hZ (X.chartObject V) p)).mapDerivedCategoryHomologyIso
      n).app _).symm
  refine (IsZero.iff_id_eq_zero _).2
    ((Space.representedAffineAssociatedFullyFaithful B integerBase hZ
      (Space.primeResidueObject B integerBase hZ (X.chartObject V) p)).map_injective ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hZa.eq_of_src _ _

end CurveFamily

end AlgebraicGeometry

end
