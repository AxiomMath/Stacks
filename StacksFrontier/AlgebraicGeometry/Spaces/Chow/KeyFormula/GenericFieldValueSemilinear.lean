module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldValue
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionsMeromorphic

/-!
# The value at the generic point of a prime divisor is `θ_Z⁻¹`-semilinear

Let `X` be a decent, locally Noetherian algebraic space over a scheme `S`, let `Z ⊂ X` be a prime
divisor and let `ℒ` be an invertible `𝒪_X`-module.  The meromorphic sections of the restriction
`ℒ|_Z` form a module over the function field `R(Z)`, which acts through the canonical
identification `R(Z) = Γ(Z, 𝒦_Z)` of Stacks 0ENA.  This file proves that the value at the generic
point of `Z` (`AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue`) is semilinear along
`θ_Z⁻¹ : R(Z) → κ(u)`:

`value(g · σ) = θ_Z⁻¹(g) · value(σ)`.

The computation is made over one chart diagram `(Spec κ(u), V)` over `ρ_Z`, with `V` an affine
étale chart of `Z` lying in the domain of a representative of `g` and receiving `ρ_Z`
(`AlgebraicGeometry.Space.exists_affine_etaleChart_factor_of_isDenseOpenSubspace`).  Over such a
diagram the global pullback of meromorphic sections of Stacks 0ENC is semilinear over the
chartwise pullback of meromorphic functions; the value of `g` on `V` is the coordinate of the
representative there, whose chartwise pullback to `Spec κ(u)` is the pullback of the coordinate
along `Spec κ(u) → V`, which is `θ_Z⁻¹(g)` by the characterization of evaluation at the generic
point (Stacks 0END).

## Main definitions

* `AlgebraicGeometry.Space.meromorphicFunctionToSectionsSubring`: a global meromorphic function,
  read in the spelling that acts on meromorphic sections.
* `AlgebraicGeometry.Space.PrimeDivisor.codimensionZeroPresentation`: a chosen presentation of
  the schematic locus of `Z` at its generic point.
* `AlgebraicGeometry.Space.PrimeDivisor.functionFieldToMeromorphic`: the canonical map
  `R(Z) → Γ(Z, 𝒦_Z)` of Stacks 0ENA, in that spelling.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.functionFieldToMeromorphic_val`: the value of the image of
  a rational function at every chart lying in the domain of a representative is the coordinate
  of the representative there; this pins the map down independently of the chosen presentation.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue_smul_of_chartDiagram`: semilinearity of
  the value over the chartwise pullback, for any affine chart receiving `ρ_Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue_functionField_smul`:
  `value(g · σ) = θ_Z⁻¹(g) · value(σ)`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

/-- **A global meromorphic function, in the spelling that acts on meromorphic sections**: the
same compatible family of values, read in `RingCat.sectionsSubring` of the ring sheaf of the
meromorphic ringed site. -/
def meromorphicFunctionToSectionsSubring (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    MeromorphicFunction B S hS F hF →+* ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)) where
  toFun m := ⟨fun V => m.val V, fun f => m.property f⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value over a chart of a meromorphic function read in the acting spelling. -/
theorem meromorphicFunctionToSectionsSubring_val (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (m : MeromorphicFunction B S hS F hF) (V : (SmallEtale B S hS F)ᵒᵖ) :
    (meromorphicFunctionToSectionsSubring B S hS hF m).1 V = m.val V :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

/-! ### The hypotheses of Stacks 0ENA on a prime divisor -/

include hX hN in
/-- A prime divisor of a locally Noetherian algebraic space is locally Noetherian. -/
theorem PrimeDivisor.hasEtaleLocalProperty_isLocallyNoetherian_subspace :
    HasEtaleLocalProperty B S hS Z.subspace.toFunctor
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) :=
  hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor B S hS ⟨X, hX⟩ hN Z.closed

/-- **Hypothesis (a) of Stacks 0ENA on a prime divisor**: its weakly associated points have
codimension `0`, the prime divisor being reduced. -/
theorem PrimeDivisor.localRingDimension_eq_zero_of_mem_weaklyAssociated_space :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (Z.space B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
  rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS _
    Z.integral.hasEtaleLocalProperty_isReduced] at hz

include hX hN in
/-- **Hypothesis (b) of Stacks 0ENA on a prime divisor**: its irreducible components are locally
finite, the prime divisor being locally Noetherian. -/
theorem PrimeDivisor.hasLocallyFiniteIrreducibleComponents_space :
    HasLocallyFiniteIrreducibleComponents B S hS Z.subspace.toFunctor :=
  hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS _ Z.closed.1
    (Z.hasEtaleLocalProperty_isLocallyNoetherian_subspace B S hS hX hN)

/-- **Hypothesis (c) of Stacks 0ENA on a prime divisor**: its codimension-zero points have
monomorphic field representatives, the prime divisor being decent. -/
theorem PrimeDivisor.hasMonomorphicCodimensionZeroPoints_space :
    HasMonomorphicCodimensionZeroPoints B S hS Z.subspace.toFunctor :=
  fun x _ => IsDecentSpace.hasMonomorphicFieldRepresentative B S hS _ Z.integral.2.1 x

/-- A chosen presentation of the schematic locus of a prime divisor at its codimension-zero
point. -/
def PrimeDivisor.codimensionZeroPresentation :
    CodimensionZeroPresentation B S hS Z.subspace.toFunctor :=
  (exists_codimensionZeroPresentation B S hS Z.closed.1
    (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN)
    (Z.hasMonomorphicCodimensionZeroPoints_space B S hS)).some

/-- **The canonical map `R(Z) → Γ(Z, 𝒦_Z)` of Stacks 0ENA**, in the spelling of the global
meromorphic functions that acts on meromorphic sections. -/
def PrimeDivisor.functionFieldToMeromorphic :
    rationalFunctions B S hS Z.closed.1 →+* ↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Z.subspace.toFunctor Z.closed.1).O).obj)) :=
  (meromorphicFunctionToSectionsSubring B S hS Z.closed.1).comp
    (rationalToMeromorphicRingHom (X := Z.space B S hS)
      (Z.codimensionZeroPresentation B S hS hX hN)
      (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_space B S hS)
      (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN))

/-- **The value of the image of a rational function at a chart lying in the domain of a
representative is the coordinate of the representative there.** -/
theorem PrimeDivisor.functionFieldToMeromorphic_val
    (f : PartialMap B S hS Z.closed.1 (affineLineFunctor B S hS))
    (V : SmallEtale B S hS Z.subspace.toFunctor)
    (τ : yoneda.obj V.obj.left ⟶ f.domain.toFunctor) (hτ : τ ≫ f.domain.ι = V.1.hom) :
    (Z.functionFieldToMeromorphic B S hS hX hN (f.toRationalMap B S hS)).1 (op V) =
      chartToMeromorphic (X := Z.space B S hS) V (chartCoord (X := Z.space B S hS) f.hom V τ) :=
  rationalToMeromorphic_val (X := Z.space B S hS) (Z.codimensionZeroPresentation B S hS hX hN)
    (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_space B S hS)
    (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN) f V τ hτ

/-- The map `R(Z) → Γ(Z, 𝒦_Z)` is bijective, by the third conclusion of Stacks 0ENA. -/
theorem PrimeDivisor.bijective_functionFieldToMeromorphic :
    Function.Bijective (Z.functionFieldToMeromorphic B S hS hX hN) := by
  refine ⟨fun x y hxy => injective_rationalToMeromorphic (X := Z.space B S hS)
    (Z.codimensionZeroPresentation B S hS hX hN)
    (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_space B S hS)
    (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN) ?_, fun a => ?_⟩
  · exact Subtype.ext (congrArg Subtype.val hxy)
  · obtain ⟨x, hx⟩ := surjective_rationalToMeromorphic (X := Z.space B S hS)
      (Z.codimensionZeroPresentation B S hS hX hN)
      (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_space B S hS)
      (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN) ⟨a.1, a.2⟩
    exact ⟨x, Subtype.ext (congrArg Subtype.val hx)⟩

/-! ### Semilinearity over a chart diagram -/

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- **The value at the generic point is semilinear over the chartwise pullback.**  For an
affine étale chart `V` of `Z` receiving `ρ_Z` by `g`, multiplying a meromorphic section of
`ℒ|_Z` by a global meromorphic function `a` multiplies its value by the chartwise pullback of
the value of `a` on `V`, read in `κ(u)`. -/
theorem PrimeDivisor.genericFieldValue_smul_of_chartDiagram
    (V : SmallEtale B S hS Z.subspace.toFunctor)
    (g : Z.genericFieldSpec B S hS hX hdec ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.1.hom =
      fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left))
    (a : ↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS Z.subspace.toFunctor Z.closed.1).O).obj)))
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    Z.genericFieldValue B S hS hX hdec L hL (a • σ) =
      (Z.genericFieldMeromorphicEquiv B S hS hX hdec).symm
          (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
            (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
            (genericFieldPointChartDiagram B S hS _ V g hg) (a.1 (op V))) *
        Z.genericFieldValue B S hS hX hdec L hL σ := by
  rw [Z.genericFieldValue_eq_iff B S hS hX hdec L hL]
  have h := pullbackMeromorphicSection_eval_smul_chartDiagram B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) (a • σ) σ
    (genericFieldPointChartDiagram B S hS _ V g hg)
    (isAffine_idEtaleChart_siteObject B S hS _) hV (a.1 (op V)) rfl
  refine h.trans ?_
  have hs : (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.restrictModule B S hS hX L)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
        (op (genericFieldPointChartDiagram B S hS _ V g hg).U) = _ :=
    Z.genericFieldValue_spec B S hS hX hdec L hL σ
  have hc := (Z.genericFieldMeromorphicEquiv B S hS hX hdec).apply_symm_apply
    (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
      (genericFieldPointChartDiagram B S hS _ V g hg) (a.1 (op V)))
  rw [hs, map_mul]
  refine (toMeromorphicSectionSheaf_smul B S hS _ _ _ _ _ _).symm.trans ?_
  refine congrArg _ ((meromorphicSectionModule_smul_tmul B S hS _ _ _ _ _ _ _ _ rfl).trans ?_)
  rw [hc]
  rfl

/-! ### The chartwise pullback of a rational function is `θ_Z⁻¹` of it -/

/-- **The chartwise pullback to `Spec κ(u)` of the value of a rational function on a chart lying
in the domain of a representative is `θ_Z⁻¹` of that rational function.** -/
theorem PrimeDivisor.genericFieldMeromorphicEquiv_symm_chartPullback_functionFieldToMeromorphic
    (f : PartialMap B S hS Z.closed.1 (affineLineFunctor B S hS))
    (V : SmallEtale B S hS Z.subspace.toFunctor)
    (τ : yoneda.obj V.obj.left ⟶ f.domain.toFunctor) (hτ : τ ≫ f.domain.ι = V.1.hom)
    (g : Z.genericFieldSpec B S hS hX hdec ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.1.hom =
      fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec)) :
    (Z.genericFieldMeromorphicEquiv B S hS hX hdec).symm
        (chartMeromorphicRingedSitePullbackHom B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
          (genericFieldPointChartDiagram B S hS _ V g hg)
          ((Z.functionFieldToMeromorphic B S hS hX hN (f.toRationalMap B S hS)).1 (op V))) =
      (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm (f.toRationalMap B S hS) := by
  refine (RingEquiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (congrArg (Z.genericFieldMeromorphicEquiv B S hS hX hdec)
    (Z.genericResidueFieldEquivFunctionField_symm_eq_appTop B S hS hX hdec f V.obj.left τ g
      (by rw [hτ, hg]))).symm
  refine (congrArg (chartMeromorphicRingedSitePullbackHom B S hS
      (Z.genericFieldMorphism B S hS hX hdec)
      (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
      (genericFieldPointChartDiagram B S hS _ V g hg))
    (Z.functionFieldToMeromorphic_val B S hS hX hN f V τ hτ)).trans ?_
  refine (chartMeromorphicFunctionPullback_toMeromorphicFunctionSheaf B S hS
    (Z.genericFieldMorphism B S hS hX hdec)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (genericFieldPointChartDiagram B S hS _ V g hg) _).trans ?_
  refine congrArg (chartToMeromorphic (X := Z.genericFieldSpace B S hS hX hdec)
    (Z.genericFieldChart B S hS hX hdec)) ?_
  refine Eq.trans ?_ (Iso.hom_inv_id_apply
    (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))) _).symm
  rw [chartCoord, yonedaEquiv_comp]
  rfl

include hN in
/-- **The value at the generic point is `θ_Z⁻¹`-semilinear**: for a rational function `x` of the
prime divisor and a meromorphic section `σ` of `ℒ|_Z`, the value of `x · σ` is
`θ_Z⁻¹(x)` times the value of `σ`, the action of `x` being through `R(Z) = Γ(Z, 𝒦_Z)`. -/
theorem PrimeDivisor.genericFieldValue_functionField_smul
    (x : rationalFunctions B S hS Z.closed.1)
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    Z.genericFieldValue B S hS hX hdec L hL (Z.functionFieldToMeromorphic B S hS hX hN x • σ) =
      (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm x *
        Z.genericFieldValue B S hS hX hdec L hL σ := by
  obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨V, τ, g, hV, hτ, hg⟩ := exists_affine_etaleChart_factor_of_isDenseOpenSubspace B S hS
    Z.closed.1 Z.integral (Z.genericFieldPoint B S hS hX hdec)
    (Z.class_genericFieldPoint B S hS hX hdec)
    (Z.mono_fieldMorphism_genericFieldPoint B S hS hX hdec)
    f.dense_open_domain
  rw [Z.genericFieldValue_smul_of_chartDiagram B S hS hX hdec L hL V g hg hV,
    Z.genericFieldMeromorphicEquiv_symm_chartPullback_functionFieldToMeromorphic B S hS hX hdec hN
      f V τ hτ g hg]

end AlgebraicGeometry.Space

end
