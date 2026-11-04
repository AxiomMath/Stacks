module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldStalkRatioUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericModuleStalkMem
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The restriction to a prime divisor of a global section generating `ℒ_ξ`

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let `ℒ` be
an invertible `𝒪_X`-module, let `σ ∈ Γ(X, ℒ)` be a global section and let `Z ⊂ X` be a prime
divisor with generic point `ξ`, chosen affine elementary étale neighbourhood `(U, u)` and
henselian local ring `B = 𝒪^h_{X, ξ}`.  Suppose `σ` *generates* `ℒ_ξ`, in the shape
`AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates` records it: the ratio `σ / s_ξ` of
Stacks 0EPR is the image of a unit `v` of `B`, so that `σ = v · s_ξ` is itself a generator of
`ℒ_ξ`.

This file identifies the two readings of the restriction of that generator to `Z`:

* `AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction`, the meromorphic section of
  `ℒ|_Z` attached to the unit `v` — the form in which Section 0EQU's non-canonical choice
  `s_i ∈ ℒ_{ξ_i}` of a generator enters the key formula; and
* the meromorphic section of the honest global section `σ|_Z ∈ Γ(Z, ℒ|_Z)`, the inverse image of
  `σ` along the closed immersion `Z → X`.

They agree, which is the step that lets the source's choice "`s_i = s` if `Z_i ⊄ D`" be made in
Lean: the generator delivered to `Z_i` through
`AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction` is then the restriction of the
global section itself.

## The reduction

The value at the generic point of `Z` is a bijection from the meromorphic sections of `ℒ|_Z` onto
`κ(u)` (`AlgebraicGeometry.Space.PrimeDivisor.bijective_genericFieldValue`), so both sides are
determined by that value;
`AlgebraicGeometry.Space.PrimeDivisor.eq_genericRestrictionOf_residue_iff` reads it off, and
everything reduces to one generic-fibre computation: the inverse image along `ρ_Z : Spec κ(u) → Z`
of the honest section `σ|_Z` is the image of `a · s_ξ` in the fibre, for `a` the coefficient
`AlgebraicGeometry.Space.PrimeDivisor.globalSectionStalkCoefficient` of `σ` against `s_ξ` on
`Spec 𝒪_{U, u}`.  That is the comparison of the two factorizations `ρ_Z ≫ (Z → X) = c ≫ j` of
the morphism `Spec κ(u) → X` on chart sections
(`AlgebraicGeometry.Space.modulePullbackCompIso_trans_eqToIso_hom_apply_of_eq`), evaluated at the
square `(Spec κ(u), U ×_X Z)` over `ρ_Z` built here from the universal property of the base change
`U ×_X Z` of the chosen chart.

With that, `σ|_Z` is the section of `ℒ|_Z` with value the residue of `a`, while `v · s_ξ`
restricts to the one with value the residue of `v`; and `v` *is* the image of the germ of `a`,
because `algebraMap B → Q(B)` is injective and both have the same image there by
`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_globalSectionMeromorphic`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldToBaseChangeChart`: the morphism
  `Spec κ(u) → U ×_X Z` of étale charts over `ρ_Z`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.globalSectionMeromorphic_restrict_eq_genericRestrictionOf`:
  the restriction of a global section is the meromorphic section of `ℒ|_Z` whose value at the
  generic point is the residue of the coefficient of `σ` against `s_ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor` carries
  `henselianUnitRestriction_eq_globalSectionMeromorphic_restrict`: **the restriction of the
  generator `v · s_ξ` is the restriction of the global section `σ`**, for `v` a unit of
  `𝒪^h_{X, ξ}` with `σ / s_ξ = v`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hInt : IsIntegralSpace B S hS X)
    (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-! ### `Spec κ(u)` as a chart of `Z` over the base change `U ×_X Z` -/

/-- The square `(Spec κ(u), U)` of étale charts over the composite `Spec κ(u) → X`, read through
`ρ_Z` and the inclusion of `Z`: the two factorizations `ρ_Z ≫ (Z → X) = c ≫ j` agree, and the
vertical morphism is the one of the composite square through `Spec 𝒪_{U, u}`. -/
theorem PrimeDivisor.genericFieldToEtaleChart_comm :
    ((Z.genericFieldChart B S hS hX hdec).1.hom ≫ (Z.genericFieldMorphism B S hS hX hdec).hom) ≫
        (Z.inclusionHom B S hS hX).hom =
      yoneda.map ((Z.genericFieldToStalkChartDiagram B S hS hX hdec).g ≫
          (Z.genericStalkChartDiagram B S hS hX hdec).g) ≫
        (Z.genericEtaleChart B S hS hX hdec).1.hom := by
  have h := (ChartDiagram.comp B S hS (Z.genericFieldToStalk B S hS hX hdec)
    (Z.genericStalkMorphism B S hS hX hdec)
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec).g
    (Z.genericStalkChartDiagram B S hS hX hdec).g
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec).comm
    (Z.genericStalkChartDiagram B S hS hX hdec).comm).comm
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ h)
  exact congrArg ((Z.genericFieldChart B S hS hX hdec).1.hom ≫ ·)
    (congrArg (fun f ↦ f.hom) (Z.genericFieldMorphism_comp_inclusion B S hS hX hdec))

/-- **`Spec κ(u)` as a chart of `Z` over the base change `U ×_X Z`** of the chosen affine
elementary étale neighbourhood `U` of the generic point: the morphism induced by `ρ_Z` and by the
composite `Spec κ(u) → Spec 𝒪_{U, u} → U`, which agree over `X`. -/
def PrimeDivisor.genericFieldToBaseChangeChart :
    (SmallEtale.toOver B S hS (Z.genericFieldSpace B S hS hX hdec).1).obj
        (Z.genericFieldChart B S hS hX hdec) ⟶
      (SmallEtale.toOver B S hS Z.subspace.toFunctor).obj
        (Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec)) :=
  (Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift
    ((Z.genericFieldChart B S hS hX hdec).1.hom ≫ (Z.genericFieldMorphism B S hS hX hdec).hom)
    ((Z.genericFieldToStalkChartDiagram B S hS hX hdec).g ≫
      (Z.genericStalkChartDiagram B S hS hX hdec).g)
    (Z.genericFieldToEtaleChart_comm B S hS hX hdec)

/-- The morphism `Spec κ(u) → U ×_X Z` lies over `ρ_Z`. -/
theorem PrimeDivisor.genericFieldToBaseChangeChart_comm :
    (Z.genericFieldChart B S hS hX hdec).1.hom ≫ (Z.genericFieldMorphism B S hS hX hdec).hom =
      yoneda.map (Z.genericFieldToBaseChangeChart B S hS hX hdec) ≫
        (Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec)).1.hom :=
  ((Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift_fst _ _ _).symm

/-- The morphism `Spec κ(u) → U ×_X Z` followed by the projection to `U` is the composite
`Spec κ(u) → Spec 𝒪_{U, u} → U`. -/
theorem PrimeDivisor.genericFieldToBaseChangeChart_comp_g :
    Z.genericFieldToBaseChangeChart B S hS hX hdec ≫
        (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).g =
      (Z.genericFieldToStalkChartDiagram B S hS hX hdec).g ≫
        (Z.genericStalkChartDiagram B S hS hX hdec).g :=
  (Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift_snd _ _ _

/-! ### The restriction of a global section at the generic point -/

include hN in
/-- **The restriction to `Z` of a global section is the meromorphic section of `ℒ|_Z` with value
the residue of the coefficient of the section against `s_ξ`.**  The inverse image of `σ` along
`Z → X` is an honest global section of `ℒ|_Z`, hence a meromorphic one; its pullback along
`ρ_Z : Spec κ(u) → Z` is computed on the square `(Spec κ(u), U ×_X Z)`, where it is the inverse
image of `σ|_{U ×_X Z}`, and the comparison of the two factorizations
`ρ_Z ≫ (Z → X) = c ≫ j` identifies that with the image of `a · s_ξ` in the fibre, for `a` the
coefficient of `σ` against `s_ξ` on `Spec 𝒪_{U, u}`. -/
theorem PrimeDivisor.globalSectionMeromorphic_restrict_eq_genericRestrictionOf (σ : L.sections) :
    globalSectionMeromorphic B S hS Z.closed.1 (Z.restrictModule B S hS hX L)
        (modulePullbackSections B S hS (Z.inclusion B S hS hX) L σ) =
      Z.genericRestrictionOf B S hS hX hdec hN L hL
        (IsLocalRing.residue _ (Z.globalSectionGerm B S hS hX hdec L hL σ)) := by
  have hb₁ : (Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec)).1.hom ≫
      (Z.inclusion B S hS hX).hom =
      yoneda.map (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).g ≫
        (Z.genericEtaleChart B S hS hX hdec).1.hom :=
    (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).comm
  have hgerm : Z.globalSectionGerm B S hS hX hdec L hL σ =
      (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom
        (Z.globalSectionStalkCoefficient B S hS hX hdec L hL σ) := rfl
  rw [hgerm]
  refine (Z.eq_genericRestrictionOf_residue_iff B S hS hX hdec hN L hL
    (Z.globalSectionStalkCoefficient B S hS hX hdec L hL σ) _).2 ?_
  refine Eq.trans (pullbackMeromorphicSection_eval_toMeromorphicSectionValue B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (globalSectionMeromorphic B S hS Z.closed.1 (Z.restrictModule B S hS hX L)
      (modulePullbackSections B S hS (Z.inclusion B S hS hX) L σ))
    ⟨Z.genericFieldChart B S hS hX hdec,
      Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec),
      Z.genericFieldToBaseChangeChart B S hS hX hdec,
      Z.genericFieldToBaseChangeChart_comm B S hS hX hdec⟩ _ rfl) ?_
  refine congrArg (toMeromorphicSectionValue B S hS (Z.genericFieldSpace B S hS hX hdec).1
    (Z.genericFieldSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)) ?_
  have hm : (modulePullbackSections B S hS (Z.inclusion B S hS hX) L σ).eval
        (op (Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec))) =
      (modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app
        ⟨Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec),
          Z.genericEtaleChart B S hS hX hdec,
          (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).g, hb₁⟩
        (σ.eval (op (Z.genericEtaleChart B S hS hX hdec))) :=
    (modulePullbackSections_val B S hS (Z.inclusion B S hS hX) L σ
        ⟨Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec),
          Z.genericEtaleChart B S hS hX hdec,
          (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).g,
          hb₁⟩).trans
      (modulePullbackChartFMap_app B S hS (Z.inclusion B S hS hX) L _ _).symm
  have hw : (Z.globalSectionStalkCoefficient B S hS hX hdec L hL σ •
        Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
          (𝟙 (Z.genericStalkChart B S hS hX hdec))) =
      (modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
        ⟨Z.genericStalkChart B S hS hX hdec, Z.genericEtaleChart B S hS hX hdec,
          (Z.genericStalkChartDiagram B S hS hX hdec).g,
          (Z.genericStalkChartDiagram B S hS hX hdec).comm⟩
        (σ.eval (op (Z.genericEtaleChart B S hS hX hdec))) :=
    (Z.globalSectionStalkCoefficient_spec B S hS hX hdec L hL σ).symm.trans
      (modulePullbackChartFMap_app B S hS (Z.genericStalkMorphism B S hS hX hdec) L _ _).symm
  refine Eq.trans (congrArg ((modulePullbackChartFMap B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.restrictModule B S hS hX L)).app
      ⟨Z.genericFieldChart B S hS hX hdec,
        Z.baseChangeChart B S hS hX (Z.genericEtaleChart B S hS hX hdec),
        Z.genericFieldToBaseChangeChart B S hS hX hdec,
        Z.genericFieldToBaseChangeChart_comm B S hS hX hdec⟩) hm) ?_
  rw [hw]
  exact (modulePullbackCompIso_trans_eqToIso_hom_apply_of_eq B S hS
    (Z.genericFieldMorphism B S hS hX hdec) (Z.inclusion B S hS hX)
    (Z.genericFieldToStalk B S hS hX hdec) (Z.genericStalkMorphism B S hS hX hdec) L _
    (Z.genericFieldPullbackIso B S hS hX hdec L) (Z.genericFieldPullbackIso_eq B S hS hX hdec L)
    (Z.genericFieldMorphism_comp_inclusion B S hS hX hdec).symm
    (Z.genericFieldToBaseChangeChart B S hS hX hdec)
    (Z.baseChangeChartDiagram B S hS hX (Z.genericEtaleChart B S hS hX hdec)).g
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec).g
    (Z.genericStalkChartDiagram B S hS hX hdec).g
    (Z.genericFieldToBaseChangeChart_comm B S hS hX hdec) hb₁
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec).comm
    (Z.genericStalkChartDiagram B S hS hX hdec).comm
    (Z.genericFieldToBaseChangeChart_comp_g B S hS hX hdec).symm
    (σ.eval (op (Z.genericEtaleChart B S hS hX hdec)))).symm

/-! ### The restriction of the generator `v · s_ξ` of a global section -/

include hN hInt in
/-- **The restriction of the generator `v · s_ξ` is the restriction of the global section.**  Let
`σ ∈ Γ(X, ℒ)` be a global section and let `v` be a unit of `B = 𝒪^h_{X, ξ}` whose image in `Q(B)`
is the ratio `σ / s_ξ` of Stacks 0EPR — that is, `σ = v · s_ξ` in `ℒ_ξ`, which is the witness of
`AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates` for `σ`.  Then the meromorphic section of
`ℒ|_Z` that Section 0EQU attaches to the generator `v · s_ξ` is the meromorphic section of the
honest global section `σ|_Z ∈ Γ(Z, ℒ|_Z)`.

The ratio of the meromorphic section of `σ` is the image in `Q(B)` of the germ at `ξ` of the
coefficient `a` of `σ` against `s_ξ`
(`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_globalSectionMeromorphic`), so `v` is
that germ, `algebraMap B → Q(B)` being injective; the residues of the two therefore agree under
`κ(u) ≃+* κ(B)` (Stacks 0EN0), and both sections have the same value at the generic point of
`Z`. -/
theorem PrimeDivisor.henselianUnitRestriction_eq_globalSectionMeromorphic_restrict
    (σ : L.sections) (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ)
    (hv : Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN
        (globalSectionMeromorphic B S hS hX L σ) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)
        (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec))) :
    Z.henselianUnitRestriction B S hS hX hdec hN L hL v =
      globalSectionMeromorphic B S hS Z.closed.1 (Z.restrictModule B S hS hX L)
        (modulePullbackSections B S hS (Z.inclusion B S hS hX) L σ) := by
  let _ := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have hcoe : (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) =
      stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
        (Z.genericChart B S hS hX hdec) (Z.globalSectionGerm B S hS hX hdec L hL σ) :=
    IsFractionRing.injective ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (Z.genericTotalFractionRing B S hS hX hdec)
      (hv.symm.trans
        (Z.canonicalGenericRatio_globalSectionMeromorphic B S hS hX hdec L hL hInt hN σ))
  rw [Z.globalSectionMeromorphic_restrict_eq_genericRestrictionOf B S hS hX hdec hN L hL σ,
    PrimeDivisor.henselianUnitRestriction, hcoe,
    ← Z.genericResidueFieldEquivHenselian_residue B S hS hX hdec
      (Z.globalSectionGerm B S hS hX hdec L hL σ),
    RingEquiv.symm_apply_apply]

end AlgebraicGeometry.Space

end
