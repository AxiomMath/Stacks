module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniChartReduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniParameterFunctionField

/-!
# The universal family over a chart, as a map of rings

In the situation of the Bertini theorems, the universal family `H_univ → 𝔸^r_k` restricts, over a
trivializing affine chart `U` of `X`, to a morphism of *affine* schemes: its source is the affine
open `Stacks.Bertini.FamilyDivisors.chartDivisorOpen` of `H_univ` lying over the chart of the
parameter space above `U`, whose ring is `Stacks.Bertini.FamilyDivisors.chartDivisorRing`, and its
target is `𝔸^r_k = Spec k[xⱼ]`.

The corresponding map of rings sends the coordinate `xⱼ` to the class of `xⱼ` and a scalar of `k`
to its image in the chart ring.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.chartDivisorOpen`: the part of `H_univ` over a chart.
* `Stacks.Bertini.FamilyDivisors.chartDivisorParameterMap`: the ring map
  `Γ(𝔸^r_k, ⊤) → Γ(H_univ, chart)` of the universal family over a chart.

## Main results

* `Stacks.Bertini.FamilyDivisors.isAffineOpen_chartDivisorOpen`: the part of `H_univ` over a
  chart is an affine open.
* `Stacks.Bertini.FamilyDivisors.chartDivisorParameterMap_parameterBaseΓEquiv`: the ring map of
  the universal family over a chart is `k[xⱼ] → Γ(U, ⊤)[xⱼ]/(∑ⱼ xⱼfⱼ)`, the reduction of the
  coefficientwise structural map.

## References

* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- **The part of `H_univ` over a trivializing affine chart**: the preimage in `H_univ` of the
chart of the parameter space above an affine open `U` of `X`. -/
abbrev chartDivisorOpen (U : D.X.Opens) [IsAffine U.toScheme] :
    D.universalDivisorScheme.Opens :=
  D.universalDivisor.subschemeι ⁻¹ᵁ (D.chartOpen U : D.parameterSpace.Opens)

variable (U : D.X.Opens) [IsAffine U.toScheme]

/-- The part of `H_univ` over a trivializing affine chart is an affine open. -/
theorem isAffineOpen_chartDivisorOpen : IsAffineOpen (D.chartDivisorOpen U) := by
  change IsAffineOpen (D.universalDivisor.subschemeι ⁻¹ᵁ (D.chartOpen U : D.parameterSpace.Opens))
  have : IsOpenImmersion (D.universalDivisor.subschemeCover.f (D.chartOpen U)) :=
    D.universalDivisor.subschemeCover.map_prop _
  rw [← Scheme.IdealSheafData.opensRange_subschemeCover_map D.universalDivisor (D.chartOpen U)]
  exact isAffineOpen_opensRange _

/-- The part of `H_univ` over a trivializing affine chart is an affine scheme. -/
instance isAffine_chartDivisorOpen : IsAffine (D.chartDivisorOpen U).toScheme :=
  D.isAffineOpen_chartDivisorOpen U

/-- Pulling a function on the chart of the parameter space over `U` back to `𝔸^r_U` along
`chartΓEquiv` is restricting it along `chartMap`. -/
theorem chartΓEquiv_symm_apply
    (a : Γ(D.parameterSpace, (D.chartOpen U : D.parameterSpace.Opens))) :
    (D.chartΓEquiv U).symm a =
      ((D.chartMap U).appLE (D.chartOpen U : D.parameterSpace.Opens) ⊤
        (Scheme.Hom.preimage_image_eq _ _).ge) a := by
  change (((D.chartMap U).appIso ⊤).hom) a = _
  rw [Scheme.Hom.appIso_hom']
  rfl

omit [IsAffine U.toScheme] in
/-- **The chart of `𝔸^r_X` over `U`, mapped to `𝔸^r_k`, is `𝔸^r_U → 𝔸^r_k`.** -/
theorem chartMap_comp_parameterBaseMap :
    D.chartMap U ≫ D.parameterBaseMap = AffineSpace.map D.basisIndex (U.ι ≫ D.toBase) :=
  (AffineSpace.map_comp _ _).symm

/-- **Restricting a function on `𝔸^r_k` to the chart over `U` and reading it on `𝔸^r_U`** is
pulling it back along `𝔸^r_U → 𝔸^r_k`. -/
theorem parameterBaseMap_appLE_comp_chartMap_appLE :
    D.parameterBaseMap.appLE ⊤ (D.chartOpen U : D.parameterSpace.Opens) le_top ≫
        (D.chartMap U).appLE (D.chartOpen U : D.parameterSpace.Opens) ⊤
          (Scheme.Hom.preimage_image_eq _ _).ge =
      (AffineSpace.map D.basisIndex (U.ι ≫ D.toBase)).appTop := by
  refine (Scheme.Hom.appLE_comp_appLE (D.chartMap U) D.parameterBaseMap ⊤
    (D.chartOpen U : D.parameterSpace.Opens) ⊤ le_top
    (Scheme.Hom.preimage_image_eq _ _).ge).trans ?_
  refine (Scheme.Hom.appLE_eq_app _).trans ?_
  rw [D.chartMap_comp_parameterBaseMap U]

/-- A function on `𝔸^r_k`, restricted to the chart over `U` and read in the polynomial ring of the
chart, is the image of its pullback along `𝔸^r_U → 𝔸^r_k`. -/
theorem chartMvPolynomialEquiv_parameterBaseMap_appLE (b : Γ(D.parameterBase, ⊤)) :
    D.chartMvPolynomialEquiv U
        (D.parameterBaseMap.appLE ⊤ (D.chartOpen U : D.parameterSpace.Opens) le_top b) =
      (AffineSpace.ΓIso D.basisIndex U.toScheme).hom
        ((AffineSpace.map D.basisIndex (U.ι ≫ D.toBase)).appTop b) := by
  change (AffineSpace.ΓIso D.basisIndex U.toScheme).hom
      ((D.chartΓEquiv U).symm
        (D.parameterBaseMap.appLE ⊤ (D.chartOpen U : D.parameterSpace.Opens) le_top b)) = _
  congr 1
  rw [D.chartΓEquiv_symm_apply U, ← CommRingCat.comp_apply,
    D.parameterBaseMap_appLE_comp_chartMap_appLE U]

/-! ### The ring map of the universal family over a chart -/

variable (c : D.Chart)

/-- **The ring map of the universal family over a trivializing affine chart**, from the functions
on `𝔸^r_k` to the ring `Γ(U, ⊤)[xⱼ]/(∑ⱼ xⱼfⱼ)` of `H_univ` over the chart. -/
def chartDivisorParameterMap : Γ(D.parameterBase, ⊤) →+* chartDivisorRing c :=
  (D.chartSubschemeΓEquiv c.U c.triv).toRingHom.comp
    (D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top).hom

/-- The universal family restricted to the chart factors as the projection to `𝔸^r_k` followed
by the inclusion of the universal divisor. -/
theorem universalFamily_appLE_chartDivisorOpen :
    D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top =
      D.parameterBaseMap.appLE ⊤ (D.chartOpen c.U : D.parameterSpace.Opens) le_top ≫
        D.universalDivisor.subschemeι.app (D.chartOpen c.U) := by
  rw [← Scheme.Hom.appLE_eq_app D.universalDivisor.subschemeι
    (U := (D.chartOpen c.U : D.parameterSpace.Opens))]
  exact (Scheme.Hom.appLE_comp_appLE D.universalDivisor.subschemeι D.parameterBaseMap ⊤
    (D.chartOpen c.U : D.parameterSpace.Opens) (D.chartDivisorOpen c.U) le_top le_rfl).symm

/-- The ring map of the universal family over a chart, read in the polynomial ring. -/
theorem chartDivisorParameterMap_apply (b : Γ(D.parameterBase, ⊤)) :
    D.chartDivisorParameterMap c b =
      Ideal.Quotient.mk _ ((AffineSpace.ΓIso D.basisIndex c.U.toScheme).hom
        ((AffineSpace.map D.basisIndex (c.U.ι ≫ D.toBase)).appTop b)) := by
  change D.chartSubschemeΓEquiv c.U c.triv
      ((D.universalFamily.appLE ⊤ (D.chartDivisorOpen c.U) le_top) b) = _
  rw [D.universalFamily_appLE_chartDivisorOpen c, CommRingCat.comp_apply,
    D.chartSubschemeΓEquiv_subschemeι_app c.U c.triv,
    D.chartMvPolynomialEquiv_parameterBaseMap_appLE c.U]
  rfl

/-- **The ring map of the universal family over a chart is the structural one**: it sends the
coordinate `xⱼ` to the class of `xⱼ` and a scalar `a ∈ k` to the class of the constant
`chartRingHom U a`. Equivalently, it is the reduction of the coefficientwise map
`k[xⱼ] → Γ(U, ⊤)[xⱼ]`. -/
theorem chartDivisorParameterMap_parameterBaseΓEquiv (p : MvPolynomial D.basisIndex D.k) :
    D.chartDivisorParameterMap c (D.parameterBaseΓEquiv p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (chartRingHom c.U) p) := by
  have h : (D.chartDivisorParameterMap c).comp
      (D.parameterBaseΓEquiv : MvPolynomial D.basisIndex D.k →+* _) =
      (Ideal.Quotient.mk
          (Ideal.span {Algebra.universalLinearForm (D.chartEquationIndex c.U c.triv)})).comp
        (MvPolynomial.map (chartRingHom c.U)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_) <;>
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe,
        D.chartDivisorParameterMap_apply c]
    · rw [D.parameterBaseΓEquiv_C, AffineSpace.map_appTop_over_appTop,
        AffineSpace.ΓIso_hom_appTop, MvPolynomial.map_C]
      rfl
    · rw [D.parameterBaseΓEquiv_X, AffineSpace.map_appTop_coord, AffineSpace.ΓIso_hom_coord,
        MvPolynomial.map_X]
  exact DFunLike.congr_fun h p

end Stacks.Bertini.FamilyDivisors

end
