module

public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.DegreeZeroCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgePair
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLift
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic

/-!
# The Gysin projection formula of Tag 0G88 at a positive conormal rank

Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a closed immersion of finite presentation
whose conormal sheaf is locally free of rank `c = d + 1`, and let `γ^p` be the canonical Gysin map
of [Stacks, Tag 0G86]. We prove the identity of morphisms of sheaves of which [Stacks, Tag 0G88] is
the degree-`q` cohomology:

`ω ↦ γ^p(ω|_Z)` **is** `ω ↦ ω ∧ γ^0(1)`,  as maps `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`,

the wedge being the pairing `Stacks.Gysin.conormalWedgePair`. The subscheme `Z` is only locally cut
out by `c` equations: no global family of functions on `X` occurs in the statements.

The Gysin map at `p = 0` lands in a sheaf whose degree is written `0 + c`, with `0` the cast of a
natural number, while the second factor of the wedge pairing is `Ω^c_{X/S}`. The results therefore
take a morphism `σ : Ω^{0+c}_{X/S} ⟶ Ω^c_{X/S}` together with the equation
`σ(1 ∧ d f₁ ∧ ⋯ ∧ d f_c) = d f₁ ∧ ⋯ ∧ d f_c`; the canonical `eqToHom` satisfies it, by
`Stacks.Gysin.eqToHom_app_gysinWedgeOn_one`.

## Main definitions

* `Stacks.Gysin.gysinDegreeShift`: the comparison `i_*ℋ^c_Z(Ω^{0+c}) ⟶ i_*ℋ^c_Z(Ω^c)` of the two
  spellings of the degree.
* `Stacks.Gysin.subschemeFormUnit`: the unit `1` of `Ω^0_{Z/S}`, as a global section of
  `i_*Ω^0_{Z/S}`.
* `Stacks.Gysin.IsGysinHom`: the characterisation of [Stacks, Tag 0G86], as a predicate.
* `Stacks.Gysin.conormalUnitClass`: `γ^0(1)`, the image of that unit under the Gysin map of
  [Stacks, Tag 0G86] at `p = 0`.

## Main results

* `Stacks.Gysin.conormalClsHom_comp_conormalWedgeHom`: wedging with a class of the class map of
  [Stacks, Tag 0G7Q] is the class of the wedge.
* `Stacks.Gysin.conormalUnitClass_eval`: the value of `γ^0(1)` over an open of an equation chart is
  the class of `d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`.
* `Stacks.Gysin.formRestriction_comp_gysinHom_succ`: the identity of morphisms of sheaves of which
  [Stacks, Tag 0G88] is the degree-`q` cohomology, at a conormal rank of the form `d + 1`.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.SupportedFraction
open Stacks.AlgebraicGeometry.ConormalEquations (ConormalRank)

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isQuasicoherent_relativeDifferentialForms

/-! ### The two spellings of the degree `c`, and the canonical comparison -/

/-- `0 + c = c` in `ℤ`, with the zero the cast of the natural number `0`. -/
theorem natCast_zero_add (c : ℕ) : ((0 : ℕ) : ℤ) + (c : ℤ) = (c : ℤ) := by
  rw [Nat.cast_zero, zero_add]

/-- A transport of relative differential forms along an equality of degrees acts on sections as the
identity, up to `HEq`. -/
theorem heq_eqToHom_app_degree {Y S' : Scheme.{u}} (ϖ : Y ⟶ S') {m n : ℤ} (h : m = n)
    (V : Y.Opens) (z : Γ(relativeDifferentialForms ϖ m, V)) :
    HEq ((eqToHom (congrArg (relativeDifferentialForms ϖ) h)).app V z) z := by
  subst h
  rw [eqToHom_refl]
  rfl

/-- The wedge of the unit of `Ω^•_{X/S}` with the equation wedge is the equation wedge, up to
`HEq`: the two sides are sections of the pieces in the degrees `0 + c` and `c`. -/
theorem heq_gysinWedgeOn_one (π : X ⟶ S) {c : ℕ} {W : X.Opens} (f : Fin c → Γ(X, W))
    {V : X.Opens} (hV : V ≤ W) :
    HEq (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
        ((relativeDifferentialFormsAlgebra π).one.eval (op V))) (equationsWedgeOn π f hV) :=
  (relativeDifferentialFormsAlgebra π).one_mul (c : ℤ) (op V)
    (equationsWedgeOn π f hV)

/-- The canonical comparison of the two spellings of the degree, applied to `1 ∧ d f₁ ∧ ⋯ ∧ d f_c`,
is `d f₁ ∧ ⋯ ∧ d f_c`. -/
theorem eqToHom_app_gysinWedgeOn_one (π : X ⟶ S) {c : ℕ} {W : X.Opens}
    (f : Fin c → Γ(X, W)) {V : X.Opens} (hV : V ≤ W) :
    (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c))).app V
        (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V))) =
      equationsWedgeOn π f hV :=
  eq_of_heq
    ((heq_eqToHom_app_degree π (natCast_zero_add c) V
        (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V)))).trans
      (heq_gysinWedgeOn_one π f hV))

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {d : ℕ} (p : ℕ)

/-- The comparison `σ` of the two spellings of the degree, after `i_*ℋ^c_Z`: it carries the target
of the Gysin map of [Stacks, Tag 0G86] at `p = 0` to the second factor of the wedge pairing. -/
def gysinDegreeShift {c : ℕ}
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ)) :
    gysinTarget i π c 0 ⟶ conormalSource i π c :=
  (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map σ

/-! ### The class map of a family of equations on an open, as a composite -/

/-- The class map of [Stacks, Tag 0G7Q] of a chart is the class map of the restricted coefficient
sheaf followed by the inverse of the derived excision. -/
theorem chartClsHom_eq (W : X.Opens) (f : Fin (d + 1) → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base) :
    chartClsHom i π p W f hT hTf =
      supportedFractionSource f
          ((Scheme.Modules.restrictFunctor W.ι).obj
            (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))) hT hTf ≫
        (supportCohomologyRestrictIso W (isClosed_range_base i) hT ((d + 1 : ℕ) : ℤ)
          (relativeDifferentialForms π ((p : ℤ) + ((d + 1 : ℕ) : ℤ)))).inv :=
  rfl

/-- If `φ ≫ sN = sM ≫ Ψ`, then for isomorphisms `ΦM`, `ΦN` and any `ρ`,
`(sM ≫ ΦM.inv) ≫ ((ΦM.hom ≫ Ψ) ≫ ΦN.inv) ≫ ρ = φ ≫ (sN ≫ ΦN.inv) ≫ ρ`. -/
theorem conj_comp_of_naturality {C : Type*} [Category* C] {M N AM AN RM RN D : C}
    (sM : M ⟶ AM) (sN : N ⟶ AN) (ΦM : RM ≅ AM) (ΦN : RN ≅ AN) (Ψ : AM ⟶ AN) (φ : M ⟶ N)
    (ρ : RN ⟶ D) (h : φ ≫ sN = sM ≫ Ψ) :
    (sM ≫ ΦM.inv) ≫ ((ΦM.hom ≫ Ψ) ≫ ΦN.inv) ≫ ρ = φ ≫ (sN ≫ ΦN.inv) ≫ ρ := by
  rw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    ← h, Category.assoc, Category.assoc]

/-- The class map of [Stacks, Tag 0G7Q] of a family of equations on `V`, with coefficient
`Ω^c_{X/S}`: the class map of the restriction, followed by the inverse of the derived excision. It
is `Stacks.Gysin.chartClsHom` with the coefficient degree written `c` rather than `p + c`. -/
def conormalClsHom (V : X.Opens) (f : Fin (d + 1) → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base) :
    Scheme.Modules.restrict (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ)) V.ι ⟶
      Scheme.Modules.restrict (conormalSource i π (d + 1)) V.ι :=
  supportedFractionSource f
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ)))
      (isClosed_preimage_range_base i V) hTf ≫
    (supportCohomologyRestrictIso V (isClosed_range_base i) (isClosed_preimage_range_base i V)
      ((d + 1 : ℕ) : ℤ) (relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))).inv

/-! ### Wedging with a class of the class map is the class of the wedge -/

/-- The degree comparison moves across the class map: the class map at degree `0 + c`, followed by
the comparison after `i_*ℋ^c_Z` and then by any morphism, is the comparison on forms followed by
the class map at degree `c` and that morphism. -/
theorem chartClsHom_comp_gysinDegreeShift (V : X.Opens) (f : Fin (d + 1) → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
    {D : V.toScheme.Modules}
    (ρ : Scheme.Modules.restrict (conormalSource i π (d + 1)) V.ι ⟶ D) :
    chartClsHom i π 0 V f (isClosed_preimage_range_base i V) hTf ≫
        (Scheme.Modules.restrictFunctor V.ι).map (gysinDegreeShift i π σ) ≫ ρ =
      (Scheme.Modules.restrictFunctor V.ι).map σ ≫ conormalClsHom i π V f hTf ≫ ρ :=
  Eq.trans
    (congrArg
      (fun ψ : Scheme.Modules.restrict (gysinTarget i π (d + 1) 0) V.ι ⟶
          Scheme.Modules.restrict (conormalSource i π (d + 1)) V.ι =>
        chartClsHom i π 0 V f (isClosed_preimage_range_base i V) hTf ≫ ψ ≫ ρ)
      (restrictFunctor_map_supportCohomologySheafFunctor V (isClosed_range_base i)
        (isClosed_preimage_range_base i V) ((d + 1 : ℕ) : ℤ) σ))
    (conj_comp_of_naturality _ _ _ _ _ _ ρ
      (supportedFractionSource_natural f ((Scheme.Modules.restrictFunctor V.ι).map σ)
        (isClosed_preimage_range_base i V) hTf))

/-- Wedging with a class of the class map of [Stacks, Tag 0G7Q] is the class of the wedge, as an
identity of morphisms of the restrictions to `V`. -/
theorem conormalClsHom_comp_conormalWedgeHom (V : X.Opens)
    (f : Fin (d + 1) → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    conormalClsHom i π V f hTf ≫ conormalWedgeHom i π p V ω =
      localFormWedgeHom π p V ω ≫
        chartClsHom i π p V f (isClosed_preimage_range_base i V) hTf :=
  Eq.trans
    (Eq.trans
      (congrArg (fun ψ => conormalClsHom i π V f hTf ≫ ψ) (Category.comp_id _).symm)
      (conj_comp_of_naturality _ _ _ _ _ _ (𝟙 _)
        (supportedFractionSource_natural f (localFormWedgeHom π p V ω)
          (isClosed_preimage_range_base i V) hTf)))
    (congrArg (fun ψ => localFormWedgeHom π p V ω ≫ ψ) (Category.comp_id _))

/-! ### The pairing on a class of the class map, on sections -/

/-- Restricting a section of a sheaf of modules along the identity inclusion of an open does
nothing. -/
theorem val_map_homOfLE_refl {M : X.Modules} (U : X.Opens) (m : Γ(M, U)) :
    M.val.map (homOfLE (le_refl U)).op m = m := by
  simp
  rfl

/-- The pairing of `ω` with the class of `y` is the class of `ω ∧ σ(y)`, on the sections over
`V`. -/
theorem conormalWedgeVal_chartCls (V : X.Opens) (f : Fin (d + 1) → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (y : Γ(relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)), V)) :
    conormalWedgeVal i π p V ω
        ((gysinDegreeShift i π σ).app V
          (chartCls i π 0 V f (isClosed_preimage_range_base i V) hTf V le_rfl y)) =
      chartCls i π p V f (isClosed_preimage_range_base i V) hTf V le_rfl
        ((formWedgePair π p (d + 1)).app (op V) ω (σ.app V y)) := by
  have hkey := Eq.trans
    (chartClsHom_comp_gysinDegreeShift i π V f hTf σ (conormalWedgeHom i π p V ω))
    (congrArg (fun ψ => (Scheme.Modules.restrictFunctor V.ι).map σ ≫ ψ)
      (conormalClsHom_comp_conormalWedgeHom i π p V f hTf ω))
  have hL := congrArg (fun θ => restrictSections θ V le_rfl y) hkey
  have hLHS : restrictSections (chartClsHom i π 0 V f (isClosed_preimage_range_base i V) hTf ≫
        (Scheme.Modules.restrictFunctor V.ι).map (gysinDegreeShift i π σ) ≫
          conormalWedgeHom i π p V ω) V le_rfl y =
      conormalWedgeVal i π p V ω ((gysinDegreeShift i π σ).app V
        (chartCls i π 0 V f (isClosed_preimage_range_base i V) hTf V le_rfl y)) := by
    rw [restrictSections_comp, restrictSections_comp, restrictSections_restrictFunctor_map]
    rfl
  have hRHS : restrictSections ((Scheme.Modules.restrictFunctor V.ι).map σ ≫
        localFormWedgeHom π p V ω ≫
          chartClsHom i π p V f (isClosed_preimage_range_base i V) hTf) V le_rfl y =
      chartCls i π p V f (isClosed_preimage_range_base i V) hTf V le_rfl
        ((formWedgePair π p (d + 1)).app (op V) ω (σ.app V y)) := by
    rw [restrictSections_comp, restrictSections_comp, restrictSections_restrictFunctor_map,
      restrictSections_localFormWedgeHom, val_map_homOfLE_refl]
    rfl
  exact hLHS.symm.trans (hL.trans hRHS)

/-! ### The Gysin class of one -/

/-- `1 ∈ Γ(Z, Ω^0_{Z/S})`, as a global section of `i_*Ω^0_{Z/S}`, written as the restriction to `Z`
of the unit of `Ω^•_{X/S}`. -/
def subschemeFormUnit : (pushforwardRelativeForms i π ((0 : ℕ) : ℤ)).sections :=
  SheafOfModules.sectionsMap (formRestriction i π ((0 : ℕ) : ℤ))
    (relativeDifferentialFormsAlgebra π).one

omit [IsClosedImmersion i] in
/-- The value of `Stacks.Gysin.subschemeFormUnit` over an open of `X` is the restriction to `Z` of
the unit of `Ω^•_{X/S}`. -/
theorem subschemeFormUnit_eval (V : X.Opens) :
    (subschemeFormUnit i π).eval (op V) =
      subschemeFormPullback i π ((0 : ℕ) : ℤ) V
        ((relativeDifferentialFormsAlgebra π).one.eval (op V)) :=
  (subschemeFormPullback_eq_formRestriction_app i π ((0 : ℕ) : ℤ) V
    ((relativeDifferentialFormsAlgebra π).one.eval (op V))).symm

omit [IsClosedImmersion i] in
/-- `Stacks.Gysin.subschemeFormUnit` is the unit of `Ω^•_{Z/S}`, read on `X`. -/
theorem subschemeFormUnit_eq_one (V : X.Opens) :
    (subschemeFormUnit i π).eval (op V) =
      (relativeDifferentialFormsAlgebra (i ≫ π)).one.eval (op (i ⁻¹ᵁ V)) :=
  (subschemeFormUnit_eval i π V).trans
    (relativeDifferentialFormsPullback_one i π (i ≫ π) (𝟙 S)
      (Category.comp_id (i ≫ π)).symm V)

/-- The characterising property of the Gysin map of [Stacks, Tag 0G86] in degree `q`: over every
open contained in an equation chart it is the Gysin map of [Stacks, Tag 0G83] of that chart's
equations. -/
def IsGysinHom {c : ℕ} (q : ℕ)
    (φ : pushforwardRelativeForms i π (q : ℤ) ⟶ gysinTarget i π c q) : Prop :=
  ∀ (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
    (x : Γ(pushforwardRelativeForms i π (q : ℤ), V)),
    φ.app V x =
      chartLoc i π q a.ambient a.equations
        (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
        (equationsClosedSet_restrictEquations i a.ambient
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x

/-- **`γ^0(1)`, the Gysin class of one**, at the generality of [Stacks, Tag 0G86]: the image of the
unit of `Ω^0_{Z/S}` under the Gysin map of the tag at `p = 0`, read in the degree the second factor
of the wedge pairing has. -/
def conormalUnitClass {c : ℕ}
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ))
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π c 0) :
    (conormalSource i π c).sections :=
  SheafOfModules.sectionsMap (γ₀ ≫ gysinDegreeShift i π σ) (subschemeFormUnit i π)

/-- A Gysin map of [Stacks, Tag 0G86] sends the restriction to `Z` of a form `ω` over `V` to the
class of the equation wedge `ω ∧ d f₁ ∧ ⋯ ∧ d f_c`, for the chart's equations restricted to `V`. -/
private theorem app_subschemeFormPullback_of_isGysinHom (q : ℕ)
    (γ : pushforwardRelativeForms i π (q : ℤ) ⟶ gysinTarget i π (d + 1) q)
    (hγ : IsGysinHom i π q γ) (a : EquationChart i (d + 1)) (V : X.Opens) (hV : V ≤ a.ambient)
    (ω : Γ(relativeDifferentialForms π (q : ℤ), V)) :
    γ.app V (subschemeFormPullback i π (q : ℤ) V ω) =
      chartCls i π q V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (isClosed_preimage_range_base i V)
        (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
        (gysinWedgeOn π a.equations (q : ℤ) hV ω) := by
  refine Eq.trans (hγ a V hV _) ?_
  refine Eq.trans (chartLoc_subschemeFormPullback i π q a.ambient a.equations
    (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
    (isClosed_preimage_range_base i a.ambient)
    (equationsClosedSet_restrictEquations i a.ambient
      (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV ω) ?_
  exact chartCls_homOfLE i π q hV a.equations
    (isClosed_preimage_range_base i a.ambient)
    (equationsClosedSet_restrictEquations i a.ambient
      (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)).le
    (isClosed_preimage_range_base i V)
    (equationsClosedSet_restrictEquations i V
      (isCutOutByEquationsOn_restrict hV
        (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le
    (gysinWedgeOn π a.equations (q : ℤ) hV ω)

/-- The value of `γ^0(1)` over an open `V` of an equation chart is the class of
`d f₁ ∧ ⋯ ∧ d f_c / (f₁ ⋯ f_c)`, for the chart's equations restricted to `V`. -/
theorem conormalUnitClass_eval
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π (d + 1) 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) (a : EquationChart i (d + 1)) (V : X.Opens) (hV : V ≤ a.ambient) :
    (conormalUnitClass i π σ γ₀).eval (op V) =
      (gysinDegreeShift i π σ).app V
        (chartCls i π 0 V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (isClosed_preimage_range_base i V)
          (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
          (gysinWedgeOn π a.equations ((0 : ℕ) : ℤ) hV
            ((relativeDifferentialFormsAlgebra π).one.eval (op V)))) := by
  refine Eq.trans (comp_val_app γ₀ (gysinDegreeShift i π σ) V
    ((subschemeFormUnit i π).eval (op V))) ?_
  refine congrArg ((gysinDegreeShift i π σ).app V) ?_
  exact Eq.trans (congrArg (γ₀.app V) (subschemeFormUnit_eval i π V))
    (app_subschemeFormPullback_of_isGysinHom i π 0 γ₀ hγ₀ a V hV _)

/-! ### The identity of morphisms of sheaves -/

/-- Two morphisms of sheaves of modules that agree over every open contained in a member of an open
cover are equal. -/
theorem hom_ext_of_cover {M N : X.Modules} {J : Type u} {U : J → X.Opens}
    (hU : ⨆ k, U k = ⊤) {φ ψ : M ⟶ N}
    (h : ∀ (k : J) (V : X.Opens), V ≤ U k → ∀ m : Γ(M, V), φ.app V m = ψ.app V m) :
    φ = ψ :=
  SheafOfModules.hom_ext
    (TopCat.Sheaf.eq_hom_of_restrict hU N.isSheaf (fun _ V _ => ψ.val.app (op V))
      (fun k V hV => ModuleCat.hom_ext (LinearMap.ext (h k V hV)))
      (fun _ _ _ => rfl))

/-- Let `i : Z ⟶ X` be a closed immersion of finite presentation whose conormal sheaf is locally
free of rank `c = d + 1`, let `γ^p` and `γ^0` be maps characterised as in [Stacks, Tag 0G86], and
let `σ` be a comparison of the two spellings of the degree `c` satisfying `hσ`. Then

`ω ↦ γ^p(ω|_Z)` **is** `ω ↦ ω ∧ γ^0(1)`

as morphisms `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, the wedge being the pairing
`Stacks.Gysin.conormalWedgePair`. This is the identity of morphisms of sheaves of which
[Stacks, Tag 0G88] is the degree-`q` cohomology. -/
theorem formRestriction_comp_gysinHom_succ [LocallyOfFinitePresentation i]
    (hE : ConormalRank i (d + 1))
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((d + 1 : ℕ) : ℤ))
    (hσ : ∀ (W : X.Opens) (f : Fin (d + 1) → Γ(X, W)) (V : X.Opens) (hV : V ≤ W),
      σ.app V (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V))) =
        equationsWedgeOn π f hV)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π (d + 1) p)
    (hγ : IsGysinHom i π p γ)
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π (d + 1) 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) :
    formRestriction i π (p : ℤ) ≫ γ =
      Stacks.Cohomology.rightMulHom (conormalWedgePair i π (d + 1) p)
        (conormalUnitClass i π σ γ₀) := by
  refine hom_ext_of_cover (U := fun a : EquationChart i (d + 1) => a.ambient)
    (iSup_equationChart_ambient i hE) fun a V hV ω => ?_
  have hleft : (formRestriction i π (p : ℤ) ≫ γ).app V ω =
      chartCls i π p V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (isClosed_preimage_range_base i V)
        (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
        (gysinWedgeOn π a.equations (p : ℤ) hV ω) := by
    exact Eq.trans (comp_val_app (formRestriction i π (p : ℤ)) γ V ω)
      (app_subschemeFormPullback_of_isGysinHom i π p γ hγ a V hV ω)
  refine Eq.trans hleft ?_
  refine Eq.trans ?_ (Stacks.Cohomology.rightMulHom_app_apply (conormalWedgePair i π (d + 1) p)
    (conormalUnitClass i π σ γ₀) (op V) ω).symm
  refine Eq.trans ?_ (conormalWedgePair_app i π (d + 1) p V ω
    ((conormalUnitClass i π σ γ₀).eval (op V))).symm
  refine Eq.trans ?_ (congrArg (conormalWedgeVal i π p V ω)
    (conormalUnitClass_eval i π σ γ₀ hγ₀ a V hV)).symm
  refine Eq.trans ?_ (conormalWedgeVal_chartCls i π p V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
    (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le σ ω _).symm
  exact congrArg (fun z => chartCls i π p V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
      (isClosed_preimage_range_base i V) (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
      z)
    (congrArg (fun z => (formWedgePair π p (d + 1)).app (op V) ω z)
      (hσ a.ambient a.equations V hV)).symm

end Stacks.Gysin

end
