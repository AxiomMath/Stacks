module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgeProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartFractionDeRhamAnyCount
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinConormalRankAny
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.SupportCohomologyDisjointOpen

/-!
# The Gysin projection formula of Tag 0G88 at an arbitrary conormal rank

[Stacks, Tag 0G88] is the projection formula `γ^p(α|_Z) = i^{-1}α ∧ γ^0(1)` for the Gysin maps of
[Stacks, Tag 0G86], and the hypotheses are that tag's: `i : Z ⟶ X` a closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c`, with `c ≥ 0` — as
[Stacks, Tag 0G8A] says explicitly.  This file proves it at **every** `c`.

`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ConormalWedgeProjection.lean` proves it for
`c = d + 1`, where the equation charts cover `X`.  At `c = 0` they do not: a chart carries an
empty family of equations, so its ambient open lies inside `Z`, and the charts cover only the
image of `i`.  Two things replace them:

* the covering `Stacks.Gysin.equationChart_option_cover` — the charts together with the complement
  of the image — over whose complementary member the target has a **single** section, by
  `Stacks.Gysin.subsingleton_gysinTarget_sections_of_disjoint`, so that there every pair of maps
  agrees;
* the class map of [Stacks, Tag 0G7Q] in the form
  `Stacks.Gysin.chartClsHomOfClassMap`, built from
  `Stacks.Perfect.FractionClass.classMapToSupport` rather than from
  `Stacks.Perfect.SupportedFraction.supportedFractionSource`, the latter factoring through a top
  Čech differential that an empty family does not have.

## Main results

* `Stacks.Gysin.formRestriction_comp_gysinHom_zero`: the identity of morphisms of sheaves at
  conormal rank `0`.
* `Stacks.Gysin.formRestriction_comp_gysinHom`: it at every conormal rank, by cases on `c`.
* `Stacks.Gysin.gysinHom_formRestriction_cupDegreeZero`: **[Stacks, Tag 0G88]** in every
  cohomological degree, at every conormal rank, for any `γ`, `γ^0` satisfying the
  characterisation of [Stacks, Tag 0G86].
* `Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero`: the same at the canonical maps of
  [Stacks, Tag 0G86] themselves, so that the only hypotheses are the tag's.

## References

* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.ConormalEquations (ConormalRank)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.FractionClass
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isQuasicoherent_relativeDifferentialForms

variable (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ)

/-! ### The covering of Tag 0G86, as an equality of opens -/

/-- **The equation charts together with the complement of the image cover the ambient scheme**, at
every conormal rank, read as the equality of opens that the gluing and the extensionality of
morphisms of sheaves consume.  This is `Stacks.Gysin.equationChart_option_cover`. -/
theorem iSup_equationChart_option [LocallyOfFinitePresentation i] (hE : ConormalRank i c) :
    ⨆ b : Option (EquationChart i c),
      (fun b => Option.elim b (complRangeOpens i) (fun a => a.ambient)) b = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr (equationChart_option_cover i hE x)

/-! ### The class map at degree `c`, built without a top differential -/

/-- **The class map of [Stacks, Tag 0G7Q] of a family of equations on `V`, with coefficient
`Ω^c_{X/S}`, for any number of equations.**  This is `Stacks.Gysin.conormalClsHom` with
`Stacks.Perfect.SupportedFraction.supportedFractionSource` replaced by
`Stacks.Perfect.FractionClass.classMapToSupport`, exactly as
`Stacks.Gysin.chartClsHomOfClassMap` replaces `Stacks.Gysin.chartClsHom`; the transport by the
derived excision of [Stacks, Tag 0G78] is unchanged. -/
def conormalClsHomOfClassMap (V : X.Opens) (f : Fin c → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base) :
    Scheme.Modules.restrict (relativeDifferentialForms π (c : ℤ)) V.ι ⟶
      Scheme.Modules.restrict (conormalSource i π c) V.ι :=
  classMapToSupport f
      ((Scheme.Modules.restrictFunctor V.ι).obj (relativeDifferentialForms π (c : ℤ)))
      (isClosed_preimage_range_base i V) hTf ≫
    (supportCohomologyRestrictIso V (isClosed_range_base i) (isClosed_preimage_range_base i V)
      (c : ℤ) (relativeDifferentialForms π (c : ℤ))).inv

/-- **The degree comparison moves across the class map, for any number of equations.**  This is
`Stacks.Gysin.chartClsHom_comp_gysinDegreeShift` with the class map of
`Stacks.Gysin.chartClsHomOfClassMap`; the functoriality of [Stacks, Tag 0G7T] used is
`Stacks.Gysin.classMapToSupport_naturality`, whose naturality hypothesis is carried. -/
theorem chartClsHomOfClassMap_comp_gysinDegreeShift (V : X.Opens) (f : Fin c → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ))
    (hfrac : fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)))) ≫
        (cplxMap f ((Scheme.Modules.restrictFunctor V.ι).map σ)).f c =
      (Scheme.Modules.restrictFunctor V.ι).map σ ≫ fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj (relativeDifferentialForms π (c : ℤ))))
    {D : V.toScheme.Modules}
    (ρ : Scheme.Modules.restrict (conormalSource i π c) V.ι ⟶ D) :
    chartClsHomOfClassMap i π 0 V f (isClosed_preimage_range_base i V) hTf ≫
        (Scheme.Modules.restrictFunctor V.ι).map (gysinDegreeShift i π σ) ≫ ρ =
      (Scheme.Modules.restrictFunctor V.ι).map σ ≫ conormalClsHomOfClassMap i π V f hTf ≫ ρ :=
  Eq.trans
    (congrArg
      (fun ψ : Scheme.Modules.restrict (gysinTarget i π c 0) V.ι ⟶
          Scheme.Modules.restrict (conormalSource i π c) V.ι =>
        chartClsHomOfClassMap i π 0 V f (isClosed_preimage_range_base i V) hTf ≫ ψ ≫ ρ)
      (restrictFunctor_map_supportCohomologySheafFunctor V (isClosed_range_base i)
        (isClosed_preimage_range_base i V) (c : ℤ) σ))
    (conj_comp_of_naturality _ _ _ _ _ _ ρ
      (classMapToSupport_naturality f ((Scheme.Modules.restrictFunctor V.ι).map σ)
        (isClosed_preimage_range_base i V) hTf hfrac))

/-- **Wedging with a class of the class map of [Stacks, Tag 0G7Q] is the class of the wedge, for
any number of equations.**  This is `Stacks.Gysin.conormalClsHom_comp_conormalWedgeHom` with the
class map of `Stacks.Gysin.chartClsHomOfClassMap`. -/
theorem conormalClsHomOfClassMap_comp_conormalWedgeHom (V : X.Opens)
    (f : Fin c → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (hfrac : fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj (relativeDifferentialForms π (c : ℤ))) ≫
        (cplxMap f (localFormWedgeHom π p V ω)).f c =
      localFormWedgeHom π p V ω ≫ fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) :
    conormalClsHomOfClassMap i π V f hTf ≫ conormalWedgeHom i π p V ω =
      localFormWedgeHom π p V ω ≫
        chartClsHomOfClassMap i π p V f (isClosed_preimage_range_base i V) hTf :=
  Eq.trans
    (Eq.trans
      (congrArg (fun ψ => conormalClsHomOfClassMap i π V f hTf ≫ ψ) (Category.comp_id _).symm)
      (conj_comp_of_naturality _ _ _ _ _ _ (𝟙 _)
        (classMapToSupport_naturality f (localFormWedgeHom π p V ω)
          (isClosed_preimage_range_base i V) hTf hfrac)))
    (congrArg (fun ψ => localFormWedgeHom π p V ω ≫ ψ) (Category.comp_id _))

/-- **The pairing of `ω` with the class of `y` is the class of `ω ∧ y`, for any number of
equations**, on the sections over `V`.  This is `Stacks.Gysin.conormalWedgeVal_chartCls` with the
class map of `Stacks.Gysin.chartClsOfClassMap`. -/
theorem conormalWedgeVal_chartClsOfClassMap (V : X.Opens) (f : Fin c → Γ(V.toScheme, ⊤))
    (hTf : equationsClosedSet f ⊆ V.ι ⁻¹' Set.range i.base)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ))
    (hfracσ : fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)))) ≫
        (cplxMap f ((Scheme.Modules.restrictFunctor V.ι).map σ)).f c =
      (Scheme.Modules.restrictFunctor V.ι).map σ ≫ fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj (relativeDifferentialForms π (c : ℤ))))
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (hfracω : fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj (relativeDifferentialForms π (c : ℤ))) ≫
        (cplxMap f (localFormWedgeHom π p V ω)).f c =
      localFormWedgeHom π p V ω ≫ fracTermTop f
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))
    (y : Γ(relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)), V)) :
    conormalWedgeVal i π p V ω
        ((gysinDegreeShift i π σ).app V
          (chartClsOfClassMap i π 0 V f (isClosed_preimage_range_base i V) hTf V le_rfl y)) =
      chartClsOfClassMap i π p V f (isClosed_preimage_range_base i V) hTf V le_rfl
        ((formWedgePair π p c).app (op V) ω (σ.app V y)) := by
  have hkey := Eq.trans
    (chartClsHomOfClassMap_comp_gysinDegreeShift i π V f hTf σ hfracσ
      (conormalWedgeHom i π p V ω))
    (congrArg (fun ψ => (Scheme.Modules.restrictFunctor V.ι).map σ ≫ ψ)
      (conormalClsHomOfClassMap_comp_conormalWedgeHom i π p V f hTf ω hfracω))
  have hL := congrArg (fun θ => restrictSections θ V le_rfl y) hkey
  have hLHS : restrictSections
        (chartClsHomOfClassMap i π 0 V f (isClosed_preimage_range_base i V) hTf ≫
        (Scheme.Modules.restrictFunctor V.ι).map (gysinDegreeShift i π σ) ≫
          conormalWedgeHom i π p V ω) V le_rfl y =
      conormalWedgeVal i π p V ω ((gysinDegreeShift i π σ).app V
        (chartClsOfClassMap i π 0 V f (isClosed_preimage_range_base i V) hTf V le_rfl y)) := by
    rw [restrictSections_comp, restrictSections_comp, restrictSections_restrictFunctor_map]
    rfl
  have hRHS : restrictSections ((Scheme.Modules.restrictFunctor V.ι).map σ ≫
        localFormWedgeHom π p V ω ≫
          chartClsHomOfClassMap i π p V f (isClosed_preimage_range_base i V) hTf) V le_rfl y =
      chartClsOfClassMap i π p V f (isClosed_preimage_range_base i V) hTf V le_rfl
        ((formWedgePair π p c).app (op V) ω (σ.app V y)) := by
    rw [restrictSections_comp, restrictSections_comp, restrictSections_restrictFunctor_map,
      restrictSections_localFormWedgeHom, val_map_homOfLE_refl]
    rfl
  exact hLHS.symm.trans (hL.trans hRHS)

/-! ### The Gysin class of one at conormal rank zero -/

/-- A Gysin map at rank `0` sends the Gysin pullback of `ω` over an open of a chart to the class of
the wedge of `ω` with the empty wedge. -/
private theorem gysinHom_app_subschemeFormPullback_zero (γ : pushforwardRelativeForms i π (p : ℤ) ⟶
      gysinTarget i π 0 p) (hγ : IsGysinHom i π p γ) (a : EquationChart i 0) (V : X.Opens)
    (hV : V ≤ a.ambient) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    γ.app V (subschemeFormPullback i π (p : ℤ) V ω) =
      chartClsOfClassMap i π p V (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (isClosed_preimage_range_base i V)
        (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
        (gysinWedgeOn π a.equations (p : ℤ) hV ω) := by
  refine Eq.trans (hγ a V hV _) ?_
  refine Eq.trans (chartLoc_subschemeFormPullbackOfClassMap i π p a.ambient a.equations
    (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
    (isClosed_preimage_range_base i a.ambient)
    (equationsClosedSet_restrictEquations i a.ambient
      (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))
    (fun {_ _} φ => fracTermTop_naturality_zero
      (restrictEquations a.ambient a.equations) φ) V hV ω) ?_
  exact chartClsOfClassMap_homOfLE i π p hV a.equations
    (isClosed_preimage_range_base i a.ambient)
    (equationsClosedSet_restrictEquations i a.ambient
      (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)).le
    (isClosed_preimage_range_base i V)
    (equationsClosedSet_restrictEquations i V
      (isCutOutByEquationsOn_restrict hV
        (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le
    (fun M => map_fracTermTop_comp_restrictCplxIso_zero (X.homOfLE hV)
      (restrictEquations a.ambient a.equations) M)
    (fun {_ _} φ => fracTermTop_naturality_zero
      (fun j => (X.homOfLE hV).appTop (restrictEquations a.ambient a.equations j)) φ)
    (gysinWedgeOn π a.equations (p : ℤ) hV ω)

/-- **The value of `γ^0(1)` over an open of an equation chart at conormal rank `0`** is the class,
for the chart's empty family of equations restricted to that open, of `1 ∧ (` the empty wedge `)`.

This is `Stacks.Gysin.conormalUnitClass_eval` with the two inputs replaced by their
any-number-of-equations forms: the Gysin formula of [Stacks, Tag 0G83] is
`Stacks.Gysin.chartLoc_subschemeFormPullbackOfClassMap` and the locality of the class map of
[Stacks, Tag 0G7Q] is `Stacks.Gysin.chartClsOfClassMap_homOfLE`.  Their naturality hypotheses are
discharged at the empty family by `Stacks.Gysin.fracTermTop_naturality_zero` and
`Stacks.Gysin.map_fracTermTop_comp_restrictCplxIso_zero`. -/
theorem conormalUnitClass_eval_zero
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((0 : ℕ) : ℤ))
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π 0 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) (a : EquationChart i 0) (V : X.Opens) (hV : V ≤ a.ambient) :
    (conormalUnitClass i π σ γ₀).eval (op V) =
      (gysinDegreeShift i π σ).app V
        (chartClsOfClassMap i π 0 V (restrictEquations V
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
  refine Eq.trans (congrArg (γ₀.app V) (subschemeFormUnit_eval i π V)) ?_
  exact gysinHom_app_subschemeFormPullback_zero i π 0 γ₀ hγ₀ a V hV _

/-! ### The identity of morphisms of sheaves at conormal rank zero -/

/-- **Stacks Project, Tag 0G88 at conormal rank `0`: the identity of morphisms of sheaves of which
the tag is the degree-`q` cohomology.**

The proof is that of `Stacks.Gysin.formRestriction_comp_gysinHom_succ` run on a different covering
and with a different construction of the class map.  The equation charts do not cover `X` at rank
`0`, so the covering is `Stacks.Gysin.equationChart_option_cover`: the charts together with the
complement of the image of `i`.  Over the complementary member the target has a **single**
section, by `Stacks.Gysin.subsingleton_gysinTarget_sections_of_disjoint`, so the two sides agree
there for no reason at all; over an open of a chart they are both the class, for the chart's empty
family of equations restricted to that open, of `ω ∧ (` the empty wedge `)`. -/
theorem formRestriction_comp_gysinHom_zero [LocallyOfFinitePresentation i]
    (hE : ConormalRank i 0)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) ⟶
      relativeDifferentialForms π ((0 : ℕ) : ℤ))
    (hσ : ∀ (W : X.Opens) (f : Fin 0 → Γ(X, W)) (V : X.Opens) (hV : V ≤ W),
      σ.app V (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V))) =
        equationsWedgeOn π f hV)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π 0 p)
    (hγ : IsGysinHom i π p γ)
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π 0 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) :
    formRestriction i π (p : ℤ) ≫ γ =
      Stacks.Cohomology.rightMulHom (conormalWedgePair i π 0 p)
        (conormalUnitClass i π σ γ₀) := by
  refine hom_ext_of_cover
    (U := fun b : Option (EquationChart i 0) =>
      Option.elim b (complRangeOpens i) (fun a => a.ambient))
    (iSup_equationChart_option i hE) fun b V hV ω => ?_
  match b, hV with
  | none, hV =>
      have := subsingleton_gysinTarget_sections_of_disjoint i π 0 p V
        (disjoint_of_le_complRangeOpens i hV)
      exact Subsingleton.elim _ _
  | some a, hV =>
      have hleft : (formRestriction i π (p : ℤ) ≫ γ).app V ω =
          chartClsOfClassMap i π p V (restrictEquations V
              (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
              (isClosed_preimage_range_base i V)
            (equationsClosedSet_restrictEquations i V
                (isCutOutByEquationsOn_restrict hV
                  (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
            (gysinWedgeOn π a.equations (p : ℤ) hV ω) := by
        refine Eq.trans (comp_val_app (formRestriction i π (p : ℤ)) γ V ω) ?_
        exact gysinHom_app_subschemeFormPullback_zero i π p γ hγ a V hV ω
      refine Eq.trans hleft ?_
      refine Eq.trans ?_ (Stacks.Cohomology.rightMulHom_app_apply (conormalWedgePair i π 0 p)
        (conormalUnitClass i π σ γ₀) (op V) ω).symm
      refine Eq.trans ?_ (conormalWedgePair_app i π 0 p V ω
        ((conormalUnitClass i π σ γ₀).eval (op V))).symm
      refine Eq.trans ?_ (congrArg (conormalWedgeVal i π p V ω)
        (conormalUnitClass_eval_zero i π σ γ₀ hγ₀ a V hV)).symm
      refine Eq.trans ?_ (conormalWedgeVal_chartClsOfClassMap i π p V (restrictEquations V
              (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
        (equationsClosedSet_restrictEquations i V
            (isCutOutByEquationsOn_restrict hV
              (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le σ
        (fracTermTop_naturality_zero (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          ((Scheme.Modules.restrictFunctor V.ι).map σ)) ω
        (fracTermTop_naturality_zero (restrictEquations V
          (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (localFormWedgeHom π p V ω)) _).symm
      exact congrArg (fun z => chartClsOfClassMap i π p V (restrictEquations V
              (fun k => X.presheaf.map (homOfLE hV).op (a.equations k)))
          (isClosed_preimage_range_base i V) (equationsClosedSet_restrictEquations i V
                (isCutOutByEquationsOn_restrict hV
                  (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish))).le V le_rfl
          z)
        (congrArg (fun z => (formWedgePair π p 0).app (op V) ω z)
          (hσ a.ambient a.equations V hV)).symm

/-! ### The identity of morphisms of sheaves, at every conormal rank -/

/-- **Stacks Project, Tag 0G88 at every conormal rank: the identity of morphisms of sheaves of
which the tag is the degree-`q` cohomology.**  Let `i : Z ⟶ X` be a closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c`, let `γ^p` and `γ^0` be maps
characterised as in [Stacks, Tag 0G86], and let `σ` be the comparison of the two spellings of the
degree `c`.  Then

`ω ↦ γ^p(ω|_Z)` **is** `ω ↦ ω ∧ γ^0(1)`

as morphisms `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, the wedge being the pairing
`Stacks.Gysin.conormalWedgePair`.

**The rank is an arbitrary natural number**, as [Stacks, Tag 0G86] states it and as
[Stacks, Tag 0G8A] says explicitly (`c ≥ 0`); neither `c ≠ 0` nor a rank of the form `d + 1` is
assumed.  The proof splits on `c` and nothing else does:

* for `c = d + 1`, `Stacks.Gysin.formRestriction_comp_gysinHom_succ`, where the equation charts
  cover `X`;
* for `c = 0`, `formRestriction_comp_gysinHom_zero`, where they cover only the image of `i` and
  the covering is augmented by its complement. -/
theorem formRestriction_comp_gysinHom [LocallyOfFinitePresentation i]
    (hE : ConormalRank i c)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ))
    (hσ : ∀ (W : X.Opens) (f : Fin c → Γ(X, W)) (V : X.Opens) (hV : V ≤ W),
      σ.app V (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V))) =
        equationsWedgeOn π f hV)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p)
    (hγ : IsGysinHom i π p γ)
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π c 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) :
    formRestriction i π (p : ℤ) ≫ γ =
      Stacks.Cohomology.rightMulHom (conormalWedgePair i π c p)
        (conormalUnitClass i π σ γ₀) := by
  match c, hE, σ, hσ, γ, hγ, γ₀, hγ₀ with
  | 0, hE, σ, hσ, γ, hγ, γ₀, hγ₀ =>
      exact formRestriction_comp_gysinHom_zero i π p hE σ hσ γ hγ γ₀ hγ₀
  | _ + 1, hE, σ, hσ, γ, hγ, γ₀, hγ₀ =>
      exact formRestriction_comp_gysinHom_succ i π p hE σ hσ γ hγ γ₀ hγ₀

/-! ### The projection formula in every cohomological degree -/

variable [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]

/-- **Stacks Project, Tag 0G88.**  Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `c`, and let
`γ^p`, `γ^0` be maps characterised as in [Stacks, Tag 0G86] — that is, which over every open
contained in an open on which `c` functions generate the ideal of `Z` are the Gysin map of
[Stacks, Tag 0G83] of those functions.  Then in every cohomological degree `q`, for every class
`α ∈ H^q(X, Ω^p_{X/S})`,

`γ^p(α|_Z) = α ∪ γ^0(1)`,

the cup product being with the degree-zero class `γ^0(1)` for the wedge pairing
`Stacks.Gysin.conormalWedgePair`.  The two sides are read as morphisms
`H^q(X, Ω^p_{X/S}) ⟶ H^q(X, i_*ℋ^c_Z(Ω^{p+c}_{X/S}))`, so the statement is the identity for all
`α` at once.

**`Z` is only locally cut out by `c` equations, and the rank `c` is arbitrary.**  No global family
of functions on `X` appears; the hypotheses are exactly those of [Stacks, Tag 0G86], and `hγ`,
`hγ₀` are not assumed results but that tag's characterisation, which determines the two maps.  The
instance at the tag's own maps, with those hypotheses discharged, is
`Stacks.Gysin.conormalGysin_formRestriction_cupDegreeZero`. -/
theorem gysinHom_formRestriction_cupDegreeZero [LocallyOfFinitePresentation i]
    (hE : ConormalRank i c)
    (σ : relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ)) ⟶
      relativeDifferentialForms π (c : ℤ))
    (hσ : ∀ (W : X.Opens) (f : Fin c → Γ(X, W)) (V : X.Opens) (hV : V ≤ W),
      σ.app V (gysinWedgeOn π f ((0 : ℕ) : ℤ) hV
          ((relativeDifferentialFormsAlgebra π).one.eval (op V))) =
        equationsWedgeOn π f hV)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p)
    (hγ : IsGysinHom i π p γ)
    (γ₀ : pushforwardRelativeForms i π ((0 : ℕ) : ℤ) ⟶ gysinTarget i π c 0)
    (hγ₀ : IsGysinHom i π 0 γ₀) (q : ℕ) :
    (_root_.Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
        (_root_.Hfunctor X.ringCatSheaf ⊤ q).map γ =
      Stacks.Cohomology.cupDegreeZero X.ringCatSheaf (conormalWedgePair i π c p)
        (conormalUnitClass i π σ γ₀) q :=
  Eq.trans ((_root_.Hfunctor X.ringCatSheaf ⊤ q).map_comp
      (formRestriction i π (p : ℤ)) γ).symm
    (congrArg (_root_.Hfunctor X.ringCatSheaf ⊤ q).map
      (formRestriction_comp_gysinHom i π p hE σ hσ γ hγ γ₀ hγ₀))

/-- **Stacks Project, Tag 0G88 at the canonical Gysin maps of [Stacks, Tag 0G86], with nothing
assumed.**  The only hypotheses are the tag's own: `i` a closed immersion of finite presentation
whose conormal sheaf is locally free of rank `c`.

**`c` is an arbitrary natural number**, as [Stacks, Tag 0G86] states it and as [Stacks, Tag 0G8A]
says explicitly (`c ≥ 0`): the case `c = 0`, in which `Z` is a *clopen* piece of `X` by
`Stacks.Gysin.isClopen_range_base_of_conormalRank_zero` and in which a chart carries the empty
family of equations, is part of the statement and not a degenerate exclusion.

The maps are `Stacks.DeRham.CohomologicalGysin.conormalGysinHom`, the `γ^p` of
[Stacks, Tag 0G86] itself, whose characterisation is
`Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app`; the degree comparison is the canonical
transport, whose one equation is `Stacks.Gysin.eqToHom_app_gysinWedgeOn_one`. -/
@[stacks 0G88]
theorem conormalGysin_formRestriction_cupDegreeZero [LocallyOfFinitePresentation i]
    (hE : ConormalRank i c) (q : ℕ) :
    (_root_.Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
        (_root_.Hfunctor X.ringCatSheaf ⊤ q).map
          (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE) =
      Stacks.Cohomology.cupDegreeZero X.ringCatSheaf (conormalWedgePair i π c p)
        (conormalUnitClass i π
          (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
          (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE)) q :=
  gysinHom_formRestriction_cupDegreeZero i π p hE _
    (fun _ f _ hV => eqToHom_app_gysinWedgeOn_one π f hV) _
    (fun a V hV x => Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app i π p hE a V hV x) _
    (fun a V hV x => Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app i π 0 hE a V hV x) q

end Stacks.Gysin

end
