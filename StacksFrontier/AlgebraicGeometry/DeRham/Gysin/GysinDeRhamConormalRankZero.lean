module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartFractionDeRhamAnyCount
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinConormalRankAny
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinExcisionAbelianAgreement

/-!
# [Stacks, Tag 0G87] at conormal rank zero

[Stacks, Tag 0G87] says that the Gysin map `γ^p` of [Stacks, Tag 0G86] is compatible with the de
Rham differentials on `Ω^•_{X/S}` and `Ω^•_{Z/S}`, where the conormal rank `c` is an arbitrary
natural number ([Stacks, Tag 0G8A]).  This file proves the case `c = 0`.

At rank `0` an equation chart carries the empty family, which generates the ideal of `Z` over an
open only where that ideal vanishes, so the charts cover `Set.range i.base` rather than all of `X`
(`Stacks.Gysin.range_subset_iSup_equationChart_ambient`).  Over an open missing `Set.range i.base`
the source of the Gysin map has only the zero section in every degree
(`Stacks.Gysin.subsingleton_pushforwardRelativeForms_of_disjoint`).

## Main results

* `Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartLoc`: the square of [Stacks, Tag 0G87]
  at one equation chart, on a form lifted to the ambient scheme, for any number of equations,
  with the local Gysin map `Stacks.Gysin.chartLoc` of the chart's equations and the right vertical
  arrow `Stacks.Gysin.gysinTargetDeRhamHom` of [Stacks, Tag 0G74] part (2).
* `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank_zero`: [Stacks, Tag 0G87] at `c = 0`.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.FractionClass
open Stacks.Tag01VSPullbackTensor (homApp_presheaf_map)

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The square at one equation chart, for any number of equations -/

/-- **The square of [Stacks, Tag 0G87] at one equation chart, on a form lifted to the ambient
scheme, for any number of equations.**  For an open `V` of the chart and an ambient `p`-form `ω`
over `V`, the local Gysin maps `Stacks.Gysin.chartLoc` of the chart in degrees `p` and `p + 1`
intertwine the de Rham differential of `ω|_Z` with the differential
`Stacks.Gysin.gysinTargetDeRhamHom` on the Gysin target, given `hfrac`, the naturality of the top
term of the extended alternating Čech complex of the chart's equations. -/
theorem abSectionsHom_gysinTargetDeRhamHom_chartLoc (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (f : Fin c → Γ(X, W))
    (hcut : IsCutOutByEquationsOn i W f) (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hgT : equationsClosedSet (restrictEquations W f) = W.ι ⁻¹' Set.range i.base)
    (hfrac : ∀ {F G : W.toScheme.Modules} (φ : F ⟶ G),
      fracTermTop (restrictEquations W f) F ≫ (cplxMap (restrictEquations W f) φ).f c =
        φ ≫ fracTermTop (restrictEquations W f) G)
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π c p) V
        (chartLoc i π p W f hcut hgT V hV (subschemeFormPullback i π (p : ℤ) V ω)) =
      chartLoc i π (p + 1) W f hcut hgT V hV
        (pushforwardDeRham i π p V (subschemeFormPullback i π (p : ℤ) V ω)) := by
  rw [chartLoc_subschemeFormPullbackOfClassMap i π p W f hcut hT hgT hfrac V hV ω,
    abSectionsHom_gysinTargetDeRhamHom_chartClsOfClassMap i π p W f hT hgT.le
      (supportCohomologyRestrictAbNatural W (isClosed_range_base i) hT c
        (ambientDeRhamShiftAbHom π c p)) V hV ω,
    pushforwardDeRham_subschemeFormPullback i π p V ω,
    chartLoc_subschemeFormPullbackOfClassMap i π (p + 1) W f hcut hT hgT hfrac V hV
      (((deRhamComplex π).d p (p + 1)).val.app (op V) ω),
    ambientDeRhamShift_gysinWedgeOn π f p hV ω]

/-! ### Stacks 0G87 at conormal rank zero -/

/-- **[Stacks, Tag 0G87] at conormal rank `0`.**  Let `π : X ⟶ S` be a morphism of schemes and
`i : Z ⟶ X` a closed immersion of finite presentation whose conormal sheaf is locally free of rank
`0`.  Let `γ` and `γ'` be the Gysin maps of [Stacks, Tag 0G86] in the degrees `p` and `p + 1`,
each characterised as `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank` characterises it: over
every open contained in an equation chart it is the Gysin map of that chart's equations — here the
**empty** family.  Then the square

`ℋ^0_Z(d_{X/S}) ∘ γ^p = γ^{p+1} ∘ d_{Z/S}`

commutes, on the sections over every open of `X`. -/
theorem gysinHom_comm_deRham_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) (p : ℕ) (hE : ConormalRank i 0)
    (γ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π 0 p)
    (γ' : pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ) ⟶ gysinTarget i π 0 (p + 1))
    (hγ : ∀ (a : EquationChart i 0) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
      γ.app V x =
        chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (hγ' : ∀ (a : EquationChart i 0) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π ((p + 1 : ℕ) : ℤ), V)),
      γ'.app V x =
        chartLoc i π (p + 1) a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π 0 p) V (γ.app V x) =
      γ'.app V (pushforwardDeRham i π p V x) := by
  have hchart : ∀ (a : EquationChart i 0) (U : X.Opens) (hU : U ≤ a.ambient)
      (ω : Γ(relativeDifferentialForms π (p : ℤ), U)),
      abSectionsHom (gysinTargetDeRhamHom i π 0 p) U
          (γ.app U (subschemeFormPullback i π (p : ℤ) U ω)) =
        γ'.app U (pushforwardDeRham i π p U (subschemeFormPullback i π (p : ℤ) U ω)) := by
    intro a U hU ω
    rw [hγ a U hU, hγ' a U hU]
    exact abSectionsHom_gysinTargetDeRhamHom_chartLoc i π p a.ambient a.equations _
      (isClosed_preimage_range_base i a.ambient) _
      (fun {_ _} φ => fracTermTop_naturality_zero (restrictEquations a.ambient a.equations) φ)
      U hU ω
  have hpt : ∀ z : ↥V, ∃ (U : X.Opens) (hU : U ≤ V), (z : X) ∈ U ∧
      (gysinTarget i π 0 (p + 1)).presheaf.map (homOfLE hU).op
          (abSectionsHom (gysinTargetDeRhamHom i π 0 p) V (γ.app V x)) =
        (gysinTarget i π 0 (p + 1)).presheaf.map (homOfLE hU).op
          (γ'.app V (pushforwardDeRham i π p V x)) := by
    rintro ⟨z, hz⟩
    obtain ⟨U, hU, hzU, hcase⟩ : ∃ (U : X.Opens) (hU : U ≤ V), z ∈ U ∧
        ((∃ (a : EquationChart i 0) (_ : U ≤ a.ambient)
            (ω : Γ(relativeDifferentialForms π (p : ℤ), U)),
            subschemeFormPullback i π (p : ℤ) U ω =
              (pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hU).op x) ∨
          (U : Set X) ∩ Set.range i.base = ∅) := by
      by_cases hzr : z ∈ Set.range i.base
      · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
          (range_subset_iSup_equationChart_ambient i hE hzr)
        have hzU : z ∈ V ⊓ a.ambient := ⟨hz, ha⟩
        have hUV : V ⊓ a.ambient ≤ V := inf_le_left
        obtain ⟨U, hUU, hzU', ω, hω⟩ := exists_subschemeFormPullback_restrict i π p
          (V ⊓ a.ambient)
          ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hUV).op x) z hzU
        refine ⟨U, hUU.trans hUV, hzU',
          Or.inl ⟨a, hUU.trans inf_le_right, ω, hω.trans ?_⟩⟩
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
        exact congrArg (fun m : U ⟶ V =>
          (pushforwardRelativeForms i π (p : ℤ)).presheaf.map m.op x) (Subsingleton.elim _ _)
      · exact ⟨V ⊓ complRangeOpens i, inf_le_left, ⟨hz, hzr⟩,
          Or.inr (disjoint_of_le_complRangeOpens i inf_le_right)⟩
    refine ⟨U, hU, hzU, ?_⟩
    rw [← abSectionsHom_res (gysinTargetDeRhamHom i π 0 p) hU (γ.app V x),
      ← homApp_presheaf_map γ (homOfLE hU) x,
      ← homApp_presheaf_map γ' (homOfLE hU) (pushforwardDeRham i π p V x),
      ← pushforwardDeRham_res i π p hU x]
    rcases hcase with ⟨a, haU, ω, hω⟩ | hdis
    · rw [← hω]
      exact hchart a U haU ω
    · have := subsingleton_pushforwardRelativeForms_of_disjoint i π (p : ℤ) U hdis
      have := subsingleton_pushforwardRelativeForms_of_disjoint i π ((p + 1 : ℕ) : ℤ) U hdis
      rw [Subsingleton.elim
          ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hU).op x) 0,
        Subsingleton.elim (pushforwardDeRham i π p U 0) 0]
      simp only [map_zero]
  choose U hU hzU hcase using hpt
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨(gysinTarget i π 0 (p + 1)).presheaf, (gysinTarget i π 0 (p + 1)).isSheaf⟩ :
      TopCat.Sheaf Ab.{u} X))
    U V (fun z => homOfLE (hU z)) (fun y hy =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hzU ⟨y, hy⟩⟩) _ _
    fun z => hcase z

end Stacks.Gysin

end
