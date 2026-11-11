module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLift
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# Base change of the Gysin map along a transverse square

This file proves [Stacks, Tag 0G89]: for a cartesian square of closed immersions satisfying the
assumptions of [Stacks, Tag 0G86], the Gysin maps `γ^p` commute with pullback of differential
forms and with the base change arrow of [Stacks, Cohomology, Remark 0G78] on the targets.

## Main results

* `Stacks.Gysin.conormalGysinHom_comp_gysinBaseChangeTargetHom`: [Stacks, Tag 0G89].
* `Stacks.Gysin.conormalGysinHom_comp_homEquiv_gysinBaseChangePull`: the same square before the
  identification `Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso` of the targets.

## Implementation notes

The proof is the source's: the commutativity is checked locally on equation charts, on forms
lifted to the ambient scheme, where both Gysin maps are given by the formula of
[Stacks, Tag 0G83]; the class maps are compatible with the right vertical arrow by
`Stacks.Gysin.chartClsOfClassMap_gysinBaseChangePull` ([Stacks, Tag 0G7U]) and the equation
wedges pull back to each other.  The pulled-back chart is
`Stacks.Gysin.EquationChart.ofIsPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.DeRham.CohomologicalGysin
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)

universe u

namespace Stacks.Gysin

variable {Z X S Z' X' S' : Scheme.{u}}

/-- The class map of a chart depends on its equations only through their values. -/
theorem chartClsOfClassMap_congr_equations (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c : ℕ} (p : ℕ) (W : X.Opens) {f₁ f₂ : Fin c → Γ(W.toScheme, ⊤)} (e : f₁ = f₂)
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf₁ : equationsClosedSet f₁ ⊆ W.ι ⁻¹' Set.range i.base)
    (hTf₂ : equationsClosedSet f₂ ⊆ W.ι ⁻¹' Set.range i.base) (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    chartClsOfClassMap i π p W f₁ hT hTf₁ V hV y =
      chartClsOfClassMap i π p W f₂ hT hTf₂ V hV y := by
  subst e
  rfl

variable (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
  (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)

/-- The equation wedge of the pulled-back chart is the pullback of the equation wedge. -/
theorem gysinWedgeOn_pullback_chart (right_comm : g ≫ π = π' ≫ t) {W : X.Opens} {c : ℕ}
    (f : Fin c → Γ(X, W)) (p : ℤ) {V : X.Opens} (hV : V ≤ W)
    (ω : Γ(relativeDifferentialForms π p, V)) :
    gysinWedgeOn π' (fun k => (g.app W).hom (f k)) p (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ W from fun _ hz => hV hz)
        (relativeDifferentialFormsPullback g π π' t right_comm p V ω) =
      relativeDifferentialFormsPullback g π π' t right_comm (p + (c : ℤ)) V
        (gysinWedgeOn π f p hV ω) := by
  have hV' : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := fun _ hz => hV hz
  rw [← gysinWedgeOn_restrict π' (fun k => (g.app W).hom (f k)) p hV',
    ← gysinWedgeOn_restrict π f p hV ω,
    relativeDifferentialFormsPullback_gysinWedgeOn g π π' t right_comm
      (fun j => (X.presheaf.map (homOfLE hV).op).hom (f j)) p ω]
  exact congrArg
    (fun z : Fin c → Γ(X', g ⁻¹ᵁ V) => gysinWedgeOn π' z p (le_refl (g ⁻¹ᵁ V))
      (relativeDifferentialFormsPullback g π π' t right_comm p V ω))
    (funext fun j => (app_structurePresheaf_map g hV (f j)).symm)

variable [IsClosedImmersion i] [LocallyOfFinitePresentation i] [IsClosedImmersion i']
  [LocallyOfFinitePresentation i']

/-- **The Gysin square of [Stacks, Tag 0G89] on a form lifted to the ambient scheme over an
equation chart.**  On `ω̃|_Z` both Gysin maps are given by the formula of [Stacks, Tag 0G83], the
class maps are compatible with the right vertical arrow by
`chartClsOfClassMap_gysinBaseChangePull` ([Stacks, Tag 0G7U]), and the equation wedge pulls back
to the equation wedge of the pulled-back equations. -/
theorem conormalGysinHom_homEquiv_app_subschemeFormPullback (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (hE' : ConormalRank i' c) (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    Scheme.Modules.Hom.app (conormalGysinHom i π p hE ≫
        (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE)) V
        (subschemeFormPullback i π (p : ℤ) V ω) =
      Scheme.Modules.Hom.app (gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ) ≫
        (modulePushforward g.toLRSHom.toShHom).map (conormalGysinHom i' π' p hE')) V
        (subschemeFormPullback i π (p : ℤ) V ω) := by
  have hcut := isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish
  have hgT := equationsClosedSet_restrictEquations i a.ambient hcut
  have hT : IsClosed (a.ambient.ι ⁻¹' Set.range i.base) :=
    (isClosed_range_base i).preimage a.ambient.ι.continuous
  have hT' : IsClosed ((g ⁻¹ᵁ a.ambient).ι ⁻¹' Set.range i'.base) :=
    (isClosed_range_base i').preimage (g ⁻¹ᵁ a.ambient).ι.continuous
  have hV' : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ a.ambient := fun _ hz => hV hz
  set ω' := relativeDifferentialFormsPullback g π π' t right_comm (p : ℤ) V ω
  let a' := EquationChart.ofIsPullback hcart a
  have hcut' := isCutOutByEquationsOn_of_isGeneratedByOn i' a'.gen a'.vanish
  have hgT' := equationsClosedSet_restrictEquations i' a'.ambient hcut'
  -- the left-hand side
  have l1 := conormalGysinHom_app i π p hE a V hV (subschemeFormPullback i π (p : ℤ) V ω)
  have l2 := chartLoc_subschemeFormPullbackOfClassMap i π p a.ambient a.equations hcut hT hgT
    (fun φ => Stacks.Perfect.FractionClass.fracTermTop_naturality _ φ) V hV ω
  have l3 := chartClsOfClassMap_gysinBaseChangePull i i' h g π π' t hcart right_comm p hE
    a.ambient (restrictEquations a.ambient a.equations) hgT hT hT' V hV
    (gysinWedgeOn π a.equations (p : ℤ) hV ω)
  -- the right-hand side
  have r1 := subschemeFormBaseChange_subschemeFormPullback i i' h g π π' t hcart.w right_comm
    (p : ℤ) V ω
  have r2 := conormalGysinHom_app i' π' p hE' a' (g ⁻¹ᵁ V) hV'
    (subschemeFormPullback i' π' (p : ℤ) (g ⁻¹ᵁ V)
      ω')
  have r3 := chartLoc_subschemeFormPullbackOfClassMap i' π' p a'.ambient a'.equations hcut' hT'
    hgT' (fun φ => Stacks.Perfect.FractionClass.fracTermTop_naturality _ φ) (g ⁻¹ᵁ V) hV'
    ω'
  have r4 := chartClsOfClassMap_congr_equations i' π' p (g ⁻¹ᵁ a.ambient)
    (restrictEquations_preimage g a.ambient a.equations) hT' hgT'.le
    (equationsClosedSet_restrict_pullback_range i i' h g hcart a.ambient _ hgT).le (g ⁻¹ᵁ V) hV'
    (gysinWedgeOn π' a'.equations (p : ℤ) hV'
      ω')
  have r5 := gysinWedgeOn_pullback_chart g π π' t right_comm a.equations (p : ℤ) hV ω
  refine (congrArg _ (l1.trans l2)).trans (l3.trans ?_)
  refine Eq.trans ?_ (congrArg (Scheme.Modules.Hom.app (conormalGysinHom i' π' p hE') (g ⁻¹ᵁ V))
    r1).symm
  refine Eq.trans ?_ (r2.trans r3).symm
  refine Eq.trans ?_ r4.symm
  exact congrArg _ r5.symm

/-- **The Gysin square of [Stacks, Tag 0G89] before the identification of the targets**: the
Gysin map of `i` followed by the transpose of the right vertical arrow is the left vertical arrow
followed by the direct image of the Gysin map of `i'`.

It is checked on sections over the opens inside an equation chart, which determine a map out of
`i_*Ω^p_{Z/S}` (`Stacks.Gysin.hom_ext_of_app_eq_equationChart`), and there locally on a cover
over which the form lifts to the ambient scheme
(`Stacks.Gysin.exists_subschemeFormPullback_restrict`), where it is
`conormalGysinHom_homEquiv_app_subschemeFormPullback`. -/
theorem conormalGysinHom_comp_homEquiv_gysinBaseChangePull (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (hE' : ConormalRank i' c) :
    conormalGysinHom i π p hE ≫
        (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (gysinBaseChangePull i i' h g π π' t hcart right_comm p hE) =
      gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ) ≫
        (modulePushforward g.toLRSHom.toShHom).map (conormalGysinHom i' π' p hE') := by
  refine hom_ext_of_app_eq_equationChart i π hE fun a V hV => ?_
  ext x
  choose Wz hWz hzW hω using fun z : V =>
    exists_subschemeFormPullback_restrict i π p V x z.1 z.2
  have hcov : V ≤ ⨆ z : V, Wz z := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨((Scheme.Modules.pushforward g).obj (gysinTarget i' π' c p)).presheaf,
      ((Scheme.Modules.pushforward g).obj (gysinTarget i' π' c p)).isSheaf⟩ :
        TopCat.Sheaf Ab.{u} X)) Wz V (fun z => homOfLE (hWz z)) hcov _ _ fun z => ?_
  obtain ⟨ω, hω'⟩ := hω z
  refine (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map _ (homOfLE (hWz z)) x).symm.trans ?_
  refine Eq.trans ?_ (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map _ (homOfLE (hWz z)) x)
  rw [← hω']
  exact conormalGysinHom_homEquiv_app_subschemeFormPullback i i' h g π π' t hcart right_comm p
    hE hE' a (Wz z) ((hWz z).trans hV) ω

/-- Reading the square through the identifications of the targets, at a variable category. -/
theorem transverse_square_formal {𝒞 : Type*} [Category 𝒞] {A B B' C C' D : 𝒞}
    (γ : A ⟶ B) (e : B ≅ B') (E : B ⟶ C) (GT : C ⟶ C') (S : A ⟶ D) (Gγ : D ⟶ C)
    (GγT : D ⟶ C') (hGγT : GγT = Gγ ≫ GT) (key : γ ≫ E = S ≫ Gγ) :
    (γ ≫ e.hom) ≫ (e.inv ≫ E ≫ GT) = S ≫ GγT := by
  rw [hGγT, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% key]

/-- **Stacks Project, Tag 0G89.**  Let `c ≥ 0` and let
```
Z' ⟶ X' ⟶ S'
↓h    ↓g    ↓t
Z  ⟶ X  ⟶ S
```
be a commutative diagram of schemes such that

1. `i : Z ⟶ X` and `i' : Z' ⟶ X'` satisfy the assumptions of [Stacks, Tag 0G86]: closed
   immersions of finite presentation whose conormal sheaves are locally free of rank `c`
   (`hE`, `hE'`);
2. the left square is cartesian (`hcart`);
3. the map `h^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of [Stacks, Tag 01R4] is an isomorphism (`_hconormal`).

Then the Gysin maps `γ^p` of [Stacks, Tag 0G86] commute with the pullback of differential forms
on the left and the base change arrow of [Stacks, Cohomology, Remark 0G78] on the right,
descended to degree `c` by the vanishing of [Stacks, Tag 0G7N].  The square is stated on `X`:
the left vertical arrow `gysinBaseChangeSourceHom` is the transpose of `h^*Ω^p_{Z/S} ⟶ Ω^p_{Z'/S'}`
pushed forward, and the right vertical arrow `gysinBaseChangeTargetHom` is the transpose along
`g^* ⊣ g_*` of the source's right vertical arrow, whose source is `g^*` of `i_*ℋ^c_Z(Ω^{p+c})`.

**On hypothesis (3).**  It is the source's hypothesis and is kept as the binder `_hconormal`,
but the proof does not consume it: given (2), the map of (3) is surjective (the ideal of `Z'` is
generated by the pullback of the ideal of `Z`), and given (1) both sides are locally free of the
same finite rank `c`, so a surjection between them is an isomorphism; in other words (3) is
implied by (1) and (2).  What the proof uses of the transversality is that the pulled-back
equations `g^♯f₁, …, g^♯f_c` of an equation chart of `Z` cut out `Z'` over the preimage chart,
`Stacks.Gysin.EquationChart.ofIsPullback`, which needs only (2).

Every arrow of the square is a construction of this library and every hypothesis is one of the
source's; nothing is taken as an input. `Stacks.Gysin.GysinBaseChange.gysinHom_baseChange` is the
same commutativity for abstract chart data, with those constructions as fields. -/
@[stacks 0G89]
theorem conormalGysinHom_comp_gysinBaseChangeTargetHom (hcart : IsPullback h i' i g)
    (right_comm : g ≫ π = π' ≫ t) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (hE' : ConormalRank i' c)
    (_hconormal : IsIso (Stacks.Immersion.immersionConormalSheafMap i' i h g
      (congrArg (fun k => k.toLRSHom.toShHom) hcart.w.symm))) :
    (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) ≫
        gysinBaseChangeTargetHom i i' h g π π' t hcart right_comm p hE =
      gysinBaseChangeSourceHom i i' h g π π' t hcart.w right_comm (p : ℤ) ≫
        (modulePushforward g.toLRSHom.toShHom).map
          (conormalGysinHom i' π' p hE' ≫
            (conormalGysinTargetIso i' π' c p).hom) :=
  transverse_square_formal _ _ _ _ _ _ _ (Functor.map_comp _ _ _)
    (conormalGysinHom_comp_homEquiv_gysinBaseChangePull i i' h g π π' t hcart right_comm p hE hE')

end Stacks.Gysin
