module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.SectionOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.RatioComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleLocalTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.RingTheory.UniqueFactorizationDomain.HeightOneOrders

/-!
# The order of vanishing of a meromorphic section on a represented space

Let `R` be an integral, locally Noetherian scheme of the big fppf site of `S`, `h_R` the algebraic
space it represents, `ℒ` an invertible `𝒪_{h_R}`-module and `t` a regular meromorphic section of
`ℒ`.  The order of vanishing `ord_{Z, ℒ}(t)` along a prime divisor `Z ⊆ h_R` (Stacks 0EPR) is read
at the canonical ratio `t / s_ξ` against a generator of `ℒ` at the generic point `ξ` of `Z`, in the
henselian local ring `𝒪^h_{h_R, ξ}`.  On the scheme `R` the module `ℒ` restricts to a module `ℒ_R`
trivialized near every point (`AlgebraicGeometry.Space.representedChartRestrictionSheaf`), and
Divisors, Definition 02SF reads the order of vanishing of an element of the generic stalk of `ℒ_R`
against a local generator in the local ring `𝒪_{R, ξ}`.  This file proves that the two theories
agree: there is a nonzero element `θ` of the generic stalk of `ℒ_R`, the *generic value* of
`t`, with

`ord_{Z, ℒ}(t) = ord_{Z, ℒ_R}(θ)`  for every prime divisor `Z` of `h_R`.

The generic value is computed on a nonempty affine open `U ⊆ R` over which `ℒ` is free on a
generator `e` (`AlgebraicGeometry.Space.exists_freeFamily_representedIdChartOpen`): it is the ratio
`t / e` of `t` against `e` over the chart `U` cuts out, read in the function field of `R`
(`AlgebraicGeometry.Space.representedChartFunctionFieldMap`), times the germ of `e` at the generic
point.  It does not depend on the generator, since two generators differ by a unit
(`AlgebraicGeometry.Space.representedChartFunctionFieldMap_chartRatio_smul_germ_eq`), nor on the
chart, since the reading is compatible with restriction
(`AlgebraicGeometry.Space.representedChartFunctionFieldMap_chartRatio_smul_germ_restrict`) and
two nonempty opens of the irreducible scheme `R` meet.  At a prime divisor `Z` both orders are
then computed on a free chart through the generic point of `Z`: the space side by Stacks 0EPR on
an arbitrary free affine chart, the scheme side as the order of the coordinate of `θ` against the
germ of the generator, and the two by
`AlgebraicGeometry.Space.ord_representedChartFunctionFieldMap`.

## Main definitions

* `AlgebraicGeometry.Space.representedIdChartOpen`: the chart of `h_R` cut out by a Zariski open of
  `R`.
* `AlgebraicGeometry.Space.representedChartRestrictionSheaf`: the restriction of a module on `h_R`
  to `R`.
* `AlgebraicGeometry.Space.representedChartFunctionFieldMap`: the reading of the meromorphic
  functions on a nonempty Zariski chart in the function field of `R`.

## Main results

* `AlgebraicGeometry.Space.isStalkBasis_germ_representedChartModule`: a free generator of `ℒ` over
  a Zariski chart is a stalk basis of `ℒ_R`.
* `AlgebraicGeometry.Space.exists_freeFamily_representedIdChartOpen`: `ℒ` is free on an affine
  Zariski chart around every point.
* `AlgebraicGeometry.Space.ord_representedChartFunctionFieldMap`: the reading in the function field
  computes the order of vanishing.
* `AlgebraicGeometry.Space.exists_genericStalk_orderOfVanishing_eq`: the orders of vanishing of
  `t` are those of an element of the generic stalk of `ℒ_R`.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (R : BigFppfOver B S hS)

/-! ### The Zariski charts of a represented space -/

section Charts

/-- The étale chart of `h_R` cut out by a Zariski open `U` of the scheme `R`: the open `U`,
regarded as a chart of `h_R` through the identity chart. -/
abbrev representedIdChartOpen (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) :
    SmallEtale B S hS (representedAlgebraicSpace B S hS R).1 :=
  (chartOpens B S hS (idEtaleChart B S hS R)).obj U

/-- A point of the chart cut out by a Zariski open `U` of `R` is the point of `h_R` corresponding
to its image in `R`. -/
theorem chartSchemeToPoints_representedIdChartOpen (U : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (v : U.toScheme) :
    chartSchemeToPoints B S hS (representedAlgebraicSpace B S hS R).1
        (representedIdChartOpen B S hS R U) v =
      (pointsEquivScheme B S hS R).symm (U.ι v) := by
  rw [← chartSchemeToPoints_map B S hS (representedAlgebraicSpace B S hS R).1
    (chartOpensHom B S hS (representedAlgebraicSpace B S hS R)
      (idEtaleChart B S hS R) U) v,
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  exact pointsMap_id_apply B S hS _

end Charts

/-! ### Free generators over Zariski charts and stalk bases -/

section Generators

variable (L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
  (representedAlgebraicSpace B S hS R).2)

/-- The restriction of a module on `h_R` to the scheme `R` through the identity chart: its sections
over a Zariski open `U` are the sections of the module over the chart `U` cuts out. -/
abbrev representedChartRestrictionSheaf : ((BigFppfOver.toScheme B S hS).obj R).Modules :=
  chartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS R) L
    (idEtaleChart B S hS R)

/-- **A free generator of `L` over a Zariski chart is a basis of the stalks of the restriction**:
if `e` is a compatible family of free generators of `L` over the charts over the chart cut out by a
Zariski open `U` of `R`, then the germ of `e(U)` at every point of `U` is a basis of the stalk of
`AlgebraicGeometry.Space.representedChartRestrictionSheaf` there. -/
theorem isStalkBasis_germ_representedChartModule
    (U : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (e : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
      (W ⟶ representedIdChartOpen B S hS R U) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e W k)
    (x : (BigFppfOver.toScheme B S hS).obj R) (hx : x ∈ U) :
    Stacks.Divisors.IsStalkBasis (representedChartRestrictionSheaf B S hS R L) x
      ((representedChartRestrictionSheaf B S hS R L).presheaf.germ U x hx
        (ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _)))) := by
  refine Stacks.Divisors.isStalkBasis_germ_of_bijective_smul _ (fun V hV => ?_) x hx
  set k := (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE hV)
  have hres : (representedChartRestrictionSheaf B S hS R L).presheaf.map (homOfLE hV).op
      (ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _))) =
      (show Γ(representedChartRestrictionSheaf B S hS R L, V) from
        ULift.up (e (representedIdChartOpen B S hS R V) k)) := by
    refine congrArg ULift.up ((hcompat _ _ (𝟙 _) k).trans ?_)
    rw [Category.comp_id]
  rw [hres]
  have hfun : (fun c : Γ((BigFppfOver.toScheme B S hS).obj R, V) =>
      c • (show Γ(representedChartRestrictionSheaf B S hS R L, V) from
        ULift.up (e (representedIdChartOpen B S hS R V) k))) =
      (fun m => (show Γ(representedChartRestrictionSheaf B S hS R L, V) from ULift.up m)) ∘
        (fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2 (representedIdChartOpen B S hS R V) ↦
            r • e (representedIdChartOpen B S hS R V) k) ∘
        (fun c => V.topIso.inv c) := rfl
  rw [hfun]
  exact (Equiv.ulift.symm.bijective).comp ((hfree _ k).comp
    (ConcreteCategory.bijective_of_isIso V.topIso.inv))

/-- **An invertible module on `h_R` is free on an affine Zariski chart around every point.** For
every point `x` of `R` there is an affine open `U ∋ x` of `R` and a compatible family of free
generators of `L` over the charts over the chart that `U` cuts out. -/
theorem exists_freeFamily_representedIdChartOpen
    (hL : IsInvertibleModule (representedAlgebraicSpace B S hS R) L)
    (x : (BigFppfOver.toScheme B S hS).obj R) :
    ∃ (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (e : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
        (W ⟶ representedIdChartOpen B S hS R U) → L.val.obj (op W))
      (_ : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
        (k : W ⟶ representedIdChartOpen B S hS R U) (g : W' ⟶ W),
        (L.val.map g.op).hom (e W k) = e W' (g ≫ k)),
      ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
        (k : W ⟶ representedIdChartOpen B S hS R U),
        Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2 W ↦ r • e W k := by
  obtain ⟨W, hWa, hxW, -⟩ := Scheme.exists_isAffineOpen_mem_le _
    (show x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj R).Opens) from trivial)
  have : IsAffine W.toScheme := hWa
  have : IsAffine (chartScheme (representedIdChartOpen B S hS R W)) := hWa
  obtain ⟨g, hxg, e, hc, hf⟩ := exists_basicOpen_freeGenerator B S hS
    (representedAlgebraicSpace B S hS R) L hL (representedIdChartOpen B S hS R W) this
    (show W.toScheme from ⟨x, hxW⟩)
  set U := W.ι ''ᵁ (chartScheme (representedIdChartOpen B S hS R W)).basicOpen g with hU
  have hUW : U ≤ W := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hUa : IsAffineOpen U :=
    ((isAffineOpen_top W.toScheme).basicOpen g).image_of_isOpenImmersion W.ι
  have hxU : x ∈ U := ⟨⟨x, hxW⟩, hxg, rfl⟩
  set i := (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE hUW)
  have hle : (⊤ : (chartScheme (representedIdChartOpen B S hS R U)).Opens) ≤
      chartSchemeMap i ⁻¹ᵁ (chartScheme (representedIdChartOpen B S hS R W)).basicOpen g := by
    rintro ⟨y, hy⟩ -
    obtain ⟨z, hz, hzy⟩ := hy
    have hzz : z = ⟨y, hUW ⟨z, hz, hzy⟩⟩ := Subtype.ext hzy
    have h1 : ((BigFppfOver.toScheme B S hS).obj R).homOfLE hUW ⟨y, ⟨z, hz, hzy⟩⟩ = z :=
      (Scheme.homOfLE_apply' hUW y _).trans hzz.symm
    exact (congrArg (fun w => w ∈ (chartScheme (representedIdChartOpen B S hS R W)).basicOpen g)
      h1).mpr hz
  let j : representedIdChartOpen B S hS R U ⟶
      openChart B S hS (representedAlgebraicSpace B S hS R).1 (representedIdChartOpen B S hS R W)
        ((chartScheme (representedIdChartOpen B S hS R W)).basicOpen g) :=
    (openChartTopIso B S hS _ (representedIdChartOpen B S hS R U)).inv ≫
      openChartHomOfLE B S hS _ (representedIdChartOpen B S hS R U) hle ≫
        openChartRestrict B S hS _ i ((chartScheme (representedIdChartOpen B S hS R W)).basicOpen g)
  refine ⟨U, hUa, hxU, fun W' k => e W' (k ≫ j), fun W₁ W₂ k h' => ?_,
    fun W₁ k => hf W₁ (k ≫ j)⟩
  exact (hc W₁ W₂ (k ≫ j) h').trans (congrArg (e W₂) (Category.assoc h' k j).symm)

end Generators

/-! ### Meromorphic functions on a Zariski chart, read in the function field -/

section FunctionField

open scoped nonZeroDivisors

/-- The algebra structure of `AlgebraicGeometry.Space.chartMeromorphicFunctionAlgebra` at the
algebraic space represented by `R`, stated at the spelling `yoneda.obj R` under which instance
search meets it. -/
abbrev representedChartMeromorphicAlgebra (U : SmallEtale B S hS (yoneda.obj R)) :
    Algebra ((structurePresheaf B S hS (yoneda.obj R)).obj (op U))
      ((meromorphicFunctionSheaf B S hS (yoneda.obj R) (isAlgebraicSpace_yoneda B S hS R)).obj.obj
        (op U)) :=
  chartMeromorphicFunctionAlgebra B S hS (representedAlgebraicSpace B S hS R) U

attribute [local instance] representedChartMeromorphicAlgebra

/-- The local rings of the scheme of a Zariski chart are nontrivial, at the spelling under which
instance search meets them. -/
abbrev nontrivial_stalk_representedIdChartOpen (U : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (v : U) : Nontrivial ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v) :=
  @IsLocalRing.toNontrivial _ _
    (inferInstance : IsLocalRing (U.toScheme.presheaf.stalk (show U.toScheme from v)))

attribute [local instance] nontrivial_stalk_representedIdChartOpen

variable [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]

/-- **The reading of a meromorphic function on a nonempty Zariski chart in the function field of
`R`.**  When the meromorphic functions `𝒦(U)` on the chart cut out by a nonempty Zariski open `U`
are the total ring of fractions of `Γ(U, 𝒪)`, a meromorphic function is read in `R(R)` along the
germ at the generic point. -/
def representedChartFunctionFieldMap (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) [Nonempty U]
    (hK : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj
        (op (representedIdChartOpen B S hS R U)))) :
    (meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj
        (op (representedIdChartOpen B S hS R U)) →+*
      ((BigFppfOver.toScheme B S hS).obj R).functionField :=
  haveI := hK
  IsLocalization.lift (M := ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
      (op (representedIdChartOpen B S hS R U)))⁰)
    (g := (((BigFppfOver.toScheme B S hS).obj R).germToFunctionField U).hom.comp
      U.topIso.hom.hom) fun y => by
    refine IsUnit.mk0 _ fun h => ?_
    have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨Nonempty.some ‹Nonempty U›, trivial⟩⟩
    have : Nontrivial ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) :=
      inferInstanceAs (Nontrivial Γ(U.toScheme, ⊤))
    have h0 : U.topIso.hom.hom (show Γ(U.toScheme, ⊤) from y.1) = 0 :=
      Scheme.germToFunctionField_injective _ U (h.trans (map_zero _).symm)
    have hy0 : y.1 = 0 :=
      (ConcreteCategory.bijective_of_isIso U.topIso.hom).1 (h0.trans (map_zero _).symm)
    exact nonZeroDivisors.coe_ne_zero y hy0

/-- On a regular function the reading in the function field is its germ at the generic point. -/
theorem representedChartFunctionFieldMap_algebraMap
    (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) [Nonempty U]
    (hK : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    (a : (structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
      (op (representedIdChartOpen B S hS R U))) :
    representedChartFunctionFieldMap B S hS R U hK (algebraMap _ _ a) =
      ((BigFppfOver.toScheme B S hS).obj R).germToFunctionField U
        (U.topIso.hom (show Γ(U.toScheme, ⊤) from a)) :=
  have := hK
  IsLocalization.lift_eq _ _

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The germ at the generic point of a function on a nonempty open `U` of an integral scheme does
not change when the function is restricted to a nonempty open `V ⊆ U`, both read through the
identifications `Γ(U, 𝒪_U) = Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.germToFunctionField_topIso_homOfLE_appTop {X : Scheme.{u}}
    [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (s : Γ(U.toScheme, ⊤)) :
    X.germToFunctionField V (V.topIso.hom ((X.homOfLE h).appTop s)) =
      X.germToFunctionField U (U.topIso.hom s) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom, Scheme.germToFunctionField]
  refine (TopCat.Presheaf.germ_res_apply' _ _ _ _ _).trans ?_
  refine (TopCat.Presheaf.germ_res_apply' _ _ _ _ _).trans ?_
  exact (TopCat.Presheaf.germ_res_apply' _ _ _ _ _).symm

/-- **The reading in the function field is compatible with restriction to a smaller chart.** -/
theorem representedChartFunctionFieldMap_map
    {U V : ((BigFppfOver.toScheme B S hS).obj R).Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (hKU : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    (hKV : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R V)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R V))))
    (x : (meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))) :
    representedChartFunctionFieldMap B S hS R V hKV
        (((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2).obj.map
          ((chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h)).op).hom x) =
      representedChartFunctionFieldMap B S hS R U hKU x := by
  have := hKU
  set g := (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h)
  have key : (representedChartFunctionFieldMap B S hS R V hKV).comp
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2).obj.map g.op).hom =
      representedChartFunctionFieldMap B S hS R U hKU := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS
      (representedAlgebraicSpace B S hS R).1).obj (op (representedIdChartOpen B S hS R U)))⁰ ?_
    ext a
    have hnat := congrArg (fun φ => φ.hom a)
      ((toMeromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).hom.naturality g.op)
    simp only [RingHom.comp_apply]
    change representedChartFunctionFieldMap B S hS R V hKV
        (((toMeromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2).hom.app (op (representedIdChartOpen B S hS R U)) ≫
          (meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
            (representedAlgebraicSpace B S hS R).2).obj.map g.op).hom a) = _
    rw [← hnat]
    exact (representedChartFunctionFieldMap_algebraMap B S hS R V hKV _).trans
      ((Scheme.germToFunctionField_topIso_homOfLE_appTop h a).trans
        (representedChartFunctionFieldMap_algebraMap B S hS R U hKU a).symm)
  exact congrArg (fun φ => φ x) key

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The order of vanishing at a point of codimension one of the image in the function field of a
nonzero element of the local ring is the length of its quotient. -/
theorem _root_.AlgebraicGeometry.Scheme.ord_algebraMap_stalk {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} (hz : Order.coheight z = 1) (r : X.presheaf.stalk z)
    (hr : r ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField r) z =
      ((Ring.ord (X.presheaf.stalk z) r).toNat : ℤ) := by
  have h := Scheme.ord_mk' hz ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ 1
  rw [IsLocalization.mk'_one, OneMemClass.coe_one, Ring.ord_one] at h
  simpa using h

/-- **The reading in the function field computes the order of vanishing.**  For a unit `x` of
the meromorphic functions on an affine nonempty Zariski chart `U` and a point `v` of `U` of
codimension one in `R`, the order of vanishing of the reading of `x` at `v`, Divisors 02RJ, is the
order of vanishing at `v` of `x` read in the total ring of fractions of the local ring. -/
theorem ord_representedChartFunctionFieldMap
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)]
    (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) [Nonempty U]
    (hU : IsAffine (chartScheme (representedIdChartOpen B S hS R U)))
    (hK : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    (v : U)
    [IsNoetherianRing ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v)]
    (hv : Order.coheight (U.ι v) = 1)
    (x : (meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U)))
    (hx : IsUnit x) :
    ((BigFppfOver.toScheme B S hS).obj R).ord
        (representedChartFunctionFieldMap B S hS R U hK x) (U.ι v) =
      Ring.ordTotalFracInt ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v)
        (chartPointMeromorphicMap B S hS (representedAlgebraicSpace B S hS R)
          (representedIdChartOpen B S hS R U) hU hK v x) (hx.map _) := by
  have := hK
  have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨Nonempty.some ‹Nonempty U›, trivial⟩⟩
  have : IsDomain ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
      (op (representedIdChartOpen B S hS R U))) := inferInstanceAs (IsDomain Γ(U.toScheme, ⊤))
  have := IsFractionRing.isDomain ((structurePresheaf B S hS
    (representedAlgebraicSpace B S hS R).1).obj (op (representedIdChartOpen B S hS R U)))
    (K := (meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U)))
  have : IsDomain ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v) :=
    (inferInstance : IsDomain (U.toScheme.presheaf.stalk (show U.toScheme from v)))
  have hξU : U.ι v ∈ U := v.2
  -- the case of a regular function
  have key : ∀ c : (structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
      (op (representedIdChartOpen B S hS R U)), c ≠ 0 →
      ∀ (hc : IsUnit (chartPointMeromorphicMap B S hS
      (representedAlgebraicSpace B S hS R) (representedIdChartOpen B S hS R U) hU hK v
        (algebraMap ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) _ c))),
      ((BigFppfOver.toScheme B S hS).obj R).ord (representedChartFunctionFieldMap B S hS R U hK
        (algebraMap ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) _ c)) (U.ι v) =
        Ring.ordTotalFracInt ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v)
          (chartPointMeromorphicMap B S hS (representedAlgebraicSpace B S hS R)
            (representedIdChartOpen B S hS R U) hU hK v
            (algebraMap ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) _ c)) hc := by
    intro c hc0 hc
    have hgv : ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.germ ⊤ v trivial).hom
        c ≠ 0 :=
      fun h => hc0 ((germ_injective_of_isIntegral (U := ⊤) U.toScheme v trivial)
        (h.trans (map_zero _).symm))
    have hiso : (U.stalkIso v).hom.hom ((U.toScheme.presheaf.germ ⊤ v trivial).hom
        (show Γ(U.toScheme, ⊤) from c)) =
        (((BigFppfOver.toScheme B S hS).obj R).presheaf.germ U (U.ι v) hξU).hom
          (U.topIso.hom (show Γ(U.toScheme, ⊤) from c)) := by
      rw [← ConcreteCategory.comp_apply]
      refine (ConcreteCategory.congr_hom
        (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) v trivial) _).trans ?_
      exact (TopCat.Presheaf.germ_res_apply' _ _ _ _ _).symm
    have hgξ : (((BigFppfOver.toScheme B S hS).obj R).presheaf.germ U (U.ι v) hξU).hom
        (U.topIso.hom (show Γ(U.toScheme, ⊤) from c)) ≠ 0 := by
      rw [← hiso]
      exact fun h => hgv ((ConcreteCategory.bijective_of_isIso (U.stalkIso v).hom).1
        (h.trans (map_zero _).symm))
    rw [representedChartFunctionFieldMap_algebraMap,
      ← Scheme.algebraMap_germ_eq_germToFunctionField _ hξU,
      Scheme.ord_algebraMap_stalk hv _ hgξ]
    refine Eq.trans ?_ (Ring.ordTotalFracInt_congr _
      (IsLocalization.map_units _ ⟨_, mem_nonZeroDivisors_of_ne_zero hgv⟩) hc
      (chartPointMeromorphicMap_algebraMap B S hS
      (representedAlgebraicSpace B S hS R) (representedIdChartOpen B S hS R U) hU hK v c).symm)
    rw [Ring.ordTotalFracInt_algebraMap _ _ (mem_nonZeroDivisors_of_ne_zero hgv), ← hiso]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ))
      (Stacks.RingTheory.HeightOneOrders.ord_ringEquiv
        ((U.stalkIso v).commRingCatIsoToRingEquiv) _)
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective
    (((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))⁰) x
  dsimp only at hx ⊢
  have ha : a ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hx
    exact not_isUnit_zero hx
  have hb : (b : (structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hspec := IsLocalization.mk'_spec ((meromorphicFunctionSheaf B S hS
    (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2).obj.obj
      (op (representedIdChartOpen B S hS R U))) a b
  have hbu : IsUnit (algebraMap
        ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) ((meromorphicFunctionSheaf B S hS
      (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2).obj.obj
        (op (representedIdChartOpen B S hS R U)))
        (b : (structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))) := IsLocalization.map_units _ b
  have hau : IsUnit (algebraMap
        ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) ((meromorphicFunctionSheaf B S hS
      (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2).obj.obj
        (op (representedIdChartOpen B S hS R U))) a) := hspec ▸ hx.mul hbu
  have hρ := congrArg (representedChartFunctionFieldMap B S hS R U hK) hspec
  rw [map_mul] at hρ
  have hcp := congrArg (chartPointMeromorphicMap B S hS (representedAlgebraicSpace B S hS R)
    (representedIdChartOpen B S hS R U) hU hK v) hspec
  rw [map_mul] at hcp
  have h1 := congrArg (fun y => ((BigFppfOver.toScheme B S hS).obj R).ord y (U.ι v)) hρ
  simp only at h1
  rw [Scheme.ord_mul ((hx.map _).ne_zero) ((hbu.map _).ne_zero)] at h1
  have h2 := Ring.ordTotalFracInt_congr
    ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v)
    ((hx.map _).mul (hbu.map _)) (hau.map _) hcp
  rw [Ring.ordTotalFracInt_mul _ _ _ (hx.map _) (hbu.map _)] at h2
  rw [key a ha (hau.map _),
    key (b : (structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U))) hb (hbu.map _)] at h1
  omega

end FunctionField

/-! ### The generic value of a meromorphic section -/

section GenericValue

attribute [local instance] representedChartMeromorphicAlgebra

variable [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
    (L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2)
    (t : MeromorphicSection.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2 L)

/-- **The generic value of a meromorphic section does not depend on the free generator.**  Over
one nonempty Zariski chart `U` and for two free generators `e`, `e'` of `L` there, the ratios of
`t` against `e` and against `e'`, read in the function field, multiplied with the generic germs of
the generators, agree. -/
theorem representedChartFunctionFieldMap_chartRatio_smul_germ_eq
    (U : ((BigFppfOver.toScheme B S hS).obj R).Opens) [Nonempty U]
    (hK : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    (e e' : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
      (W ⟶ representedIdChartOpen B S hS R U) → L.val.obj (op W))
    (hc : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hf : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e W k)
    (hc' : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U) (g : W' ⟶ W),
      (L.val.map g.op).hom (e' W k) = e' W' (g ≫ k))
    (hf' : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e' W k)
    (hη : _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) ∈ U) :
    representedChartFunctionFieldMap B S hS R U hK
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ hη
        (ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _))) =
    representedChartFunctionFieldMap B S hS R U hK
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e' hc' hf' t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ hη
        (ULift.up (e' (representedIdChartOpen B S hS R U) (𝟙 _))) := by
  obtain ⟨v, hv⟩ := exists_isUnit_smul_of_bijective_smul B S hS _ _ L
    (representedIdChartOpen B S hS R U) (e _ (𝟙 _)) (e' _ (𝟙 _)) (hf _ (𝟙 _)) (hf' _ (𝟙 _))
  -- the two ratios differ by the unit `v`
  have hr : chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t =
      algebraMap (chartRing B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2 (representedIdChartOpen B S hS R U))
        ((meromorphicChartSheaf B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U)))
        (v : chartRing B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2 (representedIdChartOpen B S hS R U)) *
        (show (meromorphicChartSheaf B S hS (representedAlgebraicSpace B S hS R).1
          (representedAlgebraicSpace B S hS R).2).obj.obj
            (op (representedIdChartOpen B S hS R U)) from
          chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e' hc' hf' t) := by
    refine chartRatio_eq_of_eval_eq B S hS _ _ L _ e hc hf t _ ?_
    refine (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS _ _ L _ e' hc' hf' t).trans ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS _ _ L _) ?_
    rw [hv]
    exact meromorphicSectionModule_tmul_smul B S hS _ _ L (representedIdChartOpen B S hS R U)
      (v : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 (representedIdChartOpen B S hS R U)) _ _
  -- the two generic germs differ by the germ of `v`
  have hg : (representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ hη
      (ULift.up (e' (representedIdChartOpen B S hS R U) (𝟙 _))) =
      ((BigFppfOver.toScheme B S hS).obj R).germToFunctionField U
          (U.topIso.hom (show Γ(U.toScheme, ⊤) from (v : chartRing B S hS
            (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2
            (representedIdChartOpen B S hS R U)))) •
        (representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ hη
          (ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _))) := by
    have hup : (show Γ(representedChartRestrictionSheaf B S hS R L, U) from
        ULift.up (e' (representedIdChartOpen B S hS R U) (𝟙 _))) =
        U.topIso.hom (show Γ(U.toScheme, ⊤) from (v : chartRing B S hS
          (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2
          (representedIdChartOpen B S hS R U))) •
          (show Γ(representedChartRestrictionSheaf B S hS R L, U) from
            ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _))) := by
      rw [hv]
      refine congrArg ULift.up (congrArg (fun r => r • e (representedIdChartOpen B S hS R U) (𝟙 _))
        ?_)
      exact (ConcreteCategory.congr_hom U.topIso.hom_inv_id _).symm
    refine (congrArg
      (fun z => ((representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ hη).hom z)
      hup).trans ?_
    exact Scheme.Modules.germ_smul (representedChartRestrictionSheaf B S hS R L) hη _ _
  have hρ : representedChartFunctionFieldMap B S hS R U hK
      (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t) =
      ((BigFppfOver.toScheme B S hS).obj R).germToFunctionField U
          (U.topIso.hom (show Γ(U.toScheme, ⊤) from (v : chartRing B S hS
            (representedAlgebraicSpace B S hS R).1 (representedAlgebraicSpace B S hS R).2
            (representedIdChartOpen B S hS R U)))) *
        representedChartFunctionFieldMap B S hS R U hK
          (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e' hc' hf' t) := by
    rw [hr]
    exact (map_mul _ _ _).trans
      (congrArg (· * _) (representedChartFunctionFieldMap_algebraMap B S hS R U hK _))
  rw [hρ, hg, mul_comm, mul_smul]

omit [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)] in
/-- The germ of a section of `AlgebraicGeometry.Space.representedChartRestrictionSheaf` restricted
along an inclusion of Zariski charts is its germ. -/
theorem germ_representedChartModule_restrict
    {U V : ((BigFppfOver.toScheme B S hS).obj R).Opens} (h : V ≤ U)
    (m : L.val.obj (op (representedIdChartOpen B S hS R U)))
    (x : (BigFppfOver.toScheme B S hS).obj R) (hx : x ∈ V) :
    (representedChartRestrictionSheaf B S hS R L).presheaf.germ V x hx
        (ULift.up ((L.val.map ((chartOpens B S hS (idEtaleChart B S hS R)).map
          (homOfLE h)).op).hom m)) =
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U x (h hx) (ULift.up m) :=
  TopCat.Presheaf.germ_res_apply (representedChartRestrictionSheaf B S hS R L).presheaf
    (homOfLE h) x hx (ULift.up m)

/-- **The generic value of a meromorphic section does not change on a smaller chart.**  For
nonempty Zariski charts `V ⊆ U` and a free generator `e` of `L` over the chart of `U`, the ratio of
`t` against `e`, read in the function field and multiplied with the generic germ of `e`, is the
same on `V`, against the restriction of `e`. -/
theorem representedChartFunctionFieldMap_chartRatio_smul_germ_restrict
    {U V : ((BigFppfOver.toScheme B S hS).obj R).Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (hKU : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    (hKV : IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R V)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R V))))
    (e : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
      (W ⟶ representedIdChartOpen B S hS R U) → L.val.obj (op W))
    (hc : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hf : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e W k)
    (hηV : _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) ∈ V) :
    representedChartFunctionFieldMap B S hS R U hKU
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U _ (h hηV)
        (ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _))) =
    representedChartFunctionFieldMap B S hS R V hKV
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R V)
          (fun W k ↦ e W (k ≫ (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h)))
          (fun W W' k g ↦ (hc W W' (k ≫ (chartOpens B S hS (idEtaleChart B S hS R)).map
            (homOfLE h)) g).trans (congrArg (e W') (Category.assoc g k _).symm))
          (fun W k ↦ hf W (k ≫ (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h))) t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ V _ hηV
        (ULift.up (e (representedIdChartOpen B S hS R V)
          (𝟙 _ ≫ (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h)))) := by
  set i := (chartOpens B S hS (idEtaleChart B S hS R)).map (homOfLE h)
  have hratio := chartRatio_restrict B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t
    (representedIdChartOpen B S hS R V) i
  have hρ := representedChartFunctionFieldMap_map B S hS R h hKU hKV
    (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t)
  have hgerm : (representedChartRestrictionSheaf B S hS R L).presheaf.germ V
      (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R)) hηV
      (ULift.up (e (representedIdChartOpen B S hS R V)
        (𝟙 (representedIdChartOpen B S hS R V) ≫ i))) =
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U
        (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R)) (h hηV)
        (ULift.up (e (representedIdChartOpen B S hS R U)
          (𝟙 (representedIdChartOpen B S hS R U)))) := by
    have e1 : e (representedIdChartOpen B S hS R V) (𝟙 (representedIdChartOpen B S hS R V) ≫ i) =
        (L.val.map i.op).hom (e (representedIdChartOpen B S hS R U)
          (𝟙 (representedIdChartOpen B S hS R U))) :=
      (congrArg (e (representedIdChartOpen B S hS R V))
        ((Category.id_comp i).trans (Category.comp_id i).symm)).trans
        (hc _ _ (𝟙 (representedIdChartOpen B S hS R U)) i).symm
    rw [e1]
    exact germ_representedChartModule_restrict B S hS R L h _ _ hηV
  rw [hgerm, hratio]
  exact congrArg (· • _) hρ.symm

/-- **The generic value of a meromorphic section is independent of the chart.**  For two nonempty
Zariski charts `U₁`, `U₂` with free generators `e₁`, `e₂` of `L`, the ratios of `t` against the
generators, read in the function field and multiplied with their generic germs, agree. -/
theorem representedChartFunctionFieldMap_chartRatio_smul_germ_eq_of_charts
    (hK : ∀ U : ((BigFppfOver.toScheme B S hS).obj R).Opens, IsAffineOpen U →
      IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))))
    {U₁ U₂ : ((BigFppfOver.toScheme B S hS).obj R).Opens} (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) [Nonempty U₁] [Nonempty U₂]
    (e₁ : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
      (W ⟶ representedIdChartOpen B S hS R U₁) → L.val.obj (op W))
    (hc₁ : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U₁) (g : W' ⟶ W),
      (L.val.map g.op).hom (e₁ W k) = e₁ W' (g ≫ k))
    (hf₁ : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U₁),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e₁ W k)
    (e₂ : (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1) →
      (W ⟶ representedIdChartOpen B S hS R U₂) → L.val.obj (op W))
    (hc₂ : ∀ (W W' : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U₂) (g : W' ⟶ W),
      (L.val.map g.op).hom (e₂ W k) = e₂ W' (g ≫ k))
    (hf₂ : ∀ (W : SmallEtale B S hS (representedAlgebraicSpace B S hS R).1)
      (k : W ⟶ representedIdChartOpen B S hS R U₂),
      Function.Bijective fun r : chartRing B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2 W ↦ r • e₂ W k)
    (hη₁ : _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) ∈ U₁)
    (hη₂ : _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) ∈ U₂) :
    representedChartFunctionFieldMap B S hS R U₁ (hK U₁ hU₁)
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U₁) e₁ hc₁ hf₁ t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U₁ _ hη₁
        (ULift.up (e₁ (representedIdChartOpen B S hS R U₁) (𝟙 _))) =
    representedChartFunctionFieldMap B S hS R U₂ (hK U₂ hU₂)
        (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U₂) e₂ hc₂ hf₂ t) •
      (representedChartRestrictionSheaf B S hS R L).presheaf.germ U₂ _ hη₂
        (ULift.up (e₂ (representedIdChartOpen B S hS R U₂) (𝟙 _))) := by
  obtain ⟨U₃, hU₃, hη₃, hU₃le⟩ := Scheme.exists_isAffineOpen_mem_le _
    (show _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R) ∈ U₁ ⊓ U₂ from ⟨hη₁, hη₂⟩)
  have : Nonempty U₃ := ⟨⟨_, hη₃⟩⟩
  have h₁ : U₃ ≤ U₁ := hU₃le.trans inf_le_left
  have h₂ : U₃ ≤ U₂ := hU₃le.trans inf_le_right
  refine (representedChartFunctionFieldMap_chartRatio_smul_germ_restrict B S hS R L t h₁
    (hK U₁ hU₁) (hK U₃ hU₃) e₁ hc₁ hf₁ hη₃).trans ?_
  refine Eq.trans ?_ (representedChartFunctionFieldMap_chartRatio_smul_germ_restrict B S hS R L t
    h₂ (hK U₂ hU₂) (hK U₃ hU₃) e₂ hc₂ hf₂ hη₃).symm
  exact representedChartFunctionFieldMap_chartRatio_smul_germ_eq B S hS R L t U₃ (hK U₃ hU₃) _ _ _ _
    _ _ hη₃

end GenericValue

/-! ### The orders of vanishing of a meromorphic section on a represented space -/

section Order

attribute [local instance] representedChartMeromorphicAlgebra

variable [IsIntegral ((BigFppfOver.toScheme B S hS).obj R)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R)]
    (hN : HasEtaleLocalProperty B S hS (representedAlgebraicSpace B S hS R).1
      (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (L : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2)
    (hL : IsInvertibleModule (representedAlgebraicSpace B S hS R) L)

/-- **The orders of vanishing of a meromorphic section on a represented integral space are those of
an element of the generic stalk of the reading of the module on the scheme.**  Let `R` be an
integral locally Noetherian scheme of the site, `L` an invertible module on the algebraic space
`h_R` and `t` a regular meromorphic section of `L`.  There is a nonzero element `θ` of the stalk at
the generic point of `R` of the restriction `L_R` of `L` to `R`, a module trivialized near every
point, whose order of vanishing along the prime divisor of `R` at the generic point of every
prime divisor `Z` of `h_R`, in the sense of Divisors 02SF, is the order of vanishing
`ord_{Z, L}(t)` of Stacks 0EPR at the canonical ratio.

The element is the generic value of `t`: over a nonempty affine open `U` of `R` on which `L` is
free on `e`, it is the ratio `t / e`, read in the function field, times the generic germ of `e`
(`AlgebraicGeometry.Space.representedChartFunctionFieldMap`), which does not depend on `U` or `e`
(`AlgebraicGeometry.Space.representedChartFunctionFieldMap_chartRatio_smul_germ_eq_of_charts`). At
a prime divisor `Z` with generic point `ξ` both orders are read on such a chart through `ξ`: on
the space side by Stacks 0EPR on an arbitrary free affine chart
(`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`),
on the scheme side as the order of the coordinate against the germ of `e`, which is a stalk basis
(`AlgebraicGeometry.Space.isStalkBasis_germ_representedChartModule`), and the two are compared by
`AlgebraicGeometry.Space.ord_representedChartFunctionFieldMap`. -/
theorem exists_genericStalk_orderOfVanishing_eq
    (t : MeromorphicSection.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS (representedAlgebraicSpace B S hS R).1
      (representedAlgebraicSpace B S hS R).2 L t) :
    ∃ θ : (representedChartRestrictionSheaf B S hS R L).presheaf.stalk
        (_root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R)),
      θ ≠ 0 ∧
      (∀ x, Stacks.Divisors.IsTrivializedNear (representedChartRestrictionSheaf B S hS R L) x) ∧
      ∀ Z : PrimeDivisor B S hS (representedAlgebraicSpace B S hS R).1,
        haveI : ∀ W : PrimeDivisor B S hS (representedAlgebraicSpace B S hS R).1,
            Nontrivial ↥(W.genericHenselianLocalRing B S hS (representedAlgebraicSpace B S hS R).2
              (isDecentSpace_yoneda B S hS R)) := fun W =>
          W.nontrivial_genericHenselianLocalRing B S hS _ (isDecentSpace_yoneda B S hS R)
            (isIntegralSpace_yoneda B S hS R) hN
        haveI : ∀ W : PrimeDivisor B S hS (representedAlgebraicSpace B S hS R).1,
            IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS
              (representedAlgebraicSpace B S hS R).2 (isDecentSpace_yoneda B S hS R)) := fun W =>
          W.isNoetherianRing_genericHenselianLocalRing B S hS _ (isDecentSpace_yoneda B S hS R)
            (isIntegralSpace_yoneda B S hS R) hN
        haveI : ∀ W : PrimeDivisor B S hS (representedAlgebraicSpace B S hS R).1,
            Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS
              (representedAlgebraicSpace B S hS R).2 (isDecentSpace_yoneda B S hS R)) := fun W =>
          W.krullDimLE_genericHenselianLocalRing B S hS _ (isDecentSpace_yoneda B S hS R)
            (isIntegralSpace_yoneda B S hS R) hN
        orderOfVanishingSection.{u, u} B S hS (representedAlgebraicSpace B S hS R).2
            (isDecentSpace_yoneda B S hS R) Z L t
            (Z.canonicalLocalRatio B S hS (representedAlgebraicSpace B S hS R).2
              (isDecentSpace_yoneda B S hS R) L hL (isIntegralSpace_yoneda B S hS R) hN) =
          Stacks.Divisors.orderOfVanishing (representedChartRestrictionSheaf B S hS R L) θ
            (Stacks.Divisors.PrimeDivisor.ofCoheightOne
              (pointsToScheme B S hS R (Z.genericPoint B S hS _))
              (PrimeDivisor.coheight_pointsToScheme_genericPoint B S hS R Z)) := by
  have hInt := isIntegralSpace_yoneda B S hS R
  have hwa := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS (representedAlgebraicSpace B S hS R).2 hInt
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS _
    (representedAlgebraicSpace B S hS R).2 hN
  have hK : ∀ U : ((BigFppfOver.toScheme B S hS).obj R).Opens, IsAffineOpen U →
      IsFractionRing ((structurePresheaf B S hS (representedAlgebraicSpace B S hS R).1).obj
        (op (representedIdChartOpen B S hS R U)))
      ((meromorphicFunctionSheaf B S hS (representedAlgebraicSpace B S hS R).1
        (representedAlgebraicSpace B S hS R).2).obj.obj (op (representedIdChartOpen B S hS R U))) :=
    fun U hU => isFractionRing_meromorphicFunctionSheaf_obj B S hS
      (representedAlgebraicSpace B S hS R) hwa hfin _ hU
  set η := _root_.genericPoint ((BigFppfOver.toScheme B S hS).obj R)
  -- the generic value, read on one chart through the generic point
  obtain ⟨U₀, hU₀, hη₀, e₀, hc₀, hf₀⟩ :=
    exists_freeFamily_representedIdChartOpen B S hS R L hL η
  have : Nonempty U₀ := ⟨⟨η, hη₀⟩⟩
  have htriv : ∀ x,
      Stacks.Divisors.IsTrivializedNear (representedChartRestrictionSheaf B S hS R L) x := by
    intro x
    obtain ⟨U, -, hx, e, hc, hf⟩ := exists_freeFamily_representedIdChartOpen B S hS R L hL x
    exact ⟨U, hx, ULift.up (e (representedIdChartOpen B S hS R U) (𝟙 _)), fun y hy =>
      isStalkBasis_germ_representedChartModule B S hS R L U e hc hf y hy⟩
  refine ⟨representedChartFunctionFieldMap B S hS R U₀ (hK U₀ hU₀)
      (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U₀) e₀ hc₀ hf₀ t) •
    (representedChartRestrictionSheaf B S hS R L).presheaf.germ U₀ η hη₀
      (ULift.up (e₀ (representedIdChartOpen B S hS R U₀) (𝟙 _))), ?_, htriv, ?_⟩
  · intro h0
    have hunit := (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS
      (representedAlgebraicSpace B S hS R) hwa hfin L (representedIdChartOpen B S hS R U₀) hU₀ e₀
      hc₀ hf₀ t ht).map (representedChartFunctionFieldMap B S hS R U₀ (hK U₀ hU₀))
    have hb := (isStalkBasis_germ_representedChartModule B S hS R L U₀ e₀ hc₀ hf₀ η hη₀).1
    exact hunit.ne_zero (hb (h0.trans (zero_smul _ _).symm))
  · intro Z
    set ξ := pointsToScheme B S hS R (Z.genericPoint B S hS _)
    obtain ⟨U, hU, hξ, e, hc, hf⟩ := exists_freeFamily_representedIdChartOpen B S hS R L hL ξ
    have : Nonempty U := ⟨⟨ξ, hξ⟩⟩
    have : IsAffine (chartScheme (representedIdChartOpen B S hS R U)) := hU
    have hηU : η ∈ U := Stacks.Divisors.genericPoint_mem_of_mem hξ
    let v : U := ⟨ξ, hξ⟩
    have hv : chartSchemeToPoints B S hS (representedAlgebraicSpace B S hS R).1
        (representedIdChartOpen B S hS R U) v = Z.genericPoint B S hS _ :=
      (chartSchemeToPoints_representedIdChartOpen B S hS R U v).trans
        ((Equiv.symm_apply_eq _).2 rfl)
    have : IsLocallyNoetherian U.toScheme := inferInstance
    have : IsNoetherianRing ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v) :=
      (inferInstance : IsNoetherianRing (U.toScheme.presheaf.stalk (show U.toScheme from v)))
    have : Ring.KrullDimLE 1 ((chartScheme (representedIdChartOpen B S hS R U)).presheaf.stalk v) :=
      Z.krullDimLE_chartStalk B S hS (representedAlgebraicSpace B S hS R).2
        (isDecentSpace_yoneda B S hS R) (representedIdChartOpen B S hS R U) v hv
    have hunit := isUnit_chartRatio_of_isRegularMeromorphicSection B S hS
      (representedAlgebraicSpace B S hS R) hwa hfin L (representedIdChartOpen B S hS R U) hU e hc
      hf t ht
    have hcunit := hunit.map (chartPointMeromorphicMap B S hS (representedAlgebraicSpace B S hS R)
      (representedIdChartOpen B S hS R U) hU (hK U hU) v)
    -- the space side, read on the chart
    rw [Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS
      (isDecentSpace_yoneda B S hS R) hInt hN hwa hfin L hL t ht
      (representedIdChartOpen B S hS R U) hU e hc hf v hv hcunit]
    -- the scheme side, read against the germ of `e` at `ξ`
    have hbasis := isStalkBasis_germ_representedChartModule B S hS R L U e hc hf ξ hξ
    have hcoord : Stacks.Divisors.IsCoordinateAt (representedChartRestrictionSheaf B S hS R L) ξ
        (representedChartFunctionFieldMap B S hS R U₀ (hK U₀ hU₀)
            (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U₀) e₀ hc₀ hf₀ t) •
          (representedChartRestrictionSheaf B S hS R L).presheaf.germ U₀ η hη₀
            (ULift.up (e₀ (representedIdChartOpen B S hS R U₀) (𝟙 _))))
        (representedChartFunctionFieldMap B S hS R U (hK U hU)
          (chartRatio B S hS _ _ L (representedIdChartOpen B S hS R U) e hc hf t)) := by
      refine ⟨_, hbasis, ?_⟩
      refine (representedChartFunctionFieldMap_chartRatio_smul_germ_eq_of_charts B S hS R L t hK hU₀
        hU e₀ hc₀ hf₀ e hc hf hη₀ hηU).trans ?_
      exact congrArg (_ • ·) (Stacks.Divisors.toGenericStalk_germ
        (L := representedChartRestrictionSheaf B S hS R L) hξ hηU _).symm
    have hgen := Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne ξ
      (PrimeDivisor.coheight_pointsToScheme_genericPoint B S hS R Z)
    rw [Stacks.Divisors.orderOfVanishing_eq (hgen ▸ htriv ξ) (hgen ▸ hcoord), hgen]
    exact (ord_representedChartFunctionFieldMap B S hS R U hU (hK U hU) v
      (PrimeDivisor.coheight_pointsToScheme_genericPoint B S hS R Z) _ hunit).symm

end Order

end AlgebraicGeometry.Space
