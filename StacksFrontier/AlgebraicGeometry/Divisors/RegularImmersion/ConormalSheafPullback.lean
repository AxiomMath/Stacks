module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Group.SurjectiveKerEq
public import StacksFrontier.AlgebraicGeometry.Conormal.CommonCharts
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential

/-!
# The conormal algebra of an immersion on an open in which its image is closed

Let `i : Z ⟶ X` be an immersion of schemes and let `U ⊆ X` be an open with `i(Z) ⊆ U` and `i(Z)`
closed in `U`.  Then `i` factors as a closed immersion `Z ⟶ U` followed by the open immersion
`U ⟶ X`, and the closed subscheme `i(Z) ⊂ U` has an ideal sheaf `ℐ ⊆ 𝒪_U`.  Stacks tag 0633(1)
asserts
`𝒞_{Z/X,*} = i^*(⨁_{n ≥ 0} ℐⁿ) = i^{-1}(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`
as graded `𝒪_Z`-algebras.  This file proves the first of those identities as an isomorphism of
sheaves of graded algebras which also carries the unit to the unit, and describes the right-hand
side over every chart of `U`: its degree-`n` sections over `i⁻¹V`, for `V` an affine open of `U`,
are `I(V)ⁿ/I(V)ⁿ⁺¹`, and those preimages form a basis of `Z`.

## Main definitions

* `Stacks.Conormal.openLift`: the factorisation `Z ⟶ U` of `i` through `U`, with
  `Stacks.Conormal.openIdeal` the ideal sheaf of its kernel — the ideal sheaf `ℐ` of the closed
  subscheme `i(Z) ⊂ U` — and `Stacks.Conormal.openReesPullback` the pullback
  `i^*(⨁_{n ≥ 0} ℐⁿ)` of the Rees algebra of `ℐ`.
* `Stacks.Conormal.ChartPresentation`: a chartwise associated-graded presentation of a sheaf of
  graded algebras on `Z` over the affine charts of `U` — in degree `n` and over `i⁻¹V`, a
  presentation of the sections as `I(V)ⁿ/I(V)ⁿ⁺¹` compatible with restriction, multiplication,
  the unit and scalars.  `Stacks.Conormal.conormalChartPresentation` and
  `Stacks.Conormal.openReesChartPresentation` are the two presentations compared here.
* `Stacks.Conormal.openChartMap`: the local presentation of `i^*(⨁_{n ≥ 0} ℐⁿ)` on a chart, the
  pullback of a Rees section of `Stacks.Conormal.reesPullbackMap` transported along the
  identification of the two preimages of the chart.

## Main results

* `Stacks.Conormal.innerChart_isBasis`: the preimages of the affine opens inside `U` form a basis
  of the topology of `Z`.
* `Stacks.Conormal.gradedAlgebraIsoOfChartPresentations`: two sheaves of graded algebras with a
  chartwise associated-graded presentation over the same open are canonically isomorphic, with
  `gradedAlgebraIsoOfChartPresentations_one` the unit law.
* `Stacks.Conormal.conormalIsoReesPullback` and `conormalIsoReesPullback_one`: Stacks 0633(1),
  `𝒞_{Z/X,*} = i^*(⨁_{n ≥ 0} ℐⁿ)`, as an isomorphism of graded `𝒪_Z`-algebras.
* `Stacks.Conormal.openChartAssociatedGradedEquiv`: the degree-`n` sections of
  `i^*(⨁_{n ≥ 0} ℐⁿ)` over `i⁻¹V` are `I(V)ⁿ/I(V)ⁿ⁺¹`, with the four laws
  `openChartAssociatedGradedEquiv_mul`, `_one`, `_smul` and `_restrict`.

## Implementation notes

The hypotheses are the two conditions packed into "`i(Z) ⊂ U` is a closed subset of `U`" in
Stacks 0633(1): `hsub : Set.range i ⊆ U` and closedness of `Set.range (openLift i U hsub)`, the
image of `Z` *inside* `U`.  The morphism `i` is not assumed to be a closed immersion, and `U` is
not assumed affine or quasi-compact.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-! ### Affine charts of an open subscheme -/

section Chart

variable (U : X.Opens) (V : X.affineOpens) (hVU : V.1 ≤ U)

/-- An affine open of `X` inside `U`, read as an affine open of `U`. -/
def openChart : (U.toScheme).affineOpens := (affineOpensRestrict U).symm ⟨V, hVU⟩

/-- The chart of `U` attached to `V` is the preimage of `V` under the inclusion of `U`. -/
lemma openChart_coe : (openChart U V hVU).1 = U.ι ⁻¹ᵁ V.1 := rfl

/-- The image in `X` of the chart of `U` attached to `V` is `V`. -/
lemma openChart_image : (U.ι ''ᵁ (openChart U V hVU).1) = V.1 := by
  have h := affineOpensRestrict_apply_coe_coe U (openChart U V hVU)
  simpa [openChart] using h.symm

/-- The functions on a chart of `U` are the functions on the affine open of `X`. -/
def openSectionEquiv : Γ(X, V) ≃+* Γ(U.toScheme, (openChart U V hVU).1) := by
  haveI : IsIso (U.ι.app V.1) := by
    rw [← openChart_image U V hVU]
    infer_instance
  change Γ(X, V) ≃+* Γ(U.toScheme, U.ι ⁻¹ᵁ V.1)
  exact (asIso (U.ι.app V.1)).commRingCatIsoToRingEquiv

/-- The identification of functions on the chart is the map on sections of the inclusion of `U`. -/
lemma openSectionEquiv_apply (a : Γ(X, V)) :
    openSectionEquiv U V hVU a = (U.ι.app V.1).hom a := rfl

/-- Passing to charts of `U` is monotone in the affine open of `X`. -/
lemma openChart_mono (W : X.affineOpens) (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1) :
    (openChart U W hWU).1 ≤ (openChart U V hVU).1 := by
  rw [openChart_coe, openChart_coe]
  exact fun x hx => hWV hx

/-- The identification of functions on charts commutes with restriction from `V` to an affine
open `W ⊆ V`. -/
lemma openSectionEquiv_naturality (W : X.affineOpens) (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1)
    (a : Γ(X, V)) :
    openSectionEquiv U W hWU (X.presheaf.map (homOfLE hWV).op a) =
      (U.toScheme).presheaf.map (homOfLE (openChart_mono U V hVU W hWU hWV)).op
        (openSectionEquiv U V hVU a) :=
  congrArg (fun f : Γ(X, V) ⟶ Γ(U.toScheme, (openChart U W hWU).1) => f.hom a)
    (Scheme.Hom.naturality U.ι (homOfLE hWV).op)

end Chart

/-! ### Chartwise associated-graded presentations -/

section Presentation

variable (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)

/-- A chartwise associated-graded presentation of a sheaf of graded algebras on `Z` over the
affine charts of an open `U` of `X`: in each nonnegative degree `n` and over the preimage of
each affine open `V ⊆ U`, a presentation of the degree-`n` sections as the quotient
`I(V)ⁿ/I(V)ⁿ⁺¹` of the kernel ideal of the chart, compatible with restriction between charts,
with multiplication, with the unit and with the scalar action of the functions upstairs. -/
structure ChartPresentation (B : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf) where
  /-- The algebra is concentrated in nonnegative degrees. -/
  negative_isZero (n : ℤ) (hn : n < 0) : Limits.IsZero (B.piece n)
  /-- An element of `I(V)ⁿ` gives a degree-`n` section over `i⁻¹V`. -/
  map (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    ↥(chartIdeal i V ^ n) →+ (B.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))
  /-- Exactly `I(V)ⁿ⁺¹` dies in degree `n`. -/
  map_eq_zero_iff (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    map V hVU n a = 0 ↔ (a : Γ(X, V)) ∈ chartIdeal i V ^ (n + 1)
  /-- Every degree-`n` section over `i⁻¹V` has a representative. -/
  map_surjective (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    Function.Surjective (map V hVU n)
  /-- Over each chart the map on functions is surjective. -/
  app_surjective (V : X.affineOpens) (hVU : V.1 ≤ U) :
    Function.Surjective ((i.app V).hom)
  /-- The presentation is linear over the map on functions of `i`. -/
  map_smul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) (r : Γ(X, V))
      (a b : ↥(chartIdeal i V ^ n)) (hb : (b : Γ(X, V)) = r * (a : Γ(X, V))) :
    map V hVU n b =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from (i.app V).hom r) • map V hVU n a
  /-- The presentation is multiplicative. -/
  map_mul (V : X.affineOpens) (hVU : V.1 ≤ U) (n m : ℕ) (a : ↥(chartIdeal i V ^ n))
      (b : ↥(chartIdeal i V ^ m)) (c : ↥(chartIdeal i V ^ (n + m)))
      (hc : (c : Γ(X, V)) = (a : Γ(X, V)) * (b : Γ(X, V))) :
    map V hVU (n + m) c =
      (B.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1)) (map V hVU n a) (map V hVU m b)
  /-- The class of `1` is the graded unit. -/
  map_one (V : X.affineOpens) (hVU : V.1 ≤ U) (a : ↥(chartIdeal i V ^ 0))
      (ha : (a : Γ(X, V)) = 1) :
    map V hVU 0 a = B.one.eval (op (i ⁻¹ᵁ V.1))
  /-- The presentations commute with restriction between charts. -/
  map_naturality (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1)
      (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ) (a : ↥(chartIdeal i V ^ n))
      (b : ↥(chartIdeal i W ^ n))
      (hb : (b : Γ(X, W)) = X.presheaf.map (homOfLE hWV).op (a : Γ(X, V))) :
    (B.piece (n : ℤ)).val.map (homOfLE hZ).op (map V hVU n a) = map W hWU n b

end Presentation

variable (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
  (hsub : Set.range i.base ⊆ (U : Set X))

include hsub

/-- An immersion whose image lies in an open of the target factors through that open. -/
def openLift : Z ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι i (by rw [Scheme.Opens.range_ι]; exact hsub)

omit [IsImmersion i] in
/-- The lift composed with the inclusion of `U` is the immersion. -/
@[simp] lemma openLift_ι : openLift i U hsub ≫ U.ι = i :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsImmersion i] in
/-- The preimage of `U` under the immersion is all of `Z`. -/
lemma preimage_eq_top : i ⁻¹ᵁ U = ⊤ := by
  ext x
  simpa using hsub ⟨x, rfl⟩

/-- The lift of an immersion through an open is an immersion. -/
instance isImmersion_openLift : IsImmersion (openLift i U hsub) := by
  have h : IsImmersion (openLift i U hsub ≫ U.ι) := by
    rw [openLift_ι]; infer_instance
  exact IsImmersion.of_comp _ U.ι

omit [IsImmersion i] in
/-- On points, the lift followed by the inclusion of `U` is the immersion. -/
lemma openLift_base_apply (z : Z) : U.ι (openLift i U hsub z) = i z := by
  conv_rhs => rw [← openLift_ι i U hsub]
  rfl

omit [IsImmersion i] in
/-- The image of the lift is the image of the immersion, read inside the open. -/
lemma range_openLift : Set.range (openLift i U hsub).base = U.ι.base ⁻¹' Set.range i.base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (openLift_base_apply i U hsub z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, U.ι.isOpenEmbedding.injective
      ((openLift_base_apply i U hsub z).trans hz)⟩

/-- The ideal sheaf of the closed subscheme `i(Z) ⊂ U`. -/
def openIdeal : (U.toScheme).IdealSheafData := (openLift i U hsub).ker

/-- The pullback along `i` of the Rees algebra `⨁ₙ ℐⁿ` of the ideal sheaf of `i(Z) ⊂ U`. -/
abbrev openReesPullback : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  gradedPullback (openLift i U hsub) (Stacks.Blowup.reesGradedAlgebra (openIdeal i U hsub))

omit [IsImmersion i] in
/-- The preimage under the lift of the chart attached to `V` is the preimage of `V` under the
immersion. -/
lemma openChart_preimage (V : X.affineOpens) (hVU : V.1 ≤ U) :
    openLift i U hsub ⁻¹ᵁ (openChart U V hVU).1 = i ⁻¹ᵁ V.1 := by
  rw [openChart_coe, ← Scheme.Hom.comp_preimage, openLift_ι]

/-! ### The closed subscheme `i(Z) ⊂ U` -/

section Closed

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))

include hcl

/-- The lift of an immersion with closed image is a closed immersion. -/
lemma isClosedImmersion_openLift : IsClosedImmersion (openLift i U hsub) :=
  IsClosedImmersion.of_isPreimmersion _ hcl

/-- An open in which the image of an immersion is closed lies in the coborder of the range. -/
lemma le_coborderRange_of_closed : U ≤ i.coborderRange := by
  intro x hx
  have hcl' : IsClosed (U.ι.base ⁻¹' Set.range i.base) := by
    rw [← range_openLift i U hsub]; exact hcl
  change x ∈ coborder (Set.range i.base)
  simp only [coborder, Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not]
  intro hxcl
  have hy : (⟨x, hx⟩ : U.toScheme) ∈ U.ι.base ⁻¹' closure (Set.range i.base) := hxcl
  have hmem := U.ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hy
  rwa [hcl'.closure_eq] at hmem

variable (V : X.affineOpens) (hVU : V.1 ≤ U)

include hVU

/-- Over every affine open inside `U` the immersion restricts to a closed immersion. -/
lemma closedImmersion_chart : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl) :=
  isClosedImmersion_resLE_of_le_coborderRange i V.1
    (le_trans hVU (le_coborderRange_of_closed i U hsub hcl))

/-- The kernel ideal of `i` over an affine chart corresponds to the ideal sheaf of
`i(Z) ⊂ U` over that chart. -/
lemma openSectionEquiv_mem_ideal (a : Γ(X, V)) :
    a ∈ chartIdeal i V ↔
      openSectionEquiv U V hVU a ∈ (openIdeal i U hsub).ideal (openChart U V hVU) := by
  have := isClosedImmersion_openLift i U hsub hcl
  rw [chartIdeal, openIdeal, Scheme.Hom.ker_apply]
  have hker : RingHom.ker (i.app V.1).hom =
      RingHom.ker ((openLift i U hsub ≫ U.ι).app V.1).hom :=
    congrArg (fun f : Z ⟶ X => RingHom.ker (f.app V.1).hom) (openLift_ι i U hsub).symm
  rw [hker, Scheme.Hom.comp_app, openSectionEquiv_apply]
  rfl

/-- The identification of functions on the chart maps the kernel ideal of `i` over `V` onto the
ideal of `i(Z) ⊂ U` over the chart. -/
lemma openSectionEquiv_map_ideal :
    Ideal.map (openSectionEquiv U V hVU) (chartIdeal i V) =
      (openIdeal i U hsub).ideal (openChart U V hVU) := by
  ext b
  have h := Ideal.apply_mem_of_equiv_iff (f := openSectionEquiv U V hVU)
    (I := chartIdeal i V) (x := (openSectionEquiv U V hVU).symm b)
  have h' := openSectionEquiv_mem_ideal i U hsub hcl V hVU ((openSectionEquiv U V hVU).symm b)
  simpa only [(openSectionEquiv U V hVU).apply_symm_apply] using h.trans h'

/-- A function lies in the `n`-th power of the kernel ideal of `i` over `V` iff its image lies
in the `n`-th power of the ideal of `i(Z) ⊂ U` over the chart. -/
lemma openSectionEquiv_mem_power (n : ℕ) (a : Γ(X, V)) :
    a ∈ chartIdeal i V ^ n ↔
      openSectionEquiv U V hVU a ∈ (openIdeal i U hsub).ideal (openChart U V hVU) ^ n := by
  have hmap : Ideal.map (openSectionEquiv U V hVU) (chartIdeal i V ^ n) =
      (openIdeal i U hsub).ideal (openChart U V hVU) ^ n := by
    rw [Ideal.map_pow, openSectionEquiv_map_ideal i U hsub hcl V hVU]
  rw [← hmap]
  exact (Ideal.apply_mem_of_equiv_iff (f := openSectionEquiv U V hVU)
    (I := chartIdeal i V ^ n) (x := a)).symm

/-- The powers of the two kernel ideals correspond. -/
def openPowerEquiv (n : ℕ) :
    ↥(chartIdeal i V ^ n) ≃+
      ↥((openIdeal i U hsub).ideal (openChart U V hVU) ^ n) where
  toFun a := ⟨openSectionEquiv U V hVU a,
    (openSectionEquiv_mem_power i U hsub hcl V hVU n a).mp a.property⟩
  invFun b := ⟨(openSectionEquiv U V hVU).symm b,
    (openSectionEquiv_mem_power i U hsub hcl V hVU n _).mpr
      (by rw [(openSectionEquiv U V hVU).apply_symm_apply]; exact b.property)⟩
  left_inv a := Subtype.ext ((openSectionEquiv U V hVU).symm_apply_apply a)
  right_inv b := Subtype.ext ((openSectionEquiv U V hVU).apply_symm_apply b)
  map_add' a b := Subtype.ext ((openSectionEquiv U V hVU).map_add a b)

/-- The correspondence of powers is the identification of functions on the chart. -/
@[simp] lemma openPowerEquiv_coe (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    ((openPowerEquiv i U hsub hcl V hVU n a :
        ↥((openIdeal i U hsub).ideal (openChart U V hVU) ^ n)) :
      Γ(U.toScheme, (openChart U V hVU).1)) = openSectionEquiv U V hVU a := rfl

/-- Over a chart, the ideal of `i(Z) ⊂ U` is the kernel of the map on functions of the lift. -/
lemma openIdeal_ideal :
    (openIdeal i U hsub).ideal (openChart U V hVU) =
      RingHom.ker ((openLift i U hsub).app (openChart U V hVU).1).hom := by
  have := isClosedImmersion_openLift i U hsub hcl
  exact (openLift i U hsub).ker_apply (openChart U V hVU)

/-- The preimage under the lift of a chart of `U` is affine. -/
lemma isAffineOpen_openChart_preimage :
    IsAffineOpen (openLift i U hsub ⁻¹ᵁ (openChart U V hVU).1) := by
  have := isClosedImmersion_openLift i U hsub hcl
  exact (openChart U V hVU).2.preimage (openLift i U hsub)

/-- Over a chart of `U`, the map on functions of the lift is surjective. -/
lemma app_openChart_surjective :
    Function.Surjective ((openLift i U hsub).app (openChart U V hVU).1).hom := by
  have := isClosedImmersion_openLift i U hsub hcl
  exact (openLift i U hsub).app_surjective (openChart U V hVU).1 (openChart U V hVU).2

/-! ### The local presentation of the pulled-back Rees algebra on a chart -/

/-- The local presentation of `i^*(⨁ₙ ℐⁿ)` on a chart: an element of `I(V)ⁿ`, where `I(V)`
is the kernel of `Γ(X, V) ⟶ Γ(Z, i⁻¹V)`, as a degree-`n` section of the pulled-back Rees
algebra over `i⁻¹V`. -/
def openChartMap (n : ℕ) :
    ↥(chartIdeal i V ^ n) →+
      ((openReesPullback i U hsub).piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  (AddEquiv.cast (M := fun W : Z.Opens =>
      ((openReesPullback i U hsub).piece (n : ℤ)).val.obj (op W))
    (openChart_preimage i U hsub V hVU)).toAddMonoidHom.comp
      ((reesPullbackMap (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)).comp
        (openPowerEquiv i U hsub hcl V hVU n).toAddMonoidHom)

/-- The value of `openChartMap` on an element of `I(V)ⁿ`. -/
lemma openChartMap_apply (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    openChartMap i U hsub hcl V hVU n a =
      AddEquiv.cast (M := fun W : Z.Opens =>
          ((openReesPullback i U hsub).piece (n : ℤ)).val.obj (op W))
        (openChart_preimage i U hsub V hVU)
        (reesPullbackMap (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)
          (openPowerEquiv i U hsub hcl V hVU n a)) := rfl

/-- Exactly `I(V)ⁿ⁺¹` dies in degree `n`. -/
theorem openChartMap_eq_zero_iff (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    openChartMap i U hsub hcl V hVU n a = 0 ↔ (a : Γ(X, V)) ∈ chartIdeal i V ^ (n + 1) := by
  rw [openChartMap_apply, AddEquiv.map_eq_zero_iff,
    reesPullbackMap_eq_zero_iff (openIdeal i U hsub) (openLift i U hsub) n
      (openChart U V hVU)
      (isAffineOpen_openChart_preimage i U hsub hcl V hVU)
      (openIdeal_ideal i U hsub hcl V hVU).symm
      (app_openChart_surjective i U hsub hcl V hVU)]
  exact (openSectionEquiv_mem_power i U hsub hcl V hVU (n + 1) a).symm

/-- Every degree-`n` section over the chart comes from `I(V)ⁿ`. -/
theorem openChartMap_surjective (n : ℕ) :
    Function.Surjective (openChartMap i U hsub hcl V hVU n) :=
  ((AddEquiv.cast (M := fun W : Z.Opens =>
        ((openReesPullback i U hsub).piece (n : ℤ)).val.obj (op W))
      (openChart_preimage i U hsub V hVU)).surjective.comp
    ((reesPullbackMap_surjective (openIdeal i U hsub) (openLift i U hsub) n
        (openChart U V hVU)
        (isAffineOpen_openChart_preimage i U hsub hcl V hVU)
        (app_openChart_surjective i U hsub hcl V hVU)).comp
      (openPowerEquiv i U hsub hcl V hVU n).surjective))

omit [IsImmersion i] hcl in
/-- The scalar carried across the identification of the two preimages of the chart is the image
of the scalar under the map on functions of `i`. -/
lemma openChart_scalar_eq (r : Γ(X, V)) :
    (AddEquiv.cast (M := fun W : Z.Opens => Γ(Z, W)) (openChart_preimage i U hsub V hVU))
        ((((openLift i U hsub).app (openChart U V hVU).1)).hom
          (openSectionEquiv U V hVU r)) = (i.app V.1).hom r := by
  rw [openSectionEquiv_apply]
  have key : ∀ (j : Z ⟶ X) (hj : openLift i U hsub ≫ U.ι = j)
      (h : openLift i U hsub ⁻¹ᵁ (U.ι ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1),
      AddEquiv.cast (M := fun W : Z.Opens => Γ(Z, W)) h
          (((openLift i U hsub).app (U.ι ⁻¹ᵁ V.1)).hom ((U.ι.app V.1).hom r)) =
        (j.app V.1).hom r := by
    intro j hj h
    subst hj
    simp only [Scheme.Hom.comp_app, AddEquiv.cast_apply]
    exact eq_of_heq (cast_heq _ _)
  exact key i (openLift_ι i U hsub) _

/-- The local presentation is linear over the map on functions. -/
theorem openChartMap_smul (n : ℕ) (r : Γ(X, V)) (a b : ↥(chartIdeal i V ^ n))
    (hb : (b : Γ(X, V)) = r * (a : Γ(X, V))) :
    openChartMap i U hsub hcl V hVU n b =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from (i.app V).hom r) •
        openChartMap i U hsub hcl V hVU n a := by
  have hba : b = r • a := by
    apply Subtype.ext
    rw [SetLike.val_smul, smul_eq_mul, hb]
  subst hba
  have hp : openPowerEquiv i U hsub hcl V hVU n (r • a) =
      (show (U.toScheme).presheaf.obj (op (openChart U V hVU).1) from
          openSectionEquiv U V hVU r) •
        openPowerEquiv i U hsub hcl V hVU n a := by
    refine Subtype.ext ?_
    change openSectionEquiv U V hVU ((r • a : ↥(chartIdeal i V ^ n)) : Γ(X, V)) =
      openSectionEquiv U V hVU r * openSectionEquiv U V hVU (a : Γ(X, V))
    rw [SetLike.val_smul, smul_eq_mul, map_mul]
  rw [openChartMap_apply, openChartMap_apply, hp,
    reesPullbackMap_smul (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)
      (openSectionEquiv U V hVU r) (openPowerEquiv i U hsub hcl V hVU n a),
    sectionSmul_cast ((openReesPullback i U hsub).piece (n : ℤ))
      (openChart_preimage i U hsub V hVU)
      (((openLift i U hsub).app (openChart U V hVU).1).hom (openSectionEquiv U V hVU r)),
    openChart_scalar_eq]

/-- The local presentation is multiplicative. -/
theorem openChartMap_mul (n m : ℕ) (a : ↥(chartIdeal i V ^ n)) (b : ↥(chartIdeal i V ^ m))
    (c : ↥(chartIdeal i V ^ (n + m))) (hc : (c : Γ(X, V)) = a * b) :
    openChartMap i U hsub hcl V hVU (n + m) c =
      ((openReesPullback i U hsub).mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1))
        (openChartMap i U hsub hcl V hVU n a) (openChartMap i U hsub hcl V hVU m b) := by
  rw [openChartMap_apply, openChartMap_apply, openChartMap_apply,
    reesPullbackMap_mul (openIdeal i U hsub) (openLift i U hsub) n m (openChart U V hVU)
      (openPowerEquiv i U hsub hcl V hVU n a) (openPowerEquiv i U hsub hcl V hVU m b)
      (openPowerEquiv i U hsub hcl V hVU (n + m) c)
      (by rw [openPowerEquiv_coe, openPowerEquiv_coe, openPowerEquiv_coe, hc, map_mul])]
  exact gradedMul_cast (openReesPullback i U hsub) (n : ℤ) (m : ℤ)
    (openChart_preimage i U hsub V hVU) _ _

/-- The class of `1` is the graded unit. -/
theorem openChartMap_one (a : ↥(chartIdeal i V ^ 0)) (ha : (a : Γ(X, V)) = 1) :
    openChartMap i U hsub hcl V hVU 0 a =
      (openReesPullback i U hsub).one.eval (op (i ⁻¹ᵁ V.1)) := by
  rw [openChartMap_apply,
    reesPullbackMap_one (openIdeal i U hsub) (openLift i U hsub) (openChart U V hVU)
      (openPowerEquiv i U hsub hcl V hVU 0 a)
      (by rw [openPowerEquiv_coe, ha, map_one])]
  exact gradedOne_cast (openReesPullback i U hsub) (openChart_preimage i U hsub V hVU)

/-- The local presentations commute with restriction between charts. -/
theorem openChartMap_naturality (W : X.affineOpens) (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1)
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (a : ↥(chartIdeal i V ^ n)) (b : ↥(chartIdeal i W ^ n))
    (hb : (b : Γ(X, W)) = X.presheaf.map (homOfLE hWV).op (a : Γ(X, V))) :
    ((openReesPullback i U hsub).piece (n : ℤ)).val.map (homOfLE hZ).op
        (openChartMap i U hsub hcl V hVU n a) =
      openChartMap i U hsub hcl W hWU n b := by
  have hZW : openLift i U hsub ⁻¹ᵁ (openChart U W hWU).1 ≤
      openLift i U hsub ⁻¹ᵁ (openChart U V hVU).1 :=
    fun x hx => openChart_mono U V hVU W hWU hWV hx
  rw [openChartMap_apply, openChartMap_apply,
    ← moduleSectionMap_cast ((openReesPullback i U hsub).piece (n : ℤ))
      (openChart_preimage i U hsub V hVU) (openChart_preimage i U hsub W hWU) hZW hZ,
    reesPullbackMap_naturality (openIdeal i U hsub) (openLift i U hsub) n
      (openChart U W hWU) (openChart U V hVU)
      (openChart_mono U V hVU W hWU hWV) hZW
      (openPowerEquiv i U hsub hcl V hVU n a) (openPowerEquiv i U hsub hcl W hWU n b)
      (by rw [openPowerEquiv_coe, openPowerEquiv_coe, hb,
        openSectionEquiv_naturality U V hVU W hWU hWV])]

end Closed

/-! ### The basis of charts inside `U` -/

/-- The affine opens of `X` inside `U`. -/
abbrev InnerChart : Type u := { V : X.affineOpens // V.1 ≤ U }

/-- The preimage in `Z` of an affine open of `X` inside `U`. -/
abbrev innerChartOpens (V : InnerChart U) : Z.Opens := i ⁻¹ᵁ V.1.1

/-- If the image of `i` is contained in `U`, the preimages of the affine opens inside `U` form a
basis of the topology of `Z`. -/
theorem innerChart_isBasis :
    Opens.IsBasis (Set.range (innerChartOpens i U)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨O, hO, hpre⟩ := i.isEmbedding.isInducing.isOpen_iff.mp W.2
  have hxO : i x ∈ O := show x ∈ i ⁻¹' O by rw [hpre]; exact hx
  have hxU : i x ∈ (U : Set X) := hsub ⟨x, rfl⟩
  obtain ⟨T, ⟨A, hA, rfl⟩, hxA, hAT⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show i x ∈ O ∩ (U : Set X) from ⟨hxO, hxU⟩) (hO.inter U.2)
  refine ⟨i ⁻¹ᵁ A, ⟨⟨⟨A, hA⟩, fun y hy => (hAT hy).2⟩, rfl⟩, hxA, ?_⟩
  intro y hy
  simpa [hpre] using (show y ∈ i ⁻¹' O from (hAT hy).1)

omit [IsImmersion i] in
/-- The pulled-back Rees algebra is concentrated in nonnegative degrees. -/
lemma openReesPullback_negative_isZero (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((openReesPullback i U hsub).piece n) :=
  gradedPullback_negative_isZero (openLift i U hsub)
    (Stacks.Blowup.reesGradedAlgebra (openIdeal i U hsub))
    (fun m hm => Stacks.Blowup.reesPiece_negative_isZero (openIdeal i U hsub) m hm) n hn

/-! ### The two presentations -/

section Presentations

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))

include hcl

/-- The chartwise presentation of the conormal algebra over an open in which the image of `i` is
closed, by the canonical local presentations of Tag 0630. -/
def conormalChartPresentation : ChartPresentation i U (conormalAlgebra i).algebra where
  negative_isZero n hn := (conormalAlgebra i).negative_isZero n hn
  map V hVU n := (conormalAlgebra i).localMap V (closedImmersion_chart i U hsub hcl V hVU) n
  map_eq_zero_iff V _ n a := (conormalAlgebra i).localMap_eq_zero_iff V _ n a
  map_surjective V _ n := (conormalAlgebra i).localMap_surjective V _ n
  app_surjective V hVU := AlgebraicGeometry.app_surjective_of_closedRestriction i V
    (closedImmersion_chart i U hsub hcl V hVU)
  map_smul V _ n r a b hb := (conormalAlgebra i).localMap_smul V _ n r a b hb
  map_mul V _ n m a b c hc := (conormalAlgebra i).localMap_mul V _ n m a b c hc
  map_one V _ a ha := (conormalAlgebra i).localMap_one V _ a ha
  map_naturality V W _ _ hWV hZ n a b hb :=
    (conormalAlgebra i).localMap_naturality V W hWV hZ _ _ n a b hb

/-- The chartwise presentation of the pulled-back Rees algebra `i^*(⨁ₙ ℐⁿ)`. -/
def openReesChartPresentation : ChartPresentation i U (openReesPullback i U hsub) where
  negative_isZero := openReesPullback_negative_isZero i U hsub
  map V hVU n := openChartMap i U hsub hcl V hVU n
  map_eq_zero_iff V hVU n a := openChartMap_eq_zero_iff i U hsub hcl V hVU n a
  map_surjective V hVU n := openChartMap_surjective i U hsub hcl V hVU n
  app_surjective V hVU := AlgebraicGeometry.app_surjective_of_closedRestriction i V
    (closedImmersion_chart i U hsub hcl V hVU)
  map_smul V hVU n r a b hb := openChartMap_smul i U hsub hcl V hVU n r a b hb
  map_mul V hVU n m a b c hc := openChartMap_mul i U hsub hcl V hVU n m a b c hc
  map_one V hVU a ha := openChartMap_one i U hsub hcl V hVU a ha
  map_naturality V W hVU hWU hWV hZ n a b hb :=
    openChartMap_naturality i U hsub hcl V hVU W hWU hWV hZ n a b hb

end Presentations

/-! ### The chartwise comparison of two presentations -/

section Compare

variable {A B : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf}
  (P : ChartPresentation i U A) (Q : ChartPresentation i U B)

/-- The comparison of the degree-`n` sections of two presented algebras over the preimage of a
chart, for `n : ℕ`: both are the quotient `I(V)ⁿ/I(V)ⁿ⁺¹` of the kernel ideal of the
chart. -/
def chartCompare (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) ≃+
      (B.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  Stacks.addEquivOfSurjectiveKerEq (P.map V hVU n) (Q.map V hVU n)
    (P.map_surjective V hVU n) (Q.map_surjective V hVU n)
    (fun a => (P.map_eq_zero_iff V hVU n a).trans (Q.map_eq_zero_iff V hVU n a).symm)

omit [IsImmersion i] hsub in
/-- The comparison carries the section of a representative to the section of the same
representative. -/
theorem chartCompare_map (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (a : ↥(chartIdeal i V ^ n)) :
    chartCompare i U P Q V hVU n (P.map V hVU n a) = Q.map V hVU n a :=
  Stacks.addEquivOfSurjectiveKerEq_apply _ _ _ _ _ a

omit [IsImmersion i] hsub in
/-- The comparison is linear over the functions on the chart. -/
theorem chartCompare_smul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (s : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)))
    (x : (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartCompare i U P Q V hVU n (s • x) =
      s • chartCompare i U P Q V hVU n x := by
  obtain ⟨a, rfl⟩ := P.map_surjective V hVU n x
  obtain ⟨r, hr⟩ := P.app_surjective V hVU (show Γ(Z, i ⁻¹ᵁ V.1) from s)
  have hmem : r * (a : Γ(X, V)) ∈ chartIdeal i V ^ n :=
    (chartIdeal i V ^ n).mul_mem_left r a.2
  rw [← hr, ← P.map_smul V hVU n r a ⟨r * (a : Γ(X, V)), hmem⟩ rfl,
    chartCompare_map i U _ _, chartCompare_map i U _ _]
  exact Q.map_smul V hVU n r a ⟨r * (a : Γ(X, V)), hmem⟩ rfl

omit [IsImmersion i] hsub in
/-- The comparison is multiplicative. -/
theorem chartCompare_mul (V : X.affineOpens) (hVU : V.1 ≤ U) (n m : ℕ)
    (x : (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)))
    (y : (A.piece (m : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartCompare i U P Q V hVU (n + m)
        ((A.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1)) x y) =
      (B.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1))
        (chartCompare i U P Q V hVU n x) (chartCompare i U P Q V hVU m y) := by
  obtain ⟨a, rfl⟩ := P.map_surjective V hVU n x
  obtain ⟨b, rfl⟩ := P.map_surjective V hVU m y
  have hmem : (a : Γ(X, V)) * (b : Γ(X, V)) ∈ chartIdeal i V ^ (n + m) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul a.2 b.2
  rw [← P.map_mul V hVU n m a b ⟨(a : Γ(X, V)) * (b : Γ(X, V)), hmem⟩ rfl,
    chartCompare_map i U _ _, chartCompare_map i U _ _, chartCompare_map i U _ _]
  exact Q.map_mul V hVU n m a b ⟨(a : Γ(X, V)) * (b : Γ(X, V)), hmem⟩ rfl

omit [IsImmersion i] hsub in
/-- The comparison carries the unit to the unit. -/
theorem chartCompare_one (V : X.affineOpens) (hVU : V.1 ≤ U) :
    chartCompare i U P Q V hVU 0 (A.one.eval (op (i ⁻¹ᵁ V.1))) =
      B.one.eval (op (i ⁻¹ᵁ V.1)) := by
  rw [← P.map_one V hVU ⟨1, by simp⟩ rfl, chartCompare_map i U _ _]
  exact Q.map_one V hVU ⟨1, by simp⟩ rfl

omit [IsImmersion i] hsub in
/-- The comparison commutes with restriction to a smaller chart of the same ambient open. -/
theorem chartCompare_restrict_le (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
    (hWV : W.1 ≤ V.1) (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (x : (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    (B.piece (n : ℤ)).val.map (homOfLE hZ).op (chartCompare i U P Q V hVU n x) =
      chartCompare i U P Q W hWU n
        ((A.piece (n : ℤ)).val.map (homOfLE hZ).op x) := by
  obtain ⟨a, rfl⟩ := P.map_surjective V hVU n x
  have hmem : X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)) ∈ chartIdeal i W ^ n :=
    map_mem_chartIdeal_pow i hWV n a.2
  rw [chartCompare_map i U _ _,
    P.map_naturality V W hVU hWU hWV hZ n a
      ⟨X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)), hmem⟩ rfl,
    chartCompare_map i U _ _]
  exact Q.map_naturality V W hVU hWU hWV hZ n a
    ⟨X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)), hmem⟩ rfl

omit [IsImmersion i] hsub in
/-- The comparison commutes with every restriction between the preimages of two charts of `U`,
even when neither chart contains the other. -/
theorem chartCompare_restrict (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (x : (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    (B.piece (n : ℤ)).val.map (homOfLE hZ).op (chartCompare i U P Q V hVU n x) =
      chartCompare i U P Q W hWU n
        ((A.piece (n : ℤ)).val.map (homOfLE hZ).op x) := by
  have hle : ∀ T : { T : X.affineOpens // T.1 ≤ W.1 ⊓ V.1 },
      i ⁻¹ᵁ T.1.1 ≤ i ⁻¹ᵁ W.1 := fun T z hz => le_trans T.2 inf_le_left hz
  refine Stacks.BasisRestriction.moduleSheafSection_ext_of_cover
    (B.piece (n : ℤ)) _ hle ?_ _ _ ?_
  · intro z hz
    have hzV : z ∈ i ⁻¹ᵁ V.1 := hZ hz
    obtain ⟨T, ⟨A', hA, rfl⟩, hzA, hAT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show i z ∈ (W.1 : Set X) ∩ (V.1 : Set X) from ⟨hz, hzV⟩)
        (W.1.2.inter V.1.2)
    exact ⟨⟨⟨A', hA⟩, fun y hy => hAT hy⟩, hzA⟩
  · intro T
    have hTV : i ⁻¹ᵁ T.1.1 ≤ i ⁻¹ᵁ V.1 := fun z hz => le_trans T.2 inf_le_right hz
    have hTU : T.1.1 ≤ U := le_trans (le_trans T.2 inf_le_right) hVU
    have hcomp : ∀ (C : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf) z,
        (C.piece (n : ℤ)).val.map (homOfLE (hle T)).op
          ((C.piece (n : ℤ)).val.map (homOfLE hZ).op z) =
        (C.piece (n : ℤ)).val.map (homOfLE hTV).op z := fun C z =>
      ((C.piece (n : ℤ)).val.map_comp_apply (homOfLE hZ).op (homOfLE (hle T)).op z).symm.trans
        ((C.piece (n : ℤ)).val.congr_map_apply (Subsingleton.elim _ _) z)
    rw [hcomp B,
      chartCompare_restrict_le i U P Q V T.1 hVU hTU (le_trans T.2 inf_le_right) hTV n x,
      ← hcomp A x]
    exact (chartCompare_restrict_le i U P Q W T.1 hWU hTU (le_trans T.2 inf_le_left)
      (hle T) n ((A.piece (n : ℤ)).val.map (homOfLE hZ).op x)).symm

/-! ### The comparison in every integer degree -/

/-- The chartwise comparison as an isomorphism of modules over the functions on the chart. -/
def chartCompareIso (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) ≅ (B.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  (AddEquiv.toLinearEquiv (chartCompare i U P Q V hVU n)
    (chartCompare_smul i U P Q V hVU n)).toModuleIso

omit [IsImmersion i] hsub in
/-- The isomorphism `chartCompareIso` acts as the chartwise comparison. -/
@[simp]
theorem chartCompareIso_hom_apply (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (x : (A.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    (chartCompareIso i U P Q V hVU n).hom x =
      chartCompare i U P Q V hVU n x :=
  rfl

/-- The chartwise comparison in every integer degree; in a negative degree both sides vanish. -/
def chartCompareIsoInt (V : X.affineOpens) (hVU : V.1 ≤ U) : ∀ n : ℤ,
    (A.piece n).val.obj (op (i ⁻¹ᵁ V.1)) ≅ (B.piece n).val.obj (op (i ⁻¹ᵁ V.1))
  | (n : ℕ) => chartCompareIso i U P Q V hVU n
  | Int.negSucc n =>
      haveI hneg : (Int.negSucc n) < 0 := Int.negSucc_lt_zero n
      have hz : ∀ z : (A.piece (Int.negSucc n)).val.obj (op (i ⁻¹ᵁ V.1)), z = 0 := fun z =>
        Stacks.SheafOfModules.section_eq_zero_of_isZero (P.negative_isZero _ hneg) _ z
      have hz' : ∀ z : (B.piece (Int.negSucc n)).val.obj (op (i ⁻¹ᵁ V.1)), z = 0 := fun z =>
        Stacks.SheafOfModules.section_eq_zero_of_isZero (Q.negative_isZero _ hneg) _ z
      (LinearEquiv.ofLinearMap 0 0 (LinearMap.ext fun z => (hz' z).symm)
        (LinearMap.ext fun z => (hz z).symm)).toModuleIso

omit [IsImmersion i] hsub in
/-- In a nonnegative degree, `chartCompareIsoInt` is `chartCompareIso`. -/
theorem chartCompareIsoInt_natCast (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    chartCompareIsoInt i U P Q V hVU (n : ℤ) =
      chartCompareIso i U P Q V hVU n :=
  rfl

omit [IsImmersion i] hsub in
/-- The comparison is multiplicative in every pair of integer degrees. -/
theorem chartCompareIsoInt_mul (V : X.affineOpens) (hVU : V.1 ≤ U) : ∀ (p q : ℤ)
    (x : (A.piece p).val.obj (op (i ⁻¹ᵁ V.1))) (y : (A.piece q).val.obj (op (i ⁻¹ᵁ V.1))),
    (chartCompareIsoInt i U P Q V hVU (p + q)).hom
        ((A.mul p q).app (op (i ⁻¹ᵁ V.1)) x y) =
      (B.mul p q).app (op (i ⁻¹ᵁ V.1))
        ((chartCompareIsoInt i U P Q V hVU p).hom x)
        ((chartCompareIsoInt i U P Q V hVU q).hom y)
  | (n : ℕ), (m : ℕ), x, y => chartCompare_mul i U P Q V hVU n m x y
  | Int.negSucc n, q, x, y => by
      have hx : x = 0 :=
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          (P.negative_isZero _ (Int.negSucc_lt_zero n)) _ x
      subst hx
      simp only [map_zero, AddMonoidHom.zero_apply]
  | (n : ℕ), Int.negSucc m, x, y => by
      have hy : y = 0 :=
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          (P.negative_isZero _ (Int.negSucc_lt_zero m)) _ y
      subst hy
      simp only [map_zero]

omit [IsImmersion i] hsub in
/-- The comparison commutes with restriction, in every integer degree. -/
theorem chartCompareIsoInt_restrict (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) : ∀ (n : ℤ) (x : (A.piece n).val.obj (op (i ⁻¹ᵁ V.1))),
    (chartCompareIsoInt i U P Q W hWU n).hom
        ((A.piece n).val.map (homOfLE hZ).op x) =
      (B.piece n).val.map (homOfLE hZ).op
        ((chartCompareIsoInt i U P Q V hVU n).hom x)
  | (n : ℕ), x => (chartCompare_restrict i U P Q V W hVU hWU hZ n x).symm
  | Int.negSucc n, x => by
      have hz' : ∀ z : (B.piece (Int.negSucc n)).val.obj (op (i ⁻¹ᵁ W.1)), z = 0 := fun z =>
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          (Q.negative_isZero _ (Int.negSucc_lt_zero n)) _ z
      exact (hz' _).trans (hz' _).symm

/-! ### The sheaf-level identification -/

/-- The canonical isomorphism between two sheaves of graded algebras on `Z` with a chartwise
associated-graded presentation over the same open. -/
def gradedAlgebraIsoOfChartPresentations : A ≅ B :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis A B (innerChartOpens i U)
    (fun n V => chartCompareIsoInt i U P Q V.1 V.2 n)
    (innerChart_isBasis i U hsub)
    (fun n V W h x => chartCompareIsoInt_restrict i U P Q V.1 W.1 V.2 W.2 h n x)
    (fun p q V x y => chartCompareIsoInt_mul i U P Q V.1 V.2 p q x y)

/-- The degree-`n` component of the identification over the preimage of a chart is the
chartwise comparison. -/
theorem gradedAlgebraIsoOfChartPresentations_hom_app_app (n : ℤ) (V : InnerChart U) :
    ((gradedAlgebraIsoOfChartPresentations i U hsub P Q).hom.app n).val.app
        (op (i ⁻¹ᵁ V.1.1)) = (chartCompareIsoInt i U P Q V.1 V.2 n).hom :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis_hom_app_app _ _ _ _ _ _ _ n V

/-- The identification `Stacks.Conormal.gradedAlgebraIsoOfChartPresentations` carries the graded
unit to the graded unit, over every open. -/
theorem gradedAlgebraIsoOfChartPresentations_one (W : Z.Opens) :
    ((gradedAlgebraIsoOfChartPresentations i U hsub P Q).hom.app 0).val.app (op W)
        (A.one.eval (op W)) = B.one.eval (op W) := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (B.piece 0) (innerChartOpens i U)
    (innerChart_isBasis i U hsub) _ _ fun V hle => ?_
  rw [← PresheafOfModules.naturality_apply
      ((gradedAlgebraIsoOfChartPresentations i U hsub P Q).hom.app 0).val (homOfLE hle).op,
    PresheafOfModules.sections_property A.one (homOfLE hle).op,
    PresheafOfModules.sections_property B.one (homOfLE hle).op,
    gradedAlgebraIsoOfChartPresentations_hom_app_app]
  exact chartCompare_one i U P Q V.1 V.2

end Compare

/-! ### Tag 0633 (1) at sheaf level -/

section Identification

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))

include hcl

/-- Let `i : Z ⟶ X` be an immersion, let `U ⊆ X` be an open with `i(Z) ⊆ U` closed in `U`, and
let `ℐ ⊆ 𝒪_U` be the ideal sheaf of the closed subscheme `i(Z) ⊂ U`. Then the conormal algebra of
`i` is the pullback `i^*(⨁_{n ≥ 0} ℐⁿ)` of the Rees algebra of `ℐ`, as sheaves of graded
`𝒪_Z`-algebras. -/
def conormalIsoReesPullback : (conormalAlgebra i).algebra ≅ openReesPullback i U hsub :=
  gradedAlgebraIsoOfChartPresentations i U hsub
    (conormalChartPresentation i U hsub hcl) (openReesChartPresentation i U hsub hcl)

/-- The identification of the conormal algebra with `i^*(⨁_{n ≥ 0} ℐⁿ)` carries the graded unit
to the graded unit over every open. -/
theorem conormalIsoReesPullback_one (W : Z.Opens) :
    ((conormalIsoReesPullback i U hsub hcl).hom.app 0).val.app (op W)
        ((conormalAlgebra i).algebra.one.eval (op W)) =
      (openReesPullback i U hsub).one.eval (op W) :=
  gradedAlgebraIsoOfChartPresentations_one i U hsub _ _ W

/-- The degree-`n` component of the identification over the preimage of a chart. -/
theorem conormalIsoReesPullback_hom_app_app (n : ℤ) (V : InnerChart U) :
    ((conormalIsoReesPullback i U hsub hcl).hom.app n).val.app (op (i ⁻¹ᵁ V.1.1)) =
      (chartCompareIsoInt i U (conormalChartPresentation i U hsub hcl)
        (openReesChartPresentation i U hsub hcl) V.1 V.2 n).hom :=
  gradedAlgebraIsoOfChartPresentations_hom_app_app i U hsub _ _ n V

/-! ### The associated-graded reading of the pulled-back Rees algebra -/

/-- The degree-`n` sections of `i^*(⨁_{n ≥ 0} ℐⁿ)` over the preimage of a chart `V ⊆ U` are
`I(V)ⁿ/I(V)ⁿ⁺¹`, where `I(V) ⊆ Γ(X, V)` is the kernel ideal of the chart. -/
def openChartAssociatedGradedEquiv (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n ≃+
      ((openReesPullback i U hsub).piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  ((affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).equiv n).trans
    (chartCompare i U (conormalChartPresentation i U hsub hcl)
      (openReesChartPresentation i U hsub hcl) V hVU n)

/-- The identification is the comparison of the two presentations after the isomorphism with
the associated graded of the conormal algebra. -/
private theorem openChartAssociatedGradedEquiv_eq (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n) :
    openChartAssociatedGradedEquiv i U hsub hcl V hVU n x =
      chartCompare i U (conormalChartPresentation i U hsub hcl)
        (openReesChartPresentation i U hsub hcl) V hVU n
        ((affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).equiv n x) :=
  rfl

/-- The class of an element of `I(V)ⁿ` maps to its image under `openChartMap`. -/
theorem openChartAssociatedGradedEquiv_mk (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    openChartAssociatedGradedEquiv i U hsub hcl V hVU n
        (AssociatedGraded.mk (chartIdeal i V) n a) =
      openChartMap i U hsub hcl V hVU n ⟨(a : Γ(X, V)), by simpa using a.property⟩ := by
  rw [openChartAssociatedGradedEquiv_eq,
    (affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).map_mk]
  exact chartCompare_map i U _ _ V hVU n _

/-- Products of homogeneous classes correspond to products of sections. -/
theorem openChartAssociatedGradedEquiv_mul (V : X.affineOpens) (hVU : V.1 ≤ U) (n m : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n)
    (y : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) m) :
    openChartAssociatedGradedEquiv i U hsub hcl V hVU (n + m)
        (AssociatedGraded.homogeneousSMul (chartIdeal i V) x y) =
      ((openReesPullback i U hsub).mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1))
        (openChartAssociatedGradedEquiv i U hsub hcl V hVU n x)
        (openChartAssociatedGradedEquiv i U hsub hcl V hVU m y) := by
  rw [openChartAssociatedGradedEquiv_eq,
    (affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).map_mul n m x y,
    chartCompare_mul i U _ _]
  rfl

/-- The degree-zero unit is respected. -/
theorem openChartAssociatedGradedEquiv_one (V : X.affineOpens) (hVU : V.1 ≤ U) :
    openChartAssociatedGradedEquiv i U hsub hcl V hVU 0
        (AssociatedGraded.mk (chartIdeal i V) 0
          (⟨1, by simp [AssociatedGraded.power]⟩ :
            AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) 0)) =
      (openReesPullback i U hsub).one.eval (op (i ⁻¹ᵁ V.1)) := by
  rw [openChartAssociatedGradedEquiv_eq,
    (affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).map_one]
  exact chartCompare_one i U _ _ V hVU

/-- The identification is linear over the quotient map on chart sections. -/
theorem openChartAssociatedGradedEquiv_smul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
    (r : Γ(X, V)) (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n) :
    openChartAssociatedGradedEquiv i U hsub hcl V hVU n (r • x) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from (i.app V).hom r) •
        openChartAssociatedGradedEquiv i U hsub hcl V hVU n x := by
  rw [openChartAssociatedGradedEquiv_eq,
    (affineSectionsEquiv i V (closedImmersion_chart i U hsub hcl V hVU)).map_smul n r x,
    chartCompare_smul i U _ _]
  rfl

/-- The identification commutes with restriction between charts. -/
theorem openChartAssociatedGradedEquiv_restrict (V W : X.affineOpens) (hVU : V.1 ≤ U)
    (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1) (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n)
    (b : AssociatedGraded.power (M := Γ(X, W)) (chartIdeal i W) n)
    (hab : (b : Γ(X, W)) = X.presheaf.map (homOfLE hWV).op (a : Γ(X, V))) :
    ((openReesPullback i U hsub).piece (n : ℤ)).val.map (homOfLE hZ).op
        (openChartAssociatedGradedEquiv i U hsub hcl V hVU n
          (AssociatedGraded.mk (chartIdeal i V) n a)) =
      openChartAssociatedGradedEquiv i U hsub hcl W hWU n
        (AssociatedGraded.mk (chartIdeal i W) n b) := by
  rw [openChartAssociatedGradedEquiv_mk, openChartAssociatedGradedEquiv_mk]
  exact openChartMap_naturality i U hsub hcl V hVU W hWU hWV hZ n _ _ (by simpa using hab)

end Identification


end Stacks.Conormal

end
