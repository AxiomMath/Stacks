module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AssociatedGradedPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSheafPullback

/-!
# The conormal algebra as the pullback of the associated graded, at sheaf level

Let `i : Z ⟶ X` be an immersion of schemes and let `U ⊆ X` be an open with `i(Z) ⊆ U` and
`i(Z)` closed in `U`, so that `i` factors through `U` as a closed immersion with ideal sheaf
`ℐ ⊆ 𝒪_U`. The second identity of Stacks tag 0633(1) reads

`𝒞_{Z/X,*} = i^{-1}(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`.

Here it is proved with the pullback `i^*` in place of the topological inverse image `i^{-1}`:
the conormal algebra of `i` is isomorphic, as a sheaf of graded `𝒪_Z`-algebras, to
`i^*(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`, and the isomorphism carries the graded unit to the graded unit. The
two readings agree, each graded piece of `⨁ ℐⁿ/ℐⁿ⁺¹` being annihilated by `ℐ`
(`Stacks.Conormal.smul_top_eq_bot_grSection`).

Both algebras carry a `Stacks.Conormal.ChartPresentation`, a chartwise presentation of their
degree-`n` sections over `i⁻¹V` as `I(V)ⁿ/I(V)ⁿ⁺¹`, and two sheaves of graded algebras carrying
one are canonically isomorphic by `Stacks.Conormal.gradedAlgebraIsoOfChartPresentations`.

## Main definitions

* `Stacks.Conormal.openGrPullback`: the pullback `i^*(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)` of the associated
  graded algebra of the ideal sheaf of `i(Z) ⊂ U`.
* `Stacks.Conormal.openGrChartMap`: its local presentation on a chart, the pullback of a
  section of the associated graded transported along the identification of the two preimages of
  the chart.
* `Stacks.Conormal.openGrChartPresentation`: the resulting chartwise presentation.

## Main results

* `Stacks.Conormal.conormalIsoGrPullback` and `conormalIsoGrPullback_one`: **the second
  identity of Stacks 0633(1) at sheaf level**, in the form
  `𝒞_{Z/X,*} ≅ i^*(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)`: an isomorphism of sheaves of graded `𝒪_Z`-algebras
  which carries the unit to the unit.
* `Stacks.Conormal.reesPullbackIsoGrPullback`: **the two right-hand sides of 0633(1) agree**,
  `i^*(⨁ₙ ℐⁿ) ≅ i^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
  (hsub : Set.range i.base ⊆ (U : Set X))

include hsub

/-- **The pullback along `i` of the associated graded algebra `⨁ₙ ℐⁿ/ℐⁿ⁺¹` of the ideal sheaf
of `i(Z) ⊂ U`** — the right-hand side of the second identity of Tag 0633(1). -/
abbrev openGrPullback : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf :=
  gradedPullback (openLift i U hsub) (grGradedAlgebra (openIdeal i U hsub))

omit [IsImmersion i] in
/-- The pulled-back associated graded algebra is concentrated in nonnegative degrees. -/
lemma openGrPullback_negative_isZero (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((openGrPullback i U hsub).piece n) :=
  gradedPullback_grGradedAlgebra_negative_isZero (openIdeal i U hsub) (openLift i U hsub) n hn

section Closed

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))
  (V : X.affineOpens) (hVU : V.1 ≤ U)

include hcl hVU

/-- **The local presentation of `i^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` on a chart.** An element of `I(V)ⁿ`, where
`I(V)` is the kernel of `Γ(X, V) ⟶ Γ(Z, i⁻¹V)`, as a degree-`n` section of the pulled-back
associated graded algebra over `i⁻¹V`. -/
def openGrChartMap (n : ℕ) :
    ↥(chartIdeal i V ^ n) →+
      ((openGrPullback i U hsub).piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  (AddEquiv.cast (M := fun W : Z.Opens =>
      ((openGrPullback i U hsub).piece (n : ℤ)).val.obj (op W))
    (openChart_preimage i U hsub V hVU)).toAddMonoidHom.comp
      ((grPullbackMap (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)).comp
        (openPowerEquiv i U hsub hcl V hVU n).toAddMonoidHom)

/-- `openGrChartMap` sends `a ∈ I(V)ⁿ` to the image under `grPullbackMap` of its image under
`openPowerEquiv`, transported along `openChart_preimage`. -/
lemma openGrChartMap_apply (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    openGrChartMap i U hsub hcl V hVU n a =
      AddEquiv.cast (M := fun W : Z.Opens =>
          ((openGrPullback i U hsub).piece (n : ℤ)).val.obj (op W))
        (openChart_preimage i U hsub V hVU)
        (grPullbackMap (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)
          (openPowerEquiv i U hsub hcl V hVU n a)) := rfl

/-- **Exactly `I(V)ⁿ⁺¹` dies in degree `n`.** -/
theorem openGrChartMap_eq_zero_iff (n : ℕ) (a : ↥(chartIdeal i V ^ n)) :
    openGrChartMap i U hsub hcl V hVU n a = 0 ↔
      (a : Γ(X, V)) ∈ chartIdeal i V ^ (n + 1) := by
  rw [openGrChartMap_apply, AddEquiv.map_eq_zero_iff,
    grPullbackMap_eq_zero_iff (openIdeal i U hsub) (openLift i U hsub) n
      (openChart U V hVU)
      (isAffineOpen_openChart_preimage i U hsub hcl V hVU)
      (openIdeal_ideal i U hsub hcl V hVU).symm
      (app_openChart_surjective i U hsub hcl V hVU)]
  exact (openSectionEquiv_mem_power i U hsub hcl V hVU (n + 1) a).symm

/-- **Every degree-`n` section over the chart comes from `I(V)ⁿ`.** -/
theorem openGrChartMap_surjective (n : ℕ) :
    Function.Surjective (openGrChartMap i U hsub hcl V hVU n) :=
  ((AddEquiv.cast (M := fun W : Z.Opens =>
        ((openGrPullback i U hsub).piece (n : ℤ)).val.obj (op W))
      (openChart_preimage i U hsub V hVU)).surjective.comp
    ((grPullbackMap_surjective (openIdeal i U hsub) (openLift i U hsub) n
        (openChart U V hVU)
        (isAffineOpen_openChart_preimage i U hsub hcl V hVU)
        (openIdeal_ideal i U hsub hcl V hVU).symm
        (app_openChart_surjective i U hsub hcl V hVU)).comp
      (openPowerEquiv i U hsub hcl V hVU n).surjective))

/-- **The local presentation is linear over the map on functions.** -/
theorem openGrChartMap_smul (n : ℕ) (r : Γ(X, V)) (a b : ↥(chartIdeal i V ^ n))
    (hb : (b : Γ(X, V)) = r * (a : Γ(X, V))) :
    openGrChartMap i U hsub hcl V hVU n b =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from (i.app V).hom r) •
        openGrChartMap i U hsub hcl V hVU n a := by
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
  rw [openGrChartMap_apply, openGrChartMap_apply, hp,
    grPullbackMap_smul (openIdeal i U hsub) (openLift i U hsub) n (openChart U V hVU)
      (openSectionEquiv U V hVU r) (openPowerEquiv i U hsub hcl V hVU n a),
    sectionSmul_cast ((openGrPullback i U hsub).piece (n : ℤ))
      (openChart_preimage i U hsub V hVU)
      (((openLift i U hsub).app (openChart U V hVU).1).hom (openSectionEquiv U V hVU r)),
    openChart_scalar_eq]

/-- **The local presentation is multiplicative.** -/
theorem openGrChartMap_mul (n m : ℕ) (a : ↥(chartIdeal i V ^ n)) (b : ↥(chartIdeal i V ^ m))
    (c : ↥(chartIdeal i V ^ (n + m))) (hc : (c : Γ(X, V)) = a * b) :
    openGrChartMap i U hsub hcl V hVU (n + m) c =
      ((openGrPullback i U hsub).mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1))
        (openGrChartMap i U hsub hcl V hVU n a) (openGrChartMap i U hsub hcl V hVU m b) := by
  rw [openGrChartMap_apply, openGrChartMap_apply, openGrChartMap_apply,
    grPullbackMap_mul (openIdeal i U hsub) (openLift i U hsub) n m (openChart U V hVU)
      (openPowerEquiv i U hsub hcl V hVU n a) (openPowerEquiv i U hsub hcl V hVU m b)
      (openPowerEquiv i U hsub hcl V hVU (n + m) c)
      (by rw [openPowerEquiv_coe, openPowerEquiv_coe, openPowerEquiv_coe, hc, map_mul])]
  exact gradedMul_cast (openGrPullback i U hsub) (n : ℤ) (m : ℤ)
    (openChart_preimage i U hsub V hVU) _ _

/-- **The class of `1` is the graded unit.** -/
theorem openGrChartMap_one (a : ↥(chartIdeal i V ^ 0)) (ha : (a : Γ(X, V)) = 1) :
    openGrChartMap i U hsub hcl V hVU 0 a =
      (openGrPullback i U hsub).one.eval (op (i ⁻¹ᵁ V.1)) := by
  rw [openGrChartMap_apply,
    grPullbackMap_one (openIdeal i U hsub) (openLift i U hsub) (openChart U V hVU)
      (openPowerEquiv i U hsub hcl V hVU 0 a)
      (by rw [openPowerEquiv_coe, ha, map_one])]
  exact gradedOne_cast (openGrPullback i U hsub) (openChart_preimage i U hsub V hVU)

/-- **The local presentations commute with restriction between charts.** -/
theorem openGrChartMap_naturality (W : X.affineOpens) (hWU : W.1 ≤ U) (hWV : W.1 ≤ V.1)
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (a : ↥(chartIdeal i V ^ n)) (b : ↥(chartIdeal i W ^ n))
    (hb : (b : Γ(X, W)) = X.presheaf.map (homOfLE hWV).op (a : Γ(X, V))) :
    ((openGrPullback i U hsub).piece (n : ℤ)).val.map (homOfLE hZ).op
        (openGrChartMap i U hsub hcl V hVU n a) =
      openGrChartMap i U hsub hcl W hWU n b := by
  have hZW : openLift i U hsub ⁻¹ᵁ (openChart U W hWU).1 ≤
      openLift i U hsub ⁻¹ᵁ (openChart U V hVU).1 :=
    fun x hx => openChart_mono U V hVU W hWU hWV hx
  rw [openGrChartMap_apply, openGrChartMap_apply,
    ← moduleSectionMap_cast ((openGrPullback i U hsub).piece (n : ℤ))
      (openChart_preimage i U hsub V hVU) (openChart_preimage i U hsub W hWU) hZW hZ,
    grPullbackMap_naturality (openIdeal i U hsub) (openLift i U hsub) n
      (openChart U V hVU) (openChart U W hWU)
      (openChart_mono U V hVU W hWU hWV) hZW
      (openPowerEquiv i U hsub hcl V hVU n a) (openPowerEquiv i U hsub hcl W hWU n b)
      (by rw [openPowerEquiv_coe, openPowerEquiv_coe, hb,
        openSectionEquiv_naturality U V hVU W hWU hWV])]

end Closed

/-! ### Tag 0633 (1), the second identity, at sheaf level -/

section Identification

variable (hcl : IsClosed (Set.range (openLift i U hsub).base))

include hcl

/-- **The chartwise presentation of the pulled-back associated graded algebra**
`i^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)`. -/
def openGrChartPresentation : ChartPresentation i U (openGrPullback i U hsub) where
  negative_isZero := openGrPullback_negative_isZero i U hsub
  map V hVU n := openGrChartMap i U hsub hcl V hVU n
  map_eq_zero_iff V hVU n a := openGrChartMap_eq_zero_iff i U hsub hcl V hVU n a
  map_surjective V hVU n := openGrChartMap_surjective i U hsub hcl V hVU n
  app_surjective V hVU := AlgebraicGeometry.app_surjective_of_closedRestriction i V
    (closedImmersion_chart i U hsub hcl V hVU)
  map_smul V hVU n r a b hb := openGrChartMap_smul i U hsub hcl V hVU n r a b hb
  map_mul V hVU n m a b c hc := openGrChartMap_mul i U hsub hcl V hVU n m a b c hc
  map_one V hVU a ha := openGrChartMap_one i U hsub hcl V hVU a ha
  map_naturality V W hVU hWU hWV hZ n a b hb :=
    openGrChartMap_naturality i U hsub hcl V hVU W hWU hWV hZ n a b hb

/-- **The second identity of Tag 0633 (1).** Let `i : Z ⟶ X` be an immersion, let
`U ⊆ X` be an open with `i(Z) ⊆ U` closed in `U`, and let `ℐ ⊆ 𝒪_U` be the ideal sheaf of the
closed subscheme `i(Z) ⊂ U`. Then the conormal algebra of `i` is the pullback of the associated
graded algebra `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹` of `ℐ`, as sheaves of graded `𝒪_Z`-algebras — the grading
and the multiplication by this isomorphism, the unit by
`Stacks.Conormal.conormalIsoGrPullback_one`.

Stacks states this identity with the topological inverse image `i^{-1}` in place of `i^*`; that
form is `Stacks.Conormal.inverseImageGrIsoConormal`. -/
def conormalIsoGrPullback : (conormalAlgebra i).algebra ≅ openGrPullback i U hsub :=
  gradedAlgebraIsoOfChartPresentations i U hsub
    (conormalChartPresentation i U hsub hcl) (openGrChartPresentation i U hsub hcl)

/-- **The second identity of Tag 0633 (1), unitality.** The identification of the conormal
algebra with `i^*(⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹)` carries the graded unit to the graded unit over every
open: it is an isomorphism of *unital* graded algebras. -/
theorem conormalIsoGrPullback_one (W : Z.Opens) :
    ((conormalIsoGrPullback i U hsub hcl).hom.app 0).val.app (op W)
        ((conormalAlgebra i).algebra.one.eval (op W)) =
      (openGrPullback i U hsub).one.eval (op W) :=
  gradedAlgebraIsoOfChartPresentations_one i U hsub _ _ W

/-- The degree-`n` component of the identification over the preimage of a chart is the
chartwise comparison. -/
theorem conormalIsoGrPullback_hom_app_app (n : ℤ) (V : InnerChart U) :
    ((conormalIsoGrPullback i U hsub hcl).hom.app n).val.app (op (i ⁻¹ᵁ V.1.1)) =
      (chartCompareIsoInt i U (conormalChartPresentation i U hsub hcl)
        (openGrChartPresentation i U hsub hcl) V.1 V.2 n).hom :=
  gradedAlgebraIsoOfChartPresentations_hom_app_app i U hsub _ _ n V

/-- **The two right-hand sides of Tag 0633 (1) agree**: the pullback of the Rees algebra and the
pullback of the associated graded are canonically isomorphic as sheaves of graded
`𝒪_Z`-algebras. -/
def reesPullbackIsoGrPullback : openReesPullback i U hsub ≅ openGrPullback i U hsub :=
  gradedAlgebraIsoOfChartPresentations i U hsub
    (openReesChartPresentation i U hsub hcl) (openGrChartPresentation i U hsub hcl)

/-- The comparison of the two right-hand sides is unital. -/
theorem reesPullbackIsoGrPullback_one (W : Z.Opens) :
    ((reesPullbackIsoGrPullback i U hsub hcl).hom.app 0).val.app (op W)
        ((openReesPullback i U hsub).one.eval (op W)) =
      (openGrPullback i U hsub).one.eval (op W) :=
  gradedAlgebraIsoOfChartPresentations_one i U hsub _ _ W

end Identification

end Stacks.Conormal

end
