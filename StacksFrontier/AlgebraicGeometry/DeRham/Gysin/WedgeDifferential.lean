module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapCutOut
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham differential and the wedge factor of the Gysin formula

Let `π : X ⟶ S` be a morphism of schemes and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`. This file proves that
the wedge factor `ω ↦ ω ∧ d f₁ ∧ ⋯ ∧ d f_c` of the Gysin formula of [Stacks, Tag 0G83] commutes
with the relative de Rham differential:

`d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = d(ω) ∧ d f₁ ∧ ⋯ ∧ d f_c`.

This is the displayed computation in the proof of [Stacks, Tag 0G85], the compatibility of the
Gysin map with the de Rham differentials, stripped of the local cohomology sheaf: the numerator
of the fraction `(ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c)` is differentiated by differentiating `ω̃`
alone.

## Main results

* `AlgebraicGeometry.SheafOfModules.d_exactOne_eq_zero` and
  `AlgebraicGeometry.SheafOfModules.d_one_eq_zero`: an exact one-form `d b` and the unit of
  `Ω^•` are closed.
* `AlgebraicGeometry.SheafOfModules.d_prodDegOne_exactOne_eq_zero`: an ordered wedge
  `d b₁ ∧ ⋯ ∧ d b_n` of exact one-forms is closed.
* `AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_right`: the graded Leibniz rule with
  a closed right factor, `d(ω ∧ η) = d(ω) ∧ η`.
* `AlgebraicGeometry.Scheme.Hom.d_equationsWedge_eval_eq_zero`: the equation wedge
  `d f₁ ∧ ⋯ ∧ d f_c` is closed.
* `AlgebraicGeometry.Scheme.Hom.d_gysinWedgeHom_app`: **the wedge factor of the Gysin formula
  commutes with the de Rham differential**, on every local section.
* `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom_comm_d`: the same commuting square as an equation
  between morphisms of sheaves of `f⁻¹𝒪_S`-modules.

## Implementation notes

The statements are about local sections rather than about morphisms of sheaves, because the de
Rham differential and the wedge factor live in different categories: `d` is a morphism of
sheaves of `f⁻¹𝒪_S`-modules, being only `f⁻¹𝒪_S`-linear, whereas
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` is a morphism of `𝒪_X`-modules. On local sections
the two are maps between the same abelian groups and the square is an honest equation; the
degree bookkeeping is carried by `HomologicalComplex.XIsoOfEq`, exactly as in the graded Leibniz
rule `AlgebraicGeometry.SheafOfModules.d_formProduct` that everything here is read off.

Degrees are natural numbers throughout, since that is the indexing of the de Rham complex and of
`AlgebraicGeometry.SheafOfModules.formProduct`; the degree `(c : ℤ)` of the equation wedge in
`AlgebraicGeometry.Scheme.Hom.equationsWedge` is the coercion of the natural number `c`, so no
transport along `Nat.cast_add` is needed.

Tag 0G85 asserts that the Gysin map `γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})` of
`AlgebraicGeometry.Scheme.Hom.gysinMap` commutes with the de Rham differentials; that statement is
`AlgebraicGeometry.Scheme.Hom.GysinMapCommutesWithDeRham` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham`, proved there by
`AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham`. What is proved here is the third and
last step of the source's proof, the one it calls clear. The action of `ℋ^c_Z` on `d`, a morphism
of sheaves of `f⁻¹𝒪_S`-modules rather than of `𝒪_X`-modules, is
`AlgebraicGeometry.Scheme.Hom.gysinTargetDeRhamMap`; it rests on part (2) of [Stacks, Tag 0G74].

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### Closed forms -/

/-- Two consecutive de Rham differentials kill every local section: `d (d ω) = 0`. This is the
square-zero axiom read on sections. -/
private theorem d_d_app_eq_zero {p : ℕ} (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) :
    (D.differential (p + 1)).val.app U ((D.differential p).val.app U ω) = 0 := by
  have h : ((D.differential p ≫ D.differential (p + 1)).val.app U) ω = 0 := by
    rw [D.squared p]; rfl
  rwa [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at h

/-- **An exact one-form is closed:** `d (d b) = 0` for a local section `b` of the structure
sheaf. The one-form `d b` is itself the differential of the degree-zero form `b`, by the
de Rham rule in degree zero, so this is the square-zero axiom. -/
theorem d_exactOne_eq_zero (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    ((deRhamComplex B D).d 1 (1 + 1)).val.app U (exactOne B U b) = 0 := by
  rw [deRhamComplex_d, ← eq_of_heq (deRhamComplex_degreeZero B D U b), deRhamComplex_d]
  exact d_d_app_eq_zero B D U _

/-- **The unit of `Ω^•` is closed:** `d 1 = 0`. In degree zero the differential is the universal
relative derivation, and a derivation kills the unit of the ring. -/
theorem d_one_eq_zero (U : (Opens X.carrier)ᵒᵖ) :
    ((deRhamComplex B D).d 0 (0 + 1)).val.app U (B.exterior.one.eval U) = 0 := by
  have hsmul : (1 : X.sheaf.obj.obj U) • B.exterior.one.eval U = B.exterior.one.eval U :=
    one_smul _ _
  have hd1 : (PresheafOfModulesOfCommRing.Derivation'.app (universalDerivation.{u, u, u} φ) U).d
      (1 : X.sheaf.obj.obj U) = 0 := PresheafOfModulesOfCommRing.Derivation.d_one _ U
  rw [← hsmul, eq_of_heq (deRhamComplex_degreeZero B D U 1), exactOne, hd1, map_zero]
  exact rfl

/-- The wedge product of a local section with zero vanishes. -/
private theorem formProduct_zero_right (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) :
    formProduct B p q U ω (0 : (B.exteriorPower q).val.obj U) = 0 :=
  map_zero _

/-- The wedge product of zero with a local section vanishes. -/
theorem formProduct_zero_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (0 : (B.exteriorPower p).val.obj U) η = 0 :=
  congrFun (congrArg (fun k : (B.exteriorPower q).val.obj U →+ _ =>
    ⇑k) (map_zero ((B.exterior.mul (p : ℤ) (q : ℤ)).app U))) η

/-- **The graded Leibniz rule with a closed right factor:** `d(ω ∧ η) = d(ω) ∧ η` when `dη = 0`.
The second summand of the Leibniz rule
`d(ω ∧ η) = d(ω) ∧ η + (-1)^p ω ∧ d(η)` vanishes. -/
theorem d_formProduct_of_closed_right (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (hη : ((deRhamComplex B D).d q (q + 1)).val.app U η = 0) :
    ((deRhamComplex B D).d (p + q) (p + q + 1)).val.app U (formProduct B p q U ω η) =
      ((deRhamComplex B D).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom.val.app U
        (formProduct B (p + 1) q U (((deRhamComplex B D).d p (p + 1)).val.app U ω) η) := by
  have hz : formProduct B p (q + 1) U ω
      (((deRhamComplex B D).d q (q + 1)).val.app U η) = 0 := by
    rw [hη]; exact formProduct_zero_right B p (q + 1) U ω
  rw [d_formProduct B D p q U ω η, hz]
  refine add_eq_left.mpr ?_
  rw [show ((deRhamComplex B D).XIsoOfEq
      (show p + (q + 1) = p + q + 1 by omega)).hom.val.app U
      (0 : (B.exteriorPower (p + (q + 1))).val.obj U) = 0 from map_zero _, smul_zero]

/-- **An ordered wedge of exact one-forms is closed:** `d(d b₁ ∧ ⋯ ∧ d b_n) = 0`. Induction on
`n`: the unit is closed, and the Leibniz rule turns the inductive step into the closedness of the
new factor `d b_n` together with the inductive hypothesis. -/
theorem d_prodDegOne_exactOne_eq_zero (n : ℕ) (U : (Opens X.carrier)ᵒᵖ) :
    ∀ b : Fin n → X.sheaf.obj.obj U,
      ((deRhamComplex B D).d n (n + 1)).val.app U
        (B.exterior.prodDegOne U n fun i => exactOne B U (b i)) = 0 := by
  induction n with
  | zero => exact fun _ => d_one_eq_zero B D U
  | succ n ih =>
      intro b
      rw [_root_.SheafOfModules.GradedAlgebra.prodDegOne_succ,
        show ((B.exterior.mul (n : ℤ) 1).app U
            (B.exterior.prodDegOne U n fun i => exactOne B U (b i.castSucc))
            (exactOne B U (b (Fin.last n)))) =
          formProduct B n 1 U
            (B.exterior.prodDegOne U n fun i => exactOne B U (b i.castSucc))
            (exactOne B U (b (Fin.last n))) from rfl,
        d_formProduct_of_closed_right B D n 1 U _ _ (d_exactOne_eq_zero B D U _)]
      have hzero : formProduct B (n + 1) 1 U
          (((deRhamComplex B D).d n (n + 1)).val.app U
            (B.exterior.prodDegOne U n fun i => exactOne B U (b i.castSucc)))
          (exactOne B U (b (Fin.last n))) = 0 := by
        rw [ih fun i => b i.castSucc]
        exact formProduct_zero_left B (n + 1) 1 U _
      rw [hzero]
      exact map_zero _

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- **The equation wedge is closed:** `d(d f₁ ∧ ⋯ ∧ d f_c) = 0`. It is an ordered wedge of exact
one-forms, by `AlgebraicGeometry.Scheme.Hom.equationsWedge_eval`. -/
theorem d_equationsWedge_eval_eq_zero (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (U : X.Opensᵒᵖ) :
    ((deRhamComplex π).d c (c + 1)).val.app U ((equationsWedge π f).eval U) = 0 :=
  AlgebraicGeometry.SheafOfModules.d_prodDegOne_exactOne_eq_zero (deRhamAlgebras π)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) c U
    fun j => X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j)

/-- **The wedge factor of the Gysin formula commutes with the de Rham differential.** On a local
`p`-form `ω` on `X`,

`d(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) = d(ω) ∧ d f₁ ∧ ⋯ ∧ d f_c`,

the two sides being compared in degree `p + c + 1` through the identification of that degree
with `p + 1 + c`. This is the last step of the proof of [Stacks, Tag 0G85]: the equation wedge is
closed, so the Leibniz rule leaves only the term in which `ω` is differentiated. -/
theorem d_gysinWedgeHom_app (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ) (U : X.Opensᵒᵖ)
    (ω : (relativeDifferentialForms π (p : ℤ)).val.obj U) :
    ((deRhamComplex π).d (p + c) (p + c + 1)).val.app U
          ((gysinWedgeHom π f (p : ℤ)).val.app U ω) =
      ((deRhamComplex π).XIsoOfEq (show p + 1 + c = p + c + 1 by omega)).hom.val.app U
        ((gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)).val.app U
          (((deRhamComplex π).d p (p + 1)).val.app U ω)) :=
  AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_right (deRhamAlgebras π)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) p c U ω
    ((equationsWedge π f).eval U) (d_equationsWedge_eval_eq_zero π f U)

/-- **The wedge factor of the Gysin formula commutes with the de Rham differential**, as an
equation between morphisms of sheaves of `f⁻¹𝒪_S`-modules. Right multiplication by
`d f₁ ∧ ⋯ ∧ d f_c` is `𝒪_X`-linear, hence in particular `f⁻¹𝒪_S`-linear, and as such it is a
morphism of the relative de Rham complex of degree `c`: the square

`Ω^p ⟶ Ω^{p+c}`, `Ω^{p+1} ⟶ Ω^{p+1+c}`

with the de Rham differentials as vertical arrows commutes, the right-hand degree being read in
the spelling `p + c + 1` of the complex. This is the degreewise statement of the first two steps
of the proof of [Stacks, Tag 0G85] for the wedge factor of the Gysin formula. -/
theorem gysinWedgeHom_comm_d (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (_root_.SheafOfModules.restrictScalars
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom
            (φ := inverseImageStructureMap π))).map (gysinWedgeHom π f (p : ℤ)) ≫
        (deRhamComplex π).d (p + c) (p + c + 1) =
      (deRhamComplex π).d p (p + 1) ≫
        (_root_.SheafOfModules.restrictScalars
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom
                (φ := inverseImageStructureMap π))).map
            (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          ((deRhamComplex π).XIsoOfEq (show p + 1 + c = p + c + 1 by omega)).hom :=
  _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ω => d_gysinWedgeHom_app π f p U ω))

end AlgebraicGeometry.Scheme.Hom

/-
Tag 0G84 is the numbered *equation* inside Remark 0G83, not a lemma: it is the display
`γ^p_{f_1, …, f_c} : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`. The map itself is
`AlgebraicGeometry.Scheme.Hom.gysinMap`, constructed under Tag 0G83.
-/
add_to_stacks 0G84 "the displayed map γ^p_{f_1, …, f_c} : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S}) of \
Remark 0G83, with both sheaves read on X through their direct images, that is as \
i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S}); both direct images are faithful, and no descent of \
either sheaf to Z is available, source and target being modules over different rings on Z. \
No hypothesis beyond the source's own, that the ideal sheaf of i is generated by \
f_1, …, f_c." AlgebraicGeometry.Scheme.Hom.gysinMap

end
