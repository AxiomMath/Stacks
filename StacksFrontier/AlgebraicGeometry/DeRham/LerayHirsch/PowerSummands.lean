module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `ξ̃` of the Leray--Hirsch theorem for the powers of one class

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and let `ξ ∈ H^d_{dR}(X/S)`. For the
classes `ξ^t ∈ H^{dt}_{dR}(X/S)`, `0 ≤ t < r`, the morphism of Proposition 0FMR is

`ξ̃ : ⨁_{t < r} Ω^•_{Y/S}[-dt] ⟶ Rf_*Ω^•_{X/S}`

(`AlgebraicGeometry.DeRhamLerayHirsch.lerayHirschPowerMorphism`). Remark 0FUN computes it, for the
projective bundle `f : ℙ(ℰ) ⟶ X` and `ξ = c₁^{dR}(𝒪(1))`, `d = 2`; its computations hold for any
class `ξ`, and they are proved here in that generality. With `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[d]` the
morphism of Remark 0FU7 and `Rf_*ξ' : Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}[d]`
(`AlgebraicGeometry.DeRhamLerayHirsch.classDirectImageEndo`):

* the summand `t = 0` of `ξ̃` is the canonical map `c : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}`;
* the summand `t` of `ξ̃` is `Rf_*ξ'[-d] ∘ ⋯ ∘ Rf_*ξ'[-dt] ∘ c[-dt]`;
* with `M = ⨁_{1 ≤ t < r} Ω^•_{Y/S}[-dt]` and `K = ⨁_{0 ≤ t < r - 1} Ω^•_{Y/S}[-dt]`, viewed in
  the source of `ξ̃`, and `id : K ⟶ M[d]` identifying the summand `t` of `K` with the summand
  `t + 1` of `M`, the square `Rf_*ξ' ∘ ξ̃|_K = (ξ̃|_M)[d] ∘ id` commutes;
* if `ξ̃` is an isomorphism and `r ≥ 1`, so is `c ⊕ ξ̃|_M : Ω^•_{Y/S} ⊕ M ⟶ Rf_*Ω^•_{X/S}`.

The source is `ξ'[d(t - 1)] ∘ ⋯ ∘ ξ'[d] ∘ ξ' = (ξ^t)'`
(`AlgebraicGeometry.SheafOfModules.iterate_deRhamClassMorphism`), so that `Rf_*` of it is the
`t`-fold composite of `Rf_*ξ'`, whose translate by `-dt` is the composite of the statement.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.classDirectImageEndo`: `Rf_*ξ'`.
* `AlgebraicGeometry.DeRhamLerayHirsch.lerayHirschPowerMorphism`: `ξ̃` for `ξ^0, …, ξ^{r - 1}`.
* `AlgebraicGeometry.DeRhamLerayHirsch.powerSummandsTail`, `powerSummandsInit`: `M` and `K`, with
  their inclusions `powerSummandsTailι`, `powerSummandsInitι` and the identification
  `powerSummandsInitIso : K ⟶ M[d]`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.ι_lerayHirschPowerMorphism_zero`: the summand `t = 0`.
* `AlgebraicGeometry.DeRhamLerayHirsch.ι_lerayHirschPowerMorphism`: the summand `t`.
* `AlgebraicGeometry.DeRhamLerayHirsch.lerayHirschPowerMorphism_comp_classDirectImageEndo`: the
  square.
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_biprodDesc_of_isIso_lerayHirschPowerMorphism`:
  `c ⊕ ξ̃|_M` is an isomorphism when `ξ̃` is one.

## References

* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The cup power `ξ^t ∈ H^{dt}_{dR}(X/S)` of a class `ξ ∈ H^d_{dR}(X/S)`. -/
abbrev classPow (p : X ⟶ S) (d : ℕ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) (d : ℤ)) (t : ℕ) :
    SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) ((d * t : ℕ) : ℤ) :=
  SheafOfModules.deRhamCohomologyPow _ _ d ξ t

/-- **`Rf_*ξ' : Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}[n]`**, the direct image of the morphism
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` of Remark 0FU7, followed by the commutation of `Rf_*` with the
translation. -/
def classDirectImageEndo (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    ShiftedHom ((relativeDirectImage f g).obj (deRhamObject (f ≫ g)))
      ((relativeDirectImage f g).obj (deRhamObject (f ≫ g))) n :=
  ShiftedHom.map (classMorphism (f ≫ g) n ξ) (relativeDirectImage f g)

/-- `ξ̃ = c ∘ Rf_*ξ'`, the canonical map followed by `Rf_*ξ'`. -/
theorem classDirectImageMorphism_eq (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    classDirectImageMorphism f g n ξ = deRhamDirectImageMap f g ≫ classDirectImageEndo f g n ξ :=
  rfl

variable (d : ℕ)
  (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (d : ℤ))

/-- **The summand `ξ̃_t[-dt]` attached to `ξ^t` is `Rf_*ξ'[-d] ∘ ⋯ ∘ Rf_*ξ'[-dt] ∘ c[-dt]`.** -/
theorem classDirectImageSummand_classPow (t : ℕ) :
    classDirectImageSummand f g ((d * t : ℕ) : ℤ) (classPow (f ≫ g) d ξ t) =
      (deRhamDirectImageMap f g)⟦-((d * t : ℕ) : ℤ)⟧' ≫
        ShiftedHom.negIterate d (classDirectImageEndo f g d ξ) t := by
  have h := SheafOfModules.iterate_deRhamClassMorphism (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) d ξ t
  rw [ShiftedHom.negIterate_eq, classDirectImageEndo, ← ShiftedHom.map_iterate,
    show ShiftedHom.iterate d (classMorphism (f ≫ g) d ξ) t =
      classMorphism (f ≫ g) _ (classPow (f ≫ g) d ξ t) from h]
  simp only [classDirectImageSummand, classDirectImageMorphism, ShiftedHom.map, Functor.map_comp,
    Category.assoc]

/-- **`Rf_*ξ' ∘ ξ̃_t[-dt] = ξ̃_{t + 1}[-d(t + 1)][d]`**, through
`Ω^•_{Y/S}[-dt] = Ω^•_{Y/S}[-d(t + 1)][d]`. -/
theorem classDirectImageSummand_classPow_comp (t : ℕ) :
    classDirectImageSummand f g ((d * t : ℕ) : ℤ) (classPow (f ≫ g) d ξ t) ≫
        classDirectImageEndo f g d ξ =
      (shiftFunctorAdd' _ (-((d * (t + 1) : ℕ) : ℤ)) (d : ℤ) (-((d * t : ℕ) : ℤ))
          (by push_cast; ring)).hom.app (deRhamObject g) ≫
        (classDirectImageSummand f g ((d * (t + 1) : ℕ) : ℤ)
          (classPow (f ≫ g) d ξ (t + 1)))⟦(d : ℤ)⟧' := by
  rw [classDirectImageSummand_classPow, classDirectImageSummand_classPow, Category.assoc,
    ShiftedHom.negIterate_comp, Functor.map_comp]
  exact (shiftFunctorAdd' _ _ _ _ _).hom.naturality_assoc (deRhamDirectImageMap f g) _

/-! ### The morphism `ξ̃` for `ξ^0, …, ξ^{r - 1}` -/

variable (r : ℕ)

/-- **The morphism `ξ̃ : ⨁_{t < r} Ω^•_{Y/S}[-dt] ⟶ Rf_*Ω^•_{X/S}`** of Proposition 0FMR for the
classes `ξ^t ∈ H^{dt}_{dR}(X/S)`, `0 ≤ t < r`. -/
abbrev lerayHirschPowerMorphism :
    (⨁ fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟶
      (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) :=
  lerayHirschMorphism f g (fun t : Fin r => d * (t : ℕ)) fun t => classPow (f ≫ g) d ξ t

/-- **The summand `t` of `ξ̃` is `Rf_*ξ'[-d] ∘ ⋯ ∘ Rf_*ξ'[-dt] ∘ c[-dt]`.** -/
@[stacks 0FUN "the restriction of xi~ to the summand Omega_{X/S}[-2t] is \
Rp_*xi'[-2] o ... o Rp_*xi'[-2t] o c_{P/X}[-2t]; stated for every morphism p : P -> X over S, \
every class xi of every degree d and every number r of summands"]
theorem ι_lerayHirschPowerMorphism (t : Fin r) :
    biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) t ≫
        lerayHirschPowerMorphism f g d ξ r =
      (deRhamDirectImageMap f g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧' ≫
        ShiftedHom.negIterate d (classDirectImageEndo f g d ξ) t := by
  rw [lerayHirschPowerMorphism, lerayHirschMorphism, biproduct.ι_desc]
  exact classDirectImageSummand_classPow f g d ξ t

/-- **The summand `t = 0` of `ξ̃` is the canonical map `c : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}`**, read on
`Ω^•_{Y/S}[0] = Ω^•_{Y/S}`. -/
@[stacks 0FUN "the arrow of xi~ for t = 0 is the canonical map c_{P/X} of Section 07HX; stated for \
every morphism p : P -> X over S and every class xi"]
theorem ι_lerayHirschPowerMorphism_zero (hr : 0 < r) :
    biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟨0, hr⟩ ≫
        lerayHirschPowerMorphism f g d ξ r =
      (shiftFunctorZero' _ (-((d * 0 : ℕ) : ℤ)) (by simp)).hom.app (deRhamObject g) ≫
        deRhamDirectImageMap f g := by
  rw [ι_lerayHirschPowerMorphism]
  exact (shiftFunctorZero' _ _ _).hom.naturality (deRhamDirectImageMap f g)

/-- **`M = ⨁_{1 ≤ t < r} Ω^•_{Y/S}[-dt]`**, indexed by `t - 1`. -/
abbrev powerSummandsTail :=
  ⨁ fun t : Fin (r - 1) => (deRhamObject g)⟦-((d * ((t : ℕ) + 1) : ℕ) : ℤ)⟧

/-- **`K = ⨁_{0 ≤ t < r - 1} Ω^•_{Y/S}[-dt]`.** -/
abbrev powerSummandsInit :=
  ⨁ fun t : Fin (r - 1) => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧

/-- The inclusion of `M` into the source `⨁_{t < r} Ω^•_{Y/S}[-dt]` of `ξ̃`. -/
def powerSummandsTailι :
    powerSummandsTail g d r ⟶ ⨁ fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧ :=
  biproduct.desc fun t => biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧)
    ⟨(t : ℕ) + 1, by omega⟩

/-- The inclusion of `K` into the source `⨁_{t < r} Ω^•_{Y/S}[-dt]` of `ξ̃`. -/
def powerSummandsInitι :
    powerSummandsInit g d r ⟶ ⨁ fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧ :=
  biproduct.desc fun t => biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧)
    ⟨(t : ℕ), by omega⟩

/-- **The identification `id : K ⟶ M[d]`** sending the summand `Ω^•_{Y/S}[-dt]` of `K` to the
summand `Ω^•_{Y/S}[-d(t + 1)][d] = Ω^•_{Y/S}[-dt]` of `M[d]`. -/
def powerSummandsInitIso : powerSummandsInit g d r ⟶ (powerSummandsTail g d r)⟦(d : ℤ)⟧ :=
  biproduct.desc fun t =>
    (shiftFunctorAdd' _ (-((d * ((t : ℕ) + 1) : ℕ) : ℤ)) (d : ℤ) (-((d * (t : ℕ) : ℕ) : ℤ))
        (by push_cast; ring)).hom.app (deRhamObject g) ≫
      (biproduct.ι (fun t : Fin (r - 1) => (deRhamObject g)⟦-((d * ((t : ℕ) + 1) : ℕ) : ℤ)⟧)
        t)⟦(d : ℤ)⟧'

/-- **The square of Remark 0FUN commutes**: `Rf_*ξ' ∘ ξ̃|_K = (ξ̃|_M)[d] ∘ id`. -/
@[stacks 0FUN "the square K -> M[2], Rp_*Omega_{P/S} -> Rp_*Omega_{P/S}[2] commutes: \
Rp_*xi' o xi~|_K = (xi~|_M)[2] o id; stated for every morphism p : P -> X over S, every class xi \
of every degree d and every number r of summands"]
theorem lerayHirschPowerMorphism_comp_classDirectImageEndo :
    powerSummandsInitι g d r ≫ lerayHirschPowerMorphism f g d ξ r ≫ classDirectImageEndo f g d ξ =
      powerSummandsInitIso g d r ≫
        (powerSummandsTailι g d r ≫ lerayHirschPowerMorphism f g d ξ r)⟦(d : ℤ)⟧' := by
  refine biproduct.hom_ext' _ _ fun t => ?_
  simp only [powerSummandsInitι, powerSummandsInitIso, biproduct.ι_desc_assoc, Category.assoc]
  rw [← Functor.map_comp, ← Category.assoc (biproduct.ι _ t), powerSummandsTailι,
    biproduct.ι_desc, ← Category.assoc, ι_lerayHirschPowerMorphism, ι_lerayHirschPowerMorphism,
    ← classDirectImageSummand_classPow, ← classDirectImageSummand_classPow]
  exact classDirectImageSummand_classPow_comp f g d ξ t

/-- The projection of the source `⨁_{t < r} Ω^•_{Y/S}[-dt]` of `ξ̃` onto `M`. -/
def powerSummandsTailπ :
    (⨁ fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟶ powerSummandsTail g d r :=
  biproduct.lift fun t => biproduct.π (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧)
    ⟨(t : ℕ) + 1, by omega⟩

/-- The inclusion of `M` followed by the projection onto the summand `t = 0` is zero. -/
theorem powerSummandsTailι_π_zero (hr : 0 < r) :
    powerSummandsTailι g d r ≫
      biproduct.π (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟨0, hr⟩ = 0 := by
  refine biproduct.hom_ext' _ _ fun s => ?_
  rw [powerSummandsTailι, biproduct.ι_desc_assoc, Limits.comp_zero,
    biproduct.ι_π_ne _ (by simp [Fin.ext_iff])]

/-- The inclusion of the summand `t = 0` followed by the projection onto `M` is zero. -/
theorem ι_zero_powerSummandsTailπ (hr : 0 < r) :
    biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟨0, hr⟩ ≫
      powerSummandsTailπ g d r = 0 := by
  refine biproduct.hom_ext _ _ fun s => ?_
  rw [powerSummandsTailπ, Category.assoc, biproduct.lift_π, Limits.zero_comp,
    biproduct.ι_π_ne _ (by simp [Fin.ext_iff])]

/-- The inclusion of the summand `s + 1` followed by the projection onto `M` is the inclusion of
the summand of `M` indexed by `s`. -/
theorem ι_succ_powerSummandsTailπ (s : Fin (r - 1)) :
    biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧)
        ⟨(s : ℕ) + 1, by omega⟩ ≫ powerSummandsTailπ g d r =
      biproduct.ι (fun t : Fin (r - 1) => (deRhamObject g)⟦-((d * ((t : ℕ) + 1) : ℕ) : ℤ)⟧) s := by
  refine biproduct.hom_ext _ _ fun s' => ?_
  rw [powerSummandsTailπ, Category.assoc, biproduct.lift_π]
  by_cases h : s = s'
  · subst h
    rw [biproduct.ι_π_self, biproduct.ι_π_self]
  · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne _ (by simpa [Fin.ext_iff] using h)]

/-- The projection onto `M` is a retraction of the inclusion of `M`. -/
theorem powerSummandsTailι_π :
    powerSummandsTailι g d r ≫ powerSummandsTailπ g d r = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun s => ?_
  rw [powerSummandsTailι, biproduct.ι_desc_assoc, ι_succ_powerSummandsTailπ, Category.comp_id]

/-- The source `⨁_{t < r} Ω^•_{Y/S}[-dt]` of `ξ̃` is the sum of its summand `t = 0`, read as
`Ω^•_{Y/S}`, and of `M`. -/
def powerSummandsSplit (hr : 0 < r) :
    deRhamObject g ⊞ powerSummandsTail g d r ≅
      ⨁ fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧ where
  hom := biprod.desc ((shiftFunctorZero' _ (-((d * 0 : ℕ) : ℤ)) (by simp)).inv.app
        (deRhamObject g) ≫
      biproduct.ι (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟨0, hr⟩)
    (powerSummandsTailι g d r)
  inv := biprod.lift
    (biproduct.π (fun t : Fin r => (deRhamObject g)⟦-((d * (t : ℕ) : ℕ) : ℤ)⟧) ⟨0, hr⟩ ≫
      (shiftFunctorZero' _ (-((d * 0 : ℕ) : ℤ)) (by simp)).hom.app (deRhamObject g))
    (powerSummandsTailπ g d r)
  hom_inv_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, biprod.lift_fst, biproduct.ι_π_self_assoc,
          Iso.inv_hom_id_app, biprod.inl_fst]
        rfl
      · rw [Category.assoc, Category.assoc, biprod.lift_snd, ι_zero_powerSummandsTailπ,
          Limits.comp_zero, biprod.inl_snd]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, reassoc_of% powerSummandsTailι_π_zero,
          Limits.zero_comp, biprod.inr_fst]
      · rw [Category.assoc, biprod.lift_snd, powerSummandsTailι_π, biprod.inr_snd]
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun t => ?_
    rw [biprod.lift_desc, Category.comp_id, Preadditive.comp_add]
    obtain ⟨t, ht⟩ := t
    rcases t with _ | t
    · simp only [Category.assoc]
      rw [biproduct.ι_π_self_assoc, Iso.hom_inv_id_app_assoc,
        reassoc_of% ι_zero_powerSummandsTailπ, Limits.zero_comp, add_zero]
    · simp only [Category.assoc]
      rw [biproduct.ι_π_ne_assoc _ (by simp [Fin.ext_iff]), Limits.zero_comp, zero_add,
        reassoc_of% ι_succ_powerSummandsTailπ g d r ⟨t, by omega⟩, powerSummandsTailι,
        biproduct.ι_desc]

/-- For `r ≥ 1`, `c ⊕ ξ̃|_M : Ω^•_{Y/S} ⊕ M ⟶ Rf_*Ω^•_{X/S}` is `ξ̃` precomposed with the
isomorphism `powerSummandsSplit`. -/
theorem biprodDesc_eq_powerSummandsSplit_hom_comp (hr : 0 < r) :
    biprod.desc (deRhamDirectImageMap f g)
        (powerSummandsTailι g d r ≫ lerayHirschPowerMorphism f g d ξ r) =
      (powerSummandsSplit g d r hr).hom ≫ lerayHirschPowerMorphism f g d ξ r := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp only [biprod.inl_desc, powerSummandsSplit, biprod.inl_desc_assoc, Category.assoc,
      ι_lerayHirschPowerMorphism_zero f g d ξ r hr, Iso.inv_hom_id_app_assoc]
  · rw [biprod.inr_desc, powerSummandsSplit, biprod.inr_desc_assoc]

/-- **`c ⊕ ξ̃|_M : Ω^•_{Y/S} ⊕ M ⟶ Rf_*Ω^•_{X/S}` is an isomorphism** when `ξ̃` is one and
`r ≥ 1`. -/
theorem isIso_biprodDesc_of_isIso_lerayHirschPowerMorphism (hr : 0 < r)
    [IsIso (lerayHirschPowerMorphism f g d ξ r)] :
    IsIso (biprod.desc (deRhamDirectImageMap f g)
      (powerSummandsTailι g d r ≫ lerayHirschPowerMorphism f g d ξ r)) := by
  rw [biprodDesc_eq_powerSummandsSplit_hom_comp f g d ξ r hr]
  infer_instance

end AlgebraicGeometry.DeRhamLerayHirsch

end
