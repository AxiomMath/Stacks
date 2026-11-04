module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGA
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Pullback

/-!
# The Leray--Hirsch morphism for Hodge cohomology

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, let `ℋ_{X/S} = ⨁_p Ω^p_{X/S}[-p]` be
the Hodge complex of `X` over `S`, with zero differential, a sheaf of differential graded
`(f ≫ g)⁻¹𝒪_S`-algebras, and let `ξ_i ∈ H^{n_i}(X, ℋ_{X/S})`. The argument of Proposition 0FMR
runs on `ℋ` in place of the de Rham complex. For each `i`, Section 0FU3 attaches to `ξ_i` a
morphism `ξ'_i : ℋ_{X/S} ⟶ ℋ_{X/S}[n_i]` of `D(X, (f ≫ g)⁻¹𝒪_S)`, and one forms the composite

`ξ̃_i : ℋ_{Y/S} ⟶ Rf_*ℋ_{X/S} ⟶ Rf_*ℋ_{X/S}[n_i]`

of the canonical map with `Rf_*ξ'_i`, in `D(Y, g⁻¹𝒪_S)`, and the morphism

`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}`.

Through the Leray identification `RΓ(Y, Rf_*ℋ_{X/S}) = RΓ(X, ℋ_{X/S})`, the morphism `ξ̃` induces
on `H^k(Y, -)` the map `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`. In particular, if `ξ̃` is an isomorphism, then
this map is bijective in every degree.

## Main definitions

* `Stacks.HodgeWeil.hodgeObject`: the Hodge complex `ℋ_{X/S}` as an object of
  `D(X, p⁻¹𝒪_S)`.
* `Stacks.HodgeWeil.hodgeDirectImageMap`: the canonical map `ℋ_{Y/S} ⟶ Rf_*ℋ_{X/S}`.
* `Stacks.HodgeWeil.hodgeDgaPullback`: the pullback `f^* : H^m(Y, ℋ_{Y/S}) ⟶ H^m(X, ℋ_{X/S})`.
* `Stacks.HodgeWeil.hodgeClassDirectImageMorphism`: `ξ̃_i`.
* `Stacks.HodgeWeil.hodgeLerayHirschMorphism`: `ξ̃`.

## Main results

* `Stacks.HodgeWeil.lerayCohomologyIso_hodgeDirectImageMap`: the canonical map induces `f^*` on
  cohomology.
* `Stacks.HodgeWeil.lerayCohomologyIso_hodgeClassDirectImageSummand`: `ξ̃_i[-n_i]` induces
  `a ↦ ξ_i ∪ f^*a`.
* `Stacks.HodgeWeil.sum_dgaCohomologyCup_eq_lerayCohomologyIso`: `H^k(Y, ξ̃)` is
  `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`.
* `Stacks.HodgeWeil.bijective_cohomologyFunctor_hodgeLerayHirschMorphism_iff`: `H^k(Y, ξ̃)` is
  bijective if and only if `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in degree `k`.
* `Stacks.HodgeWeil.bijective_sum_dgaCohomologyCup_of_isIso`: if `ξ̃` is an isomorphism, then
  `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in every degree.

## Implementation notes

The direct image is `AlgebraicGeometry.DeRhamLerayHirsch.relativeDirectImage`, taken along the
morphism of ringed spaces `AlgebraicGeometry.DeRhamLerayHirsch.baseMap` of the square
`(f, 𝟙 S)`, and the canonical map of Hodge complexes is `Stacks.HodgeWeil.hodgeDgaPushforward` of
the same square. The pullback `f^*` is `Stacks.HodgeWeil.cohomologyPullback` along that map of
complexes; it is by definition the canonical map followed by the Leray identification, so the
first step of the computation holds by definition. The cup product is
`Stacks.HodgeWeil.dgaCohomologyCup` of the Hodge differential graded algebra, and the action of
`ξ'_i` on cohomology is property (3) of Remark 0FU7,
`Stacks.HodgeWeil.hodgeDgaCup_eq_dgaClassMorphism`.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules
open AlgebraicGeometry.DeRhamLerayHirsch (baseMap relativeDirectImage cohomologyFunctor)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso lerayCohomologyIso_naturality_apply
  lerayCohomologyIso_shift)
open Stacks.Cohomology.GlobalKunneth (baseSections)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.HodgeWeil

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-! ### The morphism `ξ̃` -/

/-- The Hodge complex `ℋ_{X/S} = ⨁_p Ω^p_{X/S}[-p]` as an object of `D(X, p⁻¹𝒪_S)`. -/
abbrev hodgeObject (p : X ⟶ S) :
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase p))) :=
  DerivedCategory.Q.obj (hodgeDGA (Scheme.Hom.deRhamAlgebras p)).complex

/-- **The canonical map `ℋ_{Y/S} ⟶ Rf_*ℋ_{X/S}`** in `D(Y, g⁻¹𝒪_S)`: the canonical map of Hodge
complexes `ℋ_{Y/S} ⟶ f_*ℋ_{X/S}` followed by the comparison `f_* ⟶ Rf_*`. -/
def hodgeDirectImageMap :
    hodgeObject g ⟶ (relativeDirectImage f g).obj (hodgeObject (f ≫ g)) :=
  DerivedCategory.Q.map (hodgeDgaPushforward f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm) ≫
    pushforwardComparisonQ (baseMap f g) (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))).complex

/-- **The pullback `f^* : H^m(Y, ℋ_{Y/S}) ⟶ H^m(X, ℋ_{X/S})`** of Hodge cohomology, the pullback
along the canonical map of Hodge complexes of the square `(f, 𝟙 S)`. -/
abbrev hodgeDgaPullback (m : ℤ) (a : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) m) :
    dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) m :=
  (cohomologyPullback (baseMap f g)
    (hodgeDgaPushforward f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm) m).hom a

/-- The morphism `ξ' : ℋ_{X/S} ⟶ ℋ_{X/S}[n]` of Section 0FU3 attached to `ξ ∈ H^n(X, ℋ_{X/S})`. -/
abbrev hodgeClassMorphism (p : X ⟶ S) (n : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) n) :
    hodgeObject p ⟶ (hodgeObject p)⟦n⟧ :=
  dgaClassMorphism (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) n ξ

/-- `ξ̃ : ℋ_{Y/S} ⟶ Rf_*ℋ_{X/S}[n]`, the canonical map followed by `Rf_*ξ'`. -/
def hodgeClassDirectImageMorphism (n : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    hodgeObject g ⟶ ((relativeDirectImage f g).obj (hodgeObject (f ≫ g)))⟦n⟧ :=
  hodgeDirectImageMap f g ≫ (relativeDirectImage f g).map (hodgeClassMorphism (f ≫ g) n ξ) ≫
    ((relativeDirectImage f g).commShiftIso n).hom.app _

/-- `ξ̃[-n] : ℋ_{Y/S}[-n] ⟶ Rf_*ℋ_{X/S}`. -/
def hodgeClassDirectImageSummand (n : ℤ)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    (hodgeObject g)⟦-n⟧ ⟶ (relativeDirectImage f g).obj (hodgeObject (f ≫ g)) :=
  (hodgeClassDirectImageMorphism f g n ξ)⟦-n⟧' ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

/-- **The morphism `ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}`** of Proposition 0FMR, for
Hodge cohomology. -/
def hodgeLerayHirschMorphism {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) :
    (⨁ fun i => (hodgeObject g)⟦-(n i : ℤ)⟧) ⟶
      (relativeDirectImage f g).obj (hodgeObject (f ≫ g)) :=
  biproduct.desc fun i => hodgeClassDirectImageSummand f g (n i) (ξ i)

/-! ### The morphism `ξ̃` on cohomology -/

/-- **The canonical map `ℋ_{Y/S} ⟶ Rf_*ℋ_{X/S}` induces the pullback on Hodge cohomology**: on
`H^m(Y, -)`, followed by the Leray identification `H^m(Y, Rf_*ℋ_{X/S}) = H^m(X, ℋ_{X/S})`, it is
`f^* : H^m(Y, ℋ_{Y/S}) ⟶ H^m(X, ℋ_{X/S})`. -/
theorem lerayCohomologyIso_hodgeDirectImageMap (m : ℤ)
    (a : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) m) :
    (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) m).hom
        (((DerivedCategory.homologyFunctor _ m).map
          ((baseSections (inverseImageBase g)).map (hodgeDirectImageMap f g))).hom a) =
      hodgeDgaPullback f g m a :=
  rfl

/-- **`ξ'` on cohomology is the cup product with `ξ`** (Remark 0FU7, property (3)), read in
degree `k = n + m`. -/
theorem shiftHomologyIsoU_hodgeClassMorphism (p : X ⟶ S) (n m k : ℤ) (h : n + m = k)
    (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) n)
    (η : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) m) :
    (shiftHomologyIsoU (baseSections (inverseImageBase p)) (hodgeObject p) n m k h).hom
        (((DerivedCategory.homologyFunctor _ m).map
          ((baseSections (inverseImageBase p)).map (hodgeClassMorphism p n ξ))).hom η) =
      (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras p))) h)).hom
        (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras p)) n m ξ η) := by
  subst h
  rw [← hodgeDgaCup, hodgeDgaCup_eq_dgaClassMorphism, eqToHom_refl]
  rfl

/-- **`ξ̃_i[-n]` on cohomology is `a ↦ ξ ∪ f^*a`** (the computation in the proof of
Proposition 0FMR, for Hodge cohomology): the map
`H^k(Y, ℋ_{Y/S}[-n]) ⟶ H^k(Y, Rf_*ℋ_{X/S})` induced by `ξ̃[-n]`, read through
`H^k(Y, ℋ_{Y/S}[-n]) = H^m(Y, ℋ_{Y/S})` and the Leray identification
`H^k(Y, Rf_*ℋ_{X/S}) = H^k(X, ℋ_{X/S})`, sends `a` to `ξ ∪ f^*a`, for `n + m = k`. -/
theorem lerayCohomologyIso_hodgeClassDirectImageSummand (n k m : ℤ) (h₁ : -n + k = m)
    (h₂ : n + m = k) (ξ : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) n)
    (a : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) m) :
    (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom
        (((DerivedCategory.homologyFunctor _ k).map ((baseSections (inverseImageBase g)).map
          (hodgeClassDirectImageSummand f g n ξ))).hom
          ((shiftHomologyIsoU (baseSections (inverseImageBase g)) (hodgeObject g) (-n) k m
            h₁).inv.hom a)) =
      (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g)))) h₂)).hom
        (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) n m ξ
          (hodgeDgaPullback f g m a)) := by
  have e₁ := ConcreteCategory.congr_hom
    (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_inv_comp_map_shift
      (baseSections (inverseImageBase g)) n (hodgeClassDirectImageMorphism f g n ξ) k m h₁ h₂) a
  have e₂ := ConcreteCategory.congr_hom
    (lerayCohomologyIso_shift (baseMap f g) (hodgeObject (f ≫ g)) n m k h₂)
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
      ((relativeDirectImage f g).map (hodgeClassMorphism (f ≫ g) n ξ)))).hom
      (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
        (hodgeDirectImageMap f g))).hom a))
  have e₃ := lerayCohomologyIso_naturality_apply (baseMap f g) (hodgeClassMorphism (f ≫ g) n ξ) m
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
      (hodgeDirectImageMap f g))).hom a)
  have e₄ := lerayCohomologyIso_hodgeDirectImageMap f g m a
  have e₅ := shiftHomologyIsoU_hodgeClassMorphism (f ≫ g) n m k h₂ ξ (hodgeDgaPullback f g m a)
  simp only [ConcreteCategory.comp_apply] at e₁ e₂
  refine (congrArg (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom e₁).trans ?_
  have hd : ((DerivedCategory.homologyFunctor _ m).map
        ((baseSections (inverseImageBase g)).map (hodgeClassDirectImageMorphism f g n ξ)) ≫
      (shiftHomologyIsoU (baseSections (inverseImageBase g))
        ((relativeDirectImage f g).obj (hodgeObject (f ≫ g))) n m k h₂).hom).hom a =
      (shiftHomologyIsoU (baseSections (inverseImageBase g))
        ((relativeDirectImage f g).obj (hodgeObject (f ≫ g))) n m k h₂).hom.hom
        (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
          (((relativeDirectImage f g).commShiftIso n).hom.app (hodgeObject (f ≫ g))))).hom
          (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
            ((relativeDirectImage f g).map (hodgeClassMorphism (f ≫ g) n ξ)))).hom
            (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
              (hodgeDirectImageMap f g))).hom a))) := by
    simp only [hodgeClassDirectImageMorphism, Functor.map_comp, ModuleCat.hom_comp]
    rfl
  refine (congrArg (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom hd).trans ?_
  refine e₂.trans ?_
  rw [e₃, e₄]
  exact e₅

/-- `H^k(Y, ℋ_{Y/S}[-n]) ≅ H^m(Y, ℋ_{Y/S})` for `-n + k = m`. -/
abbrev hodgeShiftIso (n k m : ℤ) (h : -n + k = m) :=
  shiftHomologyIsoU (baseSections (inverseImageBase g)) (hodgeObject g) (-n) k m h

/-- The summands `ℋ_{Y/S}[-n_i]` of the source of `ξ̃`. -/
abbrev hodgeSourceSummand {N : ℕ} (n : Fin N → ℕ) (i : Fin N) :
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) :=
  (hodgeObject g)⟦-(n i : ℤ)⟧

/-- The map `(a_i) ↦ (a_i)` from `∏_i H^{k-n_i}(Y, ℋ_{Y/S})` to `∏_i H^k(Y, ℋ_{Y/S}[-n_i])`. -/
abbrev hodgeShiftProdMap (k : ℤ) {N : ℕ} (n : Fin N → ℕ)
    (a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i)) (i : Fin N) :
    (cohomologyFunctor g k).obj (hodgeSourceSummand g n i) :=
  (hodgeShiftIso g (n i) k (k - n i) (by omega)).inv.hom (a i)

/-- The identifications `H^{k-n_i}(Y, ℋ_{Y/S}) ≅ H^k(Y, ℋ_{Y/S}[-n_i])`, taken together, are a
bijection of products. -/
theorem bijective_hodgeShiftProdMap (k : ℤ) {N : ℕ} (n : Fin N → ℕ) :
    Function.Bijective (hodgeShiftProdMap g k n) :=
  (Equiv.piCongrRight fun i =>
    (hodgeShiftIso g (n i) k (k - n i) (by omega)).symm.toLinearEquiv.toEquiv).bijective

/-- **`H^k(Y, ξ̃)` is the map `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`** (the computation in the proof of
Proposition 0FMR, for Hodge cohomology): read through
`H^k(Y, ⨁ ℋ_{Y/S}[-n_i]) = ⨁_i H^{k-n_i}(Y, ℋ_{Y/S})` and the Leray identification
`H^k(Y, Rf_*ℋ_{X/S}) = H^k(X, ℋ_{X/S})`, the map induced by `ξ̃ = ⨁ ξ̃_i[-n_i]` on `H^k(Y, -)` is
`(a_i) ↦ ∑ ξ_i ∪ f^*a_i`. -/
theorem sum_dgaCohomologyCup_eq_lerayCohomologyIso {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ)
    (a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i)) :
    ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i) (ξ i)
          (hodgeDgaPullback f g (k - n i) (a i))) =
      (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom.hom
        (((cohomologyFunctor g k).map (hodgeLerayHirschMorphism f g n ξ)).hom
          (∑ i, ((cohomologyFunctor g k).map (biproduct.ι (hodgeSourceSummand g n) i)).hom
            (hodgeShiftProdMap g k n a i))) := by
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hι : biproduct.ι (hodgeSourceSummand g n) i ≫ hodgeLerayHirschMorphism f g n ξ =
      hodgeClassDirectImageSummand f g (n i) (ξ i) := biproduct.ι_desc _ _
  have hG := congrArg (fun φ => ((cohomologyFunctor g k).map φ).hom
    ((hodgeShiftIso g (n i) k (k - n i) (by omega)).inv.hom (a i))) hι
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hG
  exact (lerayCohomologyIso_hodgeClassDirectImageSummand f g (n i) k (k - n i) (by omega)
    (add_sub_cancel (n i : ℤ) k) (ξ i) (a i)).symm.trans
    (congrArg (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom.hom hG.symm)

/-- **`H^k(Y, ξ̃)` is bijective if and only if `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in degree
`k`**: the two differ by the bijections `H^k(Y, ⨁ ℋ_{Y/S}[-n_i]) = ⨁_i H^{k-n_i}(Y, ℋ_{Y/S})`
and `H^k(Y, Rf_*ℋ_{X/S}) = H^k(X, ℋ_{X/S})`. -/
theorem bijective_cohomologyFunctor_hodgeLerayHirschMorphism_iff {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ) :
    Function.Bijective ((cohomologyFunctor g k).map (hodgeLerayHirschMorphism f g n ξ)).hom ↔
      Function.Bijective
        (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
          ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))))
              (add_sub_cancel (n i : ℤ) k))).hom
            (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i)
              (ξ i) (hodgeDgaPullback f g (k - n i) (a i)))) := by
  have hB := (CategoryTheory.Limits.bijective_sum_map_biproduct_ι (hodgeSourceSummand g n)
    (cohomologyFunctor g k)).comp (bijective_hodgeShiftProdMap g k n)
  have hL : Function.Bijective
      (lerayCohomologyIso (baseMap f g) (hodgeObject (f ≫ g)) k).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have he := funext (sum_dgaCohomologyCup_eq_lerayCohomologyIso f g n ξ k)
  rw [he]
  exact (Function.Bijective.of_comp_iff' hL _).symm.trans
    (Function.Bijective.of_comp_iff _ hB).symm

/-- **The cohomological half of Proposition 0FMR for Hodge cohomology, given the derived half.**
If `ξ̃ : ⨁ ℋ_{Y/S}[-n_i] ⟶ Rf_*ℋ_{X/S}` is an isomorphism in `D(Y, g⁻¹𝒪_S)`, then in every degree
`k` the map

`⨁_i H^{k - n_i}(Y, ℋ_{Y/S}) ⟶ H^k(X, ℋ_{X/S}), (a_i) ↦ ∑ ξ_i ∪ f^*a_i`

is bijective. -/
theorem bijective_sum_dgaCohomologyCup_of_isIso {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    [IsIso (hodgeLerayHirschMorphism f g n ξ)] (k : ℤ) :
    Function.Bijective
      (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
        ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i)
            (ξ i) (hodgeDgaPullback f g (k - n i) (a i)))) :=
  (bijective_cohomologyFunctor_hodgeLerayHirschMorphism_iff f g n ξ k).1
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)

end Stacks.HodgeWeil

end
