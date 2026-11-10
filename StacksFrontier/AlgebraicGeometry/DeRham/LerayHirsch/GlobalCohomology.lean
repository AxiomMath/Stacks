module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayShift
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechPullback

/-!
# The morphism `ξ̃` of the Leray--Hirsch theorem on cohomology

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and `ξ_i ∈ H^{n_i}_{dR}(X/S)`. The proof
of [Stacks, Tag 0FMR] observes that, through
`RΓ(Y, Rf_*Ω^•_{X/S}) = RΓ(X, Ω^•_{X/S})`, the morphism `ξ̃_i : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}[n_i]`
induces on cohomology the map `η ↦ ξ_i ∪ f^*η` from `H^m_{dR}(Y/S)` to `H^{m+n_i}_{dR}(X/S)`.
Consequently, if `ξ̃ = ⨁ ξ̃_i[-n_i]` is an isomorphism then so is
`(a_i) ↦ ∑ ξ_i ∪ f^*a_i`, which is the second assertion of the proposition given the first.

## Main results

* `Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_inv_comp_map_shift`: a morphism
  `φ : A ⟶ T[n]` read on cohomology after shifting back by `-n`.
* `CategoryTheory.Limits.bijective_sum_map_biproduct_ι`: an additive functor into modules
  carries a finite biproduct to a product.
* `AlgebraicGeometry.DeRhamLerayHirsch.lerayCohomologyIso_deRhamDirectImageMap`: the canonical
  map `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` induces `f^*` on cohomology.
* `AlgebraicGeometry.DeRhamLerayHirsch.lerayCohomologyIso_classDirectImageSummand`: `ξ̃_i[-n_i]`
  induces `a ↦ ξ_i ∪ f^*a`.
* `AlgebraicGeometry.DeRhamLerayHirsch.sum_deRhamCohomologyCup_eq_lerayCohomologyIso`: `H^k(Y, ξ̃)`
  is `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`.
* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_cohomologyFunctor_lerayHirschMorphism_iff`:
  `H^k(Y, ξ̃)` is bijective if and only if `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in degree `k`.
* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_deRhamCohomologyCup_of_isIso`: if `ξ̃` is an
  isomorphism, then `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in every degree.

## Implementation notes

The ingredients are: the edge identity of the library expressing the pullback of de Rham cohomology
through the canonical map and the Leray identification
(`Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback`),
property (3) of Remark 0FU7
(`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`), the naturality of
the Leray identification and its compatibility with the shift
(`Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_shift`). The cup product is the one of
Section 50.4 (`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup`), defined without any
hypothesis on `X`, and `f^*` is `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamPullbackModule`.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)

universe u

namespace Stacks.Cohomology.RealizationShift

variable {C : Type*} [Category* C] [HasShift C ℤ] {B : Type*} [Category* B] [Abelian B]
  [HasDerivedCategory B] (F : C ⥤ DerivedCategory B) [F.CommShift ℤ]

/-- The identification `Hᵏ(F(T[0])) ≅ Hᵏ(F T)` is `F` of the identification `T[0] ≅ T`. -/
theorem shiftHomologyIsoU_zero_hom (T : C) (k : ℤ) (h : 0 + k = k) :
    (shiftHomologyIsoU F T 0 k k h).hom =
      (DerivedCategory.homologyFunctor B k).map (F.map ((shiftFunctorZero C ℤ).hom.app T)) := by
  have h₂ : (F.commShiftIso (0 : ℤ)).hom.app T =
      F.map ((shiftFunctorZero C ℤ).hom.app T) ≫
        (shiftFunctorZero (DerivedCategory B) ℤ).inv.app (F.obj T) := by
    simp [Functor.commShiftIso_zero]
  have h₃ := Functor.shiftIso_zero_hom_app (DerivedCategory.homologyFunctor B 0) k (F.obj T)
  change (DerivedCategory.homologyFunctor B k).map ((F.commShiftIso (0 : ℤ)).hom.app T) ≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso 0 k k h).hom.app (F.obj T) = _
  rw [h₂, h₃]
  change (DerivedCategory.homologyFunctor B k).map (F.map ((shiftFunctorZero C ℤ).hom.app T) ≫
        (shiftFunctorZero (DerivedCategory B) ℤ).inv.app (F.obj T)) ≫
      (DerivedCategory.homologyFunctor B k).map
        ((shiftFunctorZero (DerivedCategory B) ℤ).hom.app (F.obj T)) = _
  rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (DerivedCategory.homologyFunctor B k).map (Category.comp_id _)

/-- **A morphism into a translate, read on cohomology.** For `φ : A ⟶ T[n]` the map induced on
`Hᵏ(F(-))` by `φ[-n] : A[-n] ⟶ T[n][-n] = T`, read through `Hᵏ(F(A[-n])) ≅ Hᵐ(F A)`, is the map
induced by `φ` on `Hᵐ(F(-))` followed by `Hᵐ(F(T[n])) ≅ Hᵏ(F T)`, for `-n + k = m`. -/
theorem shiftHomologyIsoU_inv_comp_map_shift {A T : C} (n : ℤ) (φ : A ⟶ T⟦n⟧) (k m : ℤ)
    (h : -n + k = m) (h' : n + m = k) :
    (shiftHomologyIsoU F A (-n) k m h).inv ≫ (DerivedCategory.homologyFunctor B k).map
        (F.map (φ⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app T)) =
      (DerivedCategory.homologyFunctor B m).map (F.map φ) ≫
        (shiftHomologyIsoU F T n m k h').hom := by
  have hnat := Stacks.DeRham.GysinCupHodge.shiftHomologyIsoU_naturality F φ (-n) k m h
  have hadd := shiftHomologyIsoU_add F T (-n) n 0 (add_neg_cancel n) k m k h h'
  have hzero := shiftHomologyIsoU_zero_hom F T k (by omega)
  have hε : (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app T =
      (shiftFunctorAdd' C n (-n) 0 (add_neg_cancel n)).inv.app T ≫
        (shiftFunctorZero C ℤ).hom.app T := rfl
  rw [hε, F.map_comp, F.map_comp, Functor.map_comp, Functor.map_comp, ← hzero, ← hadd,
    Iso.inv_comp_eq, ← Category.assoc, ← Category.assoc, hnat, Category.assoc]

end Stacks.Cohomology.RealizationShift

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Ring R] {J : Type} [Fintype J]
  (Z : J → C) [HasBiproduct Z] (G : C ⥤ ModuleCat.{u} R) [G.Additive]

/-- **An additive functor into modules carries a finite biproduct to a product**: the map
`(x_j) ↦ ∑ G(ι_j)(x_j)` from `∏ G(Z_j)` to `G(⨁ Z_j)` is bijective, with inverse
`y ↦ (G(π_j)(y))_j`. -/
theorem bijective_sum_map_biproduct_ι :
    Function.Bijective (fun x : ∀ j, G.obj (Z j) => ∑ j, (G.map (biproduct.ι Z j)).hom (x j)) := by
  classical
  refine Function.bijective_iff_has_inverse.2 ⟨fun y j => (G.map (biproduct.π Z j)).hom y,
    fun x => ?_, fun y => ?_⟩
  · funext j
    simp only [map_sum]
    rw [Finset.sum_eq_single j]
    · rw [← ConcreteCategory.comp_apply, ← G.map_comp, biproduct.ι_π_self, G.map_id]
      rfl
    · intro i _ hij
      rw [← ConcreteCategory.comp_apply, ← G.map_comp, biproduct.ι_π_ne Z hij, G.map_zero]
      rfl
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · have h : (G.map (∑ j, biproduct.π Z j ≫ biproduct.ι Z j)).hom y =
        (G.map (𝟙 (⨁ Z))).hom y := by rw [biproduct.total]
    simp only [G.map_id] at h
    rw [G.map_sum] at h
    refine Eq.trans ?_ h
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [G.map_comp]
    rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry.DeRhamLerayHirsch

open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso lerayCohomologyIso_naturality_apply
  lerayCohomologyIso_shift)
open Stacks.Cohomology.GlobalKunneth (baseSections)
open scoped Stacks.StandardDerivedModel

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The canonical map `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` induces the pullback on de Rham
cohomology**: on `H^m(Y, -)`, followed by the Leray identification
`H^m(Y, Rf_*Ω^•_{X/S}) = H^m_{dR}(X/S)`, it is `f^* : H^m_{dR}(Y/S) ⟶ H^m_{dR}(X/S)`. -/
theorem lerayCohomologyIso_deRhamDirectImageMap (m : ℤ)
    (a : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m) :
    (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) m).hom
        (((DerivedCategory.homologyFunctor _ m).map
          ((baseSections (inverseImageBase g)).map (deRhamDirectImageMap f g))).hom a) =
      DeRhamKatzOdaCech.deRhamPullbackModule f g m a := by
  have h := deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback f (f ≫ g) g (𝟙 S)
    (Category.comp_id _).symm m
    ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m).inv.hom a)
  have hinv := Iso.inv_hom_id_apply
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m)
    (show (forget₂ (ModuleCat _) AddCommGrpCat.{u}).obj (SheafOfModules.deRhamCohomology
      (Scheme.Hom.deRhamAlgebras g) (SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras g)) m) from a)
  rw [hinv] at h
  have hpb : DeRhamKatzOdaCech.deRhamPullbackModule f g m a =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) m).hom.hom
        ((Scheme.Hom.deRhamCohomologyPullback f g (f ≫ g) (𝟙 S) (Category.comp_id _).symm m).hom
          ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras g)
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m).inv.hom a)) :=
    rfl
  exact h.symm.trans hpb.symm

/-- **`ξ'` on cohomology is the cup product with `ξ`** (Remark 0FU7, property (3)), read in
degree `k = n + m`. -/
theorem shiftHomologyIsoU_classMorphism (p : X ⟶ S) (n m k : ℤ) (h : n + m = k)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n)
    (η : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) m) :
    (shiftHomologyIsoU (baseSections (inverseImageBase p)) (deRhamObject p) n m k h).hom
        (((DerivedCategory.homologyFunctor _ m).map
          ((baseSections (inverseImageBase p)).map (classMorphism p n ξ))).hom η) =
      (eqToHom (congrArg (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))) h)).hom
        (SheafOfModules.deRhamCohomologyCup _ _ n m ξ η) := by
  subst h
  rw [SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism, eqToHom_refl]
  rfl

/-- **`ξ̃_i[-n]` on cohomology is `a ↦ ξ ∪ f^*a`** (the computation in the proof of
Proposition 0FMR): the map `H^k(Y, Ω^•_{Y/S}[-n]) ⟶ H^k(Y, Rf_*Ω^•_{X/S})` induced by
`ξ̃[-n]`, read through `H^k(Y, Ω^•_{Y/S}[-n]) = H^m_{dR}(Y/S)` and the Leray identification
`H^k(Y, Rf_*Ω^•_{X/S}) = H^k_{dR}(X/S)`, sends `a` to `ξ ∪ f^*a`, for `n + m = k`. -/
theorem lerayCohomologyIso_classDirectImageSummand (n k m : ℤ) (h₁ : -n + k = m) (h₂ : n + m = k)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n)
    (a : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m) :
    (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom
        (((DerivedCategory.homologyFunctor _ k).map ((baseSections (inverseImageBase g)).map
          (classDirectImageSummand f g n ξ))).hom
          ((shiftHomologyIsoU (baseSections (inverseImageBase g)) (deRhamObject g) (-n) k m
            h₁).inv.hom a)) =
      (eqToHom (congrArg (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))) h₂)).hom
        (SheafOfModules.deRhamCohomologyCup _ _ n m ξ
          (DeRhamKatzOdaCech.deRhamPullbackModule f g m a)) := by
  have e₁ := ConcreteCategory.congr_hom
    (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_inv_comp_map_shift
      (baseSections (inverseImageBase g)) n (classDirectImageMorphism f g n ξ) k m h₁ h₂) a
  have e₂ := ConcreteCategory.congr_hom
    (lerayCohomologyIso_shift (baseMap f g) (deRhamObject (f ≫ g)) n m k h₂)
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
      ((relativeDirectImage f g).map (classMorphism (f ≫ g) n ξ)))).hom
      (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
        (deRhamDirectImageMap f g))).hom a))
  have e₃ := lerayCohomologyIso_naturality_apply (baseMap f g) (classMorphism (f ≫ g) n ξ) m
    (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
      (deRhamDirectImageMap f g))).hom a)
  have e₄ := lerayCohomologyIso_deRhamDirectImageMap f g m a
  have e₅ := shiftHomologyIsoU_classMorphism (f ≫ g) n m k h₂ ξ
    (DeRhamKatzOdaCech.deRhamPullbackModule f g m a)
  simp only [ConcreteCategory.comp_apply] at e₁ e₂
  refine (congrArg (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom e₁).trans ?_
  have hd : ((DerivedCategory.homologyFunctor _ m).map
        ((baseSections (inverseImageBase g)).map (classDirectImageMorphism f g n ξ)) ≫
      (shiftHomologyIsoU (baseSections (inverseImageBase g))
        ((relativeDirectImage f g).obj (deRhamObject (f ≫ g))) n m k h₂).hom).hom a =
      (shiftHomologyIsoU (baseSections (inverseImageBase g))
        ((relativeDirectImage f g).obj (deRhamObject (f ≫ g))) n m k h₂).hom.hom
        (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
          (((relativeDirectImage f g).commShiftIso n).hom.app (deRhamObject (f ≫ g))))).hom
          (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
            ((relativeDirectImage f g).map (classMorphism (f ≫ g) n ξ)))).hom
            (((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase g)).map
              (deRhamDirectImageMap f g))).hom a))) := by
    simp only [classDirectImageMorphism, Functor.map_comp, ModuleCat.hom_comp]
    rfl
  refine (congrArg (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom hd).trans ?_
  refine e₂.trans ?_
  rw [e₃, e₄]
  exact e₅

/-- `H^k(Y, -)` on `D(Y, g⁻¹𝒪_S)`, as a functor to modules over `Γ(Y, g⁻¹𝒪_S)`. -/
abbrev cohomologyFunctor (k : ℤ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) ⥤
      ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing (inverseImageBase g)) :=
  baseSections (inverseImageBase g) ⋙ DerivedCategory.homologyFunctor _ k

/-- `H^k(Y, Ω^•_{Y/S}[-n]) ≅ H^m_{dR}(Y/S)` for `-n + k = m`. -/
abbrev shiftDeRhamIso (n k m : ℤ) (h : -n + k = m) :=
  shiftHomologyIsoU (baseSections (inverseImageBase g)) (deRhamObject g) (-n) k m h

/-- The summands of the source of `ξ̃`. -/
abbrev sourceSummand {N : ℕ} (n : Fin N → ℕ) (i : Fin N) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) :=
  (deRhamObject g)⟦-(n i : ℤ)⟧

/-- The map `(a_i) ↦ (a_i)` from `∏_i H^{k-n_i}_{dR}(Y/S)` to `∏_i H^k(Y, Ω^•_{Y/S}[-n_i])`. -/
abbrev shiftDeRhamProdMap (k : ℤ) {N : ℕ} (n : Fin N → ℕ)
    (a : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i)) (i : Fin N) :
    (cohomologyFunctor g k).obj (sourceSummand g n i) :=
  (shiftDeRhamIso g (n i) k (k - n i) (by omega)).inv.hom (a i)

/-- The identifications `H^{k-n_i}_{dR}(Y/S) ≅ H^k(Y, Ω^•_{Y/S}[-n_i])`, taken together, are a
bijection of products. -/
theorem bijective_shiftDeRhamProdMap (k : ℤ) {N : ℕ} (n : Fin N → ℕ) :
    Function.Bijective (shiftDeRhamProdMap g k n) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun x i => (shiftDeRhamIso g (n i) k (k - n i) (by omega)).hom.hom (x i), fun a => ?_,
      fun x => ?_⟩
  · funext i
    exact Iso.inv_hom_id_apply (shiftDeRhamIso g (n i) k (k - n i) (by omega)) (a i)
  · funext i
    exact Iso.hom_inv_id_apply (shiftDeRhamIso g (n i) k (k - n i) (by omega)) (x i)

/-- **`H^k(Y, ξ̃)` is the map `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`** (the computation in the proof of
Proposition 0FMR): read through `H^k(Y, ⨁ Ω^•_{Y/S}[-n_i]) = ⨁_i H^{k-n_i}_{dR}(Y/S)` and the
Leray identification `H^k(Y, Rf_*Ω^•_{X/S}) = H^k_{dR}(X/S)`, the map induced by
`ξ̃ = ⨁ ξ̃_i[-n_i]` on `H^k(Y, -)` is `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`. -/
theorem sum_deRhamCohomologyCup_eq_lerayCohomologyIso {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ)
    (a : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i)) :
    ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule f g (k - n i) (a i))) =
      (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom.hom
        (((cohomologyFunctor g k).map (lerayHirschMorphism f g n ξ)).hom
          (∑ i, ((cohomologyFunctor g k).map (biproduct.ι (sourceSummand g n) i)).hom
            (shiftDeRhamProdMap g k n a i))) := by
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hι : biproduct.ι (sourceSummand g n) i ≫ lerayHirschMorphism f g n ξ =
      classDirectImageSummand f g (n i) (ξ i) := biproduct.ι_desc _ _
  have hG := congrArg (fun φ => ((cohomologyFunctor g k).map φ).hom
    ((shiftDeRhamIso g (n i) k (k - n i) (by omega)).inv.hom (a i))) hι
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hG
  exact (lerayCohomologyIso_classDirectImageSummand f g (n i) k (k - n i) (by omega)
    (add_sub_cancel (n i : ℤ) k) (ξ i) (a i)).symm.trans
    (congrArg (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom.hom hG.symm)

/-- **`H^k(Y, ξ̃)` is bijective if and only if `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective in degree
`k`**: the two differ by the bijections `H^k(Y, ⨁ Ω^•_{Y/S}[-n_i]) = ⨁_i H^{k-n_i}_{dR}(Y/S)` and
`H^k(Y, Rf_*Ω^•_{X/S}) = H^k_{dR}(X/S)`. -/
theorem bijective_cohomologyFunctor_lerayHirschMorphism_iff {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ) :
    Function.Bijective ((cohomologyFunctor g k).map (lerayHirschMorphism f g n ξ)).hom ↔
      Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras g)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
        ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
            (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
            (DeRhamKatzOdaCech.deRhamPullbackModule f g (k - n i) (a i)))) := by
  have hB := (CategoryTheory.Limits.bijective_sum_map_biproduct_ι (sourceSummand g n)
    (cohomologyFunctor g k)).comp (bijective_shiftDeRhamProdMap g k n)
  have hL : Function.Bijective
      (lerayCohomologyIso (baseMap f g) (deRhamObject (f ≫ g)) k).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have he := funext (sum_deRhamCohomologyCup_eq_lerayCohomologyIso f g n ξ k)
  rw [he]
  exact (Function.Bijective.of_comp_iff' hL _).symm.trans
    (Function.Bijective.of_comp_iff _ hB).symm

/-- **The cohomological half of Proposition 0FMR, given the derived half.** If
`ξ̃ : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` is an isomorphism in `D(Y, g⁻¹𝒪_S)`, then in every degree
`k` the map

`⨁_i H^{k - n_i}_{dR}(Y/S) ⟶ H^k_{dR}(X/S), (a_i) ↦ ∑ ξ_i ∪ f^*a_i`

is bijective: it is `H^k(Y, ξ̃)` read through `H^k(Y, Ω^•_{Y/S}[-n_i]) = H^{k-n_i}_{dR}(Y/S)` and
the Leray identification `H^k(Y, Rf_*Ω^•_{X/S}) = H^k_{dR}(X/S)`. -/
theorem bijective_sum_deRhamCohomologyCup_of_isIso {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    [IsIso (lerayHirschMorphism f g n ξ)] (k : ℤ) :
    Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule f g (k - n i) (a i)))) :=
  (bijective_cohomologyFunctor_lerayHirschMorphism_iff f g n ξ k).1
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)

end AlgebraicGeometry.DeRhamLerayHirsch
