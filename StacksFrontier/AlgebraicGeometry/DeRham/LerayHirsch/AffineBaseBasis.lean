module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayHirschIsomorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.AffineUnitCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.TotalCupPairingLaws

/-!
# The Leray–Hirsch classes over an affine base form a basis of relative de Rham cohomology

Let `f : X ⟶ Y` be a morphism of schemes with `Y` affine and `ξ_i ∈ H^{n_i}_{dR}(X/Y)` classes
such that the associated morphism `⨁_i 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` is an isomorphism (which is
[Stacks, Tag 0FMP] under its hypotheses). Applying `H^q(Y, -)` and the Leray identification
`H^q(Y, Rf_*Ω^•_{X/Y}) = H^q_{dR}(X/Y)`, and computing `H^q(Y, 𝒪_Y[-n])` on the affine `Y`, the
classes `ξ_i` with `n_i = q` form a basis of `H^q_{dR}(X/Y)` over `Γ(Y, 𝒪_Y)`. This is the input
of [Stacks, Tag 0FUM] on the graded pieces.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_smul_evalUnit`: `H^q(Y, ⨁_i 𝒪_Y[-n_i])` is
  free on the classes of `1` in the summands with `n_i = q`.
* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_sum_smul_deRhamClass`: the basis statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamCohomologyDirectImage
open scoped Stacks.StandardDerivedModel

universe u

namespace Function

/-- Families indexed by the members of `{j // p j}` are the families `(x_j)_j` with `x_j = 0`
off `p`, through bijections `A ≃ M_j` on `p` when the `M_j` off `p` are trivial. -/
theorem bijective_dite_pi {J A : Type*} (p : J → Prop) [DecidablePred p] {M : J → Type*}
    [∀ j, Zero (M j)] (b : ∀ j, p j → A → M j) (hb : ∀ j h, Function.Bijective (b j h))
    (hz : ∀ j, ¬ p j → Subsingleton (M j)) :
    Function.Bijective (fun (v : {j // p j} → A) j =>
      if h : p j then b j h (v ⟨j, h⟩) else (0 : M j)) := by
  refine ⟨fun v w hvw => ?_, fun x => ?_⟩
  · funext ⟨j, h⟩
    exact (hb j h).injective (by simpa only [dite_eq_left h] using congrFun hvw j)
  · refine ⟨fun i => ((hb i.1 i.2).surjective (x i.1)).choose, funext fun j => ?_⟩
    by_cases h : p j
    · simpa only [dite_eq_left h] using ((hb j h).surjective (x j)).choose_spec
    · exact @Subsingleton.elim _ (hz j h) _ _

end Function

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The image of a class of degree `n_i` read in an equal degree `q`. -/
abbrev castClass {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) (q : ℤ)
    (i : {i : Fin N // (n i : ℤ) = q}) : ToType (Scheme.Hom.deRhamCohomology f q) :=
  (eqToHom (congrArg (Scheme.Hom.deRhamCohomology f) i.2)).hom (ξ i.1)

/-- A class of the module realization of `H^q_{dR}(X/Y)`, read in the `Γ(Y, 𝒪_Y)`-module
`H^q_{dR}(X/Y)`. -/
abbrev baseModuleClass (q : ℤ) (z : ToType (Scheme.Hom.deRhamCohomology f q)) :
    Scheme.Hom.deRhamCohomologyBaseModule f q :=
  (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ q).hom.hom z

/-- The inclusion of a summand `𝒪_Y[-n_i]` of the source of the Leray–Hirsch morphism, read in an
equal degree `q`. -/
def summandι {N : ℕ} (n : Fin N → ℕ) (q : ℤ) (i : {i : Fin N // (n i : ℤ) = q}) :
    DerivedCategory.Q.obj (unitComplex Y.toRingedSpace q) ⟶
      ⨁ fun i => DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i : ℤ)) :=
  eqToHom (by rw [i.2]) ≫ biproduct.ι (fun i => DerivedCategory.Q.obj
    (unitComplex Y.toRingedSpace (n i : ℤ))) i.1

/-- **The classes are the values at the unit of the summands of the Leray–Hirsch morphism**, read
through the Leray identification. -/
theorem deRhamClass_eq_lerayCohomologyIso {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ))) (q : ℤ)
    (i : {i : Fin N // (n i : ℤ) = q}) :
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ q).hom.hom
        (castClass f n ξ q i) =
      (lerayCohomologyIso (inverseImageBaseProjection f)
        (DerivedCategory.Q.obj (deRhamCochainComplex f)) q).hom
        (((DerivedCategory.homologyFunctor _ q).map ((baseSections Y.toRingedSpace).map
          (deRhamClassSumMorphism f n ξ))).hom
          (evalUnit _ q (summandι n q i))) := by
  obtain ⟨i, rfl⟩ := i
  refine (lerayCohomologyIso_evalUnit_deRhamClassToDirectImage f (n i) (ξ i)).symm.trans ?_
  refine congrArg (lerayCohomologyIso (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (deRhamCochainComplex f)) (n i)).hom ?_
  refine Eq.trans ?_ (evalUnit_comp _ _ _)
  congr 1
  rw [summandι, eqToHom_refl, Category.id_comp, deRhamClassSumMorphism, biproduct.ι_desc]

/-- **`H^q(Y, ⨁_i 𝒪_Y[-n_i])` is free over `Γ(Y, 𝒪_Y)` on the classes of `1` in the summands with
`n_i = q`**, for `Y` affine. -/
theorem bijective_sum_smul_evalUnit [IsAffine Y] {N : ℕ} (n : Fin N → ℕ) (q : ℤ) :
    Function.Bijective (fun v : {i : Fin N // (n i : ℤ) = q} → Γ(Y, ⊤) =>
      ∑ i, v i • evalUnit (⨁ fun i => DerivedCategory.Q.obj
        (unitComplex Y.toRingedSpace (n i : ℤ))) q (summandι n q i)) := by
  let Z := fun i : Fin N => DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i : ℤ))
  have := additive_baseSections Y.toRingedSpace
  let G := baseSections Y.toRingedSpace ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} (baseRing Y.toRingedSpace)) q
  let u : ∀ j, (n j : ℤ) = q → G.obj (Z j) := fun j h =>
    evalUnit (Z j) q (eqToHom (congrArg (fun k : ℤ =>
      DerivedCategory.Q.obj (unitComplex Y.toRingedSpace k)) h.symm))
  have hb : ∀ j (h : (n j : ℤ) = q), Function.Bijective (fun a : Γ(Y, ⊤) => a • u j h) := by
    intro j h
    subst h
    have e : u j rfl = unitCycleClass Y.toRingedSpace (n j) := by
      change ((DerivedCategory.homologyFunctor _ _).map ((baseSections _).map (eqToHom rfl))).hom
        _ = _
      rw [eqToHom_refl, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
    rw [e]
    exact bijective_smul_unitCycleClass Y.toRingedSpace (n j)
      (AffineUnitCohomology.isIso_sectionsUnitQ_unitComplex Y (n j))
  have hz : ∀ j, ¬ (n j : ℤ) = q → Subsingleton (G.obj (Z j)) := fun j h =>
    ModuleCat.subsingleton_of_isZero (isZero_cohomologyModule_unitComplex Y.toRingedSpace (n j) q
      (Ne.symm h) (AffineUnitCohomology.isIso_sectionsUnitQ_unitComplex Y (n j)))
  have hP := Function.bijective_dite_pi (fun j => (n j : ℤ) = q)
    (fun j h (a : Γ(Y, ⊤)) => a • u j h) hb hz
  have hS := bijective_sum_map_biproduct_ι Z G
  have key : ∀ v : {i : Fin N // (n i : ℤ) = q} → Γ(Y, ⊤),
      ∑ j, (G.map (biproduct.ι Z j)).hom
        (if h : (n j : ℤ) = q then v ⟨j, h⟩ • u j h else 0) =
      ∑ i, v i • evalUnit (⨁ fun i => DerivedCategory.Q.obj
        (unitComplex Y.toRingedSpace (n i : ℤ))) q (summandι n q i) := by
    intro v
    have e : ∀ j, (G.map (biproduct.ι Z j)).hom
        (if h : (n j : ℤ) = q then v ⟨j, h⟩ • u j h else 0) =
        if h : (n j : ℤ) = q then v ⟨j, h⟩ • (G.map (biproduct.ι Z j)).hom (u j h) else 0 := by
      intro j
      split_ifs
      exacts [(G.map (biproduct.ι Z j)).hom.map_smul _ _, (G.map (biproduct.ι Z j)).hom.map_zero]
    refine (Finset.sum_congr rfl fun j _ => e j).trans ?_
    refine (Stacks.KatzOda.Cech.sum_dite_subtype (fun j => (n j : ℤ) = q)
      (fun j h => v ⟨j, h⟩ • (G.map (biproduct.ι Z j)).hom (u j h))).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (v i • ·) (evalUnit_comp _ _ _).symm
  exact (congrArg Function.Bijective (funext key)).mp (hS.comp hP)

/-- **The Leray–Hirsch classes form a basis over an affine base** ([Stacks, Tag 0FMP] read on
cohomology): if `⨁_i 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` is an isomorphism and `Y` is affine, then in every
degree `q` the classes `ξ_i` with `n_i = q` form a basis of `H^q_{dR}(X/Y)` over `Γ(Y, 𝒪_Y)`, in
the module realization of de Rham cohomology. -/
theorem bijective_sum_smul_deRhamClass [IsAffine Y] {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i : Fin N, ToType (Scheme.Hom.deRhamCohomology f (n i : ℤ)))
    [IsIso (deRhamClassSumMorphism f n ξ)] (q : ℤ) :
    Function.Bijective (fun v : {i : Fin N // (n i : ℤ) = q} → Y.sheaf.obj.obj (Opposite.op ⊤) =>
      ∑ i, v i • baseModuleClass f q (castClass f n ξ q i)) := by
  let L := lerayCohomologyIso (inverseImageBaseProjection f)
    (DerivedCategory.Q.obj (deRhamCochainComplex f)) q
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y.toRingedSpace)) q).map
    ((baseSections Y.toRingedSpace).map (deRhamClassSumMorphism f n ξ))
  have h : (fun v : {i : Fin N // (n i : ℤ) = q} → Y.sheaf.obj.obj (Opposite.op ⊤) =>
      ∑ i, v i • baseModuleClass f q (castClass f n ξ q i)) =
      fun v => L.hom (H (∑ i, @id Γ(Y, ⊤) (v i) • evalUnit (⨁ fun i => DerivedCategory.Q.obj
        (unitComplex Y.toRingedSpace (n i : ℤ))) q (summandι n q i))) := by
    funext v
    refine Eq.trans ?_ (congrArg L.hom (map_sum H.hom _ _).symm)
    refine Eq.trans ?_ (map_sum L.hom.hom _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (congrArg (fun z : Scheme.Hom.deRhamCohomologyBaseModule f q => v i • z)
      (deRhamClass_eq_lerayCohomologyIso f n ξ q i)).trans ?_
    exact ((congrArg L.hom.hom (H.hom.map_smul (@id Γ(Y, ⊤) (v i)) _)).trans
      (L.hom.hom.map_smul (@id Γ(Y, ⊤) (v i)) _)).symm
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso L.hom).comp
    ((ConcreteCategory.bijective_of_isIso H).comp (bijective_sum_smul_evalUnit (Y := Y) n q))

end AlgebraicGeometry.DeRhamLerayHirsch

end
