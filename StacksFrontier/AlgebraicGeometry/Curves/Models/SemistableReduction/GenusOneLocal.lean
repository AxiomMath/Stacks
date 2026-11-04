module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusReduction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.AssociatedNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentRationalIntersectionPoint
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelNumericalTypeGenus
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionSequence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RationalPointSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusBound
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GeometricallyReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.ReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.SeparableComponents
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneRationalIndex

/-!
# Semistable reduction in genus one: the local statement

This file proves the local statement of Section 0CEG of the Stacks project. Let `R` be a discrete
valuation ring with fraction field `K` and residue field `k`, and let `C` be a smooth projective
curve of genus one over `K` with `H⁰(C, 𝒪_C) = K`, having a `K`-rational point, and with
`Pic(C)[ℓ] ≅ (𝐙/ℓ𝐙)^{⊕2}` for a prime `ℓ ≥ 7` invertible in `k`. Then every minimal model `X` of
`C` is at-worst-nodal of relative dimension one over `R`, and its special fibre is either a smooth
curve of genus one or a cycle of rational curves.

The argument is the source's. The numerical type `T` of `X` is minimal of genus one (Tags 0CA6
and 0CA4) and has an index with `mᵢ = wᵢ = 1` (Tag 0CE8), so by the classification (Tag 0C8T,
sorted in `AlgebraicGeometry.NumericalType.tree_or_cycle_of_isMinimal_of_genus_eq_one`) either

* (A) its intersection graph is a tree; then `Pic(T)[ℓ] = 0` (Tags 0C6X, 0CE7), so
  `(𝐙/ℓ𝐙)^{⊕2} ⊆ Pic((X_k)_{red})[ℓ]` (Tags 0CAD, 0CAE) and Tag 0CE6 forces
  `2 ≤ h¹((X_k)_{red}) + g_geom(X_k/k) ≤ 1 + ∑ wᵢgᵢ`; so `X_k` is irreducible, and equality in
  Tag 0CEA makes it smooth (Tag 0CEE); or
* (B) it is a cycle on at least three components with all `mᵢ = wᵢ = 1` and all `gᵢ = 0`; then
  `Pic(T)[ℓ]` has dimension at most one, so `Pic(X)[ℓ] ≠ 0` and `Pic(X_{k̄})[ℓ] ≠ 0` (Tags 0CAD,
  0CAE, 0CC5). Equality in Tag 0CEA makes every component smooth, so `X_{k̄}` is reduced, and the
  closing step (Tags 0C20, 0C60, 0C03, 0CDZ) makes `X_k` at-worst-nodal; every component, being a
  smooth curve of genus zero over `k` with a `k`-rational point, is a projective line (Tag 0C6U).

The inputs not yet available in the library when this file was written (Tags 0CA6, 0CE6, 0C20,
0C6U) enter `Stacks.Models.RegularProperModelSituation.genusOne_local` as hypotheses in the exact
form in which they are used, so that this untagged lemma is instantiated once they are; so does
the bound `h¹((X_k)_{red}) ≤ 1` (the surjectivity half of Tag 0CE9 together with Tag 0CE8).

## Main definitions

* `Stacks.Models.RegularProperModelSituation.IsSmoothGenusOneSpecialFiber` — the special fibre is
  a smooth curve of genus one with `H⁰ = k`.
* `Stacks.Models.RegularProperModelSituation.IsCycleOfRationalCurves` — the special fibre is a
  cycle of projective lines.

## References

* [Stacks Project, Section 0CEG](https://stacks.math.columbia.edu/tag/0CEG)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The two shapes of the special fibre -/

/-- **The special fibre is a smooth curve of genus one**: `X_k` is smooth over `k`, has only the
constants as global functions, and has genus one. -/
def IsSmoothGenusOneSpecialFiber : Prop :=
  Smooth S.specialFiberToSpec ∧
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) ∧
    genus S.specialFiberToSpec = 1

/-- **The special fibre is a cycle of rational curves.** The special fibre `X_k` has
at-worst-nodal singularities over `k`, each of its irreducible components (with its reduced
structure) is isomorphic over `k` to the projective line `𝐏¹_k`, and for some enumeration
`C₀, …, C_{n-1}` of the components, `n ≥ 2`, two distinct components `Cᵢ` and `Cⱼ` meet with
intersection number the number of ways of writing `j = i ± 1` modulo `n` (so `Cᵢ` meets exactly
`C_{i-1}` and `C_{i+1}`, each in one point when `n ≥ 3`, and the two components of a cycle of
length two meet in two points). A single irreducible nodal rational curve, the cycle of length
one, is not included: its component is not a projective line. -/
def IsCycleOfRationalCurves : Prop :=
  (letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩;
    Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber) ∧
  (∀ Z : irreducibleComponents S.specialFiber,
    Nonempty (Over.mk (S.specialFiberComponentToSpec Z) ≅
      Over.mk (projectiveSpaceOver 1 (Spec (.of S.k)) ↘ Spec (.of S.k)))) ∧
  ∃ (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber), 2 ≤ n ∧
    ∀ i j, i ≠ j → S.specialFiberIntersectionMatrix (e i) (e j) =
      (if j.val = (i.val + 1) % n then 1 else 0) + (if i.val = (j.val + 1) % n then 1 else 0)

/-! ### Preliminaries -/

/-- A component whose global functions are the constants has weight one. -/
theorem specialFiberComponentWeight_eq_one_of_isIso (Z : irreducibleComponents S.specialFiber)
    (h : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop)) :
    S.specialFiberComponentWeight Z = 1 := by
  unfold specialFiberComponentWeight
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have hbij :
      Function.Bijective (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) :=
    ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop)
  rw [← (AlgEquiv.ofBijective (Algebra.ofId S.k _) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **An index of multiplicity and weight one** (Tag 0CE8): if `C` has a `K`-rational point, the
component of `X_k` through the `k`-rational smooth point of `X_k` has multiplicity one and
weight one. -/
theorem exists_multiplicity_eq_one_and_weight_eq_one (p : Spec (.of S.K) ⟶ S.C)
    (hp : p ≫ S.C_to_K = 𝟙 _) (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ∃ i, (S.associatedNumericalType n e).multiplicity i = 1 ∧
      (S.associatedNumericalType n e).weight i = 1 := by
  classical
  obtain ⟨⟨x, -, -, hx⟩, -⟩ := S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq p hp
  let Z : irreducibleComponents S.specialFiber :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  obtain ⟨hiso, hm⟩ := hx Z mem_irreducibleComponent
  refine ⟨e.symm Z, ?_, ?_⟩
  · rw [associatedNumericalType_multiplicity, e.apply_symm_apply, hm]
    rfl
  · rw [associatedNumericalType_weight, e.apply_symm_apply,
      S.specialFiberComponentWeight_eq_one_of_isIso Z hiso]
    rfl

/-- The multiplicities have greatest common divisor one as soon as one of them is one. -/
theorem gcd_specialFiberMultiplicity_eq_one {Z : irreducibleComponents S.specialFiber}
    (hZ : S.specialFiberMultiplicity Z = 1) :
    Finset.univ.gcd S.specialFiberMultiplicity = 1 :=
  Nat.eq_one_of_dvd_one (hZ ▸ Finset.gcd_dvd (Finset.mem_univ Z))

/-- If all components have genus zero, the geometric genus of the special fibre vanishes. -/
private theorem geometricGenus_specialFiberToSpec_eq_zero
    (h : ∀ Z, S.specialFiberComponentGenus Z = 0) :
    geometricGenus S.k S.specialFiberToSpec = 0 := by
  have hle := S.geometricGenus_specialFiberToSpec_eq_sum.le.trans
    (Finset.sum_le_sum fun Z _ => S.geometricGenus_specialFiberComponent_le_weight_mul_genus Z)
  simpa [h] using hle

/-- A finite `𝐅_ℓ`-vector space containing `(𝐙/ℓ𝐙)^{⊕2}` has dimension at least two. -/
private theorem two_le_finrank_of_injective_addMonoidHom {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*}
    [AddCommGroup M] [Module (ZMod ℓ) M] [Module.Finite (ZMod ℓ) M]
    (φ : (Fin 2 → ZMod ℓ) →+ M) (hφ : Function.Injective φ) : 2 ≤ Module.finrank (ZMod ℓ) M := by
  simpa using LinearMap.finrank_le_finrank_of_injective (f := AddMonoidHom.toZModLinearMap ℓ φ) hφ

/-! ### The Picard groups -/

open Stacks.Picard in
/-- The restriction `Pic(X)[ℓ] ⟶ Pic((X_k)_{red})[ℓ]`, as a homomorphism of torsion groups. -/
def picardTorsionToSpecialFiberRed (ℓ : ℕ) :
    Submodule.torsionBy ℤ (ofScheme S.X) (ℓ : ℤ) →+
      AddSubgroup.torsionBy (ofScheme S.specialFiberRed) (ℓ : ℤ) :=
  ((schemePullbackClassHom S.specialFiberRedι).comp
    (Submodule.torsionBy ℤ (ofScheme S.X) (ℓ : ℤ)).toAddSubgroup.subtype).codRestrict _
    fun x => by
      change (ℓ : ℤ) • schemePullbackClassHom S.specialFiberRedι (x : ofScheme S.X) = 0
      rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]

open Stacks.Picard in
/-- The restriction `Pic(X)[ℓ] ⟶ Pic((X_k)_{red})[ℓ]` is injective for `ℓ` invertible in `k`
(Tag 0CAE). -/
theorem injective_picardTorsionToSpecialFiberRed (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℤ) : S.k)) :
    Function.Injective (S.picardTorsionToSpecialFiberRed ℓ) := by
  intro x y hxy
  apply Subtype.ext
  refine injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion S hℓ
    ((mem_torsionBy_iff_mem_zsmulTorsion _ _).1 x.2)
    ((mem_torsionBy_iff_mem_zsmulTorsion _ _).1 y.2) ?_
  exact congrArg Subtype.val hxy

attribute [local instance] AddSubgroup.torsionBy.zmodModule in
open Stacks.Picard NumericalType in
/-- **Case (A) of Section 0CEG on the Picard groups.** If `Pic(T)[ℓ] = 0` for the numerical type
`T` of `X`, the prime `ℓ` is invertible in `k` and prime to the multiplicities, and
`Pic(C)[ℓ] ≅ (𝐙/ℓ𝐙)^{⊕2}`, then `(𝐙/ℓ𝐙)^{⊕2}` embeds into `Pic((X_k)_{red})[ℓ]` (Tags 0CAD,
0CAE). -/
theorem two_le_finrank_picardTorsion_specialFiberRed
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit ((ℓ : ℤ) : S.k))
    (hcop : Nat.Coprime ℓ (Finset.univ.gcd S.specialFiberMultiplicity))
    (hT : Submodule.torsionBy ℤ (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ) = ⊥)
    (htors : Nonempty (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+ (Fin 2 → ZMod ℓ)))
    [FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme S.specialFiberRed) (ℓ : ℤ))] :
    2 ≤ Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme S.specialFiberRed) (ℓ : ℤ)) := by
  obtain ⟨τ⟩ := htors
  have hℓ1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  obtain ⟨hinj, hex⟩ := S.picardTorsionSequence_exact n e hℓ1 hcop
  have hsurj : Function.Surjective (S.picardTorsionRestriction (ℓ : ℤ)) := by
    intro y
    have h0 : S.picardTorsionToNumericalType n e (ℓ : ℤ) y = 0 := by
      apply Subtype.ext
      have hz := (S.picardTorsionToNumericalType n e (ℓ : ℤ) y).2
      generalize ((S.picardTorsionToNumericalType n e (ℓ : ℤ) y :
        picardGroup (S.associatedNumericalType n e))) = z at hz ⊢
      rw [hT] at hz
      exact (Submodule.mem_bot ℤ).1 hz
    exact (hex y).1 h0
  let r := LinearEquiv.ofBijective (S.picardTorsionRestriction (ℓ : ℤ)) ⟨hinj, hsurj⟩
  let c : AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+
      Submodule.torsionBy ℤ (ofScheme S.C) (ℓ : ℤ) := AddEquiv.refl _
  let φ : (Fin 2 → ZMod ℓ) →+ AddSubgroup.torsionBy (ofScheme S.specialFiberRed) (ℓ : ℤ) :=
    (S.picardTorsionToSpecialFiberRed ℓ).comp
      (r.symm.toAddEquiv.toAddMonoidHom.comp (c.toAddMonoidHom.comp τ.symm.toAddMonoidHom))
  have hφ : Function.Injective φ :=
    (S.injective_picardTorsionToSpecialFiberRed ℓ hℓ).comp
      (r.symm.injective.comp (c.injective.comp τ.symm.injective))
  exact two_le_finrank_of_injective_addMonoidHom φ hφ

attribute [local instance] AddSubgroup.torsionBy.zmodModule in
open Stacks.Picard NumericalType in
/-- **Case (B) of Section 0CEG on the Picard groups.** If `Pic(T)[ℓ]` has dimension at most one
for the numerical type `T` of `X`, the prime `ℓ` is prime to the multiplicities, and
`Pic(C)[ℓ] ≅ (𝐙/ℓ𝐙)^{⊕2}`, then `Pic(X)[ℓ] ≠ 0`: otherwise `Pic(C)[ℓ]` would embed into
`Pic(T)[ℓ]` (Tag 0CAD). -/
theorem exists_ne_zero_picardTorsion_model [DecidableEq (irreducibleComponents S.specialFiber)]
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) (ℓ : ℕ) [Fact ℓ.Prime]
    (hcop : Nat.Coprime ℓ (Finset.univ.gcd S.specialFiberMultiplicity))
    (hT : Module.finrank (ZMod ℓ)
      (AddSubgroup.torsionBy (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ)) ≤ 1)
    (htors : Nonempty (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+ (Fin 2 → ZMod ℓ))) :
    ∃ x : Submodule.torsionBy ℤ (ofScheme S.X) (ℓ : ℤ), x ≠ 0 := by
  obtain ⟨τ⟩ := htors
  have hℓ1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  obtain ⟨-, hex⟩ := S.picardTorsionSequence_exact n e hℓ1 hcop
  by_contra hall
  push Not at hall
  have htinj : Function.Injective (S.picardTorsionToNumericalType n e (ℓ : ℤ)) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    rw [hall x, map_zero]
  let c : AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+
      Submodule.torsionBy ℤ (ofScheme S.C) (ℓ : ℤ) := AddEquiv.refl _
  let d : Submodule.torsionBy ℤ (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ) ≃+
      AddSubgroup.torsionBy (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ) :=
    AddEquiv.refl _
  let φ : (Fin 2 → ZMod ℓ) →+
      AddSubgroup.torsionBy (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ) :=
    d.toAddMonoidHom.comp ((S.picardTorsionToNumericalType n e (ℓ : ℤ)).toAddMonoidHom.comp
      (c.toAddMonoidHom.comp τ.symm.toAddMonoidHom))
  have hφ : Function.Injective φ :=
    d.injective.comp (htinj.comp (c.injective.comp τ.symm.injective))
  have : Finite (AddSubgroup.torsionBy (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ)) :=
    NumericalType.finite_torsionBy_int (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  have : Module.Finite (ZMod ℓ)
      (AddSubgroup.torsionBy (picardGroup (S.associatedNumericalType n e)) (ℓ : ℤ)) :=
    Module.Finite.of_finite
  have := two_le_finrank_of_injective_addMonoidHom φ hφ
  omega

open Stacks.Picard in
/-- **A nonzero `ℓ`-torsion class on the model survives on the geometric special fibre.** Let
`X_k` be reduced with `H⁰(X_k, 𝒪) = k` and let `ℓ` be invertible in `k`. A nonzero class in
`Pic(X)[ℓ]` restricts to a nonzero class on `(X_k)_{red} = X_k` (Tag 0CAE), and that class stays
nonzero after any extension of the ground field (Tag 0CC5). -/
theorem exists_ne_zero_picardTorsion_specialFiber_baseChange [IsReduced S.specialFiber]
    [IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop)]
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℤ) : S.k)) (x : Submodule.torsionBy ℤ (ofScheme S.X) (ℓ : ℤ))
    (hx : x ≠ 0) (K : Type u) [Field K] [Algebra S.k K] :
    ∃ y : AddSubgroup.torsionBy (ofScheme (pullback S.specialFiberToSpec
      (Spec.map (CommRingCat.ofHom (algebraMap S.k K))))) (ℓ : ℤ), y ≠ 0 := by
  set M := schemePullbackClassHom S.specialFiberι (x : ofScheme S.X) with hM
  have hMne : M ≠ 0 := by
    intro h0
    have hz : S.picardTorsionToSpecialFiberRed ℓ x = 0 := by
      apply Subtype.ext
      show schemePullbackClass S.specialFiberRedι (x : ofScheme S.X) = 0
      have : S.specialFiberRedι = S.specialFiber.reductionι ≫ S.specialFiberι := rfl
      rw [this, ← schemePullbackClass_comp]
      show schemePullbackClassHom S.specialFiber.reductionι M = 0
      rw [h0, map_zero]
    exact hx ((S.injective_picardTorsionToSpecialFiberRed ℓ hℓ).eq_iff.1
      (hz.trans (map_zero _).symm))
  let : Field Γ(S.specialFiber, ⊤) :=
    (((asIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      S.specialFiberToSpec.appTop)).commRingCatIsoToRingEquiv.symm).isField
        (Field.toIsField S.k)).toField
  have hinj := Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_fieldExtension
    S.specialFiber (algebraMap S.k K) S.specialFiberToSpec
  refine ⟨⟨schemePullbackClassHom (pullback.fst S.specialFiberToSpec
    (Spec.map (CommRingCat.ofHom (algebraMap S.k K)))) M, ?_⟩, ?_⟩
  · show (ℓ : ℤ) • schemePullbackClassHom _ M = 0
    rw [← map_zsmul, hM, ← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero,
      map_zero]
  · intro h0
    apply hMne
    apply hinj
    rw [map_zero]
    exact congrArg Subtype.val h0

/-! ### Case (A): the special fibre is smooth -/

/-- A component of positive genus forces the numerical type to have one component: on a minimal
numerical type of genus one with more than one component every index is a minus-two index, of
genus zero. -/
theorem componentCount_eq_one_of_componentGenus_ne_zero (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (hg : genus S.C_to_K = 1) (Z : irreducibleComponents S.specialFiber)
    (hZ : S.specialFiberComponentGenus Z ≠ 0) : n = 1 := by
  have hgenus : (S.associatedNumericalType n e).genus = 1 := by
    rw [(S.associatedNumericalType_spec_and_genus n e).2, hg]
    rfl
  by_contra hn
  have hpos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    exact (Fin.elim0 (e.symm Z))
  have h := NumericalType.forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one _ hmin hgenus
    (by change 1 < n; omega) (e.symm Z)
  have h1 := h.1
  rw [associatedNumericalType_componentGenus, e.apply_symm_apply] at h1
  exact hZ (by exact_mod_cast h1)

/-- **Case (A) of Section 0CEG, the geometric conclusion.** Let `X` be a minimal model (its
numerical type `T` minimal) of a genus-one curve with a `K`-rational point, with
`h¹((X_k)_{red}) ≤ 1` and `g_geom(X_k/k) ≥ 1`. Then the special fibre is a smooth curve of genus
one: some component has positive genus, so `T` has a single component; the bound
`g_top + g_geom ≤ h¹((X_k)_{red})` of Tag 0CEA is then an equality, so that component is smooth
over `k` (Tag 0CEE), and it is the whole special fibre, having multiplicity one. -/
theorem isSmoothGenusOneSpecialFiber_of_one_le_geometricGenus (p : Spec (.of S.K) ⟶ S.C)
    (hp : p ≫ S.C_to_K = 𝟙 _) (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hmin : NumericalType.IsMinimal (S.associatedNumericalType n e))
    (hg : genus S.C_to_K = 1)
    (h1red : Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) ≤ 1)
    (hgeom : 1 ≤ geometricGenus S.k S.specialFiberToSpec) :
    S.IsSmoothGenusOneSpecialFiber := by
  classical
  obtain ⟨⟨x, hxrat, hxsm, hx⟩, hΓ, hgX⟩ :=
    S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq p hp
  -- some component has positive genus
  obtain ⟨Z, hZ⟩ : ∃ Z, S.specialFiberComponentGenus Z ≠ 0 := by
    by_contra hall
    push Not at hall
    have := S.geometricGenus_specialFiberToSpec_eq_zero hall
    omega
  have hn := S.componentCount_eq_one_of_componentGenus_ne_zero n e hmin hg Z hZ
  subst hn
  -- the numerical type has topological genus zero
  have htop : (S.associatedNumericalType 1 e).topologicalGenus = 0 := by
    have hedge : NumericalType.edgeCount (S.associatedNumericalType 1 e) = 0 := by
      unfold NumericalType.edgeCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter] at hab
      have h1 : a.val < b.val := hab.2.1
      have h2 : b.val < 1 := b.isLt
      omega
    unfold NumericalType.topologicalGenus
    rw [hedge, associatedNumericalType_componentCount]
    norm_num
  have hbound := S.topologicalGenus_add_geometricGenus_le_finrank_reduction x hxrat hxsm 1 e
  rw [htop] at hbound
  have heq : (S.associatedNumericalType 1 e).topologicalGenus +
      (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
    rw [htop]
    omega
  obtain ⟨-, hsmooth, -⟩ :=
    S.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction x hxrat hxsm 1 e heq
  -- the unique component is the whole special fibre
  let Z₀ : irreducibleComponents S.specialFiber :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hall : ∀ W : irreducibleComponents S.specialFiber, W = Z₀ := fun W =>
    (e.symm.injective (Subsingleton.elim _ _))
  have hm : ∀ W, S.specialFiberMultiplicity W = 1 := fun W => by
    rw [hall W]
    exact (hx Z₀ mem_irreducibleComponent).2
  have := S.isReduced_specialFiber_of_multiplicity_eq_one hm
  have : Surjective (S.specialFiberComponentι Z₀) := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ (Z₀ : Set S.specialFiber) := by
      have := hall ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
      rw [← this]
      exact mem_irreducibleComponent
    rw [← RegularModelSituation.range_specialFiberComponentι] at hy
    exact hy
  have : IsIso (S.specialFiberComponentι Z₀) :=
    isIso_of_isClosedImmersion_of_surjective _
  have : Smooth (S.specialFiberComponentToSpec Z₀) := (hsmooth Z₀ mem_irreducibleComponent).1
  have hfac : S.specialFiberToSpec =
      inv (S.specialFiberComponentι Z₀) ≫ S.specialFiberComponentToSpec Z₀ := by
    rw [IsIso.eq_inv_comp]
    rfl
  refine ⟨?_, hΓ, hgX.trans hg⟩
  rw [hfac]
  infer_instance

/-! ### Case (B): the special fibre is a cycle of projective lines -/

omit S in
/-- A point rational over the field of global functions is rational over the ground field when
the global functions are the constants. -/
theorem _root_.AlgebraicGeometry.isRationalPoint_of_isRationalPoint_toSpecΓ {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hF : IsField Γ(X, ⊤)) (x : X)
    (h : letI : Field Γ(X, ⊤) := hF.toField; IsRationalPoint X.toSpecΓ x) :
    IsRationalPoint f x := by
  let : Field Γ(X, ⊤) := hF.toField
  have hf : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  unfold IsRationalPoint at h ⊢
  rw [hf, ← Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  have := h
  infer_instance

open NumericalType.GenusOne in
/-- **Case (B) of Section 0CEG, the shape of the special fibre.** Suppose the special fibre has
at-worst-nodal singularities, every component is smooth over `k`, every component has weight one
and genus zero, and the numerical type is the cycle on `n' ≥ 3` components. Then the special
fibre is a cycle of rational curves: each component meets its successor with intersection number
`1 = [κ : k]`, so it has a `k`-rational point (and it is a smooth curve of genus zero with
`H⁰ = k`), hence it is a projective line by Tag 0C6U, which enters as the hypothesis `h0C6U`. -/
theorem isCycleOfRationalCurves_of_cycle
    (h0C6U : ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsCurve k f] [Smooth f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)],
      genus f = 0 → (∃ x, IsRationalPoint f x) →
        Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))))
    (hnodal : letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
      Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber)
    (hsm : ∀ Z, Smooth (S.specialFiberComponentToSpec Z))
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (hwg : ∀ i, (S.associatedNumericalType n e).weight i = 1 ∧
      (S.associatedNumericalType n e).componentGenus i = 0)
    (n' : ℕ) (e' : Fin n' ≃ Fin (S.associatedNumericalType n e).componentCount) (h3 : 3 ≤ n')
    (hcyc : ∀ i j, (S.associatedNumericalType n e).intersection (e' i) (e' j) =
      longIntersection .cycle n' i j) :
    S.IsCycleOfRationalCurves := by
  let E : Fin n' ≃ irreducibleComponents S.specialFiber := e'.trans e
  have hM : ∀ i j, i ≠ j → S.specialFiberIntersectionMatrix (E i) (E j) =
      (if j.val = (i.val + 1) % n' then 1 else 0) +
        (if i.val = (j.val + 1) % n' then 1 else 0) := by
    intro i j hij
    rw [← longIntersection_cycle_of_ne h3 hij, ← hcyc]
    rfl
  refine ⟨hnodal, fun Z => ?_, n', E, by omega, hM⟩
  have hw : S.specialFiberComponentWeight Z = 1 := by
    simpa using (hwg (e.symm Z)).1
  have hg : S.specialFiberComponentGenus Z = 0 := by
    simpa using (hwg (e.symm Z)).2
  have hF := (S.isField_and_finite_globalSections_specialFiberComponent Z).1
  have : Nontrivial Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hF.nontrivial
  have : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop) :=
    isIso_constants_of_finrank_globalSections_eq_one (S.specialFiberComponentToSpec Z) hw
  have := S.isCurve_specialFiberComponentToSpec Z
  have := hsm Z
  have hgenus : genus (S.specialFiberComponentToSpec Z) = 0 := by
    rw [S.genus_specialFiberComponentToSpec, hg, mul_zero]
  -- the successor of `Z` in the cycle
  set i₀ := E.symm Z with hi₀
  have hsucc : (i₀.val + 1) % n' < n' := Nat.mod_lt _ (by omega)
  let j₀ : Fin n' := ⟨(i₀.val + 1) % n', hsucc⟩
  have hij : i₀ ≠ j₀ := by
    intro h
    have h' : i₀.val = (i₀.val + 1) % n' := congrArg Fin.val h
    have hi := i₀.isLt
    rcases Nat.lt_or_ge (i₀.val + 1) n' with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at h'
      omega
    · have : i₀.val + 1 = n' := by omega
      rw [this, Nat.mod_self] at h'
      omega
  have hZ : E i₀ = Z := E.apply_symm_apply Z
  have hne : Z ≠ E j₀ := by
    rw [← hZ]
    exact E.injective.ne hij
  have hint : S.specialFiberIntersectionMatrix Z (E j₀) = S.specialFiberComponentWeight Z := by
    rw [← hZ, hM i₀ j₀ hij, hZ, hw]
    have h1 : j₀.val = (i₀.val + 1) % n' := rfl
    have h2 : i₀.val ≠ (j₀.val + 1) % n' := by
      have hi := i₀.isLt
      rcases Nat.lt_or_ge (i₀.val + 1) n' with h1' | h1'
      · have hj : j₀.val = i₀.val + 1 := by rw [h1, Nat.mod_eq_of_lt h1']
        rw [hj]
        rcases Nat.lt_or_ge (i₀.val + 2) n' with h2' | h2'
        · rw [Nat.mod_eq_of_lt h2']
          omega
        · have : i₀.val + 1 + 1 = n' := by omega
          rw [this, Nat.mod_self]
          omega
      · have hj : j₀.val = 0 := by
          rw [h1, show i₀.val + 1 = n' by omega, Nat.mod_self]
        rw [hj, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [ite_eq_left h1, ite_eq_right h2]
    norm_num
  obtain ⟨c, hc, -⟩ :=
    S.exists_isRationalPoint_smoothAt_toSpecΓ_of_componentIntersection_eq_weight hne hint
  exact h0C6U S.k _ (S.specialFiberComponentToSpec Z) hgenus
    ⟨c, isRationalPoint_of_isRationalPoint_toSpecΓ _ hF c hc⟩

/-! ### The local statement -/

omit S in
/-- A positive integer below a prime `ℓ` is prime to `ℓ`. -/
private theorem isCoprime_natCast_of_pos_of_lt {ℓ : ℕ} (hℓ : ℓ.Prime) {z : ℤ} (hz : 0 < z)
    (hzℓ : z < ℓ) : IsCoprime (ℓ : ℤ) z := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hzabs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz.le
  have hlt : z.natAbs < ℓ := by exact_mod_cast (hzabs ▸ hzℓ)
  have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz.ne'
  show Nat.Coprime ℓ z.natAbs
  exact (hℓ.coprime_iff_not_dvd).2 fun hdvd => absurd (Nat.le_of_dvd hpos hdvd) (by omega)

attribute [local instance] AddSubgroup.torsionBy.zmodModule in
open NumericalType NumericalType.GenusOne Stacks.Picard in
/-- **The local statement of Section 0CEG.** Let `X ⟶ Spec(R)` be a regular proper model (Tag
0C61) of a smooth projective curve `C` of genus one with a `K`-rational point and with
`Pic(C)[ℓ] ≅ (𝐙/ℓ𝐙)^{⊕2}` for a prime `ℓ ≥ 7` invertible in `k`. Suppose the numerical type of
`X` is minimal (Tag 0CA6 for a minimal model, `hmin`) and `h¹((X_k)_{red}, 𝒪) ≤ 1` (`h1red`: the
surjectivity of Tag 0CE9 together with Tag 0CE8). Then `X` is at-worst-nodal of relative
dimension one over `R`, and its special fibre is a smooth curve of genus one or a cycle of rational
curves.

The Tags 0CE6, 0C20 and 0C6U enter as the hypotheses `h0CE6`, `h0C20`, `h0C20eq` and `h0C6U`,
in the form in which they are used. -/
theorem genusOne_local
    (h0CE6 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
      (_hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : k)),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
          genus g + geometricGenus k g)
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
    (h0C6U : ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsCurve k f] [Smooth f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)],
      genus f = 0 → (∃ x, IsRationalPoint f x) →
        Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))))
    (hmin : ∀ (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber),
      IsMinimal (S.associatedNumericalType n e))
    (h1red : Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) ≤ 1)
    (hg : genus S.C_to_K = 1) (p : Spec (.of S.K) ⟶ S.C) (hp : p ≫ S.C_to_K = 𝟙 _)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ7 : 7 ≤ ℓ) (hℓ : (ℓ : S.k) ≠ 0)
    (htors : Nonempty (AddSubgroup.torsionBy (ofScheme S.C) (ℓ : ℤ) ≃+ (Fin 2 → ZMod ℓ))) :
    IsAtWorstNodalOfRelativeDimensionOne S.X_to_R ∧
      (S.IsSmoothGenusOneSpecialFiber ∨ S.IsCycleOfRationalCurves) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  let n := Fintype.card (irreducibleComponents S.specialFiber)
  let e : Fin n ≃ irreducibleComponents S.specialFiber := (Fintype.equivFin _).symm
  set T := S.associatedNumericalType n e with hT
  have hTmin : IsMinimal T := hmin n e
  have hTg : T.genus = 1 := by
    rw [hT, (S.associatedNumericalType_spec_and_genus n e).2, hg]
    rfl
  obtain ⟨i₀, hm₀, hw₀⟩ := S.exists_multiplicity_eq_one_and_weight_eq_one p hp n e
  have hm₀' : S.specialFiberMultiplicity (e i₀) = 1 := by
    have h := (S.associatedNumericalType_multiplicity n e i₀).symm.trans hm₀
    exact_mod_cast h
  have hcop : Nat.Coprime ℓ (Finset.univ.gcd S.specialFiberMultiplicity) := by
    rw [S.gcd_specialFiberMultiplicity_eq_one hm₀']
    exact Nat.coprime_one_right ℓ
  have hℓunit : IsUnit ((ℓ : ℤ) : S.k) := by
    rw [Int.cast_natCast]
    exact isUnit_iff_ne_zero.mpr hℓ
  obtain ⟨⟨x, hxrat, hxsm, -⟩, hΓ, hgX⟩ :=
    S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq p hp
  have : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) := hΓ
  have hdimX : topologicalKrullDim S.specialFiber = 1 :=
    S.topologicalKrullDim_specialFiber S.nonempty_specialFiber
  rcases tree_or_cycle_of_isMinimal_of_genus_eq_one T hTmin hTg i₀ hm₀ hw₀ with
    ⟨hedge, hmlt, hilt⟩ | ⟨hall, n', e', h3, hcyc⟩
  · -- case (A)
    have hℓA : ∀ i j, 0 < T.intersection i j → IsCoprime (ℓ : ℤ) (T.intersection i j) :=
      fun i j h => isCoprime_natCast_of_pos_of_lt hℓp h (by have := hilt i j; omega)
    have hℓm : ∀ i, IsCoprime (ℓ : ℤ) (T.multiplicity i) :=
      fun i => isCoprime_natCast_of_pos_of_lt hℓp (T.multiplicity_pos i)
        (by have := hmlt i; omega)
    have hTbot := torsionBy_picardGroup_eq_bot T ℓ hedge hℓA hℓm
    have hdimred : topologicalKrullDim S.specialFiber.reduction ≤ 1 :=
      le_trans
        S.specialFiber.reductionι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
        hdimX.le
    obtain ⟨hfd, hbound⟩ := h0CE6 S.k (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
      hdimred ℓ (by simpa using hℓunit)
    have := hfd
    have h2 := S.two_le_finrank_picardTorsion_specialFiberRed n e ℓ hℓunit hcop hTbot htors
    have hgenusred : genus (S.specialFiber.reductionι ≫ S.specialFiberToSpec) =
        Module.finrank S.k (cohomologyOverField S.k
          (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
          (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
      rw [genus_eq_finrank_structureSheafCohomology]
      exact (structureSheafCohomologyIsoCohomologyOverField S.k _ 1).toLinearEquiv.finrank_eq
    have hgeomred := (geometricGenus_reduction S.specialFiberToSpec).symm
    have hgeom : 1 ≤ geometricGenus S.k S.specialFiberToSpec := by
      have := h2.trans hbound
      rw [hgenusred, hgeomred] at this
      omega
    have hsmooth := S.isSmoothGenusOneSpecialFiber_of_one_le_geometricGenus p hp n e hTmin hg
      h1red hgeom
    refine ⟨S.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber ?_, Or.inl hsmooth⟩
    let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    have : Smooth (S.specialFiber ↘ Spec (.of S.k)) := hsmooth.1
    exact Stacks.Curves.hasAtWorstNodalSingularities_of_smooth S.k S.specialFiber
  · -- case (B)
    have hmult : ∀ Z, S.specialFiberMultiplicity Z = 1 := fun Z => by
      simpa [T] using (hall (e.symm Z)).1
    have : IsReduced S.specialFiber := S.isReduced_specialFiber_of_multiplicity_eq_one hmult
    have htop : T.topologicalGenus = 1 := topologicalGenus_eq_one_of_cycle T e' h3 hcyc
    have hgeom0 : geometricGenus S.k S.specialFiberToSpec = 0 := by
      have hzero : ∀ Z, S.specialFiberComponentGenus Z = 0 := fun Z => by
        simpa [T] using (hall (e.symm Z)).2.2
      exact S.geometricGenus_specialFiberToSpec_eq_zero hzero
    have hbound := S.topologicalGenus_add_geometricGenus_le_finrank_reduction x hxrat hxsm n e
    have heq : T.topologicalGenus + (geometricGenus S.k S.specialFiberToSpec : ℤ) =
        Module.finrank S.k (cohomologyOverField S.k
          (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
          (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
      rw [htop, hgeom0] at hbound ⊢
      push_cast at hbound ⊢
      omega
    have hsm : ∀ Z, Smooth (S.specialFiberComponentToSpec Z) :=
      S.smooth_specialFiberComponentToSpec_of_eq x hxrat hxsm n e heq hmult hTmin
    have hred := S.isReduced_pullback_specialFiberToSpec_of_smooth hsm (AlgebraicClosure S.k)
    -- the Picard group of the geometric special fibre has nonzero `ℓ`-torsion
    have hℓA : ∀ i j, 0 < T.intersection i j → IsCoprime (ℓ : ℤ) (T.intersection i j) := by
      intro i j hpos
      obtain ⟨a, rfl⟩ := e'.surjective i
      obtain ⟨b, rfl⟩ := e'.surjective j
      refine isCoprime_natCast_of_pos_of_lt hℓp hpos ?_
      have h4 := longIntersection_le_four .cycle n' a b
      rw [hcyc] at hpos ⊢
      omega
    have hℓm : ∀ i, IsCoprime (ℓ : ℤ) (T.multiplicity i) := fun i => by
      rw [(hall i).1]
      exact isCoprime_one_right
    have hT1 : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) ≤ 1 := by
      have h := finrank_torsionBy_picardGroup_add_componentCount_le T ℓ hℓA hℓm
      unfold topologicalGenus at htop
      omega
    obtain ⟨x₀, hx₀⟩ := S.exists_ne_zero_picardTorsion_model n e ℓ hcop hT1 htors
    obtain ⟨y, hy⟩ := S.exists_ne_zero_picardTorsion_specialFiber_baseChange ℓ hℓunit x₀ hx₀
      (AlgebraicClosure S.k)
    have hnt := nontrivial_of_ne y 0 hy
    set a := Spec.map (CommRingCat.ofHom (algebraMap S.k (AlgebraicClosure S.k))) with ha
    let : (pullback S.specialFiberToSpec a).Over (Spec (.of (AlgebraicClosure S.k))) :=
      ⟨pullback.snd S.specialFiberToSpec a⟩
    have : IsProper ((pullback S.specialFiberToSpec a) ↘ Spec (.of (AlgebraicClosure S.k))) :=
      inferInstanceAs (IsProper (pullback.snd S.specialFiberToSpec a))
    have hdimbar : topologicalKrullDim (pullback S.specialFiberToSpec a : Scheme.{u}) = 1 := by
      rw [topologicalKrullDim_baseChange S.k (AlgebraicClosure S.k) (pullback.fst _ _)
        (pullback.snd _ _) S.specialFiberToSpec (IsPullback.of_hasPullback _ _)]
      exact hdimX
    have hℓ' : (ℓ : AlgebraicClosure S.k) ≠ 0 := by
      rw [← map_natCast (algebraMap S.k (AlgebraicClosure S.k))]
      exact (map_ne_zero _).2 hℓ
    have hfdbar := (h0C20 (AlgebraicClosure S.k) (pullback S.specialFiberToSpec a) hdimbar ℓ
      hℓ').1
    have hrank := Module.finrank_pos (R := ZMod ℓ)
      (M := AddSubgroup.torsionBy (ofScheme (pullback S.specialFiberToSpec a)) (ℓ : ℤ))
    have hgbar : genus (pullback.snd S.specialFiberToSpec a) = 1 := by
      rw [ha, genus_pullback_snd_eq, hgX, hg]
    have hggbar : geometricGenus (AlgebraicClosure S.k) (pullback.snd S.specialFiberToSpec a) =
        0 := by
      rw [ha, ← geometricGenus_eq_geometricGenus_pullback_snd S.k S.specialFiberToSpec hdimX.le,
        hgeom0]
    have hnodal := S.hasAtWorstNodalSingularities_specialFiber_of_le_finrank h0C20 h0C20eq hred
      ℓ hℓ (by rw [← ha, hgbar, hggbar]; omega)
    refine ⟨S.isAtWorstNodalOfRelativeDimensionOne_of_specialFiber hnodal, Or.inr ?_⟩
    exact S.isCycleOfRationalCurves_of_cycle h0C6U hnodal hsm n e
      (fun i => ⟨(hall i).2.1, (hall i).2.2⟩) n' e' h3 hcyc

end RegularProperModelSituation

end Stacks.Models
