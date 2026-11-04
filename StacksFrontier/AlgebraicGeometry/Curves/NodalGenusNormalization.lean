module

public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkLength
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank

/-!
# The genus of a nodal curve and of its normalization

Let `X` be a proper curve over an algebraically closed field `k` all of whose singular points are
nodes, and let `ν : X^ν ⟶ X` be its normalization. The quotient `𝒬 = ν_* 𝒪_{X^ν} / 𝒪_X` has a
one-dimensional stalk at every node, so `dim_k H⁰(X, 𝒬)` is the number of nodes, and the long
exact sequence of `0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X^ν} ⟶ 𝒬 ⟶ 0` bounds the genus:

  `g(X) ≤ g(X^ν) + #(nodes of X)`.

## Main results

* `AlgebraicGeometry.finrank_normalizationQuotientStalk_eq_one_of_isNode`: at a node the stalk of
  `𝒬` is one-dimensional over `k`.
* `AlgebraicGeometry.genus_le_genus_normalization_add_ncard_singularLocus`: the genus bound.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.NormalizationQuotient
open Stacks.Curves
  (isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- **At a node, the stalk of `ν_* 𝒪_{X^ν} / 𝒪_X` is one-dimensional over `k`**, for `k`
algebraically closed. Its length over `𝒪_{X,x}` is the delta invariant, which is one at a node
([Stacks, Tag 0C1R]), and the residue field at the closed point `x` is `k`. -/
theorem finrank_normalizationQuotientStalk_eq_one_of_isNode [IsAlgClosed k] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1) (x : X)
    (hnode : Stacks.Curves.IsNode k X x) :
    Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        (X ↘ Spec (.of k)).appTop ≫ X.presheaf.germ ⊤ x trivial).hom).obj
        (normalizationQuotientStalk X
          (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))) x)) = 1 := by
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k))
  set A := X.presheaf.stalk x
  set φ : k →+* A := ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
    X.presheaf.germ ⊤ x trivial).hom
  set Q := normalizationQuotientStalk X hX x
  let : Algebra k A := φ.toAlgebra
  let : Module k Q := Module.compHom Q φ
  have : IsScalarTower k A Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalHom (algebraMap k A) :=
    ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha; exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have hlen := IsLocalRing.length_restrictScalars (A := k) (B := A) (M := Q)
  have hδ : Module.length A Q = 1 := by
    rw [length_normalizationQuotientStalk X hX x]
    exact (isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim x hnode).2.1
  -- the residue field at `x` is `k`
  have hκ : Module.length k (IsLocalRing.ResidueField A) = 1 := by
    let : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation x).hom.toAlgebra
    have h1 := finrank_residueField_of_isClosed (X ↘ Spec (.of k)) x hnode.isClosed
    have : Module.Finite k (X.residueField x) := Module.finite_of_finrank_eq_succ h1
    have e : X.residueField x ≃ₗ[k] IsLocalRing.ResidueField A :=
      { AddEquiv.refl _ with map_smul' := fun c y => rfl }
    rw [← e.length_eq, Module.length_eq_finrank, h1]
    rfl
  rw [← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k)
    (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, hδ, hκ, one_mul] at hlen
  have hfin : Module.Finite k Q := by
    have h : IsFiniteLength k Q := Module.length_ne_top_iff.mp (by rw [hlen]; exact ENat.one_ne_top)
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
    exact Module.IsNoetherian.finite k Q
  have e : ((ModuleCat.restrictScalars φ).obj Q) ≃ₗ[k] Q :=
    { AddEquiv.refl _ with map_smul' := fun c y => rfl }
  rw [e.finrank_eq]
  have := Module.length_eq_finrank k Q
  rw [hlen] at this
  exact_mod_cast this.symm

/-- **The genus of a nodal curve is at most the genus of its normalization plus the number of
its nodes.** Let `X` be a proper curve over an algebraically closed field `k` all of whose
singular points are nodes, and `ν : X^ν ⟶ X` its normalization. The Euler characteristics in
`0 ⟶ 𝒪_X ⟶ ν_* 𝒪_{X^ν} ⟶ 𝒬 ⟶ 0`, with `H¹(X, 𝒬) = 0`, `H⁰(X, 𝒪_X) ⊆ H⁰(X^ν, 𝒪_{X^ν})` and
`dim_k H⁰(X, 𝒬) = #Sing(X)` (one dimension per node), give the bound. -/
theorem genus_le_genus_normalization_add_ncard_singularLocus [IsAlgClosed k]
    [IsCurve k (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hsing : ∀ x ∈ singularLocus X, Stacks.Curves.IsNode k X x) :
    (genus (X ↘ Spec (.of k)) : ℤ) ≤
      genus (normalizationOverField k (X ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))) +
        (singularLocus X).ncard := by
  set f := X ↘ Spec (.of k)
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  have hdim1 : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) f
  have hdim : topologicalKrullDim X ≤ 1 := hdim1.le
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite (normalizationOverField k f) := isFinite_normalizationOverField k f
  have : IsLocallyNoetherian (normalizationSchemeOverField k f) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField k f ≫ f)
  have : (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have : (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hS := shortExact_normalizationSequence k f
  have hQcoh := isCoherent_normalizationQuotient k f
  have hQsupp := topologicalKrullDim_supp_normalizationQuotient_le_zero k f
  have hOX : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hP : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward (normalizationOverField k f)).obj
      (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite _ _
  -- the Euler characteristics
  have hvan : ∀ (F : X.Modules) (m : ℕ), 2 ≤ m → IsZero (cohomologyOverField k f F m) :=
    fun F m hm => isZero_cohomologyOverField_two_le k f hdim F m hm
  have hsum := finsum_alternating_finrank_cohomologyOverField_add_of_shortExact_of_outer k f hS 2
    (fun n _ => @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hOX n)
    (fun n _ => @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hQcoh n)
    (hvan _) (hvan _)
  simp only [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f _ (hvan _)]
    at hsum
  -- `H¹(X, 𝒬) = 0`
  have h1Q : Module.finrank k (cohomologyOverField k f (normalizationQuotient X hX) 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero
      (@isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k _ X f _ _ hQcoh hQsupp 1
        Nat.one_pos)
    exact Module.finrank_zero_of_subsingleton
  -- `H⁰(X, 𝒪_X) ⊆ H⁰(X, ν_* 𝒪_{X^ν})`
  have h0 : Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) ≤
      Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
        (normalizationOverField k f)).obj
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 0) := by
    obtain ⟨-, hinj, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
    have := @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ _ hP 0
    exact LinearMap.finrank_le_finrank_of_injective hinj
  -- the genus of the normalization
  have h1P : Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
      (normalizationOverField k f)).obj
      (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 1) =
      genus (normalizationOverField k f ≫ f) :=
    (finrank_cohomologyOverField_pushforward_of_isAffineHom k (normalizationOverField k f) f
      _ 1).symm.trans (finrank_cohomologyOverField_one_unit_eq_genus k _)
  have h1O := finrank_cohomologyOverField_one_unit_eq_genus k f
  -- `dim_k H⁰(X, 𝒬)` is the number of nodes
  have hQ0 : Module.finrank k (cohomologyOverField k f (normalizationQuotient X hX) 0) =
      (singularLocus X).ncard := by
    classical
    let : Fintype ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)) :=
      (finite_supp_of_supp_le_zero k f _ hQsupp).fintype
    rw [@finrank_cohomologyOverField_zero_eq_sum_finrank_stalk k _ X f _ _ hQcoh hQsupp]
    have hsupp := supp_normalizationQuotient k f
    have hterm : ∀ x : ↥(_root_.SheafOfModules.supp (normalizationQuotient X hX)),
        Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
          f.appLE ⊤ ⊤ (by simp) ≫ X.presheaf.germ ⊤ x.1 trivial).hom).obj
          (OXModule.stalk (normalizationQuotient X hX) x.1)) = 1 := fun x => by
      have hφ : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp) ≫
          X.presheaf.germ ⊤ x.1 trivial).hom = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x.1 trivial).hom :=
        congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t ≫
          X.presheaf.germ ⊤ x.1 trivial).hom) (appLE_top_top_eq_appTop f _)
      rw [congrArg (fun ψ : k →+* X.presheaf.stalk x.1 => Module.finrank k
        ((ModuleCat.restrictScalars ψ).obj (OXModule.stalk (normalizationQuotient X hX) x.1))) hφ]
      have hx : x.1 ∈ singularLocus X := hsupp ▸ x.2
      exact finrank_normalizationQuotientStalk_eq_one_of_isNode k X hdim1 x.1 (hsing x.1 hx)
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_univ, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hsupp]
  have key : (Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
        (normalizationOverField k f)).obj
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pushforward
        (normalizationOverField k f)).obj
        (SheafOfModules.unit (normalizationSchemeOverField k f).ringCatSheaf)) 1) : ℤ) =
      ((Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ)) +
      ((Module.finrank k (cohomologyOverField k f (normalizationQuotient X hX) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (normalizationQuotient X hX) 1) : ℤ)) :=
    hsum
  rw [h1Q, h1P, h1O, hQ0] at key
  have h0' := (Int.ofNat_le.mpr h0)
  push_cast at key h0' ⊢
  linarith

end AlgebraicGeometry

end
