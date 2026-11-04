module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularCompletionProper
public import StacksFrontier.RingTheory.ApproximationProperty.Core
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generizations of a point and the dimension of the local ring

A point `x'` of a scheme with `x' ⤳ x` is a *generization* of `x`; the local ring of `X` at such
a point is a localization of the local ring at `x`, namely the one cut out by the corresponding
prime of `𝒪_{X,x}` under `Spec 𝒪_{X,x} ⟶ X`. This file collects what an induction on
`dim 𝒪_{X,x}` over the generizations of `x` needs: the dimension of the local ring is monotone
along generization and drops strictly at a proper generization, a point of positive local
dimension has a generization whose local ring has dimension exactly one, and normality of
`𝒪_{X,x}`, regularity of `𝒪_{X,x}` and the dimension bound along a flat morphism all pass to
generizations.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_le_of_specializes` and
  `AlgebraicGeometry.ringKrullDim_stalk_lt_of_specializes`: monotonicity and strict drop of
  `dim 𝒪_{X,x}` along generization.
* `AlgebraicGeometry.exists_specializes_ringKrullDim_stalk_eq_one`: a point whose local ring has
  positive dimension has a generization whose local ring has dimension one.
* `AlgebraicGeometry.exists_preimage_ringKrullDim_stalk_ge`: a surjective closed map lifts a
  lower bound on the local dimension.
* `AlgebraicGeometry.isNormalRing_stalk_of_specializes`: normality of the local ring passes to
  generizations. Its regularity analogue is
  `AlgebraicGeometry.isRegularLocalRing_stalk_of_specializes`, already available in
  `StacksFrontier/AlgebraicGeometry/Spaces/RegularCompletionProper.lean`.
* `AlgebraicGeometry.exists_isOpen_subset_union_closure_singleton`: on a Noetherian sober space,
  an open set containing every proper generization of `x` contains a neighbourhood of `x` up to
  the closure of `x`.

## Implementation notes

The dimension of `𝒪_{X,x}` is read off the topology by Mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, which identifies it with the coheight of `x`
in the specialization order; monotonicity and the strict drop are then order-theoretic, and the
generization of dimension one comes from `Order.coe_lt_coheight_iff`.

Normality is `IsNormalRing`, the predicate of `StacksFrontier/RingTheory/IntegrallyClosed/Defs.lean`
asserting that every localization at a prime is an integrally closed domain. Its transfer to a
generization is not a localization argument in the statement: a generization of `x` is a point of
the image of `Spec 𝒪_{X,x} ⟶ X`, whose stalk maps isomorphically to the stalk of `Spec 𝒪_{X,x}`
at the corresponding prime, which is a localization of `𝒪_{X,x}`.

The regularity of the local rings of `Spec A` for a regular local ring `A`, which the purity
induction also uses, is the base's `AlgebraicGeometry.isRegularLocalRing_stalk_spec`
(`ResolutionOfSurfaces/Boundedness/RegularLocalRingRational.lean`); this file had its own copy of
that lemma, which is removed.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The dimension of the local ring is monotone along generization. -/
@[ega "IV 5.1.13" "special case"]
theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {x x' : X}
    (h : x' ⤳ x) :
    ringKrullDim (X.presheaf.stalk x') ≤ ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr (Order.coheight_anti (show x ≤ x' from h))

/-- In a locally Noetherian scheme every point has finite coheight. -/
private theorem coheight_lt_top {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    Order.coheight x < ⊤ := by
  apply WithBot.coe_lt_coe.mp
  simpa only [WithBot.coe_top, ← ringKrullDim_stalk_eq_coheight] using
    (ringKrullDim_lt_top (R := X.presheaf.stalk x))

/-- The dimension of the local ring drops strictly at a proper generization. -/
theorem ringKrullDim_stalk_lt_of_specializes {X : Scheme.{u}} [IsLocallyNoetherian X] {x x' : X}
    (h : x' ⤳ x) (hne : x' ≠ x) :
    ringKrullDim (X.presheaf.stalk x') < ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  apply WithBot.coe_lt_coe.mpr
  apply Order.coheight_strictAnti
  · exact lt_of_le_not_ge (show x ≤ x' from h) (fun h' ↦ hne (h.antisymm h').eq)
  · exact coheight_lt_top x'

/-- A point whose local ring has positive dimension has a generization whose local ring has
dimension exactly one. -/
theorem exists_specializes_ringKrullDim_stalk_eq_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) (hx : 1 ≤ ringKrullDim (X.presheaf.stalk x)) :
    ∃ x' : X, x' ⤳ x ∧ ringKrullDim (X.presheaf.stalk x') = 1 := by
  by_cases hdim : ringKrullDim (X.presheaf.stalk x) = 1
  · exact ⟨x, specializes_refl x, hdim⟩
  have hlt : (1 : ℕ∞) < Order.coheight x := by
    apply WithBot.coe_lt_coe.mp
    rw [← ringKrullDim_stalk_eq_coheight]
    exact lt_of_le_of_ne hx (Ne.symm hdim)
  obtain ⟨x', hxx', hx'⟩ := (Order.coe_lt_coheight_iff (coheight_lt_top x)).mp hlt
  refine ⟨x', hxx'.le, ?_⟩
  simpa only [Nat.cast_one, WithBot.coe_one, ringKrullDim_stalk_eq_coheight] using
    congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hx'

/-- A surjective closed map lifts a lower bound on the dimension of the local ring: each chain of
generizations of `y` is lifted one step at a time, a specializing map producing the preimage of
each step. -/
theorem exists_preimage_ringKrullDim_stalk_ge {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hclosed : IsClosedMap f)
    (hsurj : Function.Surjective f) (y : Y) (n : ℕ)
    (hy : (n : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)) :
    ∃ x : X, f x = y ∧ (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  induction n generalizing y with
  | zero =>
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, rfl, ringKrullDim_nonneg_of_nontrivial⟩
  | succ n ih =>
    have hlt : (n : ℕ∞) < Order.coheight y := by
      apply WithBot.coe_lt_coe.mp
      rw [← ringKrullDim_stalk_eq_coheight]
      exact (show (n : WithBot ℕ∞) < (n + 1 : ℕ) by exact_mod_cast Nat.lt_succ_self n).trans_le hy
    obtain ⟨z, hyz, hdz⟩ := (Order.coe_lt_coheight_iff (coheight_lt_top y)).mp hlt
    obtain ⟨x', hx', hdx'⟩ := ih z (by
      rw [ringKrullDim_stalk_eq_coheight, hdz]
      exact_mod_cast le_rfl)
    obtain ⟨x, hxx', hx⟩ := hclosed.specializingMap
      (show f x' ⤳ y from hx' ▸ hyz.le)
    have hne : x' ≠ x := fun heq ↦
      hyz.ne (hx.symm.trans ((congrArg f heq).symm.trans hx'))
    exact ⟨x, hx, by
      simpa only [Nat.cast_add, Nat.cast_one] using ENat.WithBot.add_one_le_iff.mpr
        (hdx'.trans_lt (ringKrullDim_stalk_lt_of_specializes hxx' hne))⟩

/-- The local ring of `X` at a point of the image of `Spec 𝒪_{X,x} ⟶ X` is the localization of
`𝒪_{X,x}` at the corresponding prime, so its dimension is that prime's height. -/
theorem ringKrullDim_stalk_fromSpecStalk (X : Scheme.{u}) (x : X)
    (q : Spec (X.presheaf.stalk x)) :
    ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x q)) =
      (q.asIdeal.height : WithBot ℕ∞) := by
  have := isIso_stalkMap_of_flat_isPreimmersion (X.fromSpecStalk x) q
  have : q.asIdeal.IsPrime := q.isPrime
  exact (asIso ((X.fromSpecStalk x).stalkMap q)).commRingCatIsoToRingEquiv.ringKrullDim.trans
    ((Spec.stalkIso (X.presheaf.stalk x) q).commRingCatIsoToRingEquiv.ringKrullDim.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)))

/-- Along a flat morphism the dimension of the local ring of the target at the image is at most
that of the source: a flat local homomorphism has going down, so the height of the maximal ideal
can only grow. -/
@[ega "IV 21.10.7" "special case"]
theorem ringKrullDim_stalk_le_of_flat {X' X : Scheme.{u}} (j : X' ⟶ X) [Flat j] (x' : X') :
    ringKrullDim (X.presheaf.stalk (j x')) ≤ ringKrullDim (X'.presheaf.stalk x') := by
  let R := X.presheaf.stalk (j x')
  let S := X'.presheaf.stalk x'
  let _ : Algebra R S := (j.stalkMap x').hom.toAlgebra
  have _ : IsLocalHom (algebraMap R S) := j.prop x'
  have _ : Module.Flat R S := Flat.stalkMap j x'
  have _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  have _ : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr (Ideal.height_le_height_of_liesOver_of_hasGoingDown _ _)

/-- Normality of the local ring passes to generizations. -/
theorem isNormalRing_stalk_of_specializes {X : Scheme.{u}} {x x' : X} (h : x' ⤳ x)
    (hx : IsNormalRing (X.presheaf.stalk x)) : IsNormalRing (X.presheaf.stalk x') := by
  obtain ⟨q, rfl⟩ := (show x' ∈ Set.range (X.fromSpecStalk x) by
    simpa only [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using h)
  have := isIso_stalkMap_of_flat_isPreimmersion (X.fromSpecStalk x) q
  have _ : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨hd, hn⟩ := hx q.asIdeal
  have _ : IsDomain (Localization.AtPrime q.asIdeal) := hd
  have _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := hn
  exact IsNormalRing.congr
    ((asIso ((X.fromSpecStalk x).stalkMap q)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso (X.presheaf.stalk x) q).commRingCatIsoToRingEquiv).symm
    (IsNormalRing.of_isIntegrallyClosed _)

/-- On a Noetherian sober space, an open set containing every proper generization of `x`
contains an open neighbourhood of `x` up to the closure of `x`.

The complement of the open set is a finite union of irreducible closed sets; discarding those
that do not contain `x` leaves an open neighbourhood of `x`, and a point of that neighbourhood
outside the open set lies in one of the retained pieces, whose generic point is then a
generization of `x` lying outside the open set, hence is `x` itself. -/
theorem exists_isOpen_subset_union_closure_singleton {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] (U : Set T) (hU : IsOpen U) (x : T)
    (h : ∀ z : T, z ⤳ x → z ≠ x → z ∈ U) :
    ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∪ closure {x} := by
  classical
  obtain ⟨S, hSfin, hSclosed, hSirr, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hU.isClosed_compl
  let D := {s ∈ S | x ∉ s}
  have hD : D.Finite := hSfin.subset fun _ hs ↦ hs.1
  refine ⟨(⋃₀ D)ᶜ, (hD.isClosed_sUnion fun s hs ↦ hSclosed s hs.1).isOpen_compl,
    fun ⟨s, hs, hxs⟩ ↦ hs.2 hxs, fun z hz ↦ ?_⟩
  by_cases hzU : z ∈ U
  · exact Or.inl hzU
  obtain ⟨s, hs, hzs⟩ : z ∈ ⋃₀ S := hS ▸ hzU
  have hxs : x ∈ s := by
    by_contra hxs
    exact hz ⟨s, ⟨hs, hxs⟩, hzs⟩
  obtain ⟨η, hη⟩ := QuasiSober.sober (hSirr s hs) (hSclosed s hs)
  have hηx : η = x := by
    by_contra hne
    exact (hS.symm ▸ Set.mem_sUnion_of_mem hη.mem hs : η ∈ Uᶜ) (h η (hη.specializes hxs) hne)
  exact Or.inr (by rwa [← hηx, hη.def])

end AlgebraicGeometry

end
