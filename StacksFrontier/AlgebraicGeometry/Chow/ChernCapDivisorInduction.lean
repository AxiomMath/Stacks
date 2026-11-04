module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inductive step of Stacks 0FDX, on an arbitrary test scheme

Stacks 0FDX says that for invertible modules `ℒ_1, …, ℒ_{d+1}` on a scheme `X` of topological
dimension at most `d`, locally of finite type over the base scheme of chapter 42 of the Stacks
Project, the product of first Chern classes `c₁(ℒ_1) ∘ ⋯ ∘ c₁(ℒ_{d+1})` is zero in `A^{d+1}(X)`.
A bivariant class vanishes exactly when its cap operation vanishes on **every** test scheme
`h : T ⟶ X` locally of finite type (Stacks 02UC), with no bound on the dimension of `T`, so the
conclusion unwinds to

  `c₁(h^*ℒ_1) ∩ ⋯ ∩ c₁(h^*ℒ_{d+1}) ∩ α = 0`   in `A_k(T)`,  for every `α ∈ A_{k+d+1}(T)`,

quantified over all such `h`. `Stacks.Chow.BivariantClass.cap_eq_zero_of_topologicalKrullDim_le`
of `StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing` reaches only the test schemes
of dimension at most `d`, by a delta-dimension count; the source reaches all of them by induction
on `d`, and this file proves the inductive step of that induction in the cap-level form above.

## The step

Let `ℒ = ℒ_{d+1}` carry a global section `s`, so that the zero scheme `D = Z(s)` is a closed
subscheme of `X` — by Stacks 0AYM an arbitrary invertible module is a difference of two such, and
`Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj` performs that reduction. On a
test scheme `u : T ⟶ X` the innermost cap is then a pushforward from the zero scheme of the
pulled back section:

* `c₁(u^*ℒ) ∩ − = j_* ∘ j^*` with `j : Z(u^*s) ⟶ T` the closed immersion and `j^*` the Gysin
  homomorphism of Stacks 02T8, which is Stacks 02T9
  (`Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible`), read on Chow groups here
  as `Stacks.Chow.exists_eq_properChowPushforward_invCap_capOnChow`;
* the remaining caps `c₁(u^*ℒ_1), …, c₁(u^*ℒ_d)` move inside that pushforward by the projection
  formula of Stacks 02SU, iterated
  (`Stacks.Chow.properChowPushforward_iteratedChernCapOnChow_ofFn`);
* and `Z(u^*s)` is a test scheme over `D` through the morphism `g : Z(u^*s) ⟶ Z(s)` of
  Remark 0B6Y (`Stacks.Chow.zeroSchemePullbackHom`), which is locally of finite type by
  Stacks 01T8 because `g ≫ i = j ≫ u` is, so the inductive hypothesis on `D` applies to it and
  kills the inner product.

The modules the projection formula produces on `Z(u^*s)` are the iterated pullbacks
`j^*u^*ℒ_i`, while the inductive hypothesis is stated at the pullback along the composite
`Z(u^*s) ⟶ X`; the two are identified by `AlgebraicGeometry.Scheme.Modules.pullbackComp`, through
`Stacks.Chow.invCap_capOnChow_congr` and `Stacks.Chow.iteratedChernCapOnChow_congr_forall₂`.

Nothing in the step bounds the dimension of `T`, and nothing in it bounds the dimension of `X`
either: the dimension enters only through the inductive hypothesis, whose availability on `D` is
what `Stacks.Chow.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor` prepares — an
effective Cartier divisor has nowhere dense support, so its dimension has dropped by one.

## Main results

* `Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme` — **the inductive step of
  Stacks 0FDX**, in the form in which the innermost cap has already been separated off: given the
  vanishing of a product of `n` first Chern class caps on every test scheme over the zero scheme
  `Z(s)`, the same product followed by `c₁(u^*ℒ)` vanishes on every test scheme `u : T ⟶ X`.
* `Stacks.Chow.iteratedChernCapOnChow_append_eq_zero_of_zeroScheme` — the same statement read on
  the list of `n + 1` cap operators that `Stacks.Chow.iteratedChernCapOnChow` consumes.
* `Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj` — the step for an invertible
  module presented as a difference of two modules with sections, which is the form Stacks 0AYM
  delivers: `ℒ ⊗ ℒ_2 ≅ ℒ_1` with `ℒ_1, ℒ_2` carrying global sections.
* `Stacks.Chow.invCap_capOnChow_pullback_eq_zero_of_topologicalKrullDim_le_zero` — **the base
  case**, on Chow groups: for `X` of dimension at most zero a single first Chern class cap
  annihilates every Chow class of every test scheme.
* `Stacks.Chow.firstChernClassCapOfInvertible_pullback_eq_zero_of_topologicalKrullDim_le_zero` —
  **step 1 of the proof of Stacks 0FDX on an arbitrary test scheme**, on cycles: for `X` of
  dimension zero the cap product of `h^*L` vanishes on every `h : T ⟶ X` locally of finite type,
  with no dimension hypothesis on `T`. This is what the base case above descends to Chow groups.
* `Stacks.Chow.firstChernClassCapOfInvertible_eq_zero_of_tensorObj_self_iso` — the cap product of
  an invertible module idempotent for the tensor product vanishes, which is what gives the
  previous statement its generality in `T`.
* `Stacks.Chow.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor` — **the dimension
  drop**: an effective Cartier divisor on a Noetherian space of dimension at most `d + 1` has
  dimension at most `d`.
* `Stacks.Chow.exists_eq_properChowPushforward_invCap_capOnChow` — Stacks 02T9 on Chow groups:
  capping with `c₁(ℒ)` lands in the image of the pushforward from `Z(s)`.
* `Stacks.Chow.invCap_capOnChow_congr` and `Stacks.Chow.invCap_capOnChow_tensorObj` — the cap
  operation of an invertible module depends only on its isomorphism class, and is additive in the
  module (Stacks 02SP on Chow groups).
* `Stacks.Chow.iteratedChernCapOnChow_append`, `Stacks.Chow.iteratedChernCapOnChow_singleton_eq`
  and `Stacks.Chow.iteratedChernCapOnChow_congr_forall₂` — the three manipulations of a list of
  cap operators the step performs.

## Implementation notes

### Where the induction is assembled

The induction is run in `StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionInduction`, whose
`Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le` is Stacks 0FDX on
every test scheme locally of finite type.

The assembly needs Stacks 0AYM on the divisor `D` at each stage, hence that an ample invertible
module restrict to an ample one on a closed subscheme — the easy half of Stacks 09MS. That
statement is available unconditionally, twice: as
`Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion`
(`StacksFrontier.AlgebraicGeometry.AmplePullback.Basic`, Stacks 0B3E for a closed immersion, with no
hypothesis beyond `IsClosedImmersion`), and as
`AlgebraicGeometry.Scheme.Modules.isAmple_modulePullback_of_isClosedImmersion`
(`StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Components`). The declaration
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`, whose
statement carries a `Surjective` hypothesis on the immersion that a divisor does not satisfy, is
Stacks 09MS's statement at Stacks 09MS's own hypotheses and is not the general one; it is not
needed here. Likewise `Stacks.Divisors.divisorSheaf D` has an invertibility instance for
effective Cartier `D`: `Stacks.Divisors.isInvertible_divisorSheaf` of
`StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme` is exactly that instance, at
exactly the spelling `Stacks.Chow.invCap` requires.

### The pullback along a bound morphism is invertible only as a scoped instance

Stacks 0B8L is deliberately kept out of instance search in this library, and is made an instance
`scoped` to `Stacks.AlgebraicGeometry.AmpleLimit`. The statements below quantify over test
schemes, so the invertible modules they mention are pullbacks along *bound* morphisms and cannot
be written without it; this file therefore opens that scope, as its documentation prescribes.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

/-! ### Step 1 of the source proof on an arbitrary test scheme -/

/-- **The first Chern class cap product of a tensor-idempotent invertible module vanishes.** If an
invertible module `M` on `X` satisfies `M ⊗_{𝒪_X} M ≅ M`, then `c₁(M) ∩ α = 0` for every cycle
`α`: the additivity of Stacks 02SP reads `c₁(M) ∩ α + c₁(M) ∩ α = c₁(M ⊗ M) ∩ α`, and the right
hand side is `c₁(M) ∩ α` because the cap product depends only on the isomorphism class of the
module.

`Stacks.Chow.firstChernClassCapOfInvertible_unit` is the case `M = 𝒪_X`, and this is its proof
with `𝒪_X` replaced by an arbitrary idempotent. The case that needs the generality is the
pullback `h^*𝒪_X`, which is idempotent for the tensor product without being the unit of `T` on
the nose. -/
theorem firstChernClassCapOfInvertible_eq_zero_of_tensorObj_self_iso
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : Scheme.Modules.tensorObj M M ≅ M) (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOfInvertible C p k M α = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj M M) := isInvertible_tensorObj _ _
  have hsum : firstChernClassCapOfInvertible C p k M α +
      firstChernClassCapOfInvertible C p k M α =
      0 + firstChernClassCapOfInvertible C p k M α := by
    rw [zero_add]
    exact (firstChernClassCapOfInvertible_tensorObj C p k M M α).trans
      (firstChernClassCapOfInvertible_congr C p k _ M e α)
  exact add_right_cancel hsum

/-- **Step 1 of the proof of Stacks 0FDX, on an arbitrary test scheme.** Let `X` be locally of
finite type over the base and of topological dimension at most zero, let `L` be an invertible
`𝒪_X`-module, and let `h : T ⟶ X` be locally of finite type. Then the first Chern class cap
product of `h^*L` vanishes on `T`:

  `c₁(h^*L) ∩ α = 0`  in  `A_k(T)`,  for every `α ∈ Z_{k+1}(T)`.

No dimension hypothesis is placed on `T`, and none is available: a scheme locally of finite type
over a zero-dimensional `X` may have any dimension — `𝔸¹` over a point — so
`Stacks.Chow.chowGroup_eq_zero_of_topologicalKrullDim_lt` says nothing about `T`, and
`Stacks.Chow.firstChernClassCapOfInvertible_eq_zero_of_topologicalKrullDim_le_zero` does not
apply to it. The vanishing comes from the module instead: `X` is discrete, so `L ≅ 𝒪_X`, hence
`h^*L ≅ h^*𝒪_X`, and `h^*𝒪_X` is idempotent for the tensor product because `𝒪_X` is and the
pullback of a tensor product is the tensor product of the pullbacks (Stacks 01CD,
`Stacks.Chow.pullbackTensorObjIso`).

This is the form in which step 1 is the base case of the induction on `d`: that induction
quantifies over every test scheme of the bivariant class, not over `X` alone. See the
implementation notes. -/
theorem firstChernClassCapOfInvertible_pullback_eq_zero_of_topologicalKrullDim_le_zero
    (C : ChowSituation.{u}) {X T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (h : T ⟶ X) [LocallyOfFiniteType h] (hdim : topologicalKrullDim X ≤ 0) (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (α : CycleGroup C (h ≫ sX) (k + 1)) :
    firstChernClassCapOfInvertible C (h ≫ sX) k ((Scheme.Modules.pullback h).obj L) α = 0 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have _ : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  have _ : DiscreteTopology (X : Type u) := inferInstance
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology X L
  have hunit : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (Stacks.SheafOfModules.isInvertible_unit X.sheaf.obj X.ringCatSheaf.property)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property
      ((Scheme.Modules.pullback h).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry h.toLRSHom.toShHom _ hunit
  rw [firstChernClassCapOfInvertible_congr C (h ≫ sX) k
    ((Scheme.Modules.pullback h).obj L)
    ((Scheme.Modules.pullback h).obj (SheafOfModules.unit X.ringCatSheaf))
    ((Scheme.Modules.pullback h).mapIso e) α]
  exact firstChernClassCapOfInvertible_eq_zero_of_tensorObj_self_iso C (h ≫ sX) k
    ((Scheme.Modules.pullback h).obj (SheafOfModules.unit X.ringCatSheaf))
    ((pullbackTensorObjIso h (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
      (Scheme.Modules.pullback h).mapIso
        (tensorObjUnitIso X (SheafOfModules.unit X.ringCatSheaf))) α

variable (C : ChowSituation.{u})

/-! ### Three manipulations of a list of first Chern class cap operators -/

/-- The degree after one more operator: `k + (O :: Os).length = k + 1 + Os.length`. -/
private theorem degree_cons_length {α : Type*} (k : ℤ) (O : α) (Os : List α) :
    k + ((O :: Os).length : ℤ) = k + 1 + (Os.length : ℤ) := by
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- The defining equation of an iterated cap at a nonempty list, with the class transported along
`degree_cons_length`. -/
private theorem iteratedChernCapOnChow_cons_cast {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (Os : List (ChernCapOperator C sP))
    (k : ℤ) (x : chowGroup C sP (k + ((O :: Os).length : ℤ))) :
    iteratedChernCapOnChow C sP (O :: Os) k x =
      O.capOnChow C sP k (iteratedChernCapOnChow C sP Os (k + 1)
        (chowGroupCast C sP (degree_cons_length k O Os) x)) :=
  iteratedChernCapOnChow_cons_eq C sP O Os k x _ (chowGroupCast_heq C sP _ x).symm

/-- **An iterated cap at a concatenated list is the composite of the two iterated caps.** The
head of a list is applied last, so the operators of `Ps` act first: `Os ++ Ps` caps by `Ps` and
then by `Os`. The class `y` is `x` read in the degree the right hand side iterates from. -/
theorem iteratedChernCapOnChow_append {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (Os Ps : List (ChernCapOperator C sP)) (k : ℤ)
    (x : chowGroup C sP (k + ((Os ++ Ps).length : ℤ)))
    (y : chowGroup C sP (k + (Os.length : ℤ) + (Ps.length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP (Os ++ Ps) k x =
      iteratedChernCapOnChow C sP Os k
        (iteratedChernCapOnChow C sP Ps (k + (Os.length : ℤ)) y) := by
  induction Os generalizing k with
  | nil =>
    refine chowGroup_eq_of_heq C sP (HEq.trans ?_ (iteratedChernCapOnChow_nil_heq C sP k _).symm)
    exact iteratedChernCapOnChow_heq C sP Ps (by simp) hxy
  | cons O Os ih =>
    have hc'' := congrArg (· + (Ps.length : ℤ)) (degree_cons_length k O Os)
    refine (iteratedChernCapOnChow_cons_cast C sP O (Os ++ Ps) k x).trans ?_
    rw [iteratedChernCapOnChow_cons_cast]
    congr 1
    refine (ih (k + 1) _ (chowGroupCast C sP hc'' y) ?_).trans
      (congrArg _ (chowGroup_eq_of_heq C sP ?_))
    · exact (chowGroupCast_heq C sP _ x).trans (hxy.trans (chowGroupCast_heq C sP hc'' y).symm)
    · exact ((chowGroupCast_heq C sP _ _).trans (iteratedChernCapOnChow_heq C sP Ps
        (degree_cons_length k O Os) (chowGroupCast_heq C sP hc'' y).symm)).symm

/-- **An iterated cap at a one-element list is that one cap.** The class `y` is `x` read in
degree `k + 1`. -/
theorem iteratedChernCapOnChow_singleton_eq {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (O : ChernCapOperator C sP) (k : ℤ)
    (x : chowGroup C sP (k + (([O] : List (ChernCapOperator C sP)).length : ℤ)))
    (y : chowGroup C sP (k + 1)) (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP [O] k x = O.capOnChow C sP k y := by
  rw [iteratedChernCapOnChow_cons_eq C sP O [] k x (chowGroupCast C sP (by simp) x)
    (chowGroupCast_heq C sP _ x).symm]
  congr 1
  exact chowGroup_eq_of_heq C sP ((iteratedChernCapOnChow_nil_heq C sP (k + 1) _).trans
    ((chowGroupCast_heq C sP _ x).trans hxy))

/-- **Two lists of cap operators whose operations agree termwise have the same iterated cap.**
The operators themselves need not be equal; only their operations on Chow groups. -/
theorem iteratedChernCapOnChow_congr_forall₂ {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] {Os Ps : List (ChernCapOperator C sP)}
    (hOP : List.Forall₂ (fun O P => ∀ (m : ℤ) (z : chowGroup C sP (m + 1)),
      O.capOnChow C sP m z = P.capOnChow C sP m z) Os Ps)
    (k : ℤ) (x : chowGroup C sP (k + (Os.length : ℤ))) (y : chowGroup C sP (k + (Ps.length : ℤ)))
    (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP Os k x = iteratedChernCapOnChow C sP Ps k y := by
  induction hOP generalizing k with
  | nil =>
    exact chowGroup_eq_of_heq C sP ((iteratedChernCapOnChow_nil_heq C sP k x).trans
      (hxy.trans (iteratedChernCapOnChow_nil_heq C sP k y).symm))
  | @cons O P' Os' Ps' hOP' _ ih =>
    rw [iteratedChernCapOnChow_cons_cast, iteratedChernCapOnChow_cons_cast, hOP' k]
    congr 1
    exact ih (k + 1) _ _
      ((chowGroupCast_heq C sP _ x).trans (hxy.trans (chowGroupCast_heq C sP _ y).symm))

/-! ### The cap operation of an invertible module -/

/-- **The cap operation of an invertible module depends only on its isomorphism class.** This is
`Stacks.Chow.firstChernClassCapOfInvertible_congr` read on Chow groups. -/
theorem invCap_capOnChow_congr {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) (k : ℤ) (x : chowGroup C p (k + 1)) :
    (invCap C p L).capOnChow C p k x = (invCap C p N).capOnChow C p k x := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk, invCap_capOnChow_mk]
  exact firstChernClassCapOfInvertible_congr C p k L N e α

/-- **Stacks 02SP on Chow groups:** `c₁(ℒ) ∩ x + c₁(𝒩) ∩ x = c₁(ℒ ⊗ 𝒩) ∩ x`. -/
theorem invCap_capOnChow_tensorObj {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (k : ℤ) (x : chowGroup C p (k + 1)) :
    (invCap C p L).capOnChow C p k x + (invCap C p N).capOnChow C p k x =
      (invCap C p (Scheme.Modules.tensorObj L N)).capOnChow C p k x := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := isInvertible_tensorObj _ _
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk, invCap_capOnChow_mk, invCap_capOnChow_mk]
  exact firstChernClassCapOfInvertible_tensorObj C p k L N α

/-- **Stacks 02T9 on Chow groups.** Capping with the first Chern class of an invertible module
`ℒ` carrying a global section `s` lands in the image of proper pushforward along the closed
immersion of the zero scheme `Z(s)`: the class pushed forward is the Gysin class of Stacks 02T8.

Only the membership in the image is recorded, which is all the induction of Stacks 0FDX uses. -/
theorem exists_eq_properChowPushforward_invCap_capOnChow {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (x : chowGroup C p (k + 1)) :
    ∃ γ : chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      (invCap C p L).capOnChow C p k x =
        properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
            (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k) γ := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  exact ⟨gysinHomomorphismOfInvertible C p k L s α,
    (invCap_capOnChow_mk C p L k α).trans
      (properChowPushforward_gysinHomomorphismOfInvertible C p k L s α).symm⟩

/-! ### The base case, on Chow groups -/

/-- **Step 1 of the proof of Stacks 0FDX, on Chow groups and on an arbitrary test scheme.** For
`X` locally of finite type over the base and of topological dimension at most zero, capping with
the first Chern class of the pullback of an invertible `𝒪_X`-module annihilates every Chow class
of every test scheme `u : T ⟶ X` locally of finite type. No dimension hypothesis is placed on
`T`.

It is `Stacks.Chow.firstChernClassCapOfInvertible_pullback_eq_zero_of_topologicalKrullDim_le_zero`
descended to Chow groups, which is the form the induction on `d` consumes at the bottom. The
structural morphism `q` of the test scheme is taken as a variable with the equation
`u ≫ s_X = q`, as it is in the inductive step below. -/
theorem invCap_capOnChow_pullback_eq_zero_of_topologicalKrullDim_le_zero {X T : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (hdim : topologicalKrullDim X ≤ 0) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (x : chowGroup C q (k + 1)) :
    (invCap C q ((Scheme.Modules.pullback u).obj L)).capOnChow C q k x = 0 := by
  subst hq
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk]
  exact firstChernClassCapOfInvertible_pullback_eq_zero_of_topologicalKrullDim_le_zero C sX u
    hdim k L α

/-! ### The dimension drop that terminates the induction -/

/-- **An effective Cartier divisor has dimension one less than the ambient scheme.** Its support
is nowhere dense (`AlgebraicGeometry.isNowhereDense_supportSet_of_isEffectiveCartierDivisor`) and
closed, and the space of the closed subscheme it defines is homeomorphic to that support, so the
bounded dimension drop of `IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ` applies. -/
@[ega "IV 4.1.2.1" "rare ⇒ dim(Z) < dim(Y)", ega "IV 5.2.4" "special case"]
theorem topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [NoetherianSpace X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {d : ℕ}
    (hdim : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (D.subscheme : Type u) ≤ (d : WithBot ℕ∞) := by
  have hh : (D.subscheme : Type u) ≃ₜ ↥(D.supportSet : Set X) :=
    (D.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr (by rw [Scheme.IdealSheafData.range_subschemeι]; rfl))
  rw [IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph]
  exact IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ
    (AlgebraicGeometry.isNowhereDense_supportSet_of_isEffectiveCartierDivisor D hD)
    (Scheme.IdealSheafData.isClosed_supportSet D) d hdim

/-! ### The inductive step -/

section Step

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- **The inductive step of Stacks 0FDX**, with the innermost cap separated off.

Let `ℒ` be an invertible `𝒪_X`-module with a global section `s`, let `D = Z(s)` be its zero
scheme, and let `ℒ_1, …, ℒ_n` be further invertible `𝒪_X`-modules. Assume the inductive
hypothesis on `D`: the product `c₁(ℒ_1) ∩ ⋯ ∩ c₁(ℒ_n) ∩ −`, formed from the pullbacks of the
`ℒ_i` to any test scheme over `D`, annihilates every Chow class there. Then on every test scheme
`u : T ⟶ X` locally of finite type,

  `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_n) ∩ c₁(u^*ℒ) ∩ y = 0`.

No dimension hypothesis is placed on `T`, and none on `X`: the dimension of `X` enters only
through the inductive hypothesis.

The three inputs are the ones the source uses: Stacks 02T9 writes the innermost cap as a
pushforward from `Z(u^*s)`, the iterated projection formula of Stacks 02SU moves the remaining
caps inside that pushforward, and the morphism `Z(u^*s) ⟶ Z(s)` of Remark 0B6Y exhibits
`Z(u^*s)` as a test scheme over `D`. -/
theorem iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {n : ℕ} (N : Fin n → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    (IH : ∀ (T' : Scheme.{u}) (g : T' ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme)
      (_ : LocallyOfFiniteType g) (u' : T' ⟶ X) (_ : LocallyOfFiniteType u')
      (_ : g ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (k : ℤ)
    (y : chowGroup C q (k +
      ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) + 1)) :
    iteratedChernCapOnChow C q
        (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k
        ((invCap C q ((Scheme.Modules.pullback u).obj L)).capOnChow C q
          (k + ((List.ofFn fun i =>
            invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y) = 0 := by
  -- the square of Remark 0B6Y, and the local finiteness of `g : Z(u^*s) ⟶ Z(s)` (Stacks 01T8)
  have hgj : zeroSchemePullbackHom u L s ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι =
      (pullbackZeroScheme u L s).subschemeι ≫ u := zeroSchemePullbackHom_subschemeι u L s
  have hgft : LocallyOfFiniteType (zeroSchemePullbackHom u L s) :=
    LocallyOfFiniteType.of_comp (g := (Stacks.Divisors.zeroScheme X L s).subschemeι)
      (hgj ▸ (inferInstance :
        LocallyOfFiniteType ((pullbackZeroScheme u L s).subschemeι ≫ u)))
  -- Stacks 02T9: the innermost cap is a pushforward from the zero scheme of `u^*s`
  obtain ⟨γ, hγ⟩ := exists_eq_properChowPushforward_invCap_capOnChow C q
    ((Scheme.Modules.pullback u).obj L) (AlgebraicGeometry.pullbackGlobalSections u L s)
    (k + ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y
  have hd3 : k + ((List.ofFn fun i =>
        invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) =
      k + ((List.ofFn fun i => invCap C ((pullbackZeroScheme u L s).subschemeι ≫ q)
        ((Scheme.Modules.pullback (pullbackZeroScheme u L s).subschemeι).obj
          ((Scheme.Modules.pullback u).obj (N i)))).length : ℤ) := by
    simp
  have hd4 : k + ((List.ofFn fun i =>
        invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) =
      k + ((List.ofFn fun i => invCap C ((pullbackZeroScheme u L s).subschemeι ≫ q)
        ((Scheme.Modules.pullback
          ((pullbackZeroScheme u L s).subschemeι ≫ u)).obj (N i))).length : ℤ) := by
    simp
  -- the iterated pullback and the pullback along the composite agree (Stacks 01CD)
  have e : ∀ i, (Scheme.Modules.pullback (pullbackZeroScheme u L s).subschemeι).obj
        ((Scheme.Modules.pullback u).obj (N i)) ≅
      (Scheme.Modules.pullback ((pullbackZeroScheme u L s).subschemeι ≫ u)).obj (N i) :=
    fun i => (Scheme.Modules.pullbackComp (pullbackZeroScheme u L s).subschemeι u).app (N i)
  -- Stacks 02SU, iterated: the remaining caps move inside the pushforward
  have hpf := properChowPushforward_iteratedChernCapOnChow_ofFn C
    ((pullbackZeroScheme u L s).subschemeι ≫ q) q (pullbackZeroScheme u L s).subschemeι rfl
    (fun i => (Scheme.Modules.pullback u).obj (N i)) k
    (chowGroupCast C ((pullbackZeroScheme u L s).subschemeι ≫ q) hd3 γ) _
    (properChowPushforward_heq C ((pullbackZeroScheme u L s).subschemeι ≫ q) q
      (pullbackZeroScheme u L s).subschemeι rfl hd3
      (chowGroupCast_heq C ((pullbackZeroScheme u L s).subschemeι ≫ q) hd3 γ).symm)
  -- the inner product vanishes by the inductive hypothesis on `Z(s)`
  have hzero : iteratedChernCapOnChow C ((pullbackZeroScheme u L s).subschemeι ≫ q)
      (List.ofFn fun i => invCap C ((pullbackZeroScheme u L s).subschemeι ≫ q)
        ((Scheme.Modules.pullback (pullbackZeroScheme u L s).subschemeι).obj
          ((Scheme.Modules.pullback u).obj (N i)))) k
      (chowGroupCast C ((pullbackZeroScheme u L s).subschemeι ≫ q) hd3 γ) = 0 := by
    refine (iteratedChernCapOnChow_congr_forall₂ C ((pullbackZeroScheme u L s).subschemeι ≫ q)
      (forall₂_ofFn fun i => fun m z => invCap_capOnChow_congr C _ _ _ (e i) m z) k _
      (chowGroupCast C ((pullbackZeroScheme u L s).subschemeι ≫ q) hd4 γ)
      ((chowGroupCast_heq C _ hd3 γ).trans
        (chowGroupCast_heq C _ hd4 γ).symm)).trans ?_
    exact IH _ (zeroSchemePullbackHom u L s) hgft
      ((pullbackZeroScheme u L s).subschemeι ≫ u) inferInstance hgj _ inferInstance
      (by rw [Category.assoc, hq]) k _
  rw [hγ, ← hpf, hzero, map_zero]

omit [LocallyOfFiniteType sX] in
/-- **The inductive step of Stacks 0FDX**, read on the list of `n + 1` cap operators that
`Stacks.Chow.iteratedChernCapOnChow` consumes. The operator of `ℒ` is last in the list, hence
applied first, which is the one the source decomposes into divisors. -/
theorem iteratedChernCapOnChow_append_eq_zero_of_zeroScheme (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {n : ℕ} (N : Fin n → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    (IH : ∀ (T' : Scheme.{u}) (g : T' ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme)
      (_ : LocallyOfFiniteType g) (u' : T' ⟶ X) (_ : LocallyOfFiniteType u')
      (_ : g ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (k : ℤ)
    (α : chowGroup C q (k + ((((List.ofFn fun i =>
          invCap C q ((Scheme.Modules.pullback u).obj (N i))) ++
        [invCap C q ((Scheme.Modules.pullback u).obj L)]).length : ℤ)))) :
    iteratedChernCapOnChow C q
        ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) ++
          [invCap C q ((Scheme.Modules.pullback u).obj L)]) k α = 0 := by
  have hd1 : k + ((((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) ++
        [invCap C q ((Scheme.Modules.pullback u).obj L)]).length : ℤ)) =
      k + ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) +
        (([invCap C q ((Scheme.Modules.pullback u).obj L)] :
          List (ChernCapOperator C q)).length : ℤ) := by
    simp; ring
  have hd2 : k +
        ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) +
        (([invCap C q ((Scheme.Modules.pullback u).obj L)] :
          List (ChernCapOperator C q)).length : ℤ) =
      k + ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)
        + 1 := by
    simp
  rw [iteratedChernCapOnChow_append C q _ _ k α (chowGroupCast C q hd1 α)
      (chowGroupCast_heq C q hd1 α).symm,
    iteratedChernCapOnChow_singleton_eq C q _ _ _
      (chowGroupCast C q hd2 (chowGroupCast C q hd1 α))
      (chowGroupCast_heq C q hd2 (chowGroupCast C q hd1 α)).symm]
  exact iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme C sX L s N IH u q hq k _

omit [LocallyOfFiniteType sX] in
/-- **The inductive step of Stacks 0FDX for an invertible module written as a difference of two
divisors**, which is the form Stacks 0AYM delivers.

Let `ℒ ⊗ ℒ_2 ≅ ℒ_1` with `ℒ_1, ℒ_2` invertible and carrying global sections `s_1, s_2` — the
multiplicative reading of `ℒ ≅ 𝒪_X(D_1 - D_2)`. If the product of the `n` caps of `ℒ_1, …, ℒ_n`
annihilates every Chow class of every test scheme over `Z(s_1)` and over `Z(s_2)`, then on every
test scheme `u : T ⟶ X`

  `c₁(u^*ℒ_1) ∩ ⋯ ∩ c₁(u^*ℒ_n) ∩ c₁(u^*ℒ) ∩ y = 0`.

The additivity of Stacks 02SP gives `c₁(u^*ℒ) ∩ y + c₁(u^*ℒ_2) ∩ y = c₁(u^*ℒ_1) ∩ y`, since
pullback commutes with the tensor product (Stacks 01CD), and the outer product is additive, so the
conclusion is the difference of two instances of
`Stacks.Chow.iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme`. -/
theorem iteratedChernCapOnChow_capOnChow_eq_zero_of_tensorObj (M L₁ L₂ : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₁]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₂]
    (s₁ : Γ(L₁, ⊤)) (s₂ : Γ(L₂, ⊤)) (eM : Scheme.Modules.tensorObj M L₂ ≅ L₁) {n : ℕ}
    (N : Fin n → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N i)]
    (IH₁ : ∀ (T' : Scheme.{u}) (g : T' ⟶ (Stacks.Divisors.zeroScheme X L₁ s₁).subscheme)
      (_ : LocallyOfFiniteType g) (u' : T' ⟶ X) (_ : LocallyOfFiniteType u')
      (_ : g ≫ (Stacks.Divisors.zeroScheme X L₁ s₁).subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    (IH₂ : ∀ (T' : Scheme.{u}) (g : T' ⟶ (Stacks.Divisors.zeroScheme X L₂ s₂).subscheme)
      (_ : LocallyOfFiniteType g) (u' : T' ⟶ X) (_ : LocallyOfFiniteType u')
      (_ : g ≫ (Stacks.Divisors.zeroScheme X L₂ s₂).subschemeι = u') (q' : T' ⟶ C.S)
      (_ : LocallyOfFiniteType q') (_ : u' ≫ sX = q') (m : ℤ)
      (β : chowGroup C q' (m + ((List.ofFn fun i =>
        invCap C q' ((Scheme.Modules.pullback u').obj (N i))).length : ℤ))),
      iteratedChernCapOnChow C q'
        (List.ofFn fun i => invCap C q' ((Scheme.Modules.pullback u').obj (N i))) m β = 0)
    {T : Scheme.{u}} (u : T ⟶ X) [LocallyOfFiniteType u] (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (hq : u ≫ sX = q) (k : ℤ)
    (y : chowGroup C q (k +
      ((List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ) + 1)) :
    iteratedChernCapOnChow C q
        (List.ofFn fun i => invCap C q ((Scheme.Modules.pullback u).obj (N i))) k
        ((invCap C q ((Scheme.Modules.pullback u).obj M)).capOnChow C q
          (k + ((List.ofFn fun i =>
            invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y) = 0 := by
  have hsplit : (invCap C q ((Scheme.Modules.pullback u).obj M)).capOnChow C q
        (k + ((List.ofFn fun i =>
          invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y =
      (invCap C q ((Scheme.Modules.pullback u).obj L₁)).capOnChow C q
        (k + ((List.ofFn fun i =>
          invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y -
      (invCap C q ((Scheme.Modules.pullback u).obj L₂)).capOnChow C q
        (k + ((List.ofFn fun i =>
          invCap C q ((Scheme.Modules.pullback u).obj (N i))).length : ℤ)) y := by
    rw [eq_sub_iff_add_eq, invCap_capOnChow_tensorObj]
    exact invCap_capOnChow_congr C q _ _
      ((pullbackTensorObjIso u M L₂).symm ≪≫ (Scheme.Modules.pullback u).mapIso eM) _ y
  rw [hsplit, map_sub,
    iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme C sX L₁ s₁ N IH₁ u q hq k y,
    iteratedChernCapOnChow_capOnChow_eq_zero_of_zeroScheme C sX L₂ s₂ N IH₂ u q hq k y, sub_zero]

end Step

end Stacks.Chow

end
