module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.DimensionOneDomain
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a zero cycle

Let `(S, δ)` be a base situation for Chow homology whose dimension function vanishes
identically — the case of interest being `S = Spec(k)` for a field `k`, where `δ = 0` is the
only possibility. Then `S` carries no integral closed subscheme of delta-dimension one, so no
zero cycle on `S` is rationally equivalent to zero and `A_0(S) = Z_0(S)`. If moreover `S` has a
single point, a zero cycle on `S` is just an integer, and `A_0(S) ≅ ℤ`.

For `p : X ⟶ S` proper, the *degree* of a zero cycle on `X` is its proper pushforward to `S`
read through that identification. At the level of cycles this is `Stacks.Chow.cycleDegree`: the
coefficient at the point of `S` of the pushforward cycle.

## Main definitions

* `Stacks.Chow.cycleDegree` — the degree of a zero cycle, at the level of cycles.
* `Stacks.Chow.chowGroupBaseEquivInt` — the identification `A_0(S) ≅ ℤ` for a one-point base
  with vanishing dimension function, normalised so that the fundamental cycle goes to one.

## Main results

* `Stacks.Chow.relativeDimension_of_isClosedImmersion` — a closed subscheme of the base has the
  relative dimension its image has in the base.
* `Stacks.Chow.rationalEquivalences_id_eq_bot` — over a base with vanishing dimension function
  no nonzero zero cycle on the base is rationally equivalent to zero.
* `Stacks.Chow.chowGroupBaseEquivInt_mk` — the identification `A_0(S) ≅ ℤ` reads off the
  coefficient at the point of `S`.
* `Stacks.Chow.cycleDegree_eq_zero_of_mem_rationalEquivalences` — granted Stacks 02S2 for `p`, a
  zero cycle rationally equivalent to zero has degree zero.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_schemeDeltaDimension_le` —
  Stacks 02S2 holds for every proper morphism out of a scheme of delta-dimension at most `k`.

## Implementation notes

The base is a `Stacks.Chow.ChowSituation` whose dimension function vanishes, with a chosen point,
rather than literally `Spec(k)`; for a field `k` it is `Stacks.Chow.fieldChowSituation k`, whose
base scheme is `Spec(k)` definitionally.

## References

* [Stacks Project, Tag 0AZ0](https://stacks.math.columbia.edu/tag/0AZ0)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 02QM](https://stacks.math.columbia.edu/tag/02QM)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The base situation of a field -/

/-- The base scheme of the base situation of a field is the spectrum of that field. -/
@[simp]
theorem fieldChowSituation_S (k : Type u) [Field k] :
    (fieldChowSituation k).S = AlgebraicGeometry.Spec (.of k) :=
  rfl

/-- The base scheme of the base situation of a field has at most one point. -/
instance (k : Type u) [Field k] : Subsingleton (fieldChowSituation k).S :=
  inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))

/-- The base scheme of the base situation of a field has a point. -/
instance (k : Type u) [Field k] : Nonempty (fieldChowSituation k).S :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))

/-! ### Relative dimension over a base with vanishing dimension function -/

/-- A closed subscheme of the base has, at each of its points, the relative dimension that the
image point has in the base. -/
theorem relativeDimension_of_isClosedImmersion {S X : Scheme.{u}} (δ : DimensionFunction S)
    (g : X ⟶ S) [IsClosedImmersion g] (x : X) :
    relativeDimension δ g x = δ (g.base x) := by
  conv_lhs => rw [← Category.comp_id g]
  rw [relativeDimension_comp_closedImmersion, relativeDimension_id]

variable (C : ChowSituation.{u})

/-! ### The degree of a zero cycle -/

section Cycles

variable {X : Scheme.{u}} (p : X ⟶ C.S) [IsProper p]

/-- **Stacks 0AZ1 at the level of cycles.** The degree of a zero cycle on `X` proper over the
base, read at a point `s` of the base: the coefficient at `s` of the proper pushforward of the
cycle to the base. -/
@[sga "7 XVII 5.2" "degree of a zero-cycle"]
def cycleDegree (s : C.S) : CycleGroup C p 0 →+ ℤ where
  toFun α := (properPushforward C p (𝟙 C.S) p (Category.comp_id p) 0 α).1 s
  map_zero' := by simp
  map_add' a b := by simp [properPushforward_add]

/-- The degree of a zero cycle is the coefficient of its proper pushforward to the base. -/
theorem cycleDegree_apply (s : C.S) (α : CycleGroup C p 0) :
    cycleDegree C p s α = (properPushforward C p (𝟙 C.S) p (Category.comp_id p) 0 α).1 s :=
  rfl

end Cycles

/-- On the base itself the degree of a zero cycle is its coefficient at the chosen point. -/
@[simp]
theorem cycleDegree_id (s : C.S) (α : CycleGroup C (𝟙 C.S) 0) :
    cycleDegree C (𝟙 C.S) s α = α.1 s := by
  rw [cycleDegree_apply]
  exact congrArg (fun c : CycleGroup C (𝟙 C.S) 0 ↦ c.1 s)
    (properPushforward_id C (𝟙 C.S) 0 α)

/-! ### Zero cycles on a base with vanishing dimension function -/

section VanishingDimensionFunction

variable (hδ : ∀ s : C.S, C.dimensionFunction s = 0)

include hδ

/-- A closed subscheme of the base, viewed over the base through the identity, has relative
dimension zero at every point. -/
private theorem relativeDimension_comp_id_eq_zero {Z : Scheme.{u}} (i : Z ⟶ C.S)
    [IsClosedImmersion i] (z : Z) :
    relativeDimension C.dimensionFunction (i ≫ 𝟙 C.S) z = 0 := by
  rw [relativeDimension_comp_closedImmersion, relativeDimension_id, hδ]

/-- An irreducible closed subscheme of the base has delta-dimension zero. -/
private theorem schemeDeltaDimension_comp_id_eq_zero {Z : Scheme.{u}} (i : Z ⟶ C.S)
    [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ 𝟙 C.S)] [IrreducibleSpace Z] :
    schemeDeltaDimension C (i ≫ 𝟙 C.S) = (0 : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_id_eq_zero C hδ]
  rfl

/-- **No rational equivalence on the base.** When the dimension function of the base vanishes,
the only zero cycle on the base that is rationally equivalent to zero is the zero cycle, so
`A_0(S) = Z_0(S)`. -/
theorem rationalEquivalences_id_eq_bot : rationalEquivalences C (𝟙 C.S) 0 = ⊥ := by
  refine le_antisymm (fun α hα ↦ ?_) bot_le
  obtain ⟨J, W, hW, hDim, -, g, hcoeff⟩ := hα
  have hempty : IsEmpty J := by
    refine ⟨fun j ↦ ?_⟩
    have := hW j
    exact absurd ((hDim j).symm.trans
      (schemeDeltaDimension_comp_id_eq_zero C hδ (W j).subschemeι)) (by decide)
  refine AddSubgroup.mem_bot.mpr (Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_))
  rw [hcoeff x]
  exact finsum_of_isEmpty _

/-- The degree of a zero cycle on the base, descended to the zeroth Chow group of the base, for
a base with vanishing dimension function. -/
def baseDegree (s : C.S) : chowGroup C (𝟙 C.S) 0 →+ ℤ :=
  QuotientAddGroup.lift (rationalEquivalences C (𝟙 C.S) 0) (cycleDegree C (𝟙 C.S) s)
    fun α hα ↦ by
      rw [rationalEquivalences_id_eq_bot C hδ, AddSubgroup.mem_bot] at hα
      simp [hα]

/-- The degree on the zeroth Chow group of the base reads off the coefficient of a cycle
representative at the chosen point. -/
@[simp]
theorem baseDegree_mk (s : C.S) (α : CycleGroup C (𝟙 C.S) 0) :
    baseDegree C hδ s (QuotientAddGroup.mk' (rationalEquivalences C (𝟙 C.S) 0) α) = α.1 s :=
  cycleDegree_id C s α

end VanishingDimensionFunction

/-! ### The identification of the Chow group of the base with the integers -/

section OnePointBase

variable (hδ : ∀ s : C.S, C.dimensionFunction s = 0) [Subsingleton C.S]

include hδ

/-- **The degree on the base is bijective** for a one-point base with vanishing dimension
function. -/
theorem baseDegree_bijective (s : C.S) : Function.Bijective (baseDegree C hδ s) := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
    induction z using QuotientAddGroup.induction_on with
    | H α =>
      have hzs : α.1 s = 0 := by rwa [← baseDegree_mk C hδ s α]
      refine (QuotientAddGroup.eq_zero_iff α).mpr ?_
      rw [rationalEquivalences_id_eq_bot C hδ]
      refine AddSubgroup.mem_bot.mpr (Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_))
      rw [show x = s from Subsingleton.elim x s, hzs]
      simp
  · intro z
    have hmem : Function.locallyFinsuppWithin.single s z ∈ cyclesOfDimension C (𝟙 C.S) 0 := by
      rw [mem_cyclesOfDimension_iff_forall_point]
      intro x _
      rw [relativeDimension_id, hδ]
    refine ⟨QuotientAddGroup.mk' (rationalEquivalences C (𝟙 C.S) 0) ⟨_, hmem⟩, ?_⟩
    rw [baseDegree_mk]
    simp [Function.locallyFinsuppWithin.single_apply]

/-- For a one-point base with vanishing dimension function — the spectrum of a field — the
degree of a zero cycle is an isomorphism `A_0(S) ≅ ℤ`, sending the fundamental cycle to `1`. -/
@[stacks 0AZ1 "the identification of the Chow group of the base with the integers"]
def chowGroupBaseEquivInt (s : C.S) : chowGroup C (𝟙 C.S) 0 ≃+ ℤ :=
  AddEquiv.ofBijective _ (baseDegree_bijective C hδ s)

/-- The identification `A_0(S) ≅ ℤ` reads off the coefficient of a cycle representative at the
point of the base; in particular it sends the fundamental cycle to one. -/
@[simp]
theorem chowGroupBaseEquivInt_mk (s : C.S) (α : CycleGroup C (𝟙 C.S) 0) :
    chowGroupBaseEquivInt C hδ s
        (QuotientAddGroup.mk' (rationalEquivalences C (𝟙 C.S) 0) α) = α.1 s :=
  baseDegree_mk C hδ s α

/-! ### The descent of the degree to rational equivalence -/

variable {X : Scheme.{u}} (p : X ⟶ C.S) [IsProper p]

omit [Subsingleton C.S] in
/-- **The descent of the degree to rational equivalence.** Granted Stacks 02S2 for `p`, a zero
cycle rationally equivalent to zero has degree zero. -/
theorem cycleDegree_eq_zero_of_mem_rationalEquivalences (s : C.S)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C p (𝟙 C.S) p
      (Category.comp_id p) 0) {α : CycleGroup C p 0} (hα : α ∈ rationalEquivalences C p 0) :
    cycleDegree C p s α = 0 := by
  have h := hfac α hα
  rw [rationalEquivalences_id_eq_bot C hδ, AddSubgroup.mem_bot] at h
  rw [cycleDegree_apply, h]
  simp

end OnePointBase

/-! ### Stacks 02S2 for a source of small delta-dimension -/

/-- **Stacks 02S2 for a source of delta-dimension at most `k`.** Proper pushforward of
`k`-cycles out of a scheme `X` of delta-dimension at most `k` factors through rational
equivalence. -/
theorem properPushforwardFactorsThroughRationalEquivalence_of_schemeDeltaDimension_le
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (k : EInt)) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k := by
  refine properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor C sX sY p hp
    k fun V hV hDim g ↦ absurd hDim ?_
  have := hV
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion]
  intro hEq
  have hEq' := WithBotTop.coe_injective hEq
  have hle := relativeDimension_le_of_schemeDeltaDimension_le' C sX hX
    (V.subschemeι.base (genericPoint V.subscheme))
  omega

end Stacks.Chow

end
