module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat pullback of cycles, and the Gysin map

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project and let `f : X' ⟶ X` be flat of relative dimension `r`. Stacks 02RB pulls a
`k`-cycle on `X` back to a `(k+r)`-cycle on `X'`, by taking the fundamental cycle of the
scheme-theoretic inverse image of each integral component; coefficientwise, the coefficient at
`x'` is the coefficient at `f x'` times the multiplicity of `x'` in the inverse image of the
reduced closure of `f x'`. Stacks 0FVK descends this to Chow groups.

Stacks 0B71 is the compatibility of flat pullback with the Gysin map of the zero scheme
`i : D = Z(s) ⟶ X` of a section of an invertible module. With `L' = f^*L`, `s' = f^*s` and
`D' = Z(s')` there is the square of Stacks 0B6Y

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

and the assertion is

  `(i')^* f^* α = g^* i^* α`  in  `A_{k+r}(D')`,  for `α ∈ Z_{k+1}(X)`.

## Main definitions

* `Stacks.Chow.flatPullbackWeight` — the multiplicity with which a point of `X'` enters the flat
  pullback of a cycle.
* `Stacks.Chow.flatPullbackCoeff`, `Stacks.Chow.flatPullback` — **Stacks 02RB**: flat pullback of
  cycles, coefficientwise and as a homomorphism of cycle groups.
* `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` — Stacks 02S1, that flat pullback
  preserves rational equivalence, read as a hypothesis.
* `Stacks.Chow.flatPullbackChow` — **Stacks 0FVK**: flat pullback on Chow groups.
* `Stacks.Chow.GysinCompatibleWithFlatPullback` — the identity of Stacks 0B71 on integral
  components.

## Main results

* `Stacks.Chow.flatPullbackCoeff_locallyFiniteSupport`,
  `Stacks.Chow.flatPullbackCoeff_mem_cyclesOfDimension` — the pulled-back coefficient function is
  a `(k+r)`-cycle.
* `Stacks.Chow.flatPullback_gysinRule_extendCycleGroup` — Stacks 0B71 at the level of **cycles**.
* `Stacks.Chow.gysinHomomorphism_flatPullback` — **Stacks 0B71** on Chow groups.

## Implementation notes

### What of Stacks 02RB and 0FVK is here

`Stacks.Chow.flatPullback` is the full construction of Stacks 02RB, with its two well-definedness
statements proved, and it carries the first half of that tag's covering set. The second half —
that the pullback of the fundamental cycle of an integral closed subscheme is the fundamental
cycle of its scheme-theoretic inverse image — is proved as
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles`, which composes the three coefficient
lemmas of `Bivariant42/FlatPullbackComponent.lean`. So the covering set of 02RB is complete
across the two files and each half carries its own `@[stacks 02RB]` attribute. Of
Stacks 0FVK only the definition of flat pullback on Chow groups is here, under the hypothesis
below, so no `@[stacks 0FVK]` attribute is placed in this file; the three assertions of that
tag — that the base change of `f` is again flat of relative dimension `r`, and the two
commuting squares of cycle groups and of Chow groups — are
`Stacks.Chow.flat_relativeDimension_baseChange`,
`Stacks.Chow.baseChange_flatPullback_cycles` and `Stacks.Chow.baseChange_flatPullback_chow` in
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatPullback`, which carry it.

### The parameters threaded, and why

* Stacks 02S1, that flat pullback carries cycles rationally equivalent to zero to cycles
  rationally equivalent to zero, is carried as the hypothesis
  `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence`, in the same style in which Stacks
  02S2 is carried in `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow`. The hypothesis
  *is* the existence of the map of Stacks 0FVK, so nothing is lost.

  For a **general** flat `f` of relative dimension `r` it is the theorem
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` of
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence`, proved
  unconditionally and carrying the `@[stacks 02S1]` attribute. That file imports this one, which is
  the only reason the hypothesis is threaded here; it is substituted in
  `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackDischarge`. For an **open immersion** in
  relative dimension zero the attribute sits on it in two further places:
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι` in
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence` for the
  inclusion of an open, and
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion` in
  `StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces` for an arbitrary
  open immersion. So a consumer should supply one of the three rather than assume the hypothesis.
* The component rules `chern` and `chern'` of the contained-component case of the Gysin map,
  standing in for Stacks 02SO, as in
  `StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction`.
* The invertibility of `L' = f^*L`, which is Stacks 0B8L — a theorem, but one this repository does
  not have, so it is **an extra instance hypothesis** on the statements about the Gysin map below.
* The morphism `g : D' ⟶ D` of the square of Stacks 0B6Y, together with its flatness and relative
  dimension. The statement of Stacks 0B71 quantifies over `g` and a proof that the square is
  cartesian, and derives those two from the cartesian square by
  `MorphismProperty.of_isPullback` and Stacks 02NK; those two consequences are taken directly as
  parameters here, which is a generalization.

### The compatibility hypothesis is the integral case of the source

`Stacks.Chow.GysinCompatibleWithFlatPullback` says that the identity holds at the level of cycle
coefficients on the fundamental cycle of each integral component of `X`. That is the case the
source proves, by Stacks 02RE when `W ⊄ D` and by Stacks 02SS when `W ⊆ D`; neither is formalized
here. It cannot be dropped: the Gysin maps on `X` and on `X'` are built from two unrelated
component rules.

The extension from integral components to every cycle is the work, and it is not formal — a cycle
is a *locally* finite sum of components, and the left side is a sum over the points of `X'` while
the right side is a sum over the points of `X`, so the proof reindexes the first over the fibres
of `f`. The finiteness that licenses this comes from the local finiteness of the support of the
pulled-back cycle, which is why `Stacks.Chow.flatPullbackCoeff_locallyFiniteSupport` has to be
proved and not assumed.

### No `@[stacks 0B71]`

The tag's single statement is the unconditional identity. Every declaration below carries the two
component rules, the invertibility of `f^*L`, the Stacks 02S1 hypothesis along `g` and the
integral-component compatibility, so none of them is literally the tagged statement. Accordingly
no `@[stacks]` attribute is placed in this file.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two local finiteness facts -/

/-- The indicator of the union of the supports of two locally finitely supported functions is
again locally finitely supported. -/
private theorem locallyFiniteSupport_union {X : Type u} [TopologicalSpace X] {a b : X → ℤ}
    (ha : LocallyFiniteSupport a) (hb : LocallyFiniteSupport b) :
    LocallyFiniteSupport (fun x ↦ if a x ≠ 0 ∨ b x ≠ 0 then (1 : ℤ) else 0) := by
  intro x
  obtain ⟨U, hU, hUa⟩ := ha x
  obtain ⟨V, hV, hVb⟩ := hb x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  have hsupport : (fun x ↦ if a x ≠ 0 ∨ b x ≠ 0 then (1 : ℤ) else 0).support =
      a.support ∪ b.support := by
    ext y
    by_cases ha0 : a y = 0 <;> by_cases hb0 : b y = 0 <;> simp [Function.mem_support, ha0, hb0]
  rw [hsupport]
  refine (hUa.union hVb).subset ?_
  rintro y ⟨hy, hy' | hy'⟩
  · exact Or.inl ⟨hy.1, hy'⟩
  · exact Or.inr ⟨hy.2, hy'⟩

/-- The indicator of the union of the supports of a finite family of locally finitely supported
functions is again locally finitely supported. -/
private theorem locallyFiniteSupport_finset_union {ι : Type u} {X : Type u} [TopologicalSpace X]
    (t : Finset ι) (a : ι → X → ℤ) (ha : ∀ i ∈ t, LocallyFiniteSupport (a i)) :
    LocallyFiniteSupport (fun x ↦ if ∃ i ∈ t, a i x ≠ 0 then (1 : ℤ) else 0) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro x
    exact ⟨Set.univ, Filter.univ_mem, by simp⟩
  | @insert i t hi ih =>
    simpa [Finset.mem_insert, or_left_comm, or_assoc] using
      locallyFiniteSupport_union (ha i (Finset.mem_insert_self i t))
        (ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))

/-! ### Flat pullback of cycles -/

/-- **Stacks 02RB.** The multiplicity with which a point `x'` of `X'` enters the flat pullback of
a cycle along `f : X' ⟶ X`: the coefficient, at `x'`, of the fundamental cycle of the
scheme-theoretic inverse image of the reduced closure of `f x'`. That reduced closure is
represented by its vanishing ideal sheaf, whose inverse image is the `comap` ideal sheaf. -/
def flatPullbackWeight (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (f : X' ⟶ X) (j : ℤ) (x' : X') : ℤ :=
  closedSubschemeCycleCoeff C sX'
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({f.base x'} : Set X))).comap f).subschemeι) j x'

/-- **Stacks 02RB.** The coefficient at `x'` of the flat pullback of a cycle: the coefficient of
the cycle at `f x'`, times the multiplicity `Stacks.Chow.flatPullbackWeight`. -/
def flatPullbackCoeff (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) (r : ℕ)
    (k : ℤ) (c : CycleGroup C sX k) (x' : X') : ℤ :=
  c.1 (f.base x') * flatPullbackWeight C sX' f (k + (r : ℤ)) x'

/-- The coefficient function of a flat pullback is locally finitely supported: around a point
`x'` of `X'` only finitely many components of `c` pass through `f x'`, and each of them
contributes a cycle with locally finite support. -/
theorem flatPullbackCoeff_locallyFiniteSupport (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (_hbase : f ≫ sX = sX') (r : ℕ)
    (_hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (c : CycleGroup C sX k) :
    LocallyFiniteSupport (flatPullbackCoeff C sX' sX f r k c) := by
  classical
  let csupp : Set X := Function.support c.1.toFun
  have hcsupp : LocallyFinite (fun y : csupp ↦ ({(y : X)} : Set X)) :=
    (Function.locallyFinsupp.locallyFiniteSupport c.1).locallyFinite_support
  intro x'
  obtain ⟨V, hV, hVfinite⟩ := hcsupp (f.base x')
  let finiteI : Finset csupp := hVfinite.toFinset
  let a (y : csupp) (z : X') : ℤ :=
    closedSubschemeCycleCoeff C sX'
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(y.1 : X)} : Set X))).comap f).subschemeι) (k + (r : ℤ)) z
  have ha : ∀ y ∈ finiteI, LocallyFiniteSupport (a y) := fun y _ ↦
    closedSubschemeCycleCoeff_locallyFiniteSupport C sX'
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(y.1 : X)} : Set X))).comap f).subschemeι) (k + (r : ℤ))
  obtain ⟨W, hW, hWfinite⟩ := locallyFiniteSupport_finset_union finiteI a ha x'
  refine ⟨f.base ⁻¹' V ∩ W, Filter.inter_mem (f.continuous.continuousAt hV) hW, ?_⟩
  refine hWfinite.subset ?_
  intro z hz
  have hprod : c.1 (f.base z) ≠ 0 ∧ flatPullbackWeight C sX' f (k + (r : ℤ)) z ≠ 0 :=
    mul_ne_zero_iff.1 (by simpa [flatPullbackCoeff] using Function.mem_support.1 hz.2)
  let y : csupp := ⟨f.base z, Function.mem_support.2 hprod.1⟩
  have hzunion : ∃ j ∈ finiteI, a j z ≠ 0 :=
    ⟨y, (Set.Finite.mem_toFinset hVfinite).2 ⟨f.base z, by simp [y], hz.1.1⟩,
      by simpa [a, y, flatPullbackWeight] using hprod.2⟩
  refine ⟨hz.1.2, ?_⟩
  show z ∈ (fun q ↦ if ∃ j ∈ finiteI, a j q ≠ 0 then (1 : ℤ) else 0).support
  exact Function.mem_support.2 (by simp [hzunion])

/-- The pulled-back coefficient function is a cycle of delta-dimension `k + r`: a point
contributing to it has relative dimension `k + r`, since otherwise its multiplicity in the
inverse image vanishes. -/
theorem flatPullbackCoeff_mem_cyclesOfDimension (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (c : CycleGroup C sX k) :
    (⟨flatPullbackCoeff C sX' sX f r k c, fun _ _ ↦ trivial, fun x' _ ↦
      flatPullbackCoeff_locallyFiniteSupport C sX' sX f hbase r hf k c x'⟩ :
        AlgebraicCycle X' ℤ) ∈ cyclesOfDimension C sX' (k + (r : ℤ)) := by
  rw [mem_cyclesOfDimension]
  intro Z hZ
  change flatPullbackCoeff C sX' sX f r k c Z.isIrreducible.genericPoint ≠ 0 at hZ
  have hcoeff := (mul_ne_zero_iff.1 hZ).2
  have hdim : relativeDimension C.dimensionFunction sX' Z.isIrreducible.genericPoint =
      k + (r : ℤ) := by
    unfold flatPullbackWeight closedSubschemeCycleCoeff at hcoeff
    split at hcoeff
    · rename_i h
      exact h.choose_spec.2
    · contradiction
  rw [deltaDimension_eq_of_isGenericPoint C sX' Z Z.isIrreducible.genericPoint
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
  exact hdim

/-- **Stacks 02RB.** Flat pullback of cycles along a flat morphism of relative dimension `r`, as
a homomorphism `Z_k(X) ⟶ Z_{k+r}(X')`. -/
@[stacks 02RB "flat pullback homomorphism"]
def flatPullback (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) :
    CycleGroup C sX k →+ CycleGroup C sX' (k + (r : ℤ)) where
  toFun c := ⟨⟨flatPullbackCoeff C sX' sX f r k c, fun _ _ ↦ trivial, fun x' _ ↦
      flatPullbackCoeff_locallyFiniteSupport C sX' sX f hbase r hf k c x'⟩,
      flatPullbackCoeff_mem_cyclesOfDimension C sX' sX f hbase r hf k c⟩
  map_zero' := by
    apply Subtype.ext
    ext x'
    change flatPullbackCoeff C sX' sX f r k 0 x' = 0
    simp [flatPullbackCoeff]
  map_add' a b := by
    apply Subtype.ext
    ext x'
    change flatPullbackCoeff C sX' sX f r k (a + b) x' =
      flatPullbackCoeff C sX' sX f r k a x' + flatPullbackCoeff C sX' sX f r k b x'
    simp [flatPullbackCoeff, add_mul]

/-- **Stacks 02RB.** The coefficient formula for the flat pullback of a cycle. -/
@[simp]
theorem flatPullback_apply (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (c : CycleGroup C sX k) (x' : X') :
    (flatPullback C sX' sX f hbase r hf k c).1 x' =
      c.1 (f.base x') * flatPullbackWeight C sX' f (k + (r : ℤ)) x' :=
  rfl

/-! ### Flat pullback on Chow groups -/

/-- **Stacks 02S1.** The assertion that flat pullback of `k`-cycles along `f` carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero, hence factors through
rational equivalence.

Carried as a hypothesis here only because its proof is downstream:
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` proves it unconditionally for
an arbitrary flat `f` of relative dimension `r`, and for an open immersion
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι` and
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion` do the same. All
three carry the `@[stacks 02S1]` attribute and should be supplied rather than assumed. See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`. -/
def FlatPullbackFactorsThroughRationalEquivalence (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) : Prop :=
  ∀ α ∈ rationalEquivalences C sX k,
    flatPullback C sX' sX f hbase r hf k α ∈ rationalEquivalences C sX' (k + (r : ℤ))

/-- **Stacks 0FVK.** Flat pullback on Chow groups, `f^* : A_k(X) ⟶ A_{k+r}(X')`, induced by flat
pullback of cycles and granted that it factors through rational equivalence. -/
def flatPullbackChow (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase r hf k) :
    chowGroup C sX k →+ chowGroup C sX' (k + (r : ℤ)) :=
  QuotientAddGroup.map (rationalEquivalences C sX k)
    (rationalEquivalences C sX' (k + (r : ℤ)))
    (flatPullback C sX' sX f hbase r hf k) fun α hα ↦ hfac α hα

/-- **Stacks 0FVK.** On the class of a cycle, flat pullback on Chow groups is the class of the
flat pullback of that cycle. -/
@[simp]
theorem flatPullbackChow_mk (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase r hf k)
    (α : CycleGroup C sX k) :
    flatPullbackChow C sX' sX f hbase r hf k hfac
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sX' (k + (r : ℤ)))
        (flatPullback C sX' sX f hbase r hf k α) :=
  rfl

/-! ### Transporting a cycle along an equality of degrees -/

/-- The coefficient function of a cycle is unchanged by transport along an equality of
delta-dimensions. Stacks 0B71 needs one such transport, because the flat pullback of a
`(k+1)`-cycle has degree `(k+1) + r` while the Gysin map in degree `k + r` consumes a cycle of
degree `(k+r) + 1`. -/
theorem val_cycleGroup_cast (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {j j' : ℤ} (h : j = j') (α : CycleGroup C q j) :
    (h ▸ α : CycleGroup C q j').1 = α.1 := by
  subst h
  rfl

/-! ### Stacks 0B71 on integral components -/

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
    ((Scheme.Modules.pullback f).obj L)]
  (chern : FirstChernComponentClassRule C p k)
  (chern' : FirstChernComponentClassRule C (f ≫ p) (k + (r : ℤ)))
  (g : (pullbackZeroScheme f L s).subscheme ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme)
  [LocallyOfFiniteType g] [Flat g] (hg : AlgebraicGeometry.RelativeDimension g r)
  (hbase : g ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) =
    (pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))

/-- **Stacks 0B71 on integral components.** The assertion that for every integral component of
`X` of delta-dimension `k + 1` — equivalently, for every point `x` of relative dimension `k + 1` —
the sum over the fibre `f^{-1}(x)` of the Gysin component cycles on `X'`, weighted by the flat
pullback multiplicity, is the flat pullback along `g` of the Gysin component cycle of `x`.

This is the case the source proves, by Stacks 02RE when the component is not contained in the
zero scheme and by Stacks 02SS when it is. It is carried as a hypothesis here; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`.

It is not merely unproved: as an equality of cycle coefficients it is independent of the axioms, so
no declaration can produce it. On a component contained in the zero scheme
`Stacks.Chow.gysinComponentCycle` is the pushforward of `Quotient.out` of a first Chern class,
an unconstrained representative, and `Stacks.Chow.FirstChernComponentClassRule` relates the rule on
`X` to the rule on `X'` not at all, so a coefficientwise equality between a fibre sum of
representatives chosen on `X'` and the pullback of one chosen on `X` does not follow. The same
obstruction is recorded for the proper-pushforward twin in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly`. What is true, and proved
without hypotheses at the first Chern class rules of an invertible module, is the rational
equivalence form `Stacks.Chow.GysinRationallyCompatibleWithFlatPullback`; it suffices wherever the
conclusion is an equality of Chow classes. -/
def GysinCompatibleWithFlatPullback : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 →
    ∀ y' : (pullbackZeroScheme f L s).subscheme,
      ∑ᶠ x' ∈ f.base ⁻¹' {x},
          flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
            (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)
              (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' =
        (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
          (gysinComponentCycleAt C p k L s chern x)).1 y'

/-! ### Stacks 0B71 -/

/-- **Stacks 0B71, at the level of cycles.** Granted the identity on integral components, Gysin
pullback through the zero scheme of `s` commutes with flat pullback, already on cycles.

The left side is a locally finite sum over the points of `X'` and the right side one over the
points of `X`. The proof reindexes the first over the fibres of `f`, using
`Stacks.Chow.finsum_finsum_mem_fiber`; the finiteness it needs comes from the local finiteness of
the support of the pulled-back cycle. After that the hypothesis applies term by term, and only
the points carrying a nonzero coefficient of `α` are compared — those have relative dimension
`k + 1` because `α` is a `(k+1)`-cycle. -/
theorem flatPullback_gysinRule_extendCycleGroup
    (hcomp : GysinCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase)
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    (gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
        ((gysinRule C p k L s chern).extendCycleGroup α) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y'
  set β := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α with hβ
  set R' := gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern' with hR'
  set G : X' → ℤ := fun x' ↦ β.1 x' *
    (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' with hG
  -- only the components of the pulled-back cycle passing through `y'` contribute
  have hGfin : (Function.support G).Finite := by
    refine (finite_support_inter_generalizations β.1.locallyFiniteSupport
      (isCompact_singleton (x := (pullbackZeroScheme f L s).subschemeι.base y'))).subset ?_
    intro x' hx'
    replace hx' : β.1 x' * R'.toComponentRule.cycle x' y' ≠ 0 := hx'
    exact ⟨⟨_, rfl, R'.toComponentRule.mem_closure_of_apply_ne_zero x' y'
      (right_ne_zero_of_mul hx')⟩, left_ne_zero_of_mul hx'⟩
  -- the left hand side, reindexed over the fibres of `f`
  have hLHS : (R'.extendCycleGroup (hcast ▸ β)).1 y' =
      ∑ᶠ x : X, ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x' := by
    rw [finsum_finsum_mem_fiber f.base G hGfin,
      show (R'.extendCycleGroup (hcast ▸ β)).1 y' =
        R'.toComponentRule.extendCoeff (hcast ▸ β : CycleGroup C (f ≫ p) _).1 y' from rfl,
      val_cycleGroup_cast C (f ≫ p) hcast β]
    rfl
  -- the right hand side, as a locally finite sum over the points of `X`
  have hRHS : (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
      ((gysinRule C p k L s chern).extendCycleGroup α)).1 y' =
      ∑ᶠ x : X, α.1 x *
        (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
          (gysinComponentCycleAt C p k L s chern x)).1 y' := by
    rw [flatPullback_apply,
      show ((gysinRule C p k L s chern).extendCycleGroup α).1 (g.base y') =
        ∑ᶠ x : X, α.1 x * (gysinComponentCycleAt C p k L s chern x).1 (g.base y') from rfl,
      finsum_mul]
    exact finsum_congr fun x ↦ by rw [flatPullback_apply]; ring
  rw [hLHS, hRHS]
  refine finsum_congr fun x ↦ ?_
  -- the coefficient at a point of the fibre over `x`
  have hGval : ∀ x' : X', f.base x' = x → G x' = α.1 x *
      (flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
        (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y') := by
    intro x' hx'
    have h1 : β.1 x' = α.1 x * flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' := by
      rw [hβ, flatPullback_apply, hx']
    simp only [hG]
    rw [h1, mul_assoc]
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
      rw [hGval x' hx', hx, zero_mul]
  · rw [← hcomp x ((mem_cyclesOfDimension_iff_forall_point C p (k + 1) α.1).1 α.2 x hx) y',
      mul_finsum_mem]
    exact finsum_mem_congr rfl fun x' hx' ↦ hGval x' hx'

/-- **Stacks 0B71.** Gysin pullback through the zero scheme of a section commutes with flat
pullback: `(i')^* f^* α = g^* i^* α` in `A_{k+r}(D')` for every `α ∈ Z_{k+1}(X)`.

The component rules of the Gysin maps on `X` and on `X'`, their compatibility along `f`, the
invertibility of `f^*L` (Stacks 0B8L) and the vanishing of Stacks 02S1 along `g` needed for
`Stacks.Chow.flatPullbackChow` are explicit parameters; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`. The identity holds already at the
level of cycles, which is `Stacks.Chow.flatPullback_gysinRule_extendCycleGroup`.

No Stacks attribute is placed here: both of the parameters above are assumed, so this is the
flat-pullback axiom granted itself. It is proved without them, at the first Chern class rules of an
invertible module, in
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible`, which carries the
attribute. -/
theorem gysinHomomorphism_flatPullback
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k)
    (hcomp : GysinCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase)
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    gysinHomomorphism C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) chern'
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k hfac
        (gysinHomomorphism C p k L s chern α) := by
  show QuotientAddGroup.mk ((gysinRule C (f ≫ p) (k + (r : ℤ))
    ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup
      (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α)) = _
  rw [flatPullback_gysinRule_extendCycleGroup C p f r hf k L s chern chern' g hg hbase hcomp
    hcast α]
  rfl

end Stacks.Chow

end
