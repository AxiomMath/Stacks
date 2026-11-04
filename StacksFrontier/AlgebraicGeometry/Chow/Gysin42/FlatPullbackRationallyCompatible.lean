module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection

/-!
# Stacks 0B71 for an invertible module, with no hypothesis

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X' ⟶ X` be
flat and locally of finite type of relative dimension `r` between schemes locally of finite type
over `S`, let `L` be an invertible module on `X` with `s ∈ Γ(X, L)`, and let `i : D = Z(s) ⟶ X`
and `i' : D' = Z(f^*s) ⟶ X'` be the two zero schemes. Remark 0B6Y produces the cartesian square

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

and Stacks 0B71 is the identity `(i')^* f^* α = g^* i^* α` in `CH_{k+r}(D')` for `α ∈ Z_{k+1}(X)`.

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackInvertible` proves that identity carrying
two hypotheses: the vanishing of Stacks 02S1 along `g`, and `GysinCompatibleWithFlatPullback`,
which asserts the tag itself on integral components as an **equality of cycle coefficients**. This
file removes both.

The equality of coefficients is unavailable: on a component `W ⊆ D` the Gysin rule of Stacks 02T8
pushes forward an arbitrary representative `Quotient.out` of `c₁(L|_W) ∩ [W]`, so the two sides
agree only up to rational equivalence. So the hypothesis is first weakened to
`Stacks.Chow.GysinRationallyCompatibleWithFlatPullback`, which asks for a rational equivalence
carried on the part of `D'` lying over `f^{-1}(W)`, and the weakened form is then proved outright
for the component rules of an invertible module.

## Main results

* `Stacks.Chow.GysinRationallyCompatibleWithFlatPullback` — the component case of Stacks 0B71 up
  to rational equivalence, with the carrier of the equivalence retained.
* `Stacks.Chow.flatPullback_gysinRule_rationallyEquivalent` — Stacks 0B71 on cycles, up to
  rational equivalence, from that hypothesis.
* `Stacks.Chow.gysinRationallyCompatibleWithFlatPullback_invertible` — **the hypothesis, proved**
  at the component rules of `L` and of `f^*L`.
* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible` — **Stacks 0B71** for an
  arbitrary cycle at the Gysin map of an invertible module, with no hypothesis.

## Implementation notes

### Why the carrier is part of the statement

A cycle is a locally finite sum over its components, and Stacks 02RZ sums the component rational
equivalences only when their carriers form a locally finite family. So
`Stacks.Chow.IsRationallyEquivalentToZeroWithin` is used rather than Stacks 02RW, with the
carrier `(i')^{-1}(f^{-1}(closure {x}))` at the component of `x`; those sets are locally finite
because the `closure {x}` are.

### The two cases of the component statement

* `W ⊄ D`. Both sides are fundamental cycles of scheme-theoretic intersections — on `X'` by
  Stacks 02RB and 02TB (1), on `D'` by Stacks 02RB along `g` and the cartesian square — so they
  are *equal*, with no rational equivalence at all. That is
  `Stacks.Chow.gysinComponentDifference_eq_zero_of_not_le`. The side conditions come from the
  integrality of `W`: `W ∩ D` is an effective Cartier divisor on `W`, and its flat pullback is
  one on `f^{-1}(W)`; the dimension bound is read off from
  `Stacks.Chow.zeroScheme_le_integralComponentAt_subschemeι_base` and the strict drop of the
  relative dimension along a nontrivial specialization.
* `W ⊆ D`. Here both Gysin component cycles are pushforwards of `Quotient.out` representatives.
  Pushing them into `X'` along `i'`,
  `Stacks.Chow.properPushforward_gysinComponentCycleAt_eq_firstChernComponentCycleAt` identifies
  the difference with the left hand side of the component case of Stacks 02SS **for the out
  rules** `Stacks.Chow.gysinOutComponentCycleRule`. Stacks 0EPJ settles that case for the
  divisor-cycle rules, as `firstChernCapRationallyCompatibleWithFlatPullback_invertible`; passing
  to the out rules costs one rational equivalence on `f^{-1}(W)` on the `X`-side (Stacks 02S1
  along the component restriction, applied to
  `Stacks.Chow.rationallyEquivalent_gysinOutComponentCycleRule`) and one application of
  Stacks 02RZ over the irreducible components of `f^{-1}(W)` on the `X'`-side. Because `W ⊆ D`,
  the subscheme `f^{-1}(W)` and each of its components is a closed subscheme of `D'`, which is
  what puts every witness inside the required carrier.

### No `@[stacks 0B71]`

No Stacks attribute is placed in this file; the tags are placed elsewhere.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Rational equivalence within a carrier: the closure properties needed here -/

/-- The sum of two cycles rationally equivalent to zero within a subset is rationally equivalent
to zero within it, by the disjoint union of the two witnessing families. -/
public theorem isRationallyEquivalentToZeroWithin_add (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T)
    (hβ : IsRationallyEquivalentToZeroWithin C p k β T) :
    IsRationallyEquivalentToZeroWithin C p k (α + β) T := by
  obtain ⟨J, W, hW, hDimW, hLocalW, hsubW, g, hg⟩ := hα
  obtain ⟨K, V, hV, hDimV, hLocalV, hsubV, h, hh⟩ := hβ
  refine ⟨J ⊕ K, Sum.elim W V,
    (fun t ↦ match t with | .inl j => hW j | .inr l => hV l),
    (fun t ↦ match t with | .inl j => hDimW j | .inr l => hDimV l), ?_,
    (fun t ↦ match t with | .inl j => hsubW j | .inr l => hsubV l),
    (fun t ↦ match t with | .inl j => g j | .inr l => h l), fun x ↦ ?_⟩
  · have hsets : (fun t : J ⊕ K ↦ ((Sum.elim W V t).support : Set X)) =
        Sum.elim (fun j ↦ ((W j).support : Set X)) (fun l ↦ ((V l).support : Set X)) :=
      funext fun t ↦ by cases t <;> rfl
    rw [hsets]
    exact locallyFinite_sum_elim _ _ hLocalW hLocalV
  · show α.1 x + β.1 x = _
    rw [hg x, hh x]
    exact (principalDivisorFamilyCoefficient_sum C p W V hW hV g h hLocalW hLocalV x).symm

/-- The negative of a cycle rationally equivalent to zero within a subset is rationally
equivalent to zero within it, via the inverses of the same rational functions. -/
public theorem isRationallyEquivalentToZeroWithin_neg (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T) :
    IsRationallyEquivalentToZeroWithin C p k (-α) T := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := hα
  refine ⟨J, W, hW, hDim, hLocal, hsub, fun j ↦ (g j)⁻¹, fun x ↦ ?_⟩
  show -α.1 x = principalDivisorFamilyCoefficient C p W hW (fun j ↦ (g j)⁻¹) x
  rw [hg x]
  unfold principalDivisorFamilyCoefficient
  rw [← finsum_neg_distrib]
  refine finsum_congr fun j ↦ ?_
  rw [principalDivisorPushforward_inv]
  rfl

/-- An integer multiple of a cycle rationally equivalent to zero within a subset is rationally
equivalent to zero within it. -/
private theorem isRationallyEquivalentToZeroWithin_zsmul (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T) (n : ℤ) :
    IsRationallyEquivalentToZeroWithin C p k (n • α) T := by
  induction n using Int.induction_on with
  | zero => simpa using isRationallyEquivalentToZeroWithin_zero C p k T
  | succ m ih =>
    rw [add_smul, one_smul]
    exact isRationallyEquivalentToZeroWithin_add C p k ih hα
  | pred m ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg]
    exact isRationallyEquivalentToZeroWithin_add C p k ih
      (isRationallyEquivalentToZeroWithin_neg C p k hα)

/-- **Stacks 02S1 with its carrier retained.** If a `k`-cycle on `X` is rationally equivalent to
zero within a subset `T`, then its flat pullback along a morphism `f : X' ⟶ X` which is flat and
locally of finite type of relative dimension `r` is rationally equivalent to zero within the
preimage of `T`.

This is the proof of `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` with the
carrier kept rather than discarded. Each term of the presentation of Stacks 02RW is rewritten by
the closed-immersion case of Stacks 02RG as the pushforward, from the scheme-theoretic inverse
image `f^{-1}(W_j)`, of a cycle rationally equivalent to zero there
(`Stacks.Chow.exists_rationallyEquivalentToZero_comap_principalDivisor`); pushing forward along a
closed immersion confines the witnesses to its image
(`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion`), which
here is `f^{-1}(W_j)`; those preimages are locally finite by Stacks 02R9 and each lies inside
`f^{-1}(T)`, so `Stacks.Chow.rationallyEquivalentToZeroWithin_finsum` reassembles them.

This is the flat-pullback counterpart of
`Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup`, which does the same
for the Gysin map. No `@[stacks 02S1]` attribute joins the one the tag already carries: nothing is
asserted here that the general theorem does not already say, only where its witnesses lie. -/
public theorem flatPullback_isRationallyEquivalentToZeroWithin (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    {α : CycleGroup C sX k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C sX k α T) :
    IsRationallyEquivalentToZeroWithin C sX' (k + (r : ℤ))
      (flatPullback C sX' sX f hbase r hf k α) (f.base ⁻¹' T) := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := hα
  choose β hβzero hβcoeff using fun j : J ↦
    exists_rationallyEquivalentToZero_comap_principalDivisor C sX' sX f hbase r hf k
      (W j) (hW j) (hDim j) (g j)
  set D : J → CycleGroup C sX' (k + (r : ℤ)) := fun j ↦
    properPushforward C (((W j).comap f).subschemeι ≫ sX') sX' ((W j).comap f).subschemeι rfl
      (k + (r : ℤ)) (β j) with hD
  -- the scheme-theoretic inverse images are the preimages of the members
  have hrange : ∀ j, Set.range (((W j).comap f).subschemeι.base) =
      f.base ⁻¹' ((W j).support : Set X) := fun j ↦ by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage]
  have hpiece : ∀ j, IsRationallyEquivalentToZeroWithin C sX' (k + (r : ℤ)) (D j)
      (f.base ⁻¹' ((W j).support : Set X)) := fun j ↦ by
    rw [← hrange j]
    exact properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
      (((W j).comap f).subschemeι ≫ sX') sX' ((W j).comap f).subschemeι rfl (k + (r : ℤ))
      (hβzero j)
  -- Stacks 02R9
  have hLF : LocallyFinite fun j ↦ f.base ⁻¹' ((W j).support : Set X) :=
    hLocal.preimage_continuous f.continuous
  have hpres : ∀ x' : X', (flatPullback C sX' sX f hbase r hf k α).1 x' =
      ∑ᶠ j : J, (D j).1 x' := fun x' ↦ by
    rw [flatPullback_apply, hg (f.base x')]
    simp only [principalDivisorFamilyCoefficient]
    rw [finsum_mul]
    exact finsum_congr fun j ↦ (hβcoeff j x').symm
  refine (rationallyEquivalentToZeroWithin_finsum C sX' (k + (r : ℤ)) D
    (fun j ↦ f.base ⁻¹' ((W j).support : Set X)) hLF hpiece hpres).mono ?_
  exact Set.iUnion_subset fun j ↦ Set.preimage_mono (hsub j)

/-! ### Stacks 0B71 on integral components, up to rational equivalence -/

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

/-- **Stacks 0B71 on integral components, up to rational equivalence.** For every integral
component of `X` of delta-dimension `k + 1` — equivalently, for every point `x` of relative
dimension `k + 1` — the sum over the fibre `f^{-1}(x)` of the Gysin component cycles on `X'`,
weighted by the flat pullback multiplicity, differs from the flat pullback along `g` of the Gysin
component cycle of `x` by a cycle rationally equivalent to zero **on the part of `D' = Z(f^*s)`
lying over `f^{-1}(closure {x})`**.

This is what the source produces: its proof of the component case ends by exhibiting a rational
equivalence on `f^{-1}(W)`, and the equivalences over the various components of a cycle are summed
by Stacks 02RZ, which needs their carriers to form a locally finite family. It is strictly weaker
than `Stacks.Chow.GysinCompatibleWithFlatPullback`, which asks for an equality of cycle
coefficients. -/
def GysinRationallyCompatibleWithFlatPullback : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 →
    ∃ a : CycleGroup C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)),
      IsRationallyEquivalentToZeroWithin C
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) a
          ((pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {x})) ∧
        ∀ y' : (pullbackZeroScheme f L s).subscheme,
          (∑ᶠ x' ∈ f.base ⁻¹' {x},
              flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
                (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ))
                  ((Scheme.Modules.pullback f).obj L)
                  (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y') -
            (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
              ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
              (gysinComponentCycleAt C p k L s chern x)).1 y' = a.1 y'

omit [Flat f] in
/-- The equality of cycle coefficients over each integral component implies the rational
equivalence over it, by the zero rational equivalence. So
`Stacks.Chow.GysinCompatibleWithFlatPullback` is the stronger of the two hypotheses and everything
proved from it is subsumed here. -/
theorem gysinRationallyCompatibleWithFlatPullback_of_compatible
    (h : GysinCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase) :
    GysinRationallyCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase := by
  intro x hx
  refine ⟨0, isRationallyEquivalentToZeroWithin_zero C _ _ _, fun y' ↦ ?_⟩
  rw [h x hx y', sub_self]
  rfl

/-! ### The Gysin cycle of the flat pullback of a fundamental cycle -/

/-- The Gysin cycle of the flat pullback of the fundamental cycle of the integral closed
subscheme through `x`, read at a point of `D' = Z(f^*s)`: it is the sum over the fibre of `f`
above `x` of the Gysin component cycles of `X'`, weighted by the flat pullback multiplicities.
This is the left hand side of the component case of Stacks 0B71. -/
private theorem extendCycleGroup_flatPullback_gysin_apply
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (x : X)
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (y' : (pullbackZeroScheme f L s).subscheme) :
    ((gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
          (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)))).1 y'
      = ∑ᶠ x' ∈ f.base ⁻¹' {x},
          flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
            (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
              (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' := by
  set R' := gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern' with hR'
  set α₀ := cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)
    with hα₀
  set γ := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α₀ with hγ
  have hone : α₀.1 x = 1 :=
    cycleAssociatedToClosedSubscheme_integralComponentAt_self C p x
      (schemeDeltaDimension_integralComponentAt_of_eq C p hx)
  have hzero : ∀ z : X, z ≠ x → α₀.1 z = 0 := fun z hz ↦
    cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p (k + 1) x hz
  have h0 : (R'.extendCycleGroup (hcast ▸ γ)).1 y' =
      ∑ᶠ x' : X', γ.1 x' *
        (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' := by
    rw [show (R'.extendCycleGroup (hcast ▸ γ)).1 y' =
        R'.toComponentRule.extendCoeff (hcast ▸ γ : CycleGroup C (f ≫ p) _).1 y' from rfl,
      val_cycleGroup_cast C (f ≫ p) hcast γ]
    rfl
  rw [h0, ← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (f.base ⁻¹' {x}) ?_]
  · refine finsum_mem_congr rfl fun x' hx' ↦ ?_
    have hbase' : f.base x' = x := hx'
    rw [hγ, flatPullback_apply, hbase', hone, one_mul]
  · intro x' hx'
    refine ⟨fun _ ↦ ?_, fun _ ↦ Set.mem_univ x'⟩
    by_contra hne
    refine hx' ?_
    have hγ0 : γ.1 x' = 0 := by
      rw [hγ, flatPullback_apply, hzero (f.base x') hne, zero_mul]
    show γ.1 x' * (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ))
      ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' = 0
    rw [hγ0, zero_mul]

/-! ### Stacks 0B71 at the level of cycles, up to rational equivalence -/

/-- **Stacks 0B71 at the level of cycles, up to rational equivalence.** Granted the rational
equivalence over each integral component, the Gysin cycle of a flat pullback and the flat pullback
of the Gysin cycle are rationally equivalent on `D' = Z(f^*s)`.

The proof writes their difference as a locally finite sum, indexed by the support of `α`, of the
rational equivalences the hypothesis supplies, each carried over the part of `D'` lying over
`f^{-1}(closure {x})`, and applies Stacks 02RZ. At a fixed point of `D'` both coefficient sums
over the points of `X` have finite support, so they may be subtracted term by term. -/
theorem flatPullback_gysinRule_rationallyEquivalent
    (hcomp : GysinRationallyCompatibleWithFlatPullback C p f r k L s chern chern' g hg hbase)
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    RationallyEquivalent C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ))
      ((gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α))
      (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
        ((gysinRule C p k L s chern).extendCycleGroup α)) := by
  have hdim : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      relativeDimension C.dimensionFunction p (i : X) = k + 1 := fun i ↦
    (mem_cyclesOfDimension_iff_forall_point C p (k + 1) α.1).1 α.2 i i.2
  choose a ha hval using fun i : ↥(Function.support (α.1 : X → ℤ)) ↦ hcomp (i : X) (hdim i)
  refine rationallyEquivalentToZero_finsum C
    ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ))
    (fun i : ↥(Function.support (α.1 : X → ℤ)) ↦ (α.1 (i : X)) • a i)
    (fun i : ↥(Function.support (α.1 : X → ℤ)) ↦
      (pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {(i : X)})) ?_
    (fun i ↦ isRationallyEquivalentToZeroWithin_zsmul C _ _ (ha i) _) ?_
  · exact ((locallyFinite_closure_support α.1.locallyFiniteSupport).preimage_continuous
      f.continuous).preimage_continuous (pullbackZeroScheme f L s).subschemeι.continuous
  · intro y'
    set β := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α with hβ
    set R' := gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' with hR'
    set R := gysinRule C p k L s chern with hR
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
        (R.extendCycleGroup α)).1 y' =
        ∑ᶠ x : X, α.1 x *
          (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
            (gysinComponentCycleAt C p k L s chern x)).1 y' := by
      rw [flatPullback_apply,
        show (R.extendCycleGroup α).1 (g.base y') =
          ∑ᶠ x : X, α.1 x * (gysinComponentCycleAt C p k L s chern x).1 (g.base y') from rfl,
        finsum_mul]
      exact finsum_congr fun x ↦ by rw [flatPullback_apply]; ring
    -- the coefficient at a point of the fibre over `x`
    have hGval : ∀ (x : X) (x' : X'), f.base x' = x → G x' = α.1 x *
        (flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y') := by
      intro x x' hx'
      have h1 : β.1 x' = α.1 x * flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' := by
        rw [hβ, flatPullback_apply, hx']
      simp only [hG]
      rw [h1, mul_assoc]
    -- both coefficient functions on `X` have finite support at `y'`, so they may be subtracted
    have hufin : Function.HasFiniteSupport
        (fun x : X ↦ ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') := by
      refine (hGfin.image f.base).subset fun x hx ↦ ?_
      by_contra hcon
      exact hx (finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
        by_contra hG0
        exact hcon ⟨x', hG0, hx'⟩)
    have hvfin : Function.HasFiniteSupport
        (fun x : X ↦ α.1 x *
          (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
            (gysinComponentCycleAt C p k L s chern x)).1 y') := by
      refine (finite_support_inter_generalizations α.1.locallyFiniteSupport
        (isCompact_singleton (x := (Stacks.Divisors.zeroScheme X L s).subschemeι.base
          (g.base y')))).subset ?_
      intro x hx
      have hx0 : α.1 x * (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
          (gysinComponentCycleAt C p k L s chern x)).1 y' ≠ 0 := hx
      rw [flatPullback_apply] at hx0
      replace hx0 : α.1 x *
        ((gysinComponentCycleAt C p k L s chern x).1 (g.base y') *
          flatPullbackWeight C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) g
            (k + (r : ℤ)) y') ≠ 0 := hx0
      exact ⟨⟨_, rfl, R.toComponentRule.mem_closure_of_apply_ne_zero x (g.base y')
        (left_ne_zero_of_mul (right_ne_zero_of_mul hx0))⟩, left_ne_zero_of_mul hx0⟩
    have hdiff : (R'.extendCycleGroup (hcast ▸ β) -
          flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
            (R.extendCycleGroup α)).1 y' =
        (∑ᶠ x : X, ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') -
          ∑ᶠ x : X, α.1 x *
            (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
              ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
              (gysinComponentCycleAt C p k L s chern x)).1 y' := by
      rw [← hLHS, ← hRHS]; rfl
    rw [hdiff, ← finsum_sub_distrib hufin hvfin, ← finsum_mem_univ,
      finsum_mem_inter_support_eq' _ Set.univ (Function.support (α.1 : X → ℤ)) ?_,
      ← finsum_set_coe_eq_finsum_mem (Function.support (α.1 : X → ℤ))]
    · refine finsum_congr fun i ↦ ?_
      have h1 : ∑ᶠ x' ∈ f.base ⁻¹' {(i : X)}, G x' =
          α.1 (i : X) * ∑ᶠ x' ∈ f.base ⁻¹' {(i : X)},
            flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
              (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ))
                ((Scheme.Modules.pullback f).obj L)
                (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x').1 y' := by
        rw [mul_finsum_mem]
        exact finsum_mem_congr rfl fun x' hx' ↦ hGval (i : X) x' hx'
      rw [h1, ← mul_sub, hval i y']
      simp only [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul,
        Pi.smul_apply, smul_eq_mul]
    · intro x hx
      refine ⟨fun _ ↦ ?_, fun _ ↦ Set.mem_univ x⟩
      by_contra hcon
      replace hcon : α.1 x = 0 := by
        simpa only [Function.mem_support, not_not] using hcon
      refine hx ?_
      show (∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') -
        α.1 x * (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hbase r hg k
          (gysinComponentCycleAt C p k L s chern x)).1 y' = 0
      rw [hcon, zero_mul, sub_zero]
      exact finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
        rw [hGval x x' hx', hcon, zero_mul]

/-! ### The Gysin component cycle of a contained component, pushed into the ambient scheme -/

/-- A rule on integral components vanishes at a point whose relative dimension is not `k + 1`:
the integral component through such a point does not have delta-dimension `k + 1`, so the
totalized rule takes the value zero there. -/
private theorem totalize_integralComponentAt_eq_zero_of_ne {C : ChowSituation.{u}}
    {Y Z : Scheme.{u}} {q : Y ⟶ C.S} [LocallyOfFiniteType q] {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {m : Z ⟶ Y} {j : ℤ} (R : IntegralComponentRule C q sZ m j) {y : Y}
    (hdim : relativeDimension C.dimensionFunction q y ≠ j + 1) :
    R.totalize (integralComponentAt y) = 0 := by
  classical
  have hcond : ¬ (IsIntegral (integralComponentAt y).subscheme ∧
      schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ q) = ((j + 1 : ℤ) : EInt)) := by
    rintro ⟨-, h2⟩
    rw [schemeDeltaDimension_integralComponentAt C q y] at h2
    exact hdim (WithBotTop.coe_injective h2)
  rw [IntegralComponentRule.totalize, dite_eq_right hcond]

/-- Pushing a cycle forward along `u` and then `v` is pushing it forward along any `w` equal to
`u ≫ v`. -/
private theorem properPushforward_properPushforward_of_comp_eq (C : ChowSituation.{u})
    {A B Z : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S}
    [LocallyOfFiniteType sB] {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (u : A ⟶ B) [IsProper u]
    (v : B ⟶ Z) [IsProper v] (w : A ⟶ Z) [IsProper w] (huvw : u ≫ v = w) (hu : u ≫ sB = sA)
    (hv : v ≫ sZ = sB) (k : ℤ) (c : CycleGroup C sA k) :
    properPushforward C sB sZ v hv k (properPushforward C sA sB u hu k c) =
      properPushforward C sA sZ w (by rw [← huvw, Category.assoc, hv, hu]) k c := by
  rw [properPushforward_properPushforward]
  exact congrFun (properPushforward_congr C _ _ _ _ huvw _ _ k) c

/-- The points of the inclusion `Z(I) ⟶ Z(D)` for `D ≤ I` lie over any set containing the
support of `I`. -/
private theorem range_inclusion_subset_preimage {Y : Scheme.{u}} {D I : Y.IdealSheafData}
    (h : D ≤ I) {T : Set Y} (hT : (I.support : Set Y) ⊆ T) :
    Set.range (Scheme.IdealSheafData.inclusion h).base ⊆ D.subschemeι.base ⁻¹' T := by
  rintro _ ⟨w, rfl⟩
  have himg : D.subschemeι.base ((Scheme.IdealSheafData.inclusion h).base w) =
      I.subschemeι.base w :=
    congrArg (fun m : I.subscheme ⟶ Y ↦ m.base w) (Scheme.IdealSheafData.inclusion_subschemeι h)
  refine hT ?_
  rw [himg, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨w, rfl⟩

section Contained

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (j : ℤ)
  (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
  (t : Γ(M, ⊤))

/-- **The Gysin component cycle of a contained component is a first Chern class component
cycle.** At a point `y` whose integral component contains the zero scheme `D = Z(t)`, the Gysin
component cycle of Stacks 02T8, pushed forward along the closed immersion of `D`, is the first
Chern class component cycle of Stacks 02SO for the rule
`Stacks.Chow.gysinOutComponentCycleRule` — the representative of `c₁(M|_W) ∩ [W]` that the
contained-component rule pushes into `D`. -/
private theorem properPushforward_gysinComponentCycleAt_eq_firstChernComponentCycleAt (y : Y)
    (hy : Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt y) :
    properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl j
        (gysinComponentCycleAt C q j M t (firstChernComponentClass C q j M) y) =
      firstChernComponentCycleAt C q j (gysinOutComponentCycleRule C q j M) y := by
  by_cases hdim : relativeDimension C.dimensionFunction q y = j + 1
  · have hW : IsIntegral (integralComponentAt y).subscheme := isIntegral_integralComponentAt y
    have hDim : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ q)
        = ((j + 1 : ℤ) : EInt) := schemeDeltaDimension_integralComponentAt_of_eq C q hdim
    have hincl : Scheme.IdealSheafData.inclusion hy ≫
        ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) =
        (integralComponentAt y).subschemeι ≫ q := by
      rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    rw [gysinComponentCycleAt_eq C q j M t (firstChernComponentClass C q j M) hdim,
      gysinComponentCycle_of_le C q j M t (firstChernComponentClass C q j M)
        (integralComponentAt y) hW hDim hy,
      firstChernComponentCycleAt_eq C q j (gysinOutComponentCycleRule C q j M) hdim]
    exact properPushforward_properPushforward_of_comp_eq C (Scheme.IdealSheafData.inclusion hy)
      (Stacks.Divisors.zeroScheme Y M t).subschemeι (integralComponentAt y).subschemeι
      (Scheme.IdealSheafData.inclusion_subschemeι hy) hincl rfl j _
  · have h1 : gysinComponentCycleAt C q j M t (firstChernComponentClass C q j M) y = 0 :=
      Subtype.ext (totalize_integralComponentAt_eq_zero_of_ne
        (gysinRule C q j M t (firstChernComponentClass C q j M)) hdim)
    have h2 : firstChernComponentCycleAt C q j (gysinOutComponentCycleRule C q j M) y = 0 :=
      Subtype.ext (totalize_integralComponentAt_eq_zero_of_ne
        (firstChernCapRule C q j (gysinOutComponentCycleRule C q j M)) hdim)
    rw [h1, h2, properPushforward_zero]

end Contained

/-! ### The fibre of a flat morphism, reindexed by the components of the inverse image -/

/-- The closures in `X'` of the generic points of the irreducible components of
`f^{-1}(closure {x})` form a locally finite family: each is contained in the image of that
component under the closed immersion of the inverse image, and those images form a locally finite
family by Stacks 0BE1. -/
private theorem locallyFinite_closure_genericPoint_comap (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (q : X' ⟶ C.S) [LocallyOfFiniteType q] (f : X' ⟶ X) (x : X) :
    LocallyFinite fun V : irreducibleComponents ((integralComponentAt x).comap f).subscheme ↦
      closure {((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint} := by
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian q
  refine (AlgebraicGeometry.locallyFinite_irreducibleComponents_image
    ((integralComponentAt x).comap f).subschemeι).subset fun V ↦ ?_
  have hVclosed : IsClosed (V : Set ((integralComponentAt x).comap f).subscheme) :=
    isClosed_of_mem_irreducibleComponents _ V.2
  have hgen : closure ({V.2.1.genericPoint} :
      Set ((integralComponentAt x).comap f).subscheme) =
      (V : Set ((integralComponentAt x).comap f).subscheme) :=
    V.2.1.isGenericPoint_genericPoint hVclosed
  refine closure_minimal (Set.singleton_subset_iff.mpr ⟨V.2.1.genericPoint, ?_, rfl⟩)
    (((integralComponentAt x).comap f).subschemeι.isClosedEmbedding.isClosedMap _ hVclosed)
  exact hgen.subset (subset_closure rfl)

/-! ### Stacks 0B71 on integral components at the Gysin map of an invertible module -/

section Invertible

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 02RG across the square of Remark 0B6Y, on cycles.** The flat pullback along `f` of
the pushforward into `X` of a cycle on `D = Z(s)` is the pushforward into `X'` of its flat
pullback along the comparison morphism `g : D' ⟶ D`.

This is the closed-immersion case of Stacks 02RG at the closed subscheme `D ⊆ X`, transported
along the identification `D' = f^{-1}(D)` of `Stacks.Divisors.zeroScheme_pullback` by the
isomorphism case of the same tag. -/
private theorem flatPullback_properPushforward_zeroSchemePullbackHom
    (β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k) :
    flatPullback C (f ≫ p) p f rfl r hf k
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k β) =
      properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (f ≫ p)
        (pullbackZeroScheme f L s).subschemeι rfl (k + (r : ℤ))
        (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
          (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
          (relativeDimension_zeroSchemePullbackHom f L s r hf) k β) := by
  have hker : (pullbackZeroScheme f L s).subschemeι.ker =
      ((Stacks.Divisors.zeroScheme X L s).comap f).subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      show pullbackZeroScheme f L s = (Stacks.Divisors.zeroScheme X L s).comap f from
        Stacks.Divisors.zeroScheme_pullback f L s]
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq (pullbackZeroScheme f L s).subschemeι
    ((Stacks.Divisors.zeroScheme X L s).comap f).subschemeι hker
  have hLFT : LocallyOfFiniteType (comapRestrict (Stacks.Divisors.zeroScheme X L s) f) :=
    locallyOfFiniteType_comapRestrict _ f
  have hFlat : Flat (comapRestrict (Stacks.Divisors.zeroScheme X L s) f) :=
    flat_comapRestrict _ f
  have hu₁ : e.hom ≫ (((Stacks.Divisors.zeroScheme X L s).comap f).subschemeι ≫ (f ≫ p)) =
      (pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p) := by
    rw [← Category.assoc, he]
  have hsq : zeroSchemePullbackHom f L s ≫ 𝟙 (Stacks.Divisors.zeroScheme X L s).subscheme =
      e.hom ≫ comapRestrict (Stacks.Divisors.zeroScheme X L s) f := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme X L s).subschemeι).1 ?_
    rw [Category.assoc, Category.id_comp, zeroSchemePullbackHom_subschemeι, Category.assoc,
      comapRestrict_subschemeι, ← Category.assoc, he]
  have hiso := flatPullback_properPushforward_of_isIso C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (((Stacks.Divisors.zeroScheme X L s).comap f).subschemeι ≫ (f ≫ p))
    (𝟙 _) (Category.id_comp _) e.hom hu₁ (zeroSchemePullbackHom f L s)
    (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl)
    (comapRestrict (Stacks.Divisors.zeroScheme X L s) f)
    (comapRestrict_comp_base C (f ≫ p) p f rfl (Stacks.Divisors.zeroScheme X L s)) hsq r
    (relativeDimension_zeroSchemePullbackHom f L s r hf)
    (relativeDimension_comapRestrict (Stacks.Divisors.zeroScheme X L s) f hf) k β
  rw [properPushforward_id] at hiso
  rw [flatPullback_properPushforward_comap C (f ≫ p) p f rfl r hf k
      (Stacks.Divisors.zeroScheme X L s) β, hiso]
  exact properPushforward_properPushforward_of_comp_eq C e.hom
    ((Stacks.Divisors.zeroScheme X L s).comap f).subschemeι
    (pullbackZeroScheme f L s).subschemeι he hu₁ rfl _ _

/-- For an integral component `W` of delta-dimension `k + 1` meeting the zero scheme `D = Z(s)`
properly, every point of `W ∩ D` has relative dimension at most `k`: the generic point of `W` is
not in `D`, since `W` is reduced and does not lie inside `D`, and the relative dimension drops
strictly at every other point of `W`. -/
private theorem relativeDimension_le_of_mem_support_of_not_le {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (hle : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) (y : X)
    (hyW : y ∈ ((integralComponentAt x).support : Set X))
    (hyD : y ∈ ((Stacks.Divisors.zeroScheme X L s).support : Set X)) :
    relativeDimension C.dimensionFunction p y ≤ k := by
  rw [coe_support_integralComponentAt] at hyW
  by_cases hyx : y = x
  · refine absurd ?_ hle
    obtain ⟨z, hz⟩ : ∃ z : (Stacks.Divisors.zeroScheme X L s).subscheme,
        (Stacks.Divisors.zeroScheme X L s).subschemeι.base z = y := by
      rw [← Scheme.IdealSheafData.range_subschemeι] at hyD
      exact hyD
    rw [← hyx, ← hz]
    exact zeroScheme_le_integralComponentAt_subschemeι_base L s z
  · have hlt := relativeDimension_lt_of_specializes C p
      (specializes_iff_mem_closure.mpr hyW) (fun h ↦ hyx h.symm)
    rw [hx] at hlt
    omega

/-- The scheme-theoretic intersection of an integral component of delta-dimension `k + 1` with a
zero scheme it is not contained in has delta-dimension at most `k`. -/
private theorem schemeDeltaDimension_comap_zeroScheme_le {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (hle : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) :
    schemeDeltaDimension C
        (((integralComponentAt x).comap
            (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) ≤ (k : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) _ fun w ↦ ?_
  rw [relativeDimension_comp_closedImmersion]
  refine relativeDimension_le_of_mem_support_of_not_le C p k L s hx hle _ ?_ ?_
  · have h : ((integralComponentAt x).comap
        (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι.base w ∈
        Set.range ((integralComponentAt x).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι.base := ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap] at h
    exact h
  · have h : (Stacks.Divisors.zeroScheme X L s).subschemeι.base
        (((integralComponentAt x).comap
          (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι.base w) ∈
        Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base := ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at h
    exact h

/-- **The uncontained case of Stacks 0B71 on an integral component.** When the integral component
`W = closure {x}` of delta-dimension `k + 1` is not contained in the zero scheme `D = Z(s)`, the
sum over the fibre `f^{-1}(x)` of the Gysin component cycles on `X'` is the flat pullback along
`g` of the Gysin component cycle of `x`, already as cycles.

Both sides are fundamental cycles of scheme-theoretic intersections: the left side by Stacks 02RB
and Stacks 02TB (1) on `X'`, whose two side conditions hold because `f^{-1}(W)` meets
`D' = Z(f^*s)` in the flat pullback of the effective Cartier divisor `W ∩ D`; the right side by
Stacks 02RB along `g` and the cartesian square of Remark 0B6Y. -/
private theorem gysinComponentDifference_eq_zero_of_not_le
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (hle : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x)
    (y' : (pullbackZeroScheme f L s).subscheme) :
    (∑ᶠ x' ∈ f.base ⁻¹' {x},
        flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s)
            (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1 y') =
      (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) x)).1 y' := by
  have hWint : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hWdim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p)
      = ((k + 1 : ℤ) : EInt) := schemeDeltaDimension_integralComponentAt_of_eq C p hx
  have hWle : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p)
      ≤ ((k + 1 : ℤ) : EInt) := le_of_eq hWdim
  -- the intersection of `W` with `D` is an effective Cartier divisor on `W`
  have hDW : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L s).comap (integralComponentAt x).subschemeι) :=
    Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral L s
      (integralComponentAt x) hWint hle
  -- hence so is the intersection of `f^{-1}(W)` with `D'`, by flat pullback
  have : Flat (comapRestrict (integralComponentAt x) f) :=
    flat_comapRestrict (integralComponentAt x) f
  have hDW' : Stacks.Divisors.IsEffectiveCartierDivisor
      ((pullbackZeroScheme f L s).comap
        ((integralComponentAt x).comap f).subschemeι) := by
    have h : Stacks.Divisors.IsEffectiveCartierDivisor
        (((Stacks.Divisors.zeroScheme X L s).comap
          (integralComponentAt x).subschemeι).comap
            (comapRestrict (integralComponentAt x) f)) :=
      Stacks.Divisors.isPullbackDefined_of_flat (comapRestrict (integralComponentAt x) f) _ hDW
    rw [← Scheme.IdealSheafData.comap_comp, comapRestrict_subschemeι,
      Scheme.IdealSheafData.comap_comp] at h
    rw [show pullbackZeroScheme f L s = (Stacks.Divisors.zeroScheme X L s).comap f from
      Stacks.Divisors.zeroScheme_pullback f L s]
    exact h
  -- the delta-dimension of `f^{-1}(W)`, by Stacks 02RE (1)
  have hZ' : schemeDeltaDimension C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) ≤
        ((k + (r : ℤ) + 1 : ℤ) : EInt) := by
    have h := schemeDeltaDimension_comap_le_of_relativeDimension C (f ≫ p) p f rfl r hf
      (integralComponentAt x) (k + 1) hWle
    rw [show (k + 1 + (r : ℤ) : ℤ) = (k + (r : ℤ) + 1 : ℤ) from by ring] at h
    exact h
  -- Stacks 02TB (1) on `X'`
  have hL := gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme C (f ≫ p) (k + (r : ℤ))
    ((Scheme.Modules.pullback f).obj L)
    (Stacks.Divisors.sectionsOfTop ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s)) ((integralComponentAt x).comap f)
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hZ')
    (by simpa only [Stacks.Divisors.sectionsOfTop_eval_top] using hDW')
  rw [Stacks.Divisors.sectionsOfTop_eval_top ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s)] at hL
  rw [← extendCycleGroup_flatPullback_gysin_apply C p f r hf k L s
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
      hcast x hx y',
    flatPullback_cycleAssociatedToClosedSubscheme_comap f C p r hf k (integralComponentAt x) hWle,
    hL, gysinComponentCycleAt_eq C p k L s (firstChernComponentClass C p k L) hx,
    gysinComponentCycle_of_not_le C p k L s (firstChernComponentClass C p k L)
      (integralComponentAt x) hWint hWdim hle,
    flatPullback_zeroSchemePullbackHom_cycleAssociatedToClosedSubscheme f L s C p r hf k
      ((integralComponentAt x).comap (Stacks.Divisors.zeroScheme X L s).subschemeι)
      (schemeDeltaDimension_comap_zeroScheme_le C p k L s hx hle),
    comap_zeroSchemePullbackHom f L s (integralComponentAt x)]

/-! ### The contained case of Stacks 0B71 on an integral component -/

omit [Flat f] in
/-- **The Gysin component cycle at a point over a contained component, read in `X'`.** When the
integral component `W = closure {x}` lies inside the zero scheme `D = Z(s)` and `x'` lies over
`x`, the integral component of `x'` lies inside `D' = Z(f^*s)`, so the Gysin component cycle at
`x'` is the first Chern class component cycle of the out rule of `f^*L`, pushed into `X'`. -/
private theorem gysinComponentCycleAt_apply_eq_firstChernComponentCycleAt_apply
    {x : X} (hle : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) {x' : X'}
    (hx' : f.base x' = x) (y' : (pullbackZeroScheme f L s).subscheme) :
    (gysinComponentCycleAt C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)
        (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
          ((Scheme.Modules.pullback f).obj L)) x').1 y' =
      (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
        (gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
          ((Scheme.Modules.pullback f).obj L)) x').1
        ((pullbackZeroScheme f L s).subschemeι.base y') := by
  have hle' : pullbackZeroScheme f L s ≤ integralComponentAt x' := by
    refine (pullbackZeroScheme_le_integralComponentAt_iff f L s x').2 ?_
    rw [hx']
    exact hle
  rw [← properPushforward_gysinComponentCycleAt_eq_firstChernComponentCycleAt C (f ≫ p)
      (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) x' hle',
    properPushforward_apply_image_of_isClosedImmersion]

/-- **The flat pullback along `g` of the Gysin component cycle of a contained component, read in
`X'`.** Across the square of Remark 0B6Y the pullback along `g` of the Gysin component cycle of
`x` is the flat pullback along `f` of the first Chern class component cycle of the out rule of
`L` at `x`. -/
private theorem flatPullback_gysinComponentCycleAt_apply_of_le
    {x : X} (hle : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x)
    (y' : (pullbackZeroScheme f L s).subscheme) :
    (flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) x)).1 y' =
      (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (gysinOutComponentCycleRule C p k L) x)).1
        ((pullbackZeroScheme f L s).subschemeι.base y') := by
  rw [← properPushforward_gysinComponentCycleAt_eq_firstChernComponentCycleAt C p k L s x hle,
    flatPullback_properPushforward_zeroSchemePullbackHom C p f r hf k L s,
    properPushforward_apply_image_of_isClosedImmersion]

/-- **The contained case of Stacks 0B71 on an integral component.** When the integral component
`W = closure {x}` of delta-dimension `k + 1` lies inside the zero scheme `D = Z(s)`, the Gysin
cycle of the flat pullback of `[W]` and the flat pullback along `g` of the Gysin component cycle
of `x` differ by a cycle rationally equivalent to zero on the part of `D' = Z(f^*s)` lying over
`f^{-1}(W)`.

Pushing both cycles into `X'` along the closed immersion of `D'`,
`Stacks.Chow.properPushforward_gysinComponentCycleAt_eq_firstChernComponentCycleAt` turns their
difference into the left hand side of the component case of Stacks 02SS for the *out* rules
`Stacks.Chow.gysinOutComponentCycleRule`. Stacks 0EPJ, in the form
`Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible`, settles that case for
the divisor-cycle rules; the passage to the out rules costs a rational equivalence on `f^{-1}(W)`
on the `X`-side — Stacks 02S1 along the component restriction `f^{-1}(W) ⟶ W` applied to
`Stacks.Chow.rationallyEquivalent_gysinOutComponentCycleRule` — and, on the `X'`-side, one
application of Stacks 02RZ over the irreducible components of `f^{-1}(W)`. Because `W ⊆ D`, the
inverse image `f^{-1}(W)` and each of those components is a closed subscheme of `D'`, which is
what keeps every witness inside the required carrier. -/
private theorem gysinComponentDifference_rationallyEquivalentToZeroWithin_of_le
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (hle : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) :
    IsRationallyEquivalentToZeroWithin C
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ))
      ((gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
              (AlgebraicGeometry.pullbackGlobalSections f L s)
              (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
                ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
            (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
              (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1))) -
          flatPullback C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
            (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
            (relativeDimension_zeroSchemePullbackHom f L s r hf) k
            (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) x))
      ((pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {x})) := by
  classical
  have hWint := isIntegral_integralComponentAt x
  have hWdim := schemeDeltaDimension_integralComponentAt_of_eq C p hx
  have hgt := locallyOfFiniteType_comapRestrict (integralComponentAt x) f
  have hgf := flat_comapRestrict (integralComponentAt x) f
  have hgd := relativeDimension_comapRestrict (integralComponentAt x) f hf
  have hgb := comapRestrict_comp_base C (f ≫ p) p f rfl (integralComponentAt x)
  -- `W ⊆ D` gives `f^{-1}(W) ⊆ D'`, so `f^{-1}(W)` is a closed subscheme of `D'`
  have hD'W' : pullbackZeroScheme f L s ≤ (integralComponentAt x).comap f := by
    rw [show pullbackZeroScheme f L s = (Stacks.Divisors.zeroScheme X L s).comap f from
      Stacks.Divisors.zeroScheme_pullback f L s]
    exact Scheme.IdealSheafData.comap_mono f hle
  have hinclW' : Scheme.IdealSheafData.inclusion hD'W' ≫
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) =
      ((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  -- a cycle on a closed subscheme of `D'`, pushed into `X'`, is read off on `D'`
  have hpushD' : ∀ (I : X'.IdealSheafData) (hI : pullbackZeroScheme f L s ≤ I)
      (hIc : Scheme.IdealSheafData.inclusion hI ≫
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) = I.subschemeι ≫ (f ≫ p))
      (γ : CycleGroup C (I.subschemeι ≫ (f ≫ p)) (k + (r : ℤ)))
      (y' : (pullbackZeroScheme f L s).subscheme),
      (properPushforward C (I.subschemeι ≫ (f ≫ p)) (f ≫ p) I.subschemeι rfl (k + (r : ℤ))
          γ).1 ((pullbackZeroScheme f L s).subschemeι.base y') =
        (properPushforward C (I.subschemeι ≫ (f ≫ p))
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          (Scheme.IdealSheafData.inclusion hI) hIc (k + (r : ℤ)) γ).1 y' := by
    intro I hI hIc γ y'
    have hstep : properPushforward C (I.subschemeι ≫ (f ≫ p)) (f ≫ p) I.subschemeι rfl
          (k + (r : ℤ)) γ =
        properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (f ≫ p)
          (pullbackZeroScheme f L s).subschemeι rfl (k + (r : ℤ))
          (properPushforward C (I.subschemeι ≫ (f ≫ p))
            ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
            (Scheme.IdealSheafData.inclusion hI) hIc (k + (r : ℤ)) γ) := by
      exact (properPushforward_properPushforward_of_comp_eq C (Scheme.IdealSheafData.inclusion hI)
        (pullbackZeroScheme f L s).subschemeι I.subschemeι
        (Scheme.IdealSheafData.inclusion_subschemeι hI) hIc rfl _ γ).symm
    rw [hstep, properPushforward_apply_image_of_isClosedImmersion]
  -- Stacks 0EPJ at `x`, for the divisor-cycle rules
  obtain ⟨a₀, ha₀, hval₀⟩ :=
    firstChernCapRationallyCompatibleWithFlatPullback_invertible C p f r hf k L x hx
  -- the `X`-side discrepancy between the out rule and the divisor-cycle rule
  obtain ⟨a₂, ha₂def⟩ : ∃ a₂ : CycleGroup C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)), a₂ =
      flatPullback C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
        ((integralComponentAt x).subschemeι ≫ p) (comapRestrict (integralComponentAt x) f) hgb r
        hgd k
        (gysinOutComponentCycleRule C p k L (integralComponentAt x) hWint hWdim -
          firstChernComponentCycleRule C p k L (integralComponentAt x) hWint hWdim) := ⟨_, rfl⟩
  have ha₂ : IsRationallyEquivalentToZero C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) a₂ := by
    rw [ha₂def]
    exact flatPullbackFactorsThroughRationalEquivalence_general C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
      ((integralComponentAt x).subschemeι ≫ p) (comapRestrict (integralComponentAt x) f) hgb r
      hgd k _
      (rationallyEquivalent_gysinOutComponentCycleRule C p k L (integralComponentAt x) hWint
        hWdim)
  have hXside : flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (gysinOutComponentCycleRule C p k L) x) -
      flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) x) =
      properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) a₂ := by
    rw [← map_sub, firstChernComponentCycleAt_eq C p k _ hx,
      firstChernComponentCycleAt_eq C p k _ hx,
      show firstChernComponentCycle C p k (gysinOutComponentCycleRule C p k L)
              (integralComponentAt x) hWint hWdim -
            firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
              (integralComponentAt x) hWint hWdim =
          properPushforward C ((integralComponentAt x).subschemeι ≫ p) p
            (integralComponentAt x).subschemeι rfl k
            (gysinOutComponentCycleRule C p k L (integralComponentAt x) hWint hWdim -
              firstChernComponentCycleRule C p k L (integralComponentAt x) hWint hWdim) from
        (properPushforward_sub C ((integralComponentAt x).subschemeι ≫ p) p
          (integralComponentAt x).subschemeι rfl k _ _).symm,
      flatPullback_properPushforward_comap C (f ≫ p) p f rfl r hf k (integralComponentAt x),
      ha₂def]
  -- the two witnesses on `f^{-1}(W)`, pushed into `D'`
  obtain ⟨b, hbdef⟩ : ∃ b : CycleGroup C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)), b =
      properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        (Scheme.IdealSheafData.inclusion hD'W') hinclW' (k + (r : ℤ)) (a₀ - a₂) := ⟨_, rfl⟩
  have hbwithin : IsRationallyEquivalentToZeroWithin C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) b
      ((pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {x})) := by
    rw [hbdef]
    refine (properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
      (Scheme.IdealSheafData.inclusion hD'W') hinclW' (k + (r : ℤ))
      ((rationalEquivalences C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
        (k + (r : ℤ))).sub_mem ha₀ ha₂)).mono ?_
    exact range_inclusion_subset_preimage hD'W' (coe_support_integralComponentPreimage f x).subset
  -- the data attached to an irreducible component of `f^{-1}(W)`
  have hgpbase : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      f.base (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) = x := by
    intro V
    rw [base_genericPoint_irreducibleComponents_comap f (integralComponentAt x) V]
    exact subschemeι_genericPoint_integralComponentAt x
  have hgpdim : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      relativeDimension C.dimensionFunction (f ≫ p)
          (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)
        = k + (r : ℤ) + 1 := by
    intro V
    have h := relativeDimension_genericPoint_irreducibleComponent C
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
      ((integralComponentAt x).subschemeι ≫ p) (comapRestrict (integralComponentAt x) f) hgb r
      hgd hWdim V
    rw [relativeDimension_comp_closedImmersion] at h
    rw [h]
    ring
  have hgpint : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      IsIntegral (integralComponentAt
        (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).subscheme :=
    fun V ↦ isIntegral_integralComponentAt _
  have hgpsdim : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      schemeDeltaDimension C ((integralComponentAt
            (((integralComponentAt x).comap f).subschemeι.base
              V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
        = ((k + (r : ℤ) + 1 : ℤ) : EInt) := fun V ↦
    schemeDeltaDimension_integralComponentAt_of_eq C (f ≫ p) (hgpdim V)
  have hgple : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      pullbackZeroScheme f L s ≤ integralComponentAt
        (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) := by
    intro V
    refine (pullbackZeroScheme_le_integralComponentAt_iff f L s _).2 ?_
    rw [hgpbase V]
    exact hle
  have hgpincl : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      Scheme.IdealSheafData.inclusion (hgple V) ≫
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) =
      (integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
        V.2.1.genericPoint)).subschemeι ≫ (f ≫ p) := fun V ↦ by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  obtain ⟨ee, hee⟩ : ∃ ee : ∀ V : irreducibleComponents
        ((integralComponentAt x).comap f).subscheme,
        CycleGroup C ((integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)),
      ∀ V, ee V =
        gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
            (integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
              V.2.1.genericPoint)) (hgpint V) (hgpsdim V) -
          firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L)
            (integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
              V.2.1.genericPoint)) (hgpint V) (hgpsdim V) := ⟨_, fun _ ↦ rfl⟩
  have heerat : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      IsRationallyEquivalentToZero C
        ((integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) (ee V) := fun V ↦ by
    rw [hee V]
    exact rationallyEquivalent_gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
      ((Scheme.Modules.pullback f).obj L) _ (hgpint V) (hgpsdim V)
  obtain ⟨Dfam, hDfam⟩ : ∃ Dfam : irreducibleComponents
        ((integralComponentAt x).comap f).subscheme →
        CycleGroup C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)),
      ∀ V, Dfam V = flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ))
          (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) •
        properPushforward C ((integralComponentAt
            (((integralComponentAt x).comap f).subschemeι.base
              V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          (Scheme.IdealSheafData.inclusion (hgple V)) (hgpincl V) (k + (r : ℤ)) (ee V) :=
    ⟨_, fun _ ↦ rfl⟩
  have hDfamwithin : ∀ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
      IsRationallyEquivalentToZeroWithin C
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) (Dfam V)
        ((pullbackZeroScheme f L s).subschemeι.base ⁻¹'
          closure {((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint}) := by
    intro V
    rw [hDfam V]
    refine isRationallyEquivalentToZeroWithin_zsmul C _ _
      ((properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
        ((integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        (Scheme.IdealSheafData.inclusion (hgple V)) (hgpincl V) (k + (r : ℤ))
        (heerat V)).mono ?_) _
    exact range_inclusion_subset_preimage (hgple V) (coe_support_integralComponentAt _).subset
  have hcl := locallyFinite_closure_genericPoint_comap C (f ≫ p) f x
  have hEloc : LocallyFinite fun V : irreducibleComponents
      ((integralComponentAt x).comap f).subscheme ↦
      (pullbackZeroScheme f L s).subschemeι.base ⁻¹'
        closure {((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint} :=
    hcl.preimage_continuous (pullbackZeroScheme f L s).subschemeι.continuous
  have hUnion : (⋃ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
        (pullbackZeroScheme f L s).subschemeι.base ⁻¹'
          closure {((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint}) ⊆
      (pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {x}) := by
    refine Set.iUnion_subset fun V ↦ Set.preimage_mono ?_
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (isClosed_closure.preimage
      f.continuous)
    rw [Set.mem_preimage, hgpbase V]
    exact subset_closure rfl
  -- only the components through a fixed point of `X'` contribute
  have hfinsupp : ∀ (R : FirstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))) (z : X'),
      Function.HasFiniteSupport fun V : irreducibleComponents
          ((integralComponentAt x).comap f).subscheme ↦
        flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ))
            (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) R
            (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).1 z := by
    intro R z
    refine (hcl.point_finite z).subset fun V hV ↦ ?_
    by_contra hcon
    refine hV ?_
    have hz : z ∉ Set.range (integralComponentAt
        (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
      exact hcon
    have h0 : (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) R
        (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).1 z = 0 := by
      rw [firstChernComponentCycleAt_eq C (f ≫ p) (k + (r : ℤ)) R (hgpdim V)]
      exact properPushforward_apply_of_notMem_range C
        ((integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι ≫ (f ≫ p)) (f ≫ p)
        (integralComponentAt (((integralComponentAt x).comap f).subschemeι.base
          V.2.1.genericPoint)).subschemeι rfl (k + (r : ℤ)) _ hz
    show flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ))
        (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) *
      (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) R
        (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).1 z = 0
    rw [h0, mul_zero]
  -- Stacks 02RZ: the difference is `b` plus the locally finite sum of the component pieces
  have hgoal : ∀ α : CycleGroup C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        (k + (r : ℤ)),
      (∀ y' : (pullbackZeroScheme f L s).subscheme, (α - b).1 y' = ∑ᶠ V, (Dfam V).1 y') →
      IsRationallyEquivalentToZeroWithin C
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) α
        ((pullbackZeroScheme f L s).subschemeι.base ⁻¹' (f.base ⁻¹' closure {x})) := by
    intro α hα
    have hc := (rationallyEquivalentToZeroWithin_finsum C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) Dfam _ hEloc
      hDfamwithin hα).mono hUnion
    have hsum := isRationallyEquivalentToZeroWithin_add C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) hbwithin hc
    have heq : b + (α - b) = α := by abel
    rwa [heq] at hsum
  refine hgoal _ fun y' ↦ ?_
  -- the left hand side, read in `X'` through the out rule
  have hL : ((gysinRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
          (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)))).1 y'
      = ∑ᶠ x' ∈ f.base ⁻¹' {x}, flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1
            ((pullbackZeroScheme f L s).subschemeι.base y') := by
    rw [extendCycleGroup_flatPullback_gysin_apply C p f r hf k L s
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
      hcast x hx y']
    refine finsum_mem_congr rfl fun x' hx' ↦ ?_
    rw [gysinComponentCycleAt_apply_eq_firstChernComponentCycleAt_apply C p f r k L s hle
      (show f.base x' = x from hx') y']
  have hR := flatPullback_gysinComponentCycleAt_apply_of_le C p f r hf k L s hle y'
  have hbval : b.1 y' = (properPushforward C
        (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) (a₀ - a₂)).1
        ((pullbackZeroScheme f L s).subschemeι.base y') := by
    rw [hbdef, ← hpushD' ((integralComponentAt x).comap f) hD'W' hinclW' (a₀ - a₂) y']
  have hsplitpush : (properPushforward C
        (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) (a₀ - a₂)).1
        ((pullbackZeroScheme f L s).subschemeι.base y') =
      (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) a₀).1
        ((pullbackZeroScheme f L s).subschemeι.base y') -
      (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) a₂).1
        ((pullbackZeroScheme f L s).subschemeι.base y') := by
    rw [properPushforward_sub]
    rfl
  have hXval : (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (gysinOutComponentCycleRule C p k L) x)).1
        ((pullbackZeroScheme f L s).subschemeι.base y') -
      (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) x)).1
        ((pullbackZeroScheme f L s).subschemeι.base y') =
      (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) a₂).1
        ((pullbackZeroScheme f L s).subschemeι.base y') := by
    rw [← hXside]
    rfl
  -- the `X'`-side difference, reindexed over the components of `f^{-1}(W)`
  have hS : (∑ᶠ x' ∈ f.base ⁻¹' {x}, flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1
            ((pullbackZeroScheme f L s).subschemeι.base y')) -
        (∑ᶠ x' ∈ f.base ⁻¹' {x}, flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1
            ((pullbackZeroScheme f L s).subschemeι.base y')) =
      ∑ᶠ V, (Dfam V).1 y' := by
    rw [finsum_fibre_flatPullbackWeight_eq_components C (f ≫ p) f x (k + 1 + (r : ℤ))
        (fun x' ↦ (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
          (gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L)) x').1
          ((pullbackZeroScheme f L s).subschemeι.base y')),
      finsum_fibre_flatPullbackWeight_eq_components C (f ≫ p) f x (k + 1 + (r : ℤ))
        (fun x' ↦ (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L)) x').1
          ((pullbackZeroScheme f L s).subschemeι.base y')),
      ← finsum_sub_distrib (hfinsupp _ _) (hfinsupp _ _)]
    refine finsum_congr fun V ↦ ?_
    have hVdiff : (properPushforward C ((integralComponentAt
            (((integralComponentAt x).comap f).subschemeι.base
              V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          (Scheme.IdealSheafData.inclusion (hgple V)) (hgpincl V) (k + (r : ℤ)) (ee V)).1 y' =
        (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (gysinOutComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L))
            (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).1
            ((pullbackZeroScheme f L s).subschemeι.base y') -
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L))
            (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint)).1
            ((pullbackZeroScheme f L s).subschemeι.base y') := by
      rw [← hpushD' _ (hgple V) (hgpincl V) (ee V) y', hee V, properPushforward_sub,
        firstChernComponentCycleAt_eq C (f ≫ p) (k + (r : ℤ)) _ (hgpdim V),
        firstChernComponentCycleAt_eq C (f ≫ p) (k + (r : ℤ)) _ (hgpdim V)]
      rfl
    rw [hDfam V]
    have hcoe : ∀ (n : ℤ) (c : CycleGroup C
        ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ))),
        (n • c).1 y' = n * c.1 y' := by
      intro n c
      simp only [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul,
        Pi.smul_apply, smul_eq_mul]
    rw [hcoe, hVdiff, mul_sub]
  have hcoeff3 : ∀ α β γ : CycleGroup C
      ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)),
      (α - β - γ).1 y' = α.1 y' - β.1 y' - γ.1 y' := fun _ _ _ ↦ rfl
  rw [hcoeff3, hL, hR, hbval, hsplitpush, ← hS]
  linarith [hval₀ ((pullbackZeroScheme f L s).subschemeι.base y'), hXval]

/-! ### Stacks 0B71 on integral components for an invertible module, unconditionally -/

/-- **Stacks 0B71 on integral components, up to rational equivalence, for an invertible module.**
At the Gysin maps of `L` and of `f^*L` and across the canonical square of Remark 0B6Y, the
component case of Stacks 0B71 holds up to rational equivalence with **no** hypothesis.

The uncontained case is `Stacks.Chow.gysinComponentDifference_eq_zero_of_not_le`, where the two
cycles are literally equal; the contained case is
`Stacks.Chow.gysinComponentDifference_rationallyEquivalentToZeroWithin_of_le`, where they differ
by the rational equivalence that Stacks 0EPJ supplies. -/
theorem gysinRationallyCompatibleWithFlatPullback_invertible :
    GysinRationallyCompatibleWithFlatPullback C p f r k L s
      (firstChernComponentClass C p k L)
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
      (zeroSchemePullbackHom f L s) (relativeDimension_zeroSchemePullbackHom f L s r hf)
      (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) := by
  intro x hx
  have hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1 := by ring
  by_cases hle : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x
  · refine ⟨_, gysinComponentDifference_rationallyEquivalentToZeroWithin_of_le C p f r hf k L s
      hcast hx hle, fun y' ↦ ?_⟩
    rw [← extendCycleGroup_flatPullback_gysin_apply C p f r hf k L s
      (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
      hcast x hx y']
    rfl
  · refine ⟨0, isRationallyEquivalentToZeroWithin_zero C _ _ _, fun y' ↦ ?_⟩
    rw [gysinComponentDifference_eq_zero_of_not_le C p f r hf k L s hcast hx hle y', sub_self]
    rfl

/-- **Stacks 0B71 for an arbitrary cycle at the Gysin map of an invertible module, with no
hypothesis.** Gysin pullback through the zero scheme of a section of an invertible module
commutes with flat pullback:

  `(i')^* f^* α = g^* i^* α`  in  `CH_{k+r}(D')`,  for every `α ∈ Z_{k+1}(X)`.

This is `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback` with both of its remaining
hypotheses discharged: the vanishing of Stacks 02S1 along `g` is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and the identity on integral
components is replaced by its rational-equivalence form
`Stacks.Chow.gysinRationallyCompatibleWithFlatPullback_invertible`, which is proved here. Both
Gysin maps are `Stacks.Chow.gysinHomomorphismOfInvertible`, no component rule is a parameter, the
invertibility of `f^*L` is an instance, and `g` is the canonical comparison morphism of Remark
0B6Y. -/
@[stacks 0B71 "the Gysin map commutes with flat pullback, (i')^* f^* = g^* i^* on A_{k+r}(D'), \
with no hypothesis: the component identity is replaced by its rational-equivalence form, proved \
here, and the vanishing of 02S1 along g by the general theorem"]
theorem gysinHomomorphismOfInvertible_flatPullback_of_invertible (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOfInvertible C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (flatPullbackFactorsThroughRationalEquivalence_general C
          ((pullbackZeroScheme f L s).subschemeι ≫ (f ≫ p))
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
          (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl) r
          (relativeDimension_zeroSchemePullbackHom f L s r hf) k)
        (gysinHomomorphismOfInvertible C p k L s α) := by
  have h0 := flatPullback_gysinRule_rationallyEquivalent C p f r hf k L s
    (firstChernComponentClass C p k L)
    (firstChernComponentClass C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
    (zeroSchemePullbackHom f L s) (relativeDimension_zeroSchemePullbackHom f L s r hf)
    (zeroSchemePullbackHom_comp f L s C p (f ≫ p) rfl)
    (gysinRationallyCompatibleWithFlatPullback_invertible C p f r hf k L s)
    (show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) α
  exact QuotientAddGroup.eq_iff_sub_mem.2 h0

end Invertible

end Stacks.Chow

end
