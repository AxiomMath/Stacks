module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections

/-!
# Gysin pullback and proper pushforward

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be proper over `S`, let `L` be an invertible module on `X` and
let `s ∈ Γ(X, L)` be a global section with zero scheme `i : D = Z(s) ⟶ X`. Setting
`L' = f^*L`, `s' = f^*s` and `D' = Z(s')` gives the square of Stacks 0B6Y

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

and Stacks 02TA is the compatibility of the Gysin maps of `i` and `i'` with proper pushforward:

  `i^* f_* α' = g_* (i')^* α'`  in  `A_k(D)`,  for `α' ∈ Z_{k+1}(X')`.

## Main definitions

* `Stacks.Chow.pullbackZeroScheme` — the zero scheme `D' = Z(f^*s)` of the pulled-back section.
* `Stacks.Chow.gysinComponentCycleAt` — the Gysin component cycle of Stacks 02T8 attached to a
  *point* of `X` rather than to an integral closed subscheme, the two being the same datum.
* `Stacks.Chow.GysinCompatibleWithPushforward` — the compatibility of Stacks 02TA on integral
  components, which is where the source invokes Stacks 02ST.

## Main results

* `Stacks.Chow.properPushforward_gysinRule_extendCycleGroup` — Stacks 02TA at the level of
  **cycles**: granted the compatibility on integral components, the Gysin cycle of a pushforward
  is the pushforward along `g` of the Gysin cycle.
* `Stacks.Chow.gysinHomomorphism_properPushforward` — **Stacks 02TA**: the same identity read
  through proper pushforward on Chow groups.
* `Stacks.Chow.gysinCompatibleWithPushforward_of_components` — the compatibility hypothesis
  restated on integral closed subschemes rather than on points.

## Implementation notes

### The square is given, not constructed

Stacks 02TA reads "form the diagram as in Remark 0B6Y". Remark 0B6Y identifies `Z(f^*s)` with
`X' ×_X D` and so produces the morphism `g : D' ⟶ D`; that identification is Stacks 0B6Y and is
not in this repository. Accordingly `g`, its properness, and the commutativity of the square over
`S` are parameters here, exactly as in the statement of Stacks 0B71, which quantifies over the
morphism between zero schemes rather than choosing one. This is a generalization: the morphism
Remark 0B6Y produces satisfies the hypotheses, so the statement of Stacks 02TA follows from the
one below. No transport along an equality of zero schemes is needed, because the Gysin map on `X'`
is taken on `Z(f^*s)` itself rather than on `X' ×_X D`.

### The parameters threaded, and why

Three inputs of the source are absent from this repository and are carried as explicit parameters,
in the way established by `StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction`,
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow` and
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward`:

* the component rules `chern` and `chern'` of the contained-component case of the Gysin map on
  `X` and on `X'`, standing in for Stacks 02SO. In the source `chern` comes from `L` and `chern'`
  from `L'`; here they are independent parameters, linked only by the compatibility hypothesis
  below;
* the vanishing of Stacks 02S2 along `g`, carried by `Stacks.Chow.properChowPushforward`, needed
  to have the map `g_* : A_k(D') ⟶ A_k(D)` of Stacks 0GU8 at all;
* the compatibility on integral components, `Stacks.Chow.GysinCompatibleWithPushforward`.

The invertibility of `L' = f^*L`, needed to form the zero scheme `Z(f^*s)` and hence the Gysin
map on `X'`, is **not** among them: it is Stacks 0B8L, and Stacks 0B8L is in this repository, as
`Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry`, registered for schemes as the
instance `Stacks.Divisors.pullback_isInvertible` in
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic`. Importing that module makes the
invertibility of `f^*L` a consequence of the invertibility of `L`, so no statement below carries
it as a hypothesis.

### The compatibility hypothesis is the integral-component case, and is indispensable

`Stacks.Chow.GysinCompatibleWithPushforward` says that the identity of Stacks 02TA holds, at the
level of cycle coefficients, on the fundamental cycle of each integral component of `X'`. That is
the whole first part of the source's proof: for `α' = [W']` it treats the cases `W' ⊄ D'` by
Stacks 02ST applied to `div_{L'|_{W'}}(s'|_{W'})` and `W' ⊆ D'` by the second assertion of
Stacks 02ST applied to `c₁(L'|_{W'}) ∩ [W']`. Neither is available here: Stacks 02ST rests on
Stacks 02RT and on the first Chern class of Stacks 02SO.

It cannot be dropped. The Gysin map here is built from an arbitrary
`Stacks.Chow.FirstChernComponentClassRule` on `X` and an arbitrary one on `X'`, and its values on
components contained in the zero scheme are whatever those rules say; two unrelated rules have no
reason to be compatible along `f`. Taking `f = 𝟙 X`, `g = 𝟙 D`, `chern` arbitrary and `chern' = 0`
already makes the conclusion fail for any `W` contained in `D` with nonzero `chern W`.

The hypothesis is strictly weaker than the conclusion: it constrains the rules only on the
fundamental cycles of single integral components, and the theorem extends it to every cycle. That
extension is where the work is — a cycle is a *locally* finite sum of components, so it needs a
sum over `X` reindexed as a sum over the fibres of `f`, and a sum over `D` reindexed over the
fibres of `g`. Those are `Stacks.Chow.ComponentRule.extendCoeff_map_apply` and
`Stacks.Chow.ComponentRule.map_extendCycle_apply`, and they are where properness is used.

### Where Stacks 02TA is carried

The declarations below quantify over the two component rules `chern` and `chern'`, so they are
statements about arbitrary rules on integral components rather than about `L` and `s`. Stacks 02TA
is carried one step further on, in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible`, where both rules are
the first Chern class of an invertible module, the morphism `g` of Remark 0B6Y is constructed and
the Stacks 02S2 hypothesis along it is discharged, leaving the integral-component compatibility as
the one grant.

Stacks 0B79, that the degree-1 Gysin rule of a triple `(ℒ, s, i : D ⟶ X)` is a bivariant class,
is `Stacks.Chow.gysinBivariantClass` in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass`; its proper-pushforward axiom is read
off from the unconditional form of the identity proved below.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The Gysin component cycle at a point -/

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)

/-- The Gysin component cycle of Stacks 02T8 attached to a *point* of `X`: the cycle the Gysin
rule attaches to the integral closed subscheme `closure {x}`, extended by zero when that
subscheme does not have delta-dimension `k + 1`.

An integral closed subscheme is the reduced induced structure on the closure of its generic point
(`Stacks.Chow.integralComponentAt_genericPointOf`), so this is the same datum as
`Stacks.Chow.gysinComponentCycle`; the point-indexed form is the one the coefficientwise
extension of the rule is written in. -/
def gysinComponentCycleAt (x : X) :
    CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  ⟨(gysinRule C p k L s chern).totalize (integralComponentAt x),
    (gysinRule C p k L s chern).totalize_mem_cyclesOfDimension _⟩

/-- At the generic point of an integral closed subscheme of delta-dimension `k + 1`, the
point-indexed Gysin component cycle is the Gysin component cycle of that subscheme. -/
theorem gysinComponentCycleAt_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    gysinComponentCycleAt C p k L s chern (genericPointOf W hW) =
      gysinComponentCycle C p k L s chern W hW hDim :=
  Subtype.ext <| (congrArg (gysinRule C p k L s chern).totalize
    (integralComponentAt_genericPointOf W hW)).trans
      ((gysinRule C p k L s chern).totalize_eq W hW hDim)

/-! ### The zero scheme of a pulled-back section -/

/-- **Stacks 0B6Y.** The zero scheme `D' = Z(f^*s)` of the pullback of a global section of an
invertible module along `f : X' ⟶ X`. Stacks 0B6Y identifies it with `X' ×_X Z(s)`; that
identification is not needed below, where the morphism `D' ⟶ Z(s)` it provides is a parameter. -/
abbrev pullbackZeroScheme (f : X' ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : X'.IdealSheafData :=
  Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s)

/-! ### Stacks 02TA on integral components -/

section Proper

variable (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p')
  (chern' : FirstChernComponentClassRule C p' k)
  (g : (pullbackZeroScheme f L s).subscheme ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme)
  [IsProper g]
  (hg : g ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) =
    (pullbackZeroScheme f L s).subschemeι ≫ p')

/-- **Stacks 02TA on integral components.** The assertion that for every integral component of
`X'` of delta-dimension `k + 1` — equivalently, for every point `x'` of relative dimension
`k + 1` — the pushforward along `g` of the Gysin component cycle attached to it on `X'` is the
Gysin component cycle attached on `X` to its image, weighted by
`Stacks.Chow.pushforwardWeight`.

This is the first part of the proof of Stacks 02TA, which the source proves by Stacks 02ST in
both the contained and the uncontained case. It is carried as a hypothesis here; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward`. The
assertion is an equality of cycle *coefficients*, as the component formula of Stacks 02T8 is. -/
def GysinCompatibleWithPushforward : Prop :=
  ∀ x' : X', relativeDimension C.dimensionFunction p' x' = k + 1 →
    ∀ y : (Stacks.Divisors.zeroScheme X L s).subscheme,
      (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k
          (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x')).1 y =
        pushforwardWeight C p' p f x' * (gysinComponentCycleAt C p k L s chern (f.base x')).1 y

omit [IsProper f] in
/-- The compatibility of the Gysin component rules along `f`, restated on integral closed
subschemes of `X'` instead of on points: the two are the same datum, by
`Stacks.Chow.integralComponentAt_genericPointOf`. -/
theorem gysinCompatibleWithPushforward_of_components
    (h : ∀ (W : X'.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p') = ((k + 1 : ℤ) : EInt))
      (y : (Stacks.Divisors.zeroScheme X L s).subscheme),
      (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k
          (gysinComponentCycle C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s) chern' W hW hDim)).1 y =
        pushforwardWeight C p' p f (genericPointOf W hW) *
          (gysinComponentCycleAt C p k L s chern (f.base (genericPointOf W hW))).1 y) :
    GysinCompatibleWithPushforward C p k L s chern p' f chern' g hg := by
  intro x' hdim y
  have hW : IsIntegral (integralComponentAt x').subscheme := isIntegral_integralComponentAt x'
  have hDim : schemeDeltaDimension C ((integralComponentAt x').subschemeι ≫ p') =
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C p' x', hdim]
  have h' := h (integralComponentAt x') hW hDim y
  rwa [← gysinComponentCycleAt_genericPointOf C p' k ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern' _ hW hDim,
    genericPointOf_integralComponentAt x'] at h'

/-! ### Stacks 02TA -/

/-- **Stacks 02TA, at the level of cycles.** Granted the compatibility on integral components,
the Gysin cycle of a proper pushforward is the pushforward along `g` of the Gysin cycle.

This is sharper than the statement of the source, which is an equality of classes in `A_k(D)`.
Both sides are locally finite sums over the integral components of `α'`, and the proof matches
them term by term: `Stacks.Chow.ComponentRule.extendCoeff_map_apply` turns the left side into
`∑_{x'} α'(x') · w(x') · c(f x')` and `Stacks.Chow.ComponentRule.map_extendCycle_apply` turns the
right side into `∑_{x'} α'(x') · g_*(c'(x'))`, after which the hypothesis applies term by term.
Only the points carrying a nonzero coefficient of `α'` are compared, and those have relative
dimension `k + 1` because `α'` is a `(k+1)`-cycle. -/
theorem properPushforward_gysinRule_extendCycleGroup
    (hcomp : GysinCompatibleWithPushforward C p k L s chern p' f chern' g hg)
    (α : CycleGroup C p' (k + 1)) :
    (gysinRule C p k L s chern).extendCycleGroup (properPushforward C p' p f hf (k + 1) α) =
      properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k
        ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  -- the left hand side: extending the Gysin rule of `X` over a pushforward along `f`
  have hcpt {A B : Scheme.{u}} (h : A ⟶ B) [IsProper h] (y : B) : IsCompact (h.base ⁻¹' {y}) :=
    h.isProperMap.isCompact_preimage isCompact_singleton
  -- the left hand side: extending the Gysin rule of `X` over a pushforward along `f`
  have hLHS : ((gysinRule C p k L s chern).extendCycleGroup
      (properPushforward C p' p f hf (k + 1) α)).1 y =
      ∑ᶠ x' : X', α.1 x' * pushforwardWeight C p' p f x' *
        (gysinComponentCycleAt C p k L s chern (f.base x')).1 y :=
    (ComponentRule.extendCoeff_map_apply _ f.isSpectralMap f.isProperMap.isClosedMap _ _ y
      (hcpt f _)).trans (finsum_congr fun _ ↦ rfl)
  -- the right hand side: pushing the Gysin cycle of `X'` forward along `g`
  have hRHS : (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k
      ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup α)).1 y =
      ∑ᶠ x' : X', α.1 x' *
        (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k
          (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x')).1 y := by
    rw [properPushforward_apply_eq_map,
      show ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').extendCycleGroup α).1 =
        (gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern').toComponentRule.extendCycle
          (pullbackZeroScheme f L s).subschemeι.continuous α.1 from rfl,
      ComponentRule.map_extendCycle_apply _ _ _ _ _ (hcpt g y)]
    exact finsum_congr fun _ ↦ rfl
  rw [hLHS, hRHS]
  refine finsum_congr fun x' ↦ ?_
  by_cases hx : α.1 x' = 0
  · rw [hx, zero_mul, zero_mul, zero_mul]
  · rw [hcomp x' ((mem_cyclesOfDimension_iff_forall_point C p' (k + 1) α.1).1 α.2 x' hx) y]
    ring

/-- **Stacks 02TA.** Gysin pullback through the zero scheme of a section commutes with proper
pushforward: `i^* f_* α' = g_* (i')^* α'` in `A_k(D)` for every `α' ∈ Z_{k+1}(X')`.

The component rules of the Gysin maps on `X` and on `X'`, their compatibility along `f`, and the
vanishing of Stacks 02S2 along `g` needed for `Stacks.Chow.properChowPushforward` are explicit
parameters; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward`. The identity holds already at the
level of cycles, which is `Stacks.Chow.properPushforward_gysinRule_extendCycleGroup`. -/
theorem gysinHomomorphism_properPushforward
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k)
    (hcomp : GysinCompatibleWithPushforward C p k L s chern p' f chern' g hg)
    (α : CycleGroup C p' (k + 1)) :
    gysinHomomorphism C p k L s chern (properPushforward C p' p f hf (k + 1) α) =
      properChowPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) g hg k hfac
        (gysinHomomorphism C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' α) := by
  change QuotientAddGroup.mk ((gysinRule C p k L s chern).extendCycleGroup
    (properPushforward C p' p f hf (k + 1) α)) = _
  rw [properPushforward_gysinRule_extendCycleGroup C p k L s chern p' f hf chern' g hg hcomp α]
  rfl

end Proper

end Stacks.Chow

end
