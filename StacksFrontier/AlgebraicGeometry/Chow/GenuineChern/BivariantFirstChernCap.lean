module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleShift
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# Bivariant classes commute with the first Chern class

Let `(S, δ)` be as in Situation 02QL, let `f : X' ⟶ X` be a morphism of schemes locally of finite
type over `S` and let `c ∈ A^p(X' ⟶ X)` be a bivariant class. For a test scheme `g : T ⟶ X` and an
invertible module `ℒ` on `T`,

  `c ∩ (c₁(ℒ) ∩ α) = c₁(ℒ') ∩ (c ∩ α)`  in  `A_{k-p}(T ×_X X')`,  for `α ∈ A_{k+1}(T)`,

where `ℒ'` is the pullback of `ℒ` to `T ×_X X'`. This is the identity of Stacks 0B7B (2) read on
the test scheme `g`.

## The argument

The zero section `0` of `ℒ` has zero scheme `i : Z(0) ⟶ T`, and by Stacks 02T9 the composite
`i_* i^*` is `c₁(ℒ) ∩ -`; the same holds on `T ×_X X'` for the pulled-back section. Condition (1)
of Stacks 0B76 carries `c` past `i_*`, condition (3) carries it past `i^*`, and the base change of
`Z(0)` is identified with the zero scheme of the pulled-back section by Remark 0B6Y. No line
bundle and no injectivity of a flat pullback is needed.

Iterating, `c` carries `c₁(ℒ)^s ∩ -` to `c₁(ℒ')^s ∩ -`, which is the form in which the identity
enters the projective bundle relation of Stacks 02U6.

## Main results

* `Stacks.Chow.BivariantChowClass.cap_firstChernClassCapChow` — the identity above.
* `Stacks.Chow.BivariantChowClass.cap_capPow_heq` — its iterate, for the powers `c₁(ℒ)^s ∩ -`.

## References

* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace BivariantChowClass

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {f : X' ⟶ X} {hf : f ≫ sX = sX'} {p : ℤ}

/-- **Stacks 0B7B (2), on a test scheme.** A bivariant class `c ∈ A^p(X' ⟶ X)` commutes with the
first Chern class of an invertible module `ℒ` on a test scheme `g : T ⟶ X`:

  `c ∩ (c₁(ℒ) ∩ α) = c₁(ℒ') ∩ (c ∩ α)`,

with `ℒ'` the pullback of `ℒ` to `T ×_X X'`. -/
theorem cap_firstChernClassCapChow (c : BivariantChowClass C sX' sX f hf p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (L : T.Modules)
    [SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L] (k : ℤ)
    (α : chowGroup C (g ≫ sX) (k + 1)) :
    haveI := GenuineChern.isInvertible_pullback (pullback.snd f g) L
    c.cap g k (firstChernClassCapChow C k (g ≫ sX) L α) =
      firstChernClassCapChow C (k - p) (pullback.fst f g ≫ sX')
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX'))
          (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α)) := by
  have := GenuineChern.isInvertible_pullback (pullback.snd f g) L
  set D := Stacks.Divisors.zeroScheme T L 0 with hD
  set L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L with hL'
  set s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L 0 with hs'
  set E := Stacks.Divisors.zeroScheme (pullback f g) L' s' with hE
  -- Stacks 02T9 on `T`, for the zero section
  rw [← GenuineChern.properChowPushforward_gysinChowOfInvertible C (g ≫ sX) k L 0
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ k) α]
  -- condition (1) of Stacks 0B76 along `i : Z(0) ⟶ T`
  have h1 := c.cap_properPushforward g D.subschemeι k (gysinChowOfInvertible C (g ≫ sX) k L 0 α)
  refine h1.trans ?_
  -- the base change of `i` is the zero scheme of the pulled-back section (Remark 0B6Y)
  rw [properChowPushforward_comp_apply C _ _ (pullback.fst f g ≫ sX')
    (bivariantDivisorBaseChangeIso f g L 0).hom E.subschemeι
    (bivariantBaseChangeMap f g D.subschemeι)
    (bivariantDivisorBaseChangeIso_hom_subschemeι f g L 0)
    (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism sX' f g L 0) rfl _ (k - p)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)]
  -- condition (3) of Stacks 0B76 for the zero section
  rw [c.cap_gysin g L 0 k α]
  -- Stacks 02T9 on `T ×_X X'`, for the pulled-back section
  exact GenuineChern.properChowPushforward_gysinChowOfInvertible C (pullback.fst f g ≫ sX') (k - p)
    L' s' _ _

/-- A first Chern class cap operator, at heterogeneously equal arguments in equal degrees. -/
private theorem capOnChow_heq' {P : Scheme.{u}} {sP : P ⟶ C.S} [LocallyOfFiniteType sP]
    (O : ChernCapOperator C sP) {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C sP (d₁ + 1)}
    {y : chowGroup C sP (d₂ + 1)} (hxy : x ≍ y) :
    O.capOnChow C sP d₁ x ≍ O.capOnChow C sP d₂ y := by
  subst hd; cases hxy; rfl

/-- **Stacks 0B7B (2), iterated.** The cap product of `c` carries `c₁(𝒪)^s ∩ -` on a test scheme
`h : P ⟶ X` to `c₁(𝒪')^s ∩ -` on `P ×_X X'`, `𝒪'` the pullback of `𝒪`. -/
theorem cap_capPow_heq (c : BivariantChowClass C sX' sX f hf p) {P : Scheme.{u}} (h : P ⟶ X)
    [LocallyOfFiniteType h] (O : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property O] (s : ℕ) :
    haveI := GenuineChern.isInvertible_pullback (pullback.snd f h) O
    ∀ (a m : ℤ) (ham : a = m + s) (m' : ℤ) (ham' : a - p = m' + s) (_ : m' = m - p)
      (x : chowGroup C (h ≫ sX) a),
      c.cap h m (capPow C (h ≫ sX) (invCap C (h ≫ sX) O) s a m ham x) ≍
        capPow C (pullback.fst f h ≫ sX')
          (invCap C (pullback.fst f h ≫ sX') ((Scheme.Modules.pullback (pullback.snd f h)).obj O))
          s (a - p) m' ham' (c.cap h a x) := by
  have := GenuineChern.isInvertible_pullback (pullback.snd f h) O
  induction s with
  | zero =>
    intro a m ham m' ham' hm x
    rw [capPow_zero_apply, capPow_zero_apply]
    refine HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm
    exact c.heq_cap h (by simpa using ham.symm) (chowGroupCast_heq C _ _ _)
  | succ s ih =>
    intro a m ham m' ham' hm x
    rw [capPow_succ_apply', capPow_succ_apply']
    refine (heq_of_eq (c.cap_firstChernClassCapChow h O m _)).trans ?_
    refine capOnChow_heq' (invCap C (pullback.fst f h ≫ sX')
      ((Scheme.Modules.pullback (pullback.snd f h)).obj O)) (by omega) ?_
    refine (cast_heq _ _).trans ?_
    exact ih a (m + 1) (by push_cast at ham ⊢; omega) (m' + 1) (by push_cast at ham' ⊢; omega)
      (by omega) x

end BivariantChowClass

end Stacks.Chow

end
