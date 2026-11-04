module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationRegularImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a factorization through a smooth scheme

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of schemes, and let `f = h ∘ i` be a factorization of `f` with
`i : X ⟶ P` an immersion and `h : P ⟶ Y` smooth. The proof of Stacks 0FV9 base changes it: with
`P' = P ×_Y Y'`, `h' : P' ⟶ Y'` the second projection and `i' : X' ⟶ P'` the morphism induced by
`g' ∘ i` and `f'`, the morphism `f'` factors as `f' = h' ∘ i'`, the left square of the diagram

```
X' --i'--> P' --h'--> Y'
|          |          |
g'         p          g
v          v          v
X  --i---> P  --h---> Y
```

is again cartesian, `i'` is an immersion and `h'` is smooth. In particular the Gysin map of
Stacks 0FF3 exists for `f'` as soon as it exists for `f`, which is the second assertion of
Stacks 0FV9.

## Main definitions

* `Stacks.Chow.SmoothFactorization.baseChange`: the factorization `f' = h' ∘ i'` above.

## Main results

* `Stacks.Chow.SmoothFactorization.isPullback_baseChange`: the left square is cartesian.
* `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion_baseChange`: if `f'` is a local
  complete intersection morphism, `i'` is a Koszul-regular immersion.
* `Stacks.Chow.GysinMapExists.of_isPullback`: the Gysin map exists for `f'` when it exists for
  `f`.

## Implementation notes

The square is an arbitrary `IsPullback g' f' f g`, in the convention `g' ≫ f = f' ≫ g` of
Stacks 0FV5 in this repository; the scheme `P'` is the chosen pullback of `h` along `g`. The left
square is cartesian by the pasting law for pullbacks: the outer rectangle is the given square and
the right square is the chosen pullback. Then `i'` is an immersion because immersions are stable
under base change, and `h'` is smooth because smooth morphisms are.

No local complete intersection hypothesis is needed for the factorization itself; it enters only
in `isKoszulRegularImmersion_baseChange`, through Stacks 069G, as
`Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion` applied to the base-changed
factorization.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

namespace SmoothFactorization

/-- The morphism `i' : X' ⟶ P ×_Y Y'` induced by `g' ∘ i` and `f'`, for a factorization
`f = h ∘ i` and a commutative square `g' ≫ f = f' ≫ g`. -/
noncomputable def baseChangeImm (F : SmoothFactorization f) (w : g' ≫ f = f' ≫ g) :
    X' ⟶ pullback F.proj g :=
  pullback.lift (g' ≫ F.imm) f' (by rw [Category.assoc, F.imm_proj, w])

/-- The composite of `i' : X' ⟶ P ×_Y Y'` with the first projection is `g' ≫ i`. -/
@[reassoc (attr := simp)]
theorem baseChangeImm_fst (F : SmoothFactorization f) (w : g' ≫ f = f' ≫ g) :
    F.baseChangeImm w ≫ pullback.fst F.proj g = g' ≫ F.imm :=
  pullback.lift_fst _ _ _

/-- The composite of `i' : X' ⟶ P ×_Y Y'` with the second projection is `f'`. -/
@[reassoc (attr := simp)]
theorem baseChangeImm_snd (F : SmoothFactorization f) (w : g' ≫ f = f' ≫ g) :
    F.baseChangeImm w ≫ pullback.snd F.proj g = f' :=
  pullback.lift_snd _ _ _

/-- **The left square of the base-changed factorization is cartesian.** For a cartesian square
`g' ≫ f = f' ≫ g` and a factorization `f = h ∘ i`, the square formed by `i' : X' ⟶ P ×_Y Y'`,
`g'`, `i` and the first projection `P ×_Y Y' ⟶ P` is cartesian, by the pasting law. -/
theorem isPullback_baseChange (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    IsPullback g' (F.baseChangeImm hsq.w) F.imm (pullback.fst F.proj g) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd F.proj g) (v₂₂ := F.proj) ?_
    (F.baseChangeImm_fst hsq.w).symm (IsPullback.of_hasPullback F.proj g)
  rw [F.baseChangeImm_snd, F.imm_proj]
  exact hsq

/-- The immersion `i' : X' ⟶ P ×_Y Y'` of the base-changed factorization is an immersion, being
a base change of `i`. -/
theorem isImmersion_baseChangeImm (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    IsImmersion (F.baseChangeImm hsq.w) :=
  MorphismProperty.of_isPullback (F.isPullback_baseChange hsq) F.isImmersion

/-- **The base change of a factorization through a smooth scheme.** For a cartesian square
`g' ≫ f = f' ≫ g` and a factorization `f = h ∘ i` with `i : X ⟶ P` an immersion and
`h : P ⟶ Y` smooth, the factorization `f' = h' ∘ i'` through `P' = P ×_Y Y'`, with `h'` the
second projection and `i'` induced by `g' ∘ i` and `f'`. -/
@[sga "6 VIII 1.6" "Proof construction"]
noncomputable def baseChange (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    SmoothFactorization f' where
  ambient := pullback F.proj g
  imm := F.baseChangeImm hsq.w
  proj := pullback.snd F.proj g
  isImmersion := F.isImmersion_baseChangeImm hsq
  isSmooth := inferInstance
  imm_proj := F.baseChangeImm_snd hsq.w

/-- The ambient scheme of the base-changed factorization is `P ×_Y Y'`. -/
@[simp]
theorem baseChange_ambient (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    (F.baseChange hsq).ambient = pullback F.proj g :=
  rfl

/-- The immersion of the base-changed factorization is `i' : X' ⟶ P ×_Y Y'`. -/
@[simp]
theorem baseChange_imm (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    (F.baseChange hsq).imm = F.baseChangeImm hsq.w :=
  rfl

/-- The smooth morphism of the base-changed factorization is the second projection
`P ×_Y Y' ⟶ Y'`. -/
@[simp]
theorem baseChange_proj (F : SmoothFactorization f) (hsq : IsPullback g' f' f g) :
    (F.baseChange hsq).proj = pullback.snd F.proj g :=
  rfl

/-- If `f'` is a local complete intersection morphism, the immersion of the base-changed
factorization is Koszul-regular: it is the immersion of a factorization of `f'` through a smooth
scheme, so Stacks 069G applies. -/
theorem isKoszulRegularImmersion_baseChange (F : SmoothFactorization f)
    (hsq : IsPullback g' f' f g) (hf' : IsLocalCompleteIntersectionMorphism f') :
    @IsKoszulRegularImmersion _ _ (F.baseChangeImm hsq.w) (F.isImmersion_baseChangeImm hsq) :=
  (F.baseChange hsq).isKoszulRegularImmersion_of_lci hf'

end SmoothFactorization

/-- **The Gysin map exists after base change** (the second assertion of Stacks 0FV9). For a
cartesian square `g' ≫ f = f' ≫ g`, if the Gysin map of Stacks 0FF3 exists for `f` then it exists
for `f'`: a factorization of `f` through a smooth scheme base changes to one of `f'`. -/
theorem GysinMapExists.of_isPullback (hsq : IsPullback g' f' f g) (h : GysinMapExists f) :
    GysinMapExists f' := by
  obtain ⟨F⟩ := (gysinMapExists_iff_nonempty f).1 h
  exact (F.baseChange hsq).gysinMapExists

end Stacks.Chow

end
