module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagram
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureFieldObstruction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBaseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCoverCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageCyclicCoefficients
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.AlgClosedField

/-!
# The normalized diagram at a first failure of étale base change: the chain of improvements

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer, as in the condition `BC(f, n, q₀)`
of [Stacks, Tag 0F02]. Suppose `BC(f, n, q)` holds while `BC(f, n, q + 1)` fails. The source
produces a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian, in which `S'` is affine, integral and normal with algebraically
closed function field, `K` is algebraically closed and `Spec K ⟶ S'` is dominant, and in which
`R^{q+1} h_*(ℤ/dℤ)` is nonzero for some `d ∣ n`. That is [Stacks, Tag 0F08], whose conclusion is
`Stacks.EtaleCohomology.FirstFailureDiagram.NormalFailureDiagram`.

This file derives that diagram from the conclusion of [Stacks, Tag 0F07], a failure of base
change over the spectrum of a field.

## Main results

* `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_field` — the chain of
  improvements, starting from the conclusion of [Stacks, Tag 0F07].
* `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_firstFailure` —
  **[Stacks, Tag 0F08]**, another name for
  `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_not_baseChangeHolds`.

## References

* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0F04](https://stacks.math.columbia.edu/tag/0F04)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FirstFailureDiagram

/-- **The base change map depends on the horizontal morphisms only through their values.** Two
spellings `g = g₂` and `h = h₂` of the horizontal morphisms of the square give base change maps
that are isomorphisms together. -/
public theorem isIso_higherBaseChangeMapAb_congr {X' S' T Y : Scheme.{u}} (f' : X' ⟶ S')
    {g g₂ : T ⟶ S'} {h h₂ : Y ⟶ X'} (e : Y ⟶ T) (hg : g = g₂) (hh : h = h₂)
    (w : h ≫ f' = e ≫ g) (w₂ : h₂ ≫ f' = e ≫ g₂) (r : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb f' g h e w r).app F) ↔
      IsIso ((higherBaseChangeMapAb f' g₂ h₂ e w₂ r).app F) := by
  subst hg hh
  rfl

/-- **The normalized diagram from a failure over a field.** With `f : X ⟶ S` and `n` as in
[Stacks, Tag 0F02], assume `BC(f, n, q)`, and let

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

be a diagram of two cartesian squares with `S'` affine and `K` a field, together with an abelian
sheaf `F` on `Spec K` annihilated by `n` whose base change map in degree `q + 1` is not an
isomorphism — the conclusion of [Stacks, Tag 0F07]. Then the normalized diagram of
`NormalFailureDiagram` exists in degree `q + 1`. -/
public theorem normalFailureDiagram_of_field {X S S' X' Y : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ)) [IsAffine S'] (s : S' ⟶ S) (p : X' ⟶ X)
    (f' : X' ⟶ S') (hp : IsPullback p f' f s) (K : Type u) [Field K]
    (g : Spec (.of K) ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1})
    (hF : ∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hfail : ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)) :
    NormalFailureDiagram f n (q + 1) :=
  normalFailureDiagram_of_not_baseChangeHolds f n q hprev fun hbc ↦
    hfail (hbc s p f' hp g h e sq F hF (q + 1) (by push_cast; exact le_rfl))

/-- **[Stacks, Tag 0F08] from the conclusion of [Stacks, Tag 0F07].** With `f : X ⟶ S` and `n`
as in [Stacks, Tag 0F02], assume `BC(f, n, q)` holds and `BC(f, n, q + 1)` does not, and let
`hfield` be the conclusion of [Stacks, Tag 0F07] in the form
`Stacks.EtaleCohomology.exists_affine_field_not_isIso_higherBaseChangeMapAb` proves it. Then the
normalized diagram of [Stacks, Tag 0F08] exists. -/
public theorem normalFailureDiagram_of_exists_field {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfield : ∃ (S' X' Y : Scheme.{u}) (_ : IsAffine S') (s : S' ⟶ S) (p : X' ⟶ X)
      (f' : X' ⟶ S') (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K)
      (g : Spec (.of K) ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
      (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}),
      (∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
        ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)) :
    NormalFailureDiagram f n (q + 1) := by
  obtain ⟨S', X', Y, hS', s, p, f', hp, K, hK, g, h, e, sq, F, hF, hni⟩ := hfield
  exact normalFailureDiagram_of_field f n q hprev s p f' hp K g h e sq F hF hni

/-- With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q)` holds and
`BC(f, n, q + 1)` does not. Then there is a diagram

```
X  ←--  X'  ←-h-  Y
|f      |         |
S  ←--  S'  ←---  Spec K
```

with both squares cartesian, `S'` affine, integral and normal with algebraically closed function
field, `K` algebraically closed with `Spec K ⟶ S'` dominant, and an integer `d ∣ n` with
`R^{q+1} h_* (ℤ/dℤ)` nonzero, `ℤ/dℤ` on `Y` being the inverse image of the constant sheaf on
`Spec K` (`Stacks.EtaleCohomology.FirstFailureDiagram.NormalFailureDiagram`). This is another
name for
`Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_not_baseChangeHolds`. -/
@[stacks 0F08]
public alias normalFailureDiagram_of_firstFailure := normalFailureDiagram_of_not_baseChangeHolds

end Stacks.EtaleCohomology.FirstFailureDiagram

end
