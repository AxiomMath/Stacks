module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow

/-!
# Injectivity of flat pullback across a relative effective Cartier divisor

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `p : V ⟶ Y` be flat of
relative dimension `r + 1` between schemes locally of finite type over `S`, and let `D ⊆ V` be a
relative effective Cartier divisor on `V/Y`, presented as the zero scheme of a global section of
an invertible module. By Stacks 02TR the Gysin map of `D` retracts the flat pullback onto the
flat pullback along `D ⟶ Y`:

  `i^* p^* α = (p|_D)^* α`.

So if flat pullback along `p|_D` is injective, then so is `p^*`. Iterated along a filtration, this
is the injectivity half of Stacks 02TY.

## Main results

* `Stacks.Chow.flatPullbackChow_injective_of_relativeEffectiveCartier` — injectivity of `p^*`
  from injectivity of `(p|_D)^*`.

## References

* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Injectivity of flat pullback descends across a relative effective Cartier divisor.** If
`D = Z(s) ⊆ V` is a relative effective Cartier divisor on `V/Y` for `p : V ⟶ Y` flat of relative
dimension `r + 1`, and flat pullback along `D ⟶ Y` is injective, then flat pullback along `p` is
injective: by Stacks 02TR the Gysin map of `D` carries `p^* α` to `(p|_D)^* α`. -/
theorem flatPullbackChow_injective_of_relativeEffectiveCartier (C : ChowSituation.{u})
    {V Y : Scheme.{u}} (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : V ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sV)
    (r : ℕ) (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : L.sections) (D : V.IdealSheafData)
    (hDs : Stacks.Divisors.zeroScheme V L (s.eval (.op ⊤)) = D)
    [Flat (D.subschemeι ≫ p)] (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p D)
    (hq : AlgebraicGeometry.RelativeDimension (D.subschemeι ≫ p) r)
    (hinj : ∀ k : ℤ, Function.Injective (flatPullbackChowOfRelativeDimension C
      (D.subschemeι ≫ sV) sY (D.subschemeι ≫ p) (by rw [Category.assoc, hbase]) r hq k))
    (m : ℤ) :
    Function.Injective (flatPullbackChowOfRelativeDimension C sV sY p hbase (r + 1) hp m) := by
  subst hDs
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = k + 1 := ⟨m - 1, by ring⟩
  intro α β hαβ
  have hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1 := by push_cast; ring
  have h := gysinChowOfInvertible_flatPullbackChow C sV sY p hbase r hp k L s hD hcast
  exact hinj (k + 1) (by rw [← h α, ← h β, hαβ])

end Stacks.Chow

end
