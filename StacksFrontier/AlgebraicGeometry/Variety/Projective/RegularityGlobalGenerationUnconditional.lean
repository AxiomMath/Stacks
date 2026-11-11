module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplicationArbitraryField

/-!
# [Stacks, Tag 08A8]: an `m`-regular sheaf is globally generated after the twist by `m`

Let `k` be a field, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_k`. [Stacks, Tag 08A8] says that if
`ℱ` is `m`-regular then `ℱ(m)` is globally generated. This file proves it.

## Main results

* `AlgebraicGeometry.isMRegular_add_nat`: an `m`-regular sheaf is `(m + j)`-regular for every
  natural number `j`.
* `AlgebraicGeometry.isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_succ_field`: if `ℱ`
  is `m`-regular and `ℱ(m + 1)` is globally generated, so is `ℱ(m)`.
* `AlgebraicGeometry.isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_field`: if `ℱ` is
  `m`-regular then `ℱ(m)` is globally generated.

## Implementation notes

Globally generated is `SheafOfModules.IsGeneratedByGlobalSections`, the sheaf-of-modules form of
[Stacks, Tag 03DE] (3): there is a family of global sections whose induced map from the free
module on that family is an epimorphism.

## References

* [Stacks Project, Tag 08A8](https://stacks.math.columbia.edu/tag/08A8)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
* [Stacks Project, Tag 08A3](https://stacks.math.columbia.edu/tag/08A3)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- `m`-regularity propagates to every larger integer by [Stacks, Tag 08A6]. -/
private theorem isMRegular_of_le (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] {m a : ℤ}
    (hF : IsMRegular k n F m) (hma : m ≤ a) : IsMRegular k n F a :=
  Int.leInduction hF (fun _ _ ih => isMRegular_add_one k n F _ ih) a hma

/-- `m`-regularity propagates upwards by [Stacks, Tag 08A6]: a coherent sheaf on `ℙⁿ_k` which is
`m`-regular is `(m + j)`-regular for every natural number `j`. -/
theorem isMRegular_add_nat (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (hF : IsMRegular k n F m) (j : ℕ) :
    IsMRegular k n F (m + j) :=
  isMRegular_of_le k n F hF (by omega)

/-- Let `k` be a field and let `ℱ` be a coherent sheaf on `ℙⁿ_k` which is `m`-regular. If
`ℱ(m + 1)` is globally generated then so is `ℱ(m)`. -/
@[sga "6 XIII 1.3" "Descent step"]
theorem isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_succ_field (k : Type u)
    [Field k] (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (hgg : SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F (m + 1)))
    (hF : IsMRegular k n F m) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) :=
  isGeneratedByGlobalSections_projectiveTwist_of_span_mulSections k n F inferInstance m hgg
    (span_mulSections_eq_top_of_isMRegular_field k n F m hF)

/-- For an `m`-regular coherent sheaf `ℱ` on `ℙⁿ_k` and an integer `a ≥ m`, if `ℱ(a)` is
globally generated then so is `ℱ(m)`. -/
@[sga "6 XIII 1.3" "special case"]
private theorem isGeneratedByGlobalSections_of_le (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] {m : ℤ}
    (hF : IsMRegular k n F m) {a : ℤ} (hma : m ≤ a) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F a) →
      SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) :=
  Int.leInduction (motive := fun a _ => SheafOfModules.IsGeneratedByGlobalSections
      (projectiveTwist n F a) → SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m))
    id (fun a ha ih h => ih
      (isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_succ_field k n F a h
        (isMRegular_of_le k n F hF ha))) a hma

/-- Let `k` be a field, let `n ≥ 0`, and let `ℱ` be a coherent sheaf on `ℙⁿ_k`. If `ℱ` is
`m`-regular then `ℱ(m)` is globally generated. -/
@[stacks 08A8 "an m-regular coherent sheaf on projective space over a field is globally \
generated after the twist by m. Everything the source's proof uses is proved: that `ℱ(d)` is \
globally generated for all `d ≫ 0` is \
`Stacks.ProjectiveSpace.exists_isGeneratedByGlobalSections_projectiveTwist_of_isCoherent`, \
clause (7) of Tag 01Q3 read through the comparison of `projectiveTwist` with the tensor powers \
of the hyperplane sheaf; the surjectivity of the multiplication map on global sections is Tag \
08A7 over an arbitrary field, \
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_field`; and the regularity at each \
twist the descent passes through is Tag 08A6, `AlgebraicGeometry.isMRegular_add_one`. The \
descent is organized as a sequence of single-twist steps rather than the source's one-shot use \
of degree-`d-m` forms, each step using the degree-one multiplication of Tag 08A7. \
Globally generated is `SheafOfModules.IsGeneratedByGlobalSections`, Stacks 03DE (3).",
  sga "6 XIII 1.3" "(iii), special case"]
theorem isGeneratedByGlobalSections_projectiveTwist_of_isMRegular_field (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m : ℤ)
    (hF : IsMRegular k n F m) :
    SheafOfModules.IsGeneratedByGlobalSections (projectiveTwist n F m) := by
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.ProjectiveSpace.exists_isGeneratedByGlobalSections_projectiveTwist_of_isCoherent n F
      inferInstance
  exact isGeneratedByGlobalSections_of_le k n F hF (le_max_left m d₀)
    (hd₀ _ (le_max_right _ _))

end AlgebraicGeometry

end
