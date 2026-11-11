module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories fibred in groupoids (Stacks 003T)

Stacks Tag `003T` (Definition 4.35.1): a functor `p : 𝒮 ⥤ 𝒞` is *fibred in groupoids* when

1. for every morphism `f : V ⟶ U` of `𝒞` and every lift `x` of `U` there is a lift `φ : y ⟶ x`
   of `f` with target `x`;
2. for every pair of morphisms `φ : y ⟶ x`, `ψ : z ⟶ x` and every `f : p(z) ⟶ p(y)` with
   `p(φ) ∘ f = p(ψ)` there is a unique lift `χ : z ⟶ y` of `f` with `φ ∘ χ = ψ`.

This is the library's canonical predicate `CategoryTheory.Functor.IsFiberedInGroupoids`, whose
fields `exists_lift` and `unique_lift` are the two conditions; this file registers it for the
tag. The equivalent characterization "fibred category with groupoid fibres" is Stacks `003V`,
`CategoryTheory.Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`.

## References

* [Stacks Project, Definition 4.35.1 (Tag 003T)](https://stacks.math.columbia.edu/tag/003T)
-/

add_to_stacks 003T "Both conditions: `exists_lift` is (1), the existence of a lift with \
prescribed target of every base morphism; `unique_lift` is (2), the unique fill-in `χ` with \
`p.map χ = f` and `χ ≫ φ = ψ`." CategoryTheory.Functor.IsFiberedInGroupoids
