module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# The relative diagonal of a morphism of algebraic spaces (Stacks 03HK)

Let `S` be a scheme contained in a big fppf site `B` and let `f : F ⟶ G` be a morphism of
presheaves on the big fppf site of `S` with `F` an algebraic space over `S`. The relative
diagonal `Δ_f : F ⟶ F ×_G F` is a base change of the absolute diagonal `F ⟶ F × F`, along
the morphism `F ×_G F ⟶ F × F` comparing the fibre product with the product. Consequently
every base-change stable property of the absolute diagonal is inherited by the relative
diagonal, with no hypothesis on the target `G`.

In particular part (1) of Stacks 03HK — representability of the relative diagonal — follows
at once from the second defining clause of
`AlgebraicGeometry.IsAlgebraicSpace`.

## Main results

* `AlgebraicGeometry.isPullback_pullbackDiagonal_diag`: the relative diagonal is a base change
  of the absolute diagonal.
* `AlgebraicGeometry.presheaf_pullbackDiagonal_of_diag`: a relatively representable property of
  the absolute diagonal passes to the relative diagonal.
* `AlgebraicGeometry.relativelyRepresentable_pullbackDiagonal`: **Stacks 03HK**, part (1).

## Implementation notes

The cartesian square is

```
F  --- 𝟙 --->   F
|               |
Δ_f            diag F
v               v
F ×_G F -----> F × F
```

whose lower edge is `prod.lift (pullback.fst f f) (pullback.snd f f)`. That it is cartesian
is checked by hand: a cone on the cospan is a morphism to `F × F` factoring through both
`F ×_G F` and `F`, and such a morphism is determined by its first component, which is the
unique lift.

Parts (2) to (5) of Stacks 03HK — the relative diagonal is locally of finite type, a
monomorphism, separated and locally quasi-finite — are each the corresponding statement for
the *absolute* diagonal of an algebraic space (Stacks 02X4) fed through
`AlgebraicGeometry.presheaf_pullbackDiagonal_of_diag`, so once Stacks 02X4 is available they
are one line apiece. Stacks 02X4 is not in this library, so only part (1) is tagged here.

## References

* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative diagonal of `f : F ⟶ G` is a base change of the absolute diagonal of `F`
along the comparison morphism `F ×_G F ⟶ F × F`. -/
theorem isPullback_pullbackDiagonal_diag (f : F ⟶ G) :
    IsPullback (𝟙 F) (pullback.diagonal f) (Limits.diag F)
      (prod.lift (pullback.fst f f) (pullback.snd f f)) := by
  have hd : pullback.diagonal f ≫ prod.lift (pullback.fst f f) (pullback.snd f f) =
      Limits.diag F := by ext <;> simp
  refine ⟨⟨hd.symm⟩, ⟨PullbackCone.IsLimit.mk hd.symm (fun s => s.fst) (fun s => by simp)
    (fun s => ?_) (fun s m hm₁ _ => by simpa using hm₁)⟩⟩
  refine pullback.hom_ext ?_ ?_
  · simpa using congrArg (fun k => k ≫ Limits.prod.fst) s.condition
  · simpa using congrArg (fun k => k ≫ Limits.prod.snd) s.condition

/-- A relatively representable property of the absolute diagonal of `F` is inherited by the
relative diagonal of any morphism out of `F`, the latter being a base change of the former
and a relative property being stable under base change. -/
theorem presheaf_pullbackDiagonal_of_diag (f : F ⟶ G)
    (P : MorphismProperty (BigFppfOver B S hS)) (hP : P.presheaf (Limits.diag F)) :
    P.presheaf (pullback.diagonal f) :=
  (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
    (isPullback_pullbackDiagonal_diag B S hS f) hP

/-- **Stacks 03HK, part (1).** The relative diagonal of a morphism out of an algebraic space
over `S` is relatively representable. The target need not be an algebraic space: the relative
diagonal is a base change of the absolute diagonal of the source, which is representable by
the second defining clause of `AlgebraicGeometry.IsAlgebraicSpace`. -/
@[stacks 03HK "part (1)"]
theorem relativelyRepresentable_pullbackDiagonal (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) :
    yoneda.relativelyRepresentable (pullback.diagonal f) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (isPullback_pullbackDiagonal_diag B S hS f) hF.diagonal_representable

end AlgebraicGeometry

end
