module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget

/-!
# Schemes over the terminal scheme

Every scheme of the big fppf site has exactly one morphism to the terminal scheme
`AlgebraicGeometry.integerBase`, so reading a scheme of the site over `Spec(ℤ)` and forgetting
the structure morphism again is the identity, on the nose:
`BigFppfOver.forget ⋙ schemeOverIntegers = 𝟭`.

## Main results

* `AlgebraicGeometry.forget_comp_schemeOverIntegers`: forgetting the structure morphism to
  `Spec(ℤ)` and reading a scheme of the site over `Spec(ℤ)` again is the identity functor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u})

/-- A scheme of the site over `Spec(ℤ)` is the scheme it forgets to, read over `Spec(ℤ)`. -/
theorem schemeOverIntegers_obj_forget (V : BigFppfOver B integerBase B.contains_integerBase) :
    (schemeOverIntegers B).obj
      ((BigFppfOver.forget B integerBase B.contains_integerBase).obj V) = V := by
  obtain ⟨left, ⟨⟨⟩⟩, hom⟩ := V
  show Over.mk _ = Over.mk hom
  congr 1
  apply ObjectProperty.hom_ext
  exact specULiftZIsTerminal.hom_ext _ _

/-- The underlying morphism of `eqToHom h` between objects of an over category is `eqToHom` of
the induced equality of underlying objects. -/
theorem over_eqToHom_left {A : B.Schemes} {X Y : Over A} (h : X = Y) :
    (eqToHom h).left = eqToHom (congrArg (fun Z : Over A => Z.left) h) := by
  subst h
  rfl

/-- **Forgetting to the site and reading over `Spec(ℤ)` again is the identity.** -/
theorem forget_comp_schemeOverIntegers :
    BigFppfOver.forget B integerBase B.contains_integerBase ⋙ schemeOverIntegers B =
      𝟭 (BigFppfOver B integerBase B.contains_integerBase) := by
  refine CategoryTheory.Functor.ext (fun (V : BigFppfOver B integerBase B.contains_integerBase) =>
    schemeOverIntegers_obj_forget B V) (fun V W f => ?_)
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, over_eqToHom_left, over_eqToHom_left]
  rfl

end AlgebraicGeometry

end
