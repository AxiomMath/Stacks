module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# Homomorphisms into an annihilated module are annihilated

Let `O` be a presheaf of commutative rings on a category, let `F` and `G` be presheaves of
`O`-modules, and let `f` be a section of `O` over an object `U`. The sections of the internal Hom
over `U` are the morphisms `F|_U ⟶ G|_U`, and the action of `f` on such a morphism is
postcomposition with multiplication by `f` on the target.

So if multiplication by `f` is zero on `G|_U`, it is zero on every morphism into `G|_U`: an ideal
annihilating a module annihilates every homomorphism into it. This is the statement that lets a
Hom sheaf be descended along a quotient of the structure sheaf whenever its target can be.

## Main statements

* `multEndoHom_eq_zero`: multiplication by `f` is the zero endomorphism of `G|_U` as soon as the
  restrictions of `f` annihilate every section of `G` over the slice over `U`.
* `smulHom_eq_zero`: consequently `f` annihilates every morphism `F|_U ⟶ G|_U`, that is, every
  section of the internal Hom over `U`.

## Implementation notes

The scalar action on the internal Hom is `smulHom`, which is *post*-composition with
`multEndoHom`, multiplication by the section on the target. That is what makes the statement a
one-line consequence of the vanishing of `multEndoHom` rather than an induction over the
structure of a morphism: no hypothesis on the source `F` is needed, and in particular `F` need
not be of finite type or even of finite presentation.

The hypothesis is phrased with the restrictions `fRestr O U f V` rather than with `f` itself,
because a morphism of the restricted modules has one component over each object of the slice
over `U` and the component over `V` is scaled by the restriction of `f` to `V`. For an ideal of
sections that hypothesis is automatic, since an ideal is stable under restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u t

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{t})
  (F G : PresheafOfModules.{t} (Oforget O))

/-- **Multiplication by a section is the zero endomorphism when it annihilates the sections.**
If every restriction of `f` annihilates every section of `G` over the slice over `U`, then
multiplication by `f` is the zero endomorphism of `G|_U`. -/
theorem multEndoHom_eq_zero (U : C) (f : (Oforget O).obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (x : ((restrFun O U).obj G).obj V), fRestr O U f V • x = 0) :
    multEndoHom O G U f = 0 := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact h V x

/-- **A homomorphism into an annihilated module is annihilated.** If every restriction of `f`
annihilates every section of `G`, then `f` annihilates every morphism `F|_U ⟶ G|_U`, that is,
every section of the internal Hom of `F` and `G` over `U`.

The action on a morphism is postcomposition with multiplication by `f` on the target, so this is
the vanishing of that multiplication; nothing is assumed about the source. -/
theorem smulHom_eq_zero (U : C) (f : (Oforget O).obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (x : ((restrFun O U).obj G).obj V), fRestr O U f V • x = 0)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    smulHom O F G U f α = 0 := by
  rw [smulHom, multEndoHom_eq_zero O G U f h, comp_zero]

end
