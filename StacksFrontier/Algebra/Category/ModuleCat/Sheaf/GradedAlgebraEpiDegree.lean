module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Epimorphy of a graded comparison in a sum of degrees

Let `A` and `B` be sheaves of graded algebras over the structure sheaf of a ringed site and let
`φ : A ⟶ B` be a unital homomorphism. If `φ` is an isomorphism in the degrees `i` and `j`, and if
the multiplication of `B` in those two degrees is locally surjective, then `φ` is an epimorphism
in the degree `i + j`: a local section of `B` in degree `i + j` is locally a sum of products of
homogeneous sections of degrees `i` and `j`, and each factor of such a product is already in the
image of `φ`.

The argument is a single commuting square of presheaves of modules. A bilinear map of presheaves
of modules is the same thing as a morphism out of the objectwise tensor product, and the
preservation of products by `φ` says exactly that the square

```
  A_i ⊗ A_j ⟶ A_{i + j}
      |            |
  A_i ⊗ A_j ⟶ B_{i + j}
```

commutes, the left vertical arrow being the tensor product of the two comparisons. That arrow is
an isomorphism, so the lower composite is locally surjective as soon as the multiplication of `B`
is; local surjectivity therefore passes to the right vertical arrow, and a locally surjective
morphism of sheaves of modules is an epimorphism.

No cover and no section-by-section argument appear: the one place where sheaf theory enters is
the local surjectivity of the multiplication of `B`, which is supplied as a hypothesis.

## Main results

* `Stacks.SheafOfModules.epi_unitalHom_app_add`: **a unital homomorphism of sheaves of graded
  algebras which is an isomorphism in the degrees `i` and `j` is an epimorphism in the degree
  `i + j`**, provided multiplication of the target in those degrees is locally surjective.
* `Stacks.SheafOfModules.ofBilinear_mul_comp_unitalHom_app`: the commuting square above.
* `Stacks.SheafOfModules.epi_of_isLocallySurjective_fac`: a morphism of sheaves of modules which
  becomes locally surjective after precomposition with a morphism of presheaves of modules is an
  epimorphism.
* `Stacks.SheafOfModules.isLocallySurjective_toSheafify`: the unit of a presheaf of modules into
  its sheafification is locally surjective.
* `Stacks.SheafOfModules.isLocallySurjective_comp`, `isLocallySurjective_of_isIso` and
  `isIso_tensorHom`: the stability properties the argument uses.

## Implementation notes

Mathlib's monoidal structure on presheaves of modules is indexed by a presheaf of rings written
syntactically as `O ⋙ forget₂ CommRingCat RingCat`. The structure sheaf of a ringed site is a
structure literal over that composite, so the two descriptions agree definitionally, but instance
search does not invert the projection; `Stacks.SheafOfModules.monoidalCategoryPresheafOfModules`
records the monoidal structure at the second spelling, and activating it locally is what makes
`⊗ₘ` available in the proofs below.

For the same reason `Stacks.SheafOfModules.isLocallySurjective_toSheafify` has to apply
`PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app` by hand: the sheaf of
rings that instance is indexed by occurs in its statement only under a projection, applied to the
identity, so nothing determines it for instance search.

The hypotheses `IsIso (φ.app i)` and `IsIso (φ.app j)`, and the isomorphy hypotheses of
`isIso_tensorHom` and `isLocallySurjective_of_isIso`, are explicit rather than instance
arguments. They are produced as theorems at the use sites, and the tensor product of two
morphisms carries a monoidal structure whose underlying category instance is a second spelling of
the one on the morphisms themselves, so an instance argument would not be matched against a
hypothesis of that shape.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe v u w t

namespace Stacks.SheafOfModules

section Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- A composite of two locally surjective morphisms of presheaves of modules is locally
surjective. -/
theorem isLocallySurjective_comp {M N P : PresheafOfModules.{w} R} {f : M ⟶ N} {g : N ⟶ P}
    (hf : PresheafOfModules.IsLocallySurjective J f)
    (hg : PresheafOfModules.IsLocallySurjective J g) :
    PresheafOfModules.IsLocallySurjective J (f ≫ g) := by
  change Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map (f ≫ g))
  rw [Functor.map_comp]
  infer_instance

/-- An isomorphism of presheaves of modules is locally surjective, being surjective on the
sections over every object of the site. -/
theorem isLocallySurjective_of_isIso {M N : PresheafOfModules.{w} R} (f : M ⟶ N)
    (hf : IsIso f) : PresheafOfModules.IsLocallySurjective J f := by
  have : IsIso ((PresheafOfModules.toPresheaf R).map f) := inferInstance
  infer_instance

end Presheaf

section Epi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **A morphism of sheaves of modules is an epimorphism as soon as some morphism of presheaves
of modules into its source becomes locally surjective after composing with it**, epimorphy of a
morphism of sheaves of modules being local surjectivity. -/
theorem epi_of_isLocallySurjective_fac {M N : _root_.SheafOfModules.{w} R}
    {P : PresheafOfModules.{w} R.obj} {g : P ⟶ M.val} {h : P ⟶ N.val} (f : M ⟶ N)
    (fac : g ≫ f.val = h) (hh : PresheafOfModules.IsLocallySurjective J h) : Epi f := by
  refine EpiMono.epi_of_isLocallySurjective f ?_
  have hfac : (PresheafOfModules.toPresheaf R.obj).map g ≫
      (PresheafOfModules.toPresheaf R.obj).map f.val =
      (PresheafOfModules.toPresheaf R.obj).map h := by
    rw [← Functor.map_comp, fac]
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac

end Epi

section Graded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O)}

attribute [local instance] monoidalCategoryPresheafOfModules

/-- A tensor product of two isomorphisms of presheaves of modules is an isomorphism. -/
theorem isIso_tensorHom {M N M' N' : PresheafOfModules.{w}
      (TensorSheafification.structureSheaf O hO).obj} (f : M ⟶ N) (g : M' ⟶ N')
    (hf : IsIso f) (hg : IsIso g) : IsIso (f ⊗ₘ g) :=
  Iso.isIso_hom (asIso f ⊗ᵢ asIso g)

variable {A B : _root_.SheafOfModules.GradedAlgebra.{w, w}
  (TensorSheafification.structureSheaf O hO)}

/-- Multiplying two homogeneous local sections and then comparing is comparing and then
multiplying: the square of presheaves of modules which says that a unital homomorphism of sheaves
of graded algebras preserves products in a fixed pair of degrees. -/
theorem ofBilinear_mul_comp_unitalHom_app
    (φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) (i j : ℤ)
    (mB : PresheafOfModules.tensorObj (B.piece i).val (B.piece j).val ⟶ (B.piece (i + j)).val)
    (hmB : ∀ (X : Cᵒᵖ) (x : (B.piece i).val.obj X) (y : (B.piece j).val.obj X),
      PresheafOfModules.Hom.app mB X (x ⊗ₜ[O.obj X] y) = (B.mul i j).app X x y) :
    PresheafOfModules.ofBilinear (A.mul i j) ≫ (φ.app (i + j)).val =
      ((φ.app i).val ⊗ₘ (φ.app j).val) ≫ mB := by
  refine PresheafOfModules.hom_ext (fun X => ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
  have hright : PresheafOfModules.Hom.app (((φ.app i).val ⊗ₘ (φ.app j).val) ≫ mB) X
        (x ⊗ₜ[O.obj X] y) =
      (B.mul i j).app X ((φ.app i).val.app X x) ((φ.app j).val.app X y) :=
    hmB X _ _
  exact ((congrArg ((φ.app (i + j)).val.app X)
    (PresheafOfModules.ofBilinear_tmul (A.mul i j) X x y)).trans
      (φ.map_mul i j X x y)).trans hright.symm

/-- **A unital homomorphism of sheaves of graded algebras which is an isomorphism in two degrees
is an epimorphism in their sum**, as soon as multiplication of the target in those two degrees is
locally surjective: a local section of the target in degree `i + j` is then locally a sum of
products of homogeneous sections, and each factor is already in the image. -/
theorem epi_unitalHom_app_add (φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) (i j : ℤ)
    (hi : IsIso (φ.app i)) (hj : IsIso (φ.app j))
    (mB : PresheafOfModules.tensorObj (B.piece i).val (B.piece j).val ⟶ (B.piece (i + j)).val)
    (hmB : ∀ (X : Cᵒᵖ) (x : (B.piece i).val.obj X) (y : (B.piece j).val.obj X),
      PresheafOfModules.Hom.app mB X (x ⊗ₜ[O.obj X] y) = (B.mul i j).app X x y)
    (hmls : PresheafOfModules.IsLocallySurjective J mB) :
    Epi (φ.app (i + j)) := by
  have h : ∀ k, IsIso (φ.app k) → IsIso (φ.app k).val := fun k hk =>
    inferInstanceAs (IsIso ((_root_.SheafOfModules.forget
      (TensorSheafification.structureSheaf O hO)).map (φ.app k)))
  have h₃ := isIso_tensorHom (φ.app i).val (φ.app j).val (h i hi) (h j hj)
  refine epi_of_isLocallySurjective_fac (φ.app (i + j))
    (ofBilinear_mul_comp_unitalHom_app φ i j mB hmB) ?_
  exact isLocallySurjective_comp (isLocallySurjective_of_isIso _ h₃) hmls

end Graded

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The unit of a presheaf of modules into its sheafification is locally surjective**: a local
section of the sheafification is, after restriction along the arrows of a covering sieve, the
image of a section of the presheaf. -/
theorem isLocallySurjective_toSheafify
    (P : PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)) :
    PresheafOfModules.IsLocallySurjective J (TensorSheafification.toSheafify O hO P) :=
  PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
    (R := TensorSheafification.structureSheaf O hO)
    (𝟙 (TensorSheafification.structureSheaf O hO).obj) P

end Sheafify

end Stacks.SheafOfModules

end
