module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraSliceRestriction

/-!
# Pushforward of a sheaf of graded algebras along a continuous functor of sites

Let `F : C ⥤ D` be a continuous functor between sites, let `R` be a sheaf of rings on `D`, let `S`
be a sheaf of rings on `C` and let `φ : S ⟶ F_* R` be a morphism of sheaves of rings. Pushing a
sheaf of `R`-modules forward along `F` and restricting its scalars along `φ` gives a sheaf of
`S`-modules whose sections over `V` are the sections of the original over `F V`. Hence a sheaf of
graded `R`-algebras `A` pushes forward to a sheaf of graded `S`-algebras
`SheafOfModules.GradedAlgebra.pushforward φ A`, each of whose structure maps is the corresponding
one of `A` read at `F V`. This file pushes forward its homomorphisms and generators. The case
`F = Over.forget U`, `φ = 𝟙` is `SheafOfModules.GradedAlgebra.over`.

## Main definitions

* `SheafOfModules.GradedAlgebra.UnitalHom.sitePushforward`: the pushforward of a homomorphism of
  sheaves of graded algebras.
* `SheafOfModules.GradedAlgebra.genSitePushforward`: the pushforward of a degree-one generator.

## Main results

* `SheafOfModules.GradedAlgebra.SquareZero.sitePushforward`: a square-zero degree-one generator
  pushes forward to a square-zero degree-one generator.
* `SheafOfModules.GradedAlgebra.UnitalHom.isIso_sitePushforward_app`: a homomorphism which is an
  isomorphism in degree `n` pushes forward to one which is.
* `SheafOfModules.GradedAlgebra.UnitalHom.isIso_sitePushforward_app_iff`: when the pushforward of
  sheaves of modules reflects isomorphisms, a homomorphism is an isomorphism in degree `n` if and
  only if its pushforward is.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a v v' u u'

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K] {S : Sheaf J RingCat.{t}} {R : Sheaf K RingCat.{t}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{t} J K).obj R)

variable {M : SheafOfModules.{a} R} {A B : GradedAlgebra.{t, a} R}

/-- The pushforward of a degree-one generator `ι : M ⟶ A.piece 1`, as a morphism into
`(pushforward φ A).piece 1`. -/
noncomputable abbrev genSitePushforward (ι : M ⟶ A.piece 1) :
    (_root_.SheafOfModules.pushforward.{a} φ).obj M ⟶ (pushforward φ A).piece 1 :=
  (_root_.SheafOfModules.pushforward.{a} φ).map ι

/-- A square-zero degree-one generator pushes forward to a square-zero degree-one generator. -/
theorem SquareZero.sitePushforward {ι : M ⟶ A.piece 1} (h : SquareZero ι) :
    SquareZero (A := _root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (genSitePushforward φ ι) :=
  fun V s => h (op (F.obj V.unop)) s

/-- The pushforward of a homomorphism of sheaves of graded algebras: each component is the
pushforward of the corresponding component. -/
noncomputable def UnitalHom.sitePushforward (g : UnitalHom A B) :
    UnitalHom (_root_.SheafOfModules.GradedAlgebra.pushforward φ A)
      (_root_.SheafOfModules.GradedAlgebra.pushforward φ B) where
  app n := (_root_.SheafOfModules.pushforward.{a} φ).map (g.app n)
  map_mul i j V x y := g.map_mul i j (op (F.obj V.unop)) x y
  map_one V := g.map_one (op (F.obj V.unop))

/-- The degree-`n` component of the pushforward of `g` is the pushforward of that of `g`. -/
@[simp]
theorem UnitalHom.sitePushforward_app (g : UnitalHom A B) (n : ℤ) :
    (g.sitePushforward φ).app n = (_root_.SheafOfModules.pushforward.{a} φ).map (g.app n) := rfl

/-- A homomorphism invertible in degree `n` pushes forward to one invertible in degree `n`. -/
instance UnitalHom.isIso_sitePushforward_app (g : UnitalHom A B) (n : ℤ) [IsIso (g.app n)] :
    IsIso ((g.sitePushforward φ).app n) :=
  inferInstanceAs (IsIso ((_root_.SheafOfModules.pushforward.{a} φ).map (g.app n)))

/-- When the pushforward of sheaves of modules reflects isomorphisms, a homomorphism of sheaves
of graded algebras whose pushforward is an isomorphism in degree `n` is an isomorphism in
degree `n`. -/
theorem UnitalHom.isIso_app_of_isIso_sitePushforward
    [(_root_.SheafOfModules.pushforward.{a} φ).ReflectsIsomorphisms]
    (g : UnitalHom A B) (n : ℤ) (h : IsIso ((g.sitePushforward φ).app n)) : IsIso (g.app n) :=
  have : IsIso ((_root_.SheafOfModules.pushforward.{a} φ).map (g.app n)) := h
  isIso_of_reflects_iso (g.app n) (_root_.SheafOfModules.pushforward.{a} φ)

/-- Invertibility in degree `n` of a homomorphism of sheaves of graded algebras and of its
pushforward are the same assertion, for a pushforward reflecting isomorphisms. -/
theorem UnitalHom.isIso_sitePushforward_app_iff
    [(_root_.SheafOfModules.pushforward.{a} φ).ReflectsIsomorphisms]
    (g : UnitalHom A B) (n : ℤ) : IsIso ((g.sitePushforward φ).app n) ↔ IsIso (g.app n) :=
  ⟨fun h => g.isIso_app_of_isIso_sitePushforward φ n h,
    fun h => have := h; g.isIso_sitePushforward_app φ n⟩

end SheafOfModules.GradedAlgebra

end
