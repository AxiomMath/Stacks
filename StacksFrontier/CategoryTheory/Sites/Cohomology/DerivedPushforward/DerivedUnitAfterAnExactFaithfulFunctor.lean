module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Invertibility of a derived unit detected after an exact conservative functor

Let `F : A ⥤ B` be an additive functor out of a Grothendieck abelian category and let
`RF : D(A) ⥤ D(B)` be a right derived functor of `K(A) ⥤ D(B)` with unit `α`. Suppose the
square
`F ⋙ V ≅ U ⋙ F₀`
commutes up to isomorphism, where `U : A ⥤ A₀` and `V : B ⥤ B₀` are exact and `V` moreover
reflects isomorphisms, and let `α₀` be the unit of a right derived functor `RF₀` of
`K(A₀) ⥤ D(B₀)`.

Then `α` is invertible at a complex `K` as soon as `α₀` is invertible at `U K` and at `U I` for
every K-injective `I`. The argument is the standard one: choose the functorial K-injective
resolution `K ⟶ I` of Stacks 079P, so that `α` is invertible at `I` by Stacks 07A5; invertibility
of `α` at `K` is then equivalent, by naturality, to invertibility of `(F.mapHomotopyCategory _ ⋙
Qh).map s` for the image `s` of the resolution, and `V.mapDerivedCategory` reflects that. After
`V` the square turns the question into the same one downstairs, where the two hypotheses on `α₀`
answer it.

This is the reduction used in the proof of unbounded base change, Stacks 0FN7, for the forgetful
functor from modules to abelian sheaves: the derived direct image of a complex of modules may be
computed after forgetting the module structure.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`: the right derived unit
  is invertible at an object once the corresponding unit downstairs, after an exact functor
  reflecting isomorphisms, is invertible there and at the images of all K-injective complexes.

## References

* [Stacks Project, Tag 0FN7](https://stacks.math.columbia.edu/tag/0FN7)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.UnboundedComplexes

universe v₁ v₂ u₁ u₂
universe wA dA vA uA dB vB uB dA₀ vA₀ uA₀ dB₀ vB₀ uB₀

/-- Given a natural transformation `α : F ⟶ G` and a morphism `s : X ⟶ Y` along which `G` and
`α` at `Y` are already invertible, `α` is invertible at `X` exactly when `F.map s` is: both
conditions say that the naturality square at `s` has an invertible remaining edge. -/
private theorem isIso_app_iff_isIso_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (s : X ⟶ Y) [IsIso (α.app Y)]
    [IsIso (G.map s)] :
    IsIso (α.app X) ↔ IsIso (F.map s) := by
  rw [← isIso_comp_right_iff (α.app X) (G.map s), ← α.naturality, isIso_comp_right_iff]

/-- The unit of a right derived functor out of the unbounded homotopy category of a Grothendieck
abelian category is invertible at a complex `K` as soon as the corresponding unit downstairs,
after an exact functor `V` which reflects isomorphisms, is invertible at the image of `K` and at
the images of all K-injective complexes.

The hypotheses are those of the forgetful functor from `Mod(O)` to abelian sheaves in the proof
of Stacks 0FN7: the square `F ⋙ V ≅ U ⋙ F₀` of exact comparisons, and the knowledge of the
derived unit for `F₀`. -/
theorem isIso_rightDerivedUnit_of_forget
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wA} A]
      [HasDerivedCategory.{dA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
    {A₀ : Type uA₀} [Category.{vA₀} A₀] [Abelian A₀] [HasDerivedCategory.{dA₀} A₀]
    {B₀ : Type uB₀} [Category.{vB₀} B₀] [Abelian B₀] [HasDerivedCategory.{dB₀} B₀]
    (F : A ⥤ B) (F₀ : A₀ ⥤ B₀) (U : A ⥤ A₀) (V : B ⥤ B₀)
    [F.Additive] [F₀.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] [V.ReflectsIsomorphisms]
    (e : F ⋙ V ≅ U ⋙ F₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RF₀ : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (α₀ : F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF₀)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hU : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α₀.app ((U.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))))
    (K : CochainComplex A ℤ)
    (hK : IsIso (α₀.app ((U.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj K
  let s := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K)
  have hs : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact inferInstanceAs
      (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))
  have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh _ s hs
  have : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
    isIso_app_of_isKInjective _ DerivedCategory.Qh RF α I inferInstance
  have : IsIso ((DerivedCategory.Qh ⋙ RF).map s) :=
    inferInstanceAs (IsIso (RF.map (DerivedCategory.Qh.map s)))
  refine (isIso_app_iff_isIso_map α s).2 ?_
  have hV : IsIso (V.mapDerivedCategory.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s)) := by
    let eH := Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
        V.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (U ⋙ F₀))
            (ComplexShape.up ℤ)).symm)
        DerivedCategory.Qh
    refine (NatIso.isIso_map_iff eH s).2 ?_
    have hq : IsIso ((U.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s) :=
      (NatIso.isIso_map_iff U.mapDerivedCategoryFactorsh s).1
        (inferInstanceAs (IsIso (U.mapDerivedCategory.map (DerivedCategory.Qh.map s))))
    have : IsIso ((DerivedCategory.Qh ⋙ RF₀).map
        ((U.mapHomotopyCategory (ComplexShape.up ℤ)).map s)) :=
      inferInstanceAs (IsIso (RF₀.map
        ((U.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s)))
    have := hU I inferInstance
    exact (isIso_app_iff_isIso_map α₀ ((U.mapHomotopyCategory (ComplexShape.up ℤ)).map s)).1 hK
  exact isIso_of_reflects_iso _ V.mapDerivedCategory

end Stacks.Cohomology.UnboundedComplexes

end
