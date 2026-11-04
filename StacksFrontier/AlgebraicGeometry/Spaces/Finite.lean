module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Finite and integral morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *finite*, respectively *integral*,
when its base change along every morphism from an affine scheme is represented by an
affine scheme which is finite, respectively integral, over that test scheme.

## Main definitions

* `AlgebraicGeometry.Space.IsFinite` is the finite-morphism property for algebraic spaces.
* `AlgebraicGeometry.Space.IsIntegralHom` is the integral-morphism property for algebraic
  spaces.

## Main results

* `AlgebraicGeometry.Space.exists_affine_pullback_comp_of_isIntegralHom` and
  `AlgebraicGeometry.Space.exists_affine_pullback_comp_of_isFinite`: an affine test of two
  successive integral, respectively finite, morphisms has compatible affine representatives,
  Cartesian over both the intermediate and the final target.
* `AlgebraicGeometry.Space.isIntegralHom_comp` and `AlgebraicGeometry.Space.isFinite_comp`:
  integral and finite morphisms of algebraic spaces are stable under composition.

## References

* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces over `S` is *finite* when, for every object `U` of the big fppf
site with affine underlying scheme and every morphism `ξ` from `yoneda.obj U` to the target, the
base change of `f` along `ξ` is represented by an object `V` of the site with affine underlying
scheme whose projection to `U` is a finite morphism of schemes. -/
@[stacks 03ZP "finite_morphism"]
abbrev IsFinite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (U : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ (ξ : yoneda.obj U ⟶ Y),
      ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
        (i : yoneda.obj V ⟶ X),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback i (yoneda.map p) f ξ

/-- A morphism of algebraic spaces over `S` is *integral* when, for every object `Z` of the big
fppf site with affine underlying scheme and every morphism `g` from `yoneda.obj Z` to the target,
the base change of `f` along `g` is represented by an object `W` of the site with affine underlying
scheme whose projection to `Z` is an integral morphism of schemes. -/
@[stacks 03ZP "integral_morphism"]
abbrev IsIntegralHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ (Z : BigFppfOver B S hS),
    IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
    ∀ (g : yoneda.obj Z ⟶ G),
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ Z)
        (q : yoneda.obj W ⟶ F),
        IsPullback q (yoneda.map p) f g ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          _root_.AlgebraicGeometry.IsIntegralHom
            ((BigFppfOver.toScheme B S hS).map p)

/-! ### Composition -/

section Comp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An affine test of two successive integral morphisms of algebraic spaces has compatible
affine representatives: the base change of `g` along the test is represented by an affine `V`
integral over the test scheme, the base change of `f` along that representative is represented
by an affine `W` integral over `V`, and `W` represents the base change of `f ≫ g` along the
original test. -/
theorem exists_affine_pullback_comp_of_isIntegralHom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIntegralHom B S hS f) (hg : IsIntegralHom B S hS g)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (ξ : yoneda.obj T ⟶ Z) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (j : yoneda.obj V ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback j (yoneda.map p) g ξ ∧
        ∃ (W : BigFppfOver B S hS) (q : W ⟶ V) (i : yoneda.obj W ⟶ X),
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
            _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map q) ∧
            IsPullback i (yoneda.map q) f j ∧
            IsPullback i (yoneda.map (q ≫ p)) (f ≫ g) ξ := by
  obtain ⟨V, p, j, hVpb, hVaff, hp⟩ := hg T hT ξ
  obtain ⟨W, q, i, hWpb, hWaff, hq⟩ := hf V hVaff j
  refine ⟨V, p, j, hVaff, hp, hVpb, W, q, i, hWaff, hq, hWpb, ?_⟩
  simpa [Category.assoc] using hWpb.paste_vert hVpb

/-- An affine test of two successive finite morphisms of algebraic spaces has compatible
affine representatives, finite at each stage and Cartesian over both the intermediate and the
final target. -/
theorem exists_affine_pullback_comp_of_isFinite (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsFinite B S hS f) (hg : IsFinite B S hS g)
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (ξ : yoneda.obj T ⟶ Z) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (j : yoneda.obj V ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback j (yoneda.map p) g ξ ∧
        ∃ (W : BigFppfOver B S hS) (q : W ⟶ V) (i : yoneda.obj W ⟶ X),
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
            _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q) ∧
            IsPullback i (yoneda.map q) f j ∧
            IsPullback i (yoneda.map (q ≫ p)) (f ≫ g) ξ := by
  obtain ⟨V, p, j, hVaff, hp, hVpb⟩ := hg T hT ξ
  obtain ⟨W, q, i, hWaff, hq, hWpb⟩ := hf V hVaff j
  refine ⟨V, p, j, hVaff, hp, hVpb, W, q, i, hWaff, hq, hWpb, ?_⟩
  simpa [Category.assoc] using hWpb.paste_vert hVpb

/-- The composite of two integral morphisms of algebraic spaces over `S` is integral. -/
@[stacks 03ZR "integral", ega "II 6.1.5" "(ii) integral"]
theorem isIntegralHom_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsIntegralHom B S hS f) (hg : IsIntegralHom B S hS g) :
    IsIntegralHom B S hS (f ≫ g) := by
  intro T hT ξ
  obtain ⟨V, p, j, _, hp, _, W, q, i, hWaff, hq, _, hpb⟩ :=
    exists_affine_pullback_comp_of_isIntegralHom B S hS f g hf hg T hT ξ
  refine ⟨W, q ≫ p, i, hpb, hWaff, ?_⟩
  rw [Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ hq hp

/-- The composite of two finite morphisms of algebraic spaces over `S` is finite. -/
@[stacks 03ZR "finite", ega "II 6.1.5" "(ii) finite"]
theorem isFinite_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFinite B S hS f) (hg : IsFinite B S hS g) :
    IsFinite B S hS (f ≫ g) := by
  intro T hT ξ
  obtain ⟨V, p, j, _, hp, _, W, q, i, hWaff, hq, _, hpb⟩ :=
    exists_affine_pullback_comp_of_isFinite B S hS f g hf hg T hT ξ
  refine ⟨W, q ≫ p, i, hWaff, ?_, hpb⟩
  rw [Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ hq hp

end Comp

end AlgebraicGeometry.Space

end
