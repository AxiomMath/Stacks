module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.CategoryTheory.Adjunction.TransposeConjugate
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison

/-!
# Changing the factorization a transpose of modules is taken along

Let `a ≫ b = c ≫ e` be a commuting square of schemes with the same source `W` and the same
target `Z`. A morphism `u : M ⟶ b_* a_* V` has an inverse adjoint transpose along the composite
adjunction `adj_b.comp adj_a`, a morphism `a^* b^* M ⟶ V`. The *other* factorization offers the
composite adjunction `adj_e.comp adj_c`, whose transposes come out of `c^* e^* M`. This file
identifies the first transpose with the second: they differ by the pseudofunctoriality
isomorphisms of the two factorizations, by the comparison of the pushforwards along the two
equal composites, and by nothing else.

The point of the identification is that only one of the two factorizations is usually the one a
criterion is stated for. In the case this file is written for, `b` is `AlgebraicGeometry.Proj.map`
of a graded ring homomorphism and `a` the chart `AlgebraicGeometry.Proj.awayι` of the source,
while `c` is `Spec.map` of the chart ring homomorphism and `e` the chart of the target: the second
factorization starts with a morphism of literal affine spectra, which is what the affine
invertibility criterion consumes, and the first is the one the comparison map is built from.

## Main results

* `Stacks.TransposeFactorization.homEquiv_symm_pushforwardCongr` and
  `Stacks.TransposeFactorization.homEquiv_symm_pushforwardComp`: the two instances of
  `CategoryTheory.homEquiv_symm_conjugateEquiv` that the square needs, namely for equal morphisms
  of schemes and for a composite morphism against the composite of the adjunctions.
* `Stacks.TransposeFactorization.homEquiv_symm_comp_eq`: **the identification.**

## Implementation notes

The conjugations are never computed by hand. Each is read off an existing characterisation —
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` through
`Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom` for a composite, and
`Stacks.TransposeFactorization.conjugateEquiv_pullbackCongr_inv` for equal morphisms, which is
proved by substituting the equality, where `AlgebraicGeometry.Scheme.Modules.pullbackCongr` is
`CategoryTheory.eqToIso` of a reflexivity and so is the identity on the nose.

No adjunction is ever rewritten along the equality `a ≫ b = c ≫ e`. Rewriting inside the type of
an adjunction fails on the dependent motive, since the adjunction's statement mentions the
morphism in both of its functors; the equality enters only through
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, which are morphisms and not types.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Stacks.TransposeFactorization

/-! ### The two conjugations the square needs -/

section Schemes

universe u

/-- **The conjugate of the inverse-image comparison of equal morphisms is the direct-image
comparison.** Both `AlgebraicGeometry.Scheme.Modules.pullbackCongr` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` are the comparison of the functors of two
equal morphisms of schemes, and they correspond under
`CategoryTheory.conjugateEquiv`.

Substituting the equality reduces this to `CategoryTheory.conjugateEquiv_id`, the inverse-image
comparison at a reflexivity being the identity on the nose. -/
public theorem conjugateEquiv_pullbackCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction g)
        (pullbackCongr h).inv =
      (pushforwardCongr h).hom := by
  subst h
  rw [show (pullbackCongr (rfl : f = f)).inv = 𝟙 _ from rfl, conjugateEquiv_id]
  ext M U
  simp

/-- **The inverse adjoint transposes along two equal morphisms of schemes differ by the
direct-image comparison.** For `u : M ⟶ f_* N` and `h : f = g`, the transpose along `g` of `u`
followed by the comparison `g_* ≅ f_*` is the transpose along `f` of `u`, preceded by the
comparison of the inverse images.

This is `CategoryTheory.homEquiv_symm_conjugateEquiv` at
`Stacks.TransposeFactorization.conjugateEquiv_pullbackCongr_inv`. -/
public theorem homEquiv_symm_pushforwardCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (N : X.Modules) (u : M ⟶ (pushforward f).obj N) :
    ((pullbackPushforwardAdjunction g).homEquiv M N).symm
        (u ≫ (pushforwardCongr h).hom.app N) =
      (pullbackCongr h).inv.app M ≫
        ((pullbackPushforwardAdjunction f).homEquiv M N).symm u := by
  rw [← conjugateEquiv_pullbackCongr_inv h]
  exact homEquiv_symm_conjugateEquiv _ _ _ u

/-- **The inverse adjoint transpose along a composite morphism is the transpose along the
composite adjunction.** For `u : M ⟶ (a ≫ b)_* N`, the transpose along `adj_b.comp adj_a` of `u`
followed by the comparison `(a ≫ b)_* ≅ b_* ∘ a_*` is the transpose along the adjunction of
`a ≫ b`, preceded by the comparison of the inverse images.

This is `CategoryTheory.homEquiv_symm_conjugateEquiv` at
`Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom`. -/
public theorem homEquiv_symm_pushforwardComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules) (u : M ⟶ (pushforward (a ≫ b)).obj N) :
    (((pullbackPushforwardAdjunction b).comp
          (pullbackPushforwardAdjunction a)).homEquiv M N).symm
        (u ≫ (pushforwardComp a b).inv.app N) =
      (pullbackComp a b).hom.app M ≫
        ((pullbackPushforwardAdjunction (a ≫ b)).homEquiv M N).symm u := by
  rw [← Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom a b]
  exact homEquiv_symm_conjugateEquiv _ _ _ u

/-! ### The identification -/

/-- **An inverse adjoint transpose taken along one factorization of a morphism of schemes, read
along another.** For a commuting square `a ≫ b = c ≫ e` of schemes and `u : M ⟶ b_* a_* V`, the
transpose of `u` along `adj_b.comp adj_a` is the transpose along `adj_e.comp adj_c` of `u`
followed by the three comparisons of direct images, preceded by the three comparisons of inverse
images.

Both sides are read through the adjunction of the common composite, which is what keeps the
equality `a ≫ b = c ≫ e` out of the type of any adjunction. -/
public theorem homEquiv_symm_comp_eq {W Y Y' Z : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ Z)
    (c : W ⟶ Y') (e : Y' ⟶ Z) (hm : a ≫ b = c ≫ e) (M : Z.Modules) (V : W.Modules)
    (u : M ⟶ (pushforward b).obj ((pushforward a).obj V)) :
    (((pullbackPushforwardAdjunction b).comp
          (pullbackPushforwardAdjunction a)).homEquiv M V).symm u =
      (pullbackComp a b).hom.app M ≫ (pullbackCongr hm).hom.app M ≫
        (pullbackComp c e).inv.app M ≫
          (((pullbackPushforwardAdjunction e).comp
                (pullbackPushforwardAdjunction c)).homEquiv M V).symm
            (u ≫ (pushforwardComp a b).hom.app V ≫ (pushforwardCongr hm).hom.app V ≫
              (pushforwardComp c e).inv.app V) := by
  have e1 : (((pullbackPushforwardAdjunction b).comp
        (pullbackPushforwardAdjunction a)).homEquiv M V).symm u =
      (pullbackComp a b).hom.app M ≫
        ((pullbackPushforwardAdjunction (a ≫ b)).homEquiv M V).symm
          (u ≫ (pushforwardComp a b).hom.app V) := by
    have h := homEquiv_symm_pushforwardComp a b M V (u ≫ (pushforwardComp a b).hom.app V)
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] at h
    exact h
  have e2 := homEquiv_symm_pushforwardCongr hm M V (u ≫ (pushforwardComp a b).hom.app V)
  have e3 := homEquiv_symm_pushforwardComp c e M V
    ((u ≫ (pushforwardComp a b).hom.app V) ≫ (pushforwardCongr hm).hom.app V)
  rw [e2] at e3
  simp only [Category.assoc] at e3 ⊢
  rw [e1, e3]
  simp

end Schemes

end Stacks.TransposeFactorization

end
