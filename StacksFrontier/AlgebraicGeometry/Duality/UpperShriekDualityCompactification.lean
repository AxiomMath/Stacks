module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekProper

/-!
# The duality formula of [Stacks, Tag 0AU2] through the tensor–internal-Hom bijection

Let `f : X ⟶ Y` be a morphism of `FTS_S`, `j` a compactification of `X` over `Y` with
`f̄ : X̄ ⟶ Y`, and `K` a dualizing complex on `Y`. Under the tensor–internal-Hom bijection of
[Stacks, Tag 08J8], the isomorphism `a(M) ≅ R𝓗om(Lf̄^* D_Y(M), a(K))` on `X̄` is the morphism
`a(M) ⊗ᴸ Lf̄^* D_Y(M) ⟶ a(K)` corresponding under `Rf̄_* ⊣ a` to the inverse projection formula
followed by the counit and the evaluation `M ⊗ᴸ D_Y(M) ⟶ K`; and the isomorphism
`f^! M ≅ D_X(Lf^* D_Y M)` of [Stacks, Tag 0AU2] is its restriction to `X`, through the
compatibility of the restriction of the derived internal Hom with the bijection
(`Stacks.Duality.TwistedInverseImageDuality.curry_pull_map_comp_pullSheafHomMap`).

These are the descriptions from which the comparison of [Stacks, Tag 0AU2] at two
compactifications is computed.

## Main results

* `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso_hom_app`: the isomorphism of
  [Stacks, Tag 0AU2] at an object, as a composite.
* `Stacks.Duality.UpperShriekDuality.curry_comp_comp_comp_comp`: the transpose of such a
  composite.
* `Stacks.Duality.UpperShriekDuality.curry_upperShriekDualityIso_hom_app`: the transpose of the
  isomorphism of [Stacks, Tag 0AU2] at an object, through the restriction of the duality
  isomorphism on the compactification.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- The tensor–internal-Hom bijection is natural in the target. -/
theorem curry_naturality_right (X : Scheme.{u}) (A B : Std X) {Z Z' : Std X} (z : Z ⟶ Z')
    (θ : A ⟶ ((sheafHom X).obj (op B)).obj Z) :
    curry X A B Z' (θ ≫ ((sheafHom X).obj (op B)).map z) = curry X A B Z θ ≫ z :=
  (tensorHomAdjunction X B).homEquiv_naturality_right_symm θ z

end Standard

section Formula

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsNoetherian Y] {K : Std Y} (hK : IsDualizing K)

end Formula

end Stacks.Duality.TwistedInverseImageDuality

namespace Stacks.Duality.UpperShriekDuality

open Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) {K : Std Y.left} (hK : IsDualizing K)

/-- The isomorphism of [Stacks, Tag 0AU2] at `M`: the comparison of the models, the restriction
of the duality isomorphism on the compactification, the restriction of the derived internal Hom,
`L(j^*) ∘ Lf̄^* = Lf^*` and the comparison of the models at `a(K)`. -/
theorem upperShriekDualityIso_hom_app (M : (plusCoh Y.left).FullSubcategory) :
    (upperShriekDualityIso f j hK).hom.app M =
      (pullModelConj j.immersion).hom.app _ ≫
        (pull j.immersion).map ((dualityIso j.toBase hK).hom.app M) ≫
        pullSheafHomMap j.immersion _ _ ≫
        ((sheafHom X.left).map ((pullCompIso j.immersion j.toBase f.left
          (immersion_comp_toBase f j)).inv.app _).op).app _ ≫
        ((sheafHom X.left).obj _).map ((pullModelConj j.immersion).app _).inv := by
  rw [upperShriekDualityIso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom, Category.id_comp,
    pullSheafHomIso_hom_app]
  rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Transposing `a ≫ r ≫ p ≫ R𝓗om(l, Z) ≫ R𝓗om(B', z)` under the tensor–internal-Hom
bijection. -/
theorem curry_comp_comp_comp_comp {Z₀ : Scheme.{u}} {A A₁ A₂ B B' Z Z' : Std Z₀} (a : A ⟶ A₁)
    (r : A₁ ⟶ A₂) (p : A₂ ⟶ ((sheafHom Z₀).obj (op B)).obj Z) (l : B' ⟶ B) (z : Z ⟶ Z') :
    curry Z₀ A B' Z' (a ≫ r ≫ p ≫ ((sheafHom Z₀).map l.op).app Z ≫
        ((sheafHom Z₀).obj (op B')).map z) =
      (((tensor Z₀).map a).app B' ≫ ((tensor Z₀).obj A₁).map l) ≫ curry Z₀ A₁ B Z (r ≫ p) ≫ z := by
  have h : r ≫ p ≫ ((sheafHom Z₀).map l.op).app Z ≫ ((sheafHom Z₀).obj (op B')).map z =
      ((r ≫ p) ≫ ((sheafHom Z₀).map l.op).app Z) ≫ ((sheafHom Z₀).obj (op B')).map z := by
    simp only [Category.assoc]
  rw [curry_naturality_left, h, curry_naturality_right, curry_naturality_middle]
  simp only [Category.assoc]

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Transposing `a ≫ Lg^*θ ≫ (Lg^* R𝓗om ⟶ R𝓗om Lg^*) ≫ R𝓗om(l, -) ≫ R𝓗om(-, z)`. -/
theorem curry_restriction {A₀ B₀ : Scheme.{u}} (g : A₀ ⟶ B₀) [IsOpenImmersion g]
    {A : Std A₀} {W P Z : Std B₀} {B : Std A₀} {Z' : Std A₀}
    (a : A ⟶ (pull g).obj W) (θ : W ⟶ ((sheafHom B₀).obj (op P)).obj Z)
    (l : B ⟶ (pull g).obj P) (z : (pull g).obj Z ⟶ Z') :
    curry A₀ A B Z' (a ≫ (pull g).map θ ≫ pullSheafHomMap g P Z ≫
        ((sheafHom A₀).map l.op).app ((pull g).obj Z) ≫
        ((sheafHom A₀).obj (op B)).map z) =
      ((tensor A₀).map a).app B ≫ ((tensor A₀).obj ((pull g).obj W)).map l ≫
        (pullTensorIso g W P).inv ≫ (pull g).map (curry B₀ W P Z θ) ≫ z := by
  rw [curry_comp_comp_comp_comp, curry_pull_map_comp_pullSheafHomMap]
  simp only [Category.assoc]

/-- The transpose of the isomorphism of [Stacks, Tag 0AU2] at `M`, through the restriction of
the duality isomorphism on the compactification. -/
theorem curry_upperShriekDualityIso_hom_app (M : (plusCoh Y.left).FullSubcategory) :
    curry X.left ((upperShriekStd f j).obj M)
        ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
        (upperShriekDualizing f j hK) ((upperShriekDualityIso f j hK).hom.app M) =
      ((tensor X.left).map ((upperShriekStdIso f j).hom.app M)).app
          ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K)) ≫
        ((tensor X.left).obj ((pull j.immersion).obj
          ((rightAdjointStd j.toBase).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))).map
          ((pullCompIso j.immersion j.toBase f.left (immersion_comp_toBase f j)).inv.app
            (((sheafHom Y.left).obj (op M.obj)).obj K)) ≫
        (pullTensorIso j.immersion
          ((rightAdjointStd j.toBase).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
          ((pull j.toBase).obj (((sheafHom Y.left).obj (op M.obj)).obj K))).inv ≫
        (pull j.immersion).map (curry j.space
          ((rightAdjointStd j.toBase).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
          ((pull j.toBase).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
          ((rightAdjointStd j.toBase).obj (dualizingObject hK))
          ((dualityIso j.toBase hK).hom.app M)) ≫
        ((pullModelConj j.immersion).app
          ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv := by
  rw [upperShriekDualityIso_hom_app]
  exact curry_restriction (A₀ := X.left) j.immersion (A := (upperShriekStd f j).obj M)
    (W := (rightAdjointStd j.toBase).obj ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)
    (P := (pull j.toBase).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    (Z := (rightAdjointStd j.toBase).obj (dualizingObject hK))
    (B := (pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    (Z' := upperShriekDualizing f j hK) ((upperShriekStdIso f j).hom.app M)
    ((dualityIso j.toBase hK).hom.app M)
    ((pullCompIso j.immersion j.toBase f.left (immersion_comp_toBase f j)).inv.app
      (((sheafHom Y.left).obj (op M.obj)).obj K))
    ((pullModelConj j.immersion).app ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv

end Stacks.Duality.UpperShriekDuality

end
