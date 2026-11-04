module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq

/-!
# Relative smoothness from relative étaleness, and the étale presentation of a DM stack

A relatively étale 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme is relatively smooth. The étale charts of a 2-fibre product give diagrams whose comparison
1-morphisms are étale, and a Deligne–Mumford algebraic stack has a surjective étale presentation
by a scheme in the relative vocabulary of `AlgebraicGeometry.Stack.IsRelativelyEtale` and
`AlgebraicGeometry.Stack.IsSurjectiveOnObjects`.

## Main results

* `AlgebraicGeometry.Stack.isRelativelySmooth_of_isRelativelyEtale`: a relatively étale
  1-morphism is relatively smooth.
* `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_diagramCone_of_chart`: the comparison
  1-morphisms of the diagram `AlgebraicGeometry.Stack.diagramCone` cut out by an étale chart of a
  2-fibre product are themselves étale.
* `AlgebraicGeometry.Stack.exists_etalePresentation_of_isDeligneMumfordStack`: a Deligne–Mumford
  algebraic stack admits a relatively étale 1-morphism from a scheme which is surjective on
  objects.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A relatively étale 1-morphism of categories fibred in groupoids over the big fppf site of `S`
is relatively smooth. -/
theorem isRelativelySmooth_of_isRelativelyEtale
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRelativelyEtale B S hS f) : IsRelativelySmooth B S hS f :=
  ⟨hf.1, fun U y hy F hF he =>
    Space.isSmooth_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) (hf.2 U y hy F hF he)⟩

/-- **The comparison 1-morphisms of a diagram whose source is an étale chart of a 2-fibre product
are étale.** Let `Q₁` be a 2-fibre product of the cospan `(b, f)`, let `cc` be an étale
1-morphism from a category of elements into its apex, and consider the diagram `cc` defines: its
left vertical 1-morphism is `cc` followed by the projection to the source of `f`, its top
horizontal morphism of algebraic spaces is a morphism inducing `cc` followed by the other
projection, and its 2-cell is the filler of `Q₁` whiskered by `cc`. Then every comparison
1-morphism from that diagram to every 2-fibre product of `(b, f)` is étale. -/
theorem isRelativelyEtale_preHom_diagramCone_of_chart
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : fibredCategory B S hS V ⟶ 𝒴)
    (Q₁ : Bicategory.TwoCommSq b f) (hQ₁ : Bicategory.IsTwoFibreProduct Q₁)
    (cc : fibredCategory B S hS U ⟶ Q₁.pt) (hcc : IsRelativelyEtale B S hS cc)
    (h : U ⟶ V) (e : (associatedMap B S hS h).1 ≅ cc ≫ Q₁.fst)
    (Q : Bicategory.TwoCommSq b f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS f (cc ≫ Q₁.snd) b h
        (Bicategory.whiskerRightIso e b ≪≫ Bicategory.whiskerLeftIso cc Q₁.iso)) Q) :
    IsRelativelyEtale B S hS k.hom := by
  refine isRelativelyEtale_preHom_of_preHom B S hS hQ₁ hQ
    (CatFiberedInGroupoids.preHomOfStrict.{u, u, u + 1, u + 1}
      (T := diagramCone B S hS f (cc ≫ Q₁.snd) b h
        (Bicategory.whiskerRightIso e b ≪≫ Bicategory.whiskerLeftIso cc Q₁.iso))
      (S := Q₁) cc e (Iso.refl _) ?_) k hcc
  simp only [Iso.refl_hom, Bicategory.id_whiskerRight, Category.comp_id]
  rfl

/-- A Deligne–Mumford algebraic stack over `S` admits a scheme of the site with a relatively étale
1-morphism onto it which is surjective on objects. -/
theorem exists_etalePresentation_of_isDeligneMumfordStack
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒜 : IsDeligneMumfordStack.{u, w} B S hS 𝒜.val) :
    ∃ (W : BigFppfOver B S hS) (pres : schemeFibredCategory B S hS W ⟶ 𝒜),
      IsRelativelyEtale B S hS pres ∧
      IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p 𝒜.val.p
        (CatFiberedInGroupoids.homFunctor pres) := by
  obtain ⟨-, hex⟩ := h𝒜
  obtain ⟨h𝒜fib, W, pres₀, hrep, hprop⟩ := hex
  set pres : schemeFibredCategory B S hS W ⟶ 𝒜 :=
    Bicategory.InducedBicategory.mkHom pres₀.hom with hpresDef
  have hrep' : IsRepresentableByAlgebraicSpaces B S hS pres.hom := hrep
  refine ⟨W, pres, ⟨hrep', fun U y hy F hF he => (hprop U y hy F hF he).2⟩, ?_⟩
  exact (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
    pres hrep').2 (fun U y hy F hF he => (hprop U y hy F hF he).1)

end AlgebraicGeometry.Stack

end
