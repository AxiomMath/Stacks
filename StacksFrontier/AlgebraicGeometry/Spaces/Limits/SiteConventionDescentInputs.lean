module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Limit descent of algebraic spaces under the site convention: the statements

This file states, as propositions and without proof, five results of the chapter "Limits of
Spaces" in the form in which they hold under the chapter's standing convention of Section 70.2
(tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, with no bound on the size of
the index:

* `AlgebraicGeometry.Space.ModelsDescendUnderConvention`,
  `AlgebraicGeometry.Space.MorphismsDescendUnderConvention` and
  `AlgebraicGeometry.Space.EqualitiesDescendUnderConvention`: the three parts of Stacks 07SK
  (essential surjectivity, fullness and faithfulness of base change from the colimit of the
  categories of algebraic spaces of finite presentation over the stages);
* `AlgebraicGeometry.Space.PropertyDescendsUnderConvention`: the shape shared by Stacks 08K0
  (flatness, for `f₀` locally of finite presentation) and Stacks 08K1 (properness, for `f₀`
  locally of finite type), read for a morphism whose target is the distinguished stage of the
  system.

They are the statements of the chapter's theorems, in the namespace `AlgebraicGeometry.Space`,
`exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits`,
`exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits`,
`eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits`,
`MorphismDescentSituation.exists_isFlat_mapAt_of_siteContainsBaseChangeLimits` and
`MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`, the first three
with the algebraicity of the limit supplied by Stacks 07SF under the convention and the last two
specialised to the case `Y₀ = B₀`, `Y₀ ⟶ B₀ = 𝟙` of Situation 084W.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The statement of Stacks 07SK, essential surjectivity, under the site convention.** For a
cofiltered inverse system of quasi-compact, quasi-separated algebraic spaces over `S` with affine
transition morphisms satisfying the convention of Section 70.2 (tag 07SD), every algebraic space
of finite presentation over the limit is the base change of one of finite presentation over a
stage. -/
def ModelsDescendUnderConvention : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
    (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
    (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
    (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
    SiteContainsBaseChangeLimits B S hS D →
    ∀ (Y : Over (limit D)), IsAlgebraicSpace B S hS Y.left →
      IsFinitePresentation B S hS Y.hom →
      ∃ (i : I) (Yᵢ : Over (D.obj i)),
        IsAlgebraicSpace B S hS Yᵢ.left ∧ IsFinitePresentation B S hS Yᵢ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ)

/-- **The statement of Stacks 07SK, fullness, under the site convention.** In the situation of
`AlgebraicGeometry.Space.ModelsDescendUnderConvention`, a morphism between the base changes to
the limit of two algebraic spaces of finite presentation over a stage comes from a morphism at a
later stage, the comparison isomorphisms being the canonical base-change comparisons. -/
def MorphismsDescendUnderConvention : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
    (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
    (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
    (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
    SiteContainsBaseChangeLimits B S hS D →
    ∀ (i : I) (Yᵢ Zᵢ : Over (D.obj i)),
      IsAlgebraicSpace B S hS Yᵢ.left → IsAlgebraicSpace B S hS Zᵢ.left →
      IsFinitePresentation B S hS Yᵢ.hom → IsFinitePresentation B S hS Zᵢ.hom →
      ∀ (f : (Over.pullback (limit.π D i)).obj Yᵢ ⟶ (Over.pullback (limit.π D i)).obj Zᵢ),
      ∃ (j : I) (e : j ⟶ i)
        (g : (Over.pullback (D.map e)).obj Yᵢ ⟶ (Over.pullback (D.map e)).obj Zᵢ)
        (α : (Over.pullback (limit.π D j)).obj ((Over.pullback (D.map e)).obj Yᵢ) ≅
          (Over.pullback (limit.π D i)).obj Yᵢ)
        (β : (Over.pullback (limit.π D j)).obj ((Over.pullback (D.map e)).obj Zᵢ) ≅
          (Over.pullback (limit.π D i)).obj Zᵢ),
        (α.hom.left ≫ pullback.fst Yᵢ.hom (limit.π D i) =
          pullback.fst ((Over.pullback (D.map e)).obj Yᵢ).hom (limit.π D j) ≫
            pullback.fst Yᵢ.hom (D.map e)) ∧
        (β.hom.left ≫ pullback.fst Zᵢ.hom (limit.π D i) =
          pullback.fst ((Over.pullback (D.map e)).obj Zᵢ).hom (limit.π D j) ≫
            pullback.fst Zᵢ.hom (D.map e)) ∧
        α.hom ≫ f = (Over.pullback (limit.π D j)).map g ≫ β.hom

/-- **The statement of Stacks 07SK, faithfulness, under the site convention.** In the situation
of `AlgebraicGeometry.Space.ModelsDescendUnderConvention`, two morphisms of algebraic spaces of
finite presentation over a stage whose base changes to the limit agree already agree after base
change to a later stage. -/
def EqualitiesDescendUnderConvention : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
    (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) →
    (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
    (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
    SiteContainsBaseChangeLimits B S hS D →
    ∀ (i : I) (Yᵢ Zᵢ : Over (D.obj i)),
      IsAlgebraicSpace B S hS Yᵢ.left → IsAlgebraicSpace B S hS Zᵢ.left →
      IsFinitePresentation B S hS Yᵢ.hom → IsFinitePresentation B S hS Zᵢ.hom →
      ∀ (f g : Yᵢ ⟶ Zᵢ),
        (Over.pullback (limit.π D i)).map f = (Over.pullback (limit.π D i)).map g →
        ∃ (j : I) (e : j ⟶ i), (Over.pullback (D.map e)).map f = (Over.pullback (D.map e)).map g

/-- **The shape of Stacks 08K0 (flatness) and 08K1 (properness) under the site convention,** for a
morphism to the distinguished stage. Let `(B_i)` be a directed inverse system of algebraic spaces
over `S` with affine transition morphisms and algebraic limit `B` satisfying the convention of
Section 70.2 (tag 07SD), let `i₀` be a stage with `B_{i₀}` quasi-compact and quasi-separated, and
let `f₀ : X₀ ⟶ B_{i₀}` be a morphism from a quasi-compact quasi-separated algebraic space with
`H f₀`. If the base change `X₀ ×_{B_{i₀}} B ⟶ B` has `P`, so does the base change
`X₀ ×_{B_{i₀}} B_i ⟶ B_i` for some `i ≥ i₀`.

For `P` flatness and `H` local finite presentation this is Stacks 08K0 in the case `Y₀ = B₀`
of Situation 084W; for `P` properness and `H` local finite type it is Stacks 08K1 in that case. -/
def PropertyDescendsUnderConvention
    (P : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
    (H : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (base : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
    (∀ i : I, IsAlgebraicSpace B S hS (base.obj (op i))) →
    (∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a)) →
    IsAlgebraicSpace B S hS (limit base) →
    SiteContainsBaseChangeLimits B S hS base →
    ∀ (i₀ : I) (X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f₀ : X₀ ⟶ base.obj (op i₀)),
      IsAlgebraicSpace B S hS X₀ →
      IsQuasiCompactSpace B S hS (base.obj (op i₀)) →
      IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op i₀)) →
      IsQuasiCompactSpace B S hS X₀ → IsAbsolutelyQuasiSeparated B S hS hZ X₀ →
      P (pullback.fst (limit.π base (op i₀)) f₀) → H f₀ →
      ∃ (i : I) (hi : i₀ ≤ i), P (pullback.fst (base.map (homOfLE hi).op) f₀)

end AlgebraicGeometry.Space

end
