module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.CategoricalModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FibredHomToSpaceExt
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Uniform categorical moduli spaces are detected on affine flat base changes (Stacks 0DUJ)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from a category fibred in groupoids over the big fppf site of a
scheme `S` to the category attached to an algebraic space `Y`. **Stacks 0DUJ** says that if every
base change of `f` along a flat morphism to `Y` from an *affine* scheme is a categorical moduli
space, then `f` is a *uniform* categorical moduli space: the same holds after every flat base
change whatever.

## Main definitions

* `AlgebraicGeometry.Stack.presheafBaseChangeSquare`: the canonical base change of a 1-morphism
  along a map of presheaves.
* `AlgebraicGeometry.Stack.baseChangeSquareOfComp`: a base change along a composite `b ≫ a`, read
  as a 2-commutative square over `a`.

## Main results

* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_affineFlatBaseChange`:
  **Stacks 0DUJ**.
* `AlgebraicGeometry.Stack.section_eq_of_chart_factorization` and
  `AlgebraicGeometry.Stack.chart_eq_of_factorization`: the existence and the uniqueness half of
  the universal property, each localized to one affine étale chart of the base.

## Implementation notes

The source assumes `𝒳` is an algebraic stack, but its argument uses nothing of `𝒳` beyond being
fibred in groupoids: all the covering data is taken from an étale atlas of the *target* algebraic
space. The statement is therefore made at that generality, and applies to algebraic stacks by
restriction.

Given a flat `a : Y' ⟶ Y` and a 1-morphism `g` out of the base change, the morphism `Y' ⟶ W` that
factors `g` is built on the affine étale charts of `Y'` and glued: over an affine chart
`b : T ⟶ Y'` the composite `b ≫ a` is flat (`AlgebraicGeometry.Space.isFlat_comp_of_etale_chart`),
so the hypothesis applies and produces a factorization there, these factorizations are compatible
with restriction along morphisms of charts
(`AlgebraicGeometry.Stack.categoricalFactorization_baseChange_naturality`), and
`AlgebraicGeometry.Space.exists_hom_of_chartHoms` glues them over a surjective étale atlas of
`Y'`. That the glued morphism does factor `g` is checked at each object of the base change lying
over a chart (`AlgebraicGeometry.Stack.section_eq_of_chart_factorization`, assembled by
`AlgebraicGeometry.Stack.hom_ext_of_atlas_charts`), and that it is the only one that does is
checked chart by chart (`AlgebraicGeometry.Stack.chart_eq_of_factorization`).

The base change along a flat morphism is an arbitrary 2-fibre product of the cospan, so the
argument is run on the canonical one
(`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`) and transported by
`AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_isTwoFibreProduct`. Comparing the base change
along `b ≫ a` with the one along `a` is what
`AlgebraicGeometry.Stack.baseChangeSquareOfComp` is for: it reads a 2-commutative square over the
composite as one over `a`, by composing the first leg with the 1-morphism attached to `b`. This
uses that `AlgebraicGeometry.Stack.associatedMap` is functorial, which is
`AlgebraicGeometry.Stack.associatedMap_comp`.

The affine hypothesis is stated for a 2-fibre product of the cospan rather than for a chosen one,
so it is independent of any presentation of the base change — matching
`AlgebraicGeometry.Stack.IsUniformCategoricalModuliSpace` itself.

Inside the proof of the main theorem the base changes along `a` and along `b ≫ a`, and the
comparison 1-morphism between them, are **local** `let`-bound data rather than top-level
definitions, and deliberately so. Hoisting them makes the step that compares the factorization
over `b ≫ a` with the one over `r ≫ b ≫ a`
(`AlgebraicGeometry.Stack.categoricalFactorization_baseChange_naturality`) ask the elaborator to
unify `(yoneda.map r ≫ b) ≫ a.hom` with `yoneda.map r ≫ b ≫ a.hom` underneath a reducible
wrapper; the two 2-fibre-product terms are then unfolded on both sides and the unification does
not terminate within the default heartbeat budget. Kept local, the comparison happens on the
morphisms alone and is immediate. This is why the proof of the main theorem is longer than the
house limit: the two halves of the universal property are factored out, but the chart-local data
they consume has to be built where it stays opaque.

## References

* [Stacks Project, Tag 0DUJ](https://stacks.math.columbia.edu/tag/0DUJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reading a base change along a composite as one along the second factor -/

section BaseChangeSquare

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {F F' G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The canonical base change of a 1-morphism `f` to the category attached to `H` along a map
of presheaves `c : F ⟶ H`.** It is the 2-fibre product of the cospan in the 2-category of
categories fibred in groupoids, at the universe instantiation that 2-category is closed under.

This is a reducible abbreviation rather than a definition: every consumer below reads off its
apex and its two projections, and the proofs that transport a factorization across it need those
to compute. -/
abbrev presheafBaseChangeSquare (c : F ⟶ H) (f : 𝒳 ⟶ fibredCategory B S hS H) :
    Bicategory.TwoCommSq (associatedMap B S hS c).1 f :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (associatedMap B S hS c).1 f

/-- **A 2-commutative square over the 1-morphism attached to a composite `b ≫ a`, read as one
over the 1-morphism attached to `a`.** The apex and the second leg are unchanged; the first leg
is composed with the 1-morphism attached to `b`, and the filling 2-cell is the same one, since
`AlgebraicGeometry.Stack.associatedMap` is functorial. -/
def baseChangeSquareOfComp (a : G ⟶ H) (b : F ⟶ G) (f : 𝒳 ⟶ fibredCategory B S hS H)
    (Q : Bicategory.TwoCommSq (associatedMap B S hS (b ≫ a)).1 f) :
    Bicategory.TwoCommSq (associatedMap B S hS a).1 f where
  pt := Q.pt
  fst := Q.fst ≫ (associatedMap B S hS b).1
  snd := Q.snd
  iso := by
    change Q.fst ≫ ((associatedMap B S hS b).1 ≫ (associatedMap B S hS a).1) ≅ Q.snd ≫ f
    rw [← associatedMap_comp]
    exact Q.iso

/-- **Composing two comparison morphisms of base changes.** A pre-morphism of 2-commutative
squares from the base change along `r ≫ b ≫ a` to the one along `b ≫ a`, followed by one from the
base change along `b ≫ a` to a square over `a`, is a pre-morphism from the base change along
`r ≫ b ≫ a` read over `a`.

The compatibility square is automatic: its two sides are 2-morphisms of 1-morphisms into the
category attached to a presheaf of sets, between which there is at most one
(`AlgebraicGeometry.Stack.subsingleton_hom₂`). -/
def preHomOfBaseChangeSquareOfComp (a : G ⟶ H) (b : F ⟶ G) (r : F' ⟶ F)
    (f : 𝒳 ⟶ fibredCategory B S hS H)
    (P : Bicategory.TwoCommSq (associatedMap B S hS a).1 f)
    (Q : Bicategory.TwoCommSq (associatedMap B S hS (b ≫ a)).1 f)
    (Q' : Bicategory.TwoCommSq (associatedMap B S hS (r ≫ b ≫ a)).1 f)
    (N : Bicategory.TwoCommSq.PreHom
      (baseChangeSquareOfComp B S hS (b ≫ a) r f Q') Q)
    (L : Bicategory.TwoCommSq.PreHom (baseChangeSquareOfComp B S hS a b f Q) P) :
    Bicategory.TwoCommSq.PreHom (baseChangeSquareOfComp B S hS a (r ≫ b) f Q') P where
  hom := N.hom ≫ L.hom
  isoFst := by
    change Q'.fst ≫ (associatedMap B S hS (r ≫ b)).1 ≅ (N.hom ≫ L.hom) ≫ P.fst
    exact eqToIso (congrArg (fun k => Q'.fst ≫ k) (associatedMap_comp B S hS r b)) ≪≫
      Bicategory.whiskerRightIso N.isoFst (associatedMap B S hS b).1 ≪≫
      Bicategory.whiskerLeftIso N.hom L.isoFst
  isoSnd := N.isoSnd ≪≫ Bicategory.whiskerLeftIso N.hom L.isoSnd
  compat := (subsingleton_hom₂ B S hS _ _).elim _ _

/-- Along a pre-morphism `M` from the base change along `b ≫ a`, read over `a`, to `P`, the first
projection followed by the 1-morphism attached to `b ≫ m` is `M.hom ≫ P.fst ≫ associatedMap m`. -/
private def restrict_iso_of_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : G ⟶ H) (b : F ⟶ G)
    (m : G ⟶ W) (f : 𝒳 ⟶ fibredCategory B S hS H)
    (P : Bicategory.TwoCommSq (associatedMap B S hS a).1 f)
    (Q : Bicategory.TwoCommSq (associatedMap B S hS (b ≫ a)).1 f)
    (M : Bicategory.TwoCommSq.PreHom (baseChangeSquareOfComp B S hS a b f Q) P) :
    Q.fst ≫ (associatedMap B S hS (b ≫ m)).1 ≅ M.hom ≫ P.fst ≫ (associatedMap B S hS m).1 :=
  eqToIso (congrArg (fun z => Q.fst ≫ z) (associatedMap_comp B S hS b m)) ≪≫
    Bicategory.whiskerRightIso M.isoFst (associatedMap B S hS m).1

end BaseChangeSquare

/-! ### Compatibility of the factorizations across a composite base change -/

/-- **The factorizations over two nested base changes agree.** Let `a : G ⟶ H` be a morphism of
algebraic spaces, let `b : F ⟶ G` and `r : F' ⟶ F`, and let `P`, `Q`, `Q'` be 2-fibre products of
`f` along `a`, `b ≫ a` and `r ≫ b ≫ a`. If the factorization of `g` over `Q` is `k : F ⟶ W` and
the one over `Q'` is `k' : F' ⟶ W`, then `k' = r ≫ k`.

Only `Q'` is required to be a categorical moduli space: the conclusion is an identity of two
factorizations through its first projection. The comparison 1-morphisms are the mediating
morphisms into `P`, and the composite of the two mediating morphisms through `Q` agrees with the
direct one because `P` is a 2-fibre product. -/
theorem categoricalFactorization_baseChange_naturality
    {F F' G H W : AlgebraicSpaces B S hS}
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : G ⟶ H) (b : F ⟶ G) (r : F' ⟶ F)
    (f : 𝒳 ⟶ fibredCategory B S hS H.obj)
    (P : Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (Q : Bicategory.TwoCommSq (associatedMap B S hS (b.hom ≫ a.hom)).1 f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (Q' : Bicategory.TwoCommSq (associatedMap B S hS (r.hom ≫ b.hom ≫ a.hom)).1 f)
    (hQ' : IsCategoricalModuliSpace B S hS F' Q'.fst)
    (g : P.pt ⟶ fibredCategory B S hS W.obj) (k : F ⟶ W) (k' : F' ⟶ W)
    (hk : Nonempty (Q.fst ≫ (associatedMap B S hS k.hom).1 ≅
      (Bicategory.twoFibreProductPreHom hP
        (baseChangeSquareOfComp B S hS a.hom b.hom f Q)).hom ≫ g))
    (hk' : Nonempty (Q'.fst ≫ (associatedMap B S hS k'.hom).1 ≅
      (Bicategory.twoFibreProductPreHom hP
        (baseChangeSquareOfComp B S hS a.hom (r.hom ≫ b.hom) f Q')).hom ≫ g)) :
    r ≫ k = k' := by
  classical
  let L := Bicategory.twoFibreProductPreHom hP (baseChangeSquareOfComp B S hS a.hom b.hom f Q)
  let L' := Bicategory.twoFibreProductPreHom hP
    (baseChangeSquareOfComp B S hS a.hom (r.hom ≫ b.hom) f Q')
  let N := Bicategory.twoFibreProductPreHom hQ
    (baseChangeSquareOfComp B S hS (b.hom ≫ a.hom) r.hom f Q')
  obtain ⟨e, -⟩ := Bicategory.twoFibreProductPreHom_rel hP
    (preHomOfBaseChangeSquareOfComp B S hS a.hom b.hom r.hom f P Q Q' N L) L'
  exact categoricalFactorization_comp B S hS hQ' r N.hom (L.hom ≫ g) (L'.hom ≫ g)
    N.isoFst (Bicategory.whiskerRightIso e g) k k' hk hk'

/-! ### Objects of a base change visible in a chart -/

/-- **An object of the base change of `f` along `a` whose first component is carried by a chart
`b` of the source comes from the base change along `b ≫ a`.** The witness is the object of the
base change along `b ≫ a` with the same base and second component, and with the element of
`yoneda.obj T` given by the factorization `t` of the first component through the chart. -/
theorem exists_preimage_preHomTwoFibreProductSquare_obj
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ H) (f : 𝒳 ⟶ fibredCategory B S hS H)
    (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ F)
    (x : (presheafBaseChangeSquare B S hS a f).pt.val.obj) (t : x.base ⟶ T)
    (ht : sectionOfBasedFunctor (presheafBaseChangeSquare B S hS a f).fst.hom.toFunctor
      (presheafBaseChangeSquare B S hS a f).fst.hom.w x = b.app (Opposite.op x.base) t) :
    ∃ y : (presheafBaseChangeSquare B S hS (b ≫ a) f).pt.val.obj,
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a).1 f (baseChangeSquareOfComp B S hS a b f
          (presheafBaseChangeSquare B S hS (b ≫ a) f))).hom.hom.obj y = x := by
  have hfaith : (fibredCategory B S hS H).val.p.Faithful := faithful_discreteProjection
  let z : (fibredCategory B S hS (yoneda.obj T)).val.obj := ⟨x.base, Discrete.mk t⟩
  have hz : (associatedMap B S hS b).1.hom.obj z = x.x := by
    rw [associatedMap_obj]
    have he := obj_eq_mk_section B S hS (presheafBaseChangeSquare B S hS a f).fst x
    change x.x = ⟨x.base, Discrete.mk _⟩ at he
    rw [ht] at he
    exact he.symm
  have hza : (associatedMap B S hS (b ≫ a)).1.hom.obj z =
      (associatedMap B S hS a).1.hom.obj x.x := by
    rw [associatedMap_comp]
    show (associatedMap B S hS a).1.hom.obj ((associatedMap B S hS b).1.hom.obj z) = _
    rw [hz]
  refine ⟨⟨x.base, z, x.y, rfl, x.hy, eqToIso hza ≪≫ x.iso, ?_⟩,
    TwoFibreProductOver.obj_ext_of_faithful rfl hz rfl⟩
  have := x.vertical
  exact IsHomLift.comp_eqToHom_lift _ (𝟙 x.base) x.iso.hom hza

/-! ### The two halves of the universal property, chart by chart -/

section ChartFactorization

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {Y Y' W : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ fibredCategory B S hS Y.obj) (a : Y' ⟶ Y)
  (hP₀ : Bicategory.IsTwoFibreProduct (presheafBaseChangeSquare B S hS a.hom f))
  (g : (presheafBaseChangeSquare B S hS a.hom f).pt ⟶ fibredCategory B S hS W.obj)
  (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Y'.obj)
  (k : (schemeSpace T : AlgebraicSpaces B S hS) ⟶ W)
  (hk : Nonempty ((presheafBaseChangeSquare B S hS (b ≫ a.hom) f).fst ≫
      (associatedMap B S hS k.hom).1 ≅
    (Bicategory.twoFibreProductPreHom hP₀ (baseChangeSquareOfComp B S hS a.hom b f
      (presheafBaseChangeSquare B S hS (b ≫ a.hom) f))).hom ≫ g))

include hP₀ hk

/-- **A morphism out of `Y'` that restricts on the chart `b` to the factorization supplied there
factors `g` at every object of the base change visible in that chart.** The object comes from the
base change along `b ≫ a` by
`AlgebraicGeometry.Stack.exists_preimage_preHomTwoFibreProductSquare_obj`, and there the
factorization is the hypothesis `hk`, carried from the arbitrary comparison 1-morphism to the
explicit one along the 2-isomorphism between them. -/
theorem section_eq_of_chart_factorization (m : Y'.obj ⟶ W.obj) (hm : b ≫ m = k.hom)
    (x : (presheafBaseChangeSquare B S hS a.hom f).pt.val.obj) (t : x.base ⟶ T)
    (ht : sectionOfBasedFunctor (presheafBaseChangeSquare B S hS a.hom f).fst.hom.toFunctor
      (presheafBaseChangeSquare B S hS a.hom f).fst.hom.w x = b.app (Opposite.op x.base) t) :
    sectionOfBasedFunctor
        ((presheafBaseChangeSquare B S hS a.hom f).fst ≫
          (associatedMap B S hS m).1).hom.toFunctor
        ((presheafBaseChangeSquare B S hS a.hom f).fst ≫
          (associatedMap B S hS m).1).hom.w x =
      sectionOfBasedFunctor g.hom.toFunctor g.hom.w x := by
  classical
  let M := CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS a.hom).1 f
    (baseChangeSquareOfComp B S hS a.hom b f (presheafBaseChangeSquare B S hS (b ≫ a.hom) f))
  obtain ⟨y, hy⟩ := exists_preimage_preHomTwoFibreProductSquare_obj B S hS a.hom f T b x t ht
  change M.hom.hom.obj y = x at hy
  obtain ⟨e, -⟩ := Bicategory.twoFibreProductPreHom_rel hP₀ M
    (Bicategory.twoFibreProductPreHom hP₀ (baseChangeSquareOfComp B S hS a.hom b f
      (presheafBaseChangeSquare B S hS (b ≫ a.hom) f)))
  have he : M.hom ≫ ((presheafBaseChangeSquare B S hS a.hom f).fst ≫
      (associatedMap B S hS m).1) = M.hom ≫ g :=
    hom_eq_of_hom₂ B S hS
      ((restrict_iso_of_comp B S hS a.hom b m f _ _ M).symm ≪≫
        eqToIso (congrArg (fun z => (presheafBaseChangeSquare B S hS (b ≫ a.hom) f).fst ≫
          (associatedMap B S hS z).1) hm) ≪≫
        hk.some ≪≫ Bicategory.whiskerRightIso e.symm g).hom
  have hx := congrArg (fun z => z.hom.obj y) he
  change ((presheafBaseChangeSquare B S hS a.hom f).fst ≫
      (associatedMap B S hS m).1).hom.obj (M.hom.hom.obj y) =
    g.hom.obj (M.hom.hom.obj y) at hx
  rw [hy] at hx
  exact section_eq_of_obj_eq B S hS _ _ x hx

/-- **A morphism out of `Y'` that factors `g` agrees on the chart `b` with the factorization
supplied there.** Restricting it to the chart exhibits `b ≫ m` as a factorization of `g` over the
base change along `b ≫ a`, and that base change is assumed to be a categorical moduli space, so
the morphism factoring through it is unique. -/
theorem chart_eq_of_factorization
    (hc : IsCategoricalModuliSpace B S hS (schemeSpace T)
      (presheafBaseChangeSquare B S hS (b ≫ a.hom) f).fst)
    (m : Y'.obj ⟶ W.obj)
    (hm : (presheafBaseChangeSquare B S hS a.hom f).fst ≫ (associatedMap B S hS m).1 ≅ g) :
    b ≫ m = k.hom :=
  congrArg (fun z => z.hom) (eq_of_isCategoricalModuliSpace B S hS hc _
    (ObjectProperty.homMk (b ≫ m)) k
    ⟨restrict_iso_of_comp B S hS a.hom b m f _ _ (Bicategory.twoFibreProductPreHom hP₀
        (baseChangeSquareOfComp B S hS a.hom b f
          (presheafBaseChangeSquare B S hS (b ≫ a.hom) f))) ≪≫
      Bicategory.whiskerLeftIso _ hm⟩ hk)

end ChartFactorization

/-! ### The affine criterion -/

/-- **Stacks 0DUJ.** A 1-morphism from a category fibred in groupoids over the big fppf site of
`S` to the category attached to an algebraic space `Y` is a *uniform* categorical moduli space as
soon as every base change of it along a flat morphism to `Y` from an affine scheme is a
categorical moduli space.

The source states this for a 1-morphism from an algebraic stack; nothing of `𝒳` beyond being
fibred in groupoids is used, so it is stated here at that generality. -/
@[stacks 0DUJ]
theorem isUniformCategoricalModuliSpace_of_affineFlatBaseChange
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Y : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ fibredCategory B S hS Y.obj)
    (h : ∀ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ a : (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y,
        Space.IsFlat B S hS a.hom →
          ∀ P : Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 f,
            Bicategory.IsTwoFibreProduct P →
              IsCategoricalModuliSpace B S hS
                (schemeSpace T : AlgebraicSpaces B S hS)
                P.fst) :
    IsUniformCategoricalModuliSpace B S hS Y f := by
  classical
  intro Y' a ha P hP
  let P₀ := presheafBaseChangeSquare B S hS a.hom f
  have hP₀ : Bicategory.IsTwoFibreProduct P₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  refine isCategoricalModuliSpace_of_isTwoFibreProduct B S hS hP hP₀ ?_
  intro W g
  let A : BigFppfOver B S hS → AlgebraicSpaces B S hS :=
    fun T => schemeSpace T
  let Q : ∀ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Y'.obj),
      Bicategory.TwoCommSq (associatedMap B S hS (b ≫ a.hom)).1 f :=
    fun T b => presheafBaseChangeSquare B S hS (b ≫ a.hom) f
  have hQ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Y'.obj) :
      Bicategory.IsTwoFibreProduct (Q T b) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  let L : ∀ (T : BigFppfOver B S hS) (b : yoneda.obj T ⟶ Y'.obj),
      Bicategory.TwoCommSq.PreHom (baseChangeSquareOfComp B S hS a.hom b f (Q T b)) P₀ :=
    fun T b => Bicategory.twoFibreProductPreHom hP₀
      (baseChangeSquareOfComp B S hS a.hom b f (Q T b))
  have hc (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (b : yoneda.obj T ⟶ Y'.obj) (hb : Space.IsEtale B S hS b) :
      IsCategoricalModuliSpace B S hS (A T) (Q T b).fst :=
    h T hT (ObjectProperty.homMk (b ≫ a.hom))
      (Space.isFlat_comp_of_etale_chart B S hS Y'.property Y.property b
        ((Space.isEtale_iff_presheaf_of_yoneda B S hS b).1 hb) a.hom ha) (Q T b) (hQ T b)
  let k : ∀ (T : BigFppfOver B S hS), IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ Y'.obj, Space.IsEtale B S hS b → (A T ⟶ W) :=
    fun T hT b hb => (hc T hT b hb W ((L T b).hom ≫ g)).choose
  have hk (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (b : yoneda.obj T ⟶ Y'.obj) (hb : Space.IsEtale B S hS b) :
      Nonempty ((Q T b).fst ≫ (associatedMap B S hS (k T hT b hb).hom).1 ≅
        (L T b).hom ≫ g) := (hc T hT b hb W ((L T b).hom ≫ g)).choose_spec.1
  have knat (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ Y'.obj)
      (hb : Space.IsEtale B S hS b) (hrb : Space.IsEtale B S hS (yoneda.map r ≫ b)) :
      yoneda.map r ≫ (k U hU b hb).hom = (k T hT (yoneda.map r ≫ b) hrb).hom :=
    congrArg (fun z => z.hom) (categoricalFactorization_baseChange_naturality B S hS a
      (ObjectProperty.homMk b : A U ⟶ Y') (ObjectProperty.homMk (yoneda.map r) : A T ⟶ A U)
      f P₀ hP₀ (Q U b) (hQ U b) (Q T (yoneda.map r ≫ b)) (hc T hT _ hrb) g
      (k U hU b hb) (k T hT (yoneda.map r ≫ b) hrb) (hk U hU b hb) (hk T hT _ hrb))
  obtain ⟨U, b, hsurj, hb⟩ := Y'.property.exists_atlas
  have hbE : Space.IsEtale B S hS b := (Space.isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  obtain ⟨l, hl⟩ := Space.exists_hom_of_chartHoms B S hS W.property.isSheaf
    (fun T hT b hb => (k T hT b hb).hom) knat Y'.property.isSheaf U b hbE hsurj
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS U
  have hbi (i : I) : Space.IsEtale B S hS (yoneda.map (π i) ≫ b) :=
    Space.isEtale_comp B S hS (hπ i) hbE
  refine ⟨ObjectProperty.homMk l, ⟨eqToIso ?_⟩, ?_⟩
  · exact hom_ext_of_atlas_charts B S hS W.property.isSheaf P₀.fst _ _ U b hb hsurj V π hcover
      fun i x t ht => section_eq_of_chart_factorization B S hS f a hP₀ g (V i) _
        (k (V i) (hV i) _ (hbi i)) (hk (V i) (hV i) _ (hbi i)) l
        (hl (V i) (hV i) (π i) (hbi i)) x t ht
  · rintro l' ⟨hl'⟩
    refine ObjectProperty.hom_ext _ (Space.hom_ext_of_etale_atlas B S hS Y'.property.isSheaf
      W.property.isSheaf b hsurj hb (Space.hom_ext_of_cover B S hS W.property.isSheaf U V π hcover
        fun i => ?_))
    show yoneda.map (π i) ≫ b ≫ l'.hom = yoneda.map (π i) ≫ b ≫ l
    rw [hl (V i) (hV i) (π i) (hbi i), ← Category.assoc]
    exact chart_eq_of_factorization B S hS f a hP₀ g (V i) _ (k (V i) (hV i) _ (hbi i))
      (hk (V i) (hV i) _ (hbi i)) (hc (V i) (hV i) _ (hbi i)) l'.hom hl'

end AlgebraicGeometry.Stack

end
