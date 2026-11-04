module

public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinChart
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The base change of a full-subcategory inclusion along a chart by an algebraic space

Let `𝒳` be an algebraic stack over `S`, let `P` be a property of its objects inherited along
morphisms — `P b` and `a ⟶ b` give `P a` — and let `𝒲 ⊆ 𝒳` be the full subcategory it cuts out,
which is again fibred in groupoids. Let `U` be a presheaf on the big fppf site of `S` and let
`c : El U ⟶ 𝒳` be a 1-morphism out of its category of elements (**Stacks 0458**), that is, a
chart of `𝒳` by a presheaf rather than by a scheme-valued point.

This file identifies the 2-fibre product `El U ×_𝒳 𝒲` over the site: if a subfunctor `V ⊆ U`
cuts out exactly the sections at which `P` holds, then `El U ×_𝒳 𝒲` is equivalent, over the big
fppf site of `S`, to the category of elements of `V`. The identification is transported to an
arbitrary 2-fibre product square over the cospan, which is the shape
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf` (**Stacks 04XD**)
consumes its `eV` argument in.

This is the counterpart for a chart by an algebraic space of
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`, which is stated
for a scheme-valued point. That statement's proof reads the base change as the category of
elements of a subfunctor of `yoneda` of a *terminal* object, whose sections form a subsingleton,
so that the bijection on isomorphism classes and both of its inverse identities are automatic.
For a chart the sections are the sections of `V` and neither identity is automatic, so the
comparison is built as an honest functor and shown to be fully faithful and essentially
surjective by vertical isomorphisms.

## Main definitions

* `AlgebraicGeometry.Stack.chartSubfunctorMap`: the 1-morphism `El V ⥤ El U` over the site
  attached to a subfunctor `V ⊆ U`.
* `AlgebraicGeometry.Stack.chartBaseChange` and
  `AlgebraicGeometry.Stack.chartBaseChangeProjection`: the 2-fibre product `El U ×_𝒳 𝒲` and its
  structure functor to the site.
* `AlgebraicGeometry.Stack.chartLocusFunctor`: the comparison functor `El V ⥤ El U ×_𝒳 𝒲`,
  sending a section of `V` over `A` to the pair consisting of that section, read in `U`, and the
  object of `𝒲` the chart attaches to it.
* `AlgebraicGeometry.Stack.fullSubcategoryFibered` and
  `AlgebraicGeometry.Stack.fullSubcategoryFiberedInclusion`: the full subcategory and its
  inclusion, read in the 2-category of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange`: the identification of
  `El U ×_𝒳 𝒲` with `El V` over the site, for the canonical 2-fibre product.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_of_isTwoFibreProduct`: the
  same for an arbitrary 2-fibre product square over the cospan, which is the form a consumer of
  **Stacks 04XD** needs.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_comp_of_isTwoFibreProduct`:
  the comparison `𝒵 ×_𝒴 𝒲 ≅ (𝒵 ×_𝒴 𝒳) ×_𝒳 𝒲 ≅ El V` for a chart `b : 𝒵 ⟶ 𝒴` of the target of a
  1-morphism `𝒳 ⟶ 𝒴` whose base change is realised by `El U`, obtained from the previous one by
  pasting the two inner squares (**Stacks 02XD**).
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_pointsWithin` and
  `AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_comp_pointsWithin`: the
  specialisations to the open substack cut out by a set `Ω` of points of `|𝒳|`, where the
  subfunctor is `AlgebraicGeometry.Space.openSubspaceOfPoints` of the inverse image of `Ω` on
  the chart. The second is the comparison
  `𝒵 ×_𝒴 𝒲 ≅ (𝒵 ×_𝒴 𝒳) ×_𝒳 𝒲` that the chart construction of **Stacks 06M3** reads the base
  change of an open substack along a smooth chart off the chart of `𝒳` by.

## Implementation notes

The comparison functor is fully faithful because the fibres of a category of elements are
discrete — a morphism is determined by the morphism of the site it lies over — and because the
inclusion of a full subcategory is faithful, so that a morphism of the 2-fibre product is
determined by its first component
(`CategoryTheory.TwoFibreProductOver.hom_ext_of_faithful`). Essential surjectivity is where the
hypothesis on `P` is used: an object of the 2-fibre product over `A` is a section `s` of `U`
together with an object of `𝒲` and a vertical isomorphism from `c(A, s)` to it, and `P` being
inherited along that isomorphism puts `s` in `V`.

The transport to an arbitrary square is
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` together with **Stacks 003Z (2)** in
the form `CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`: a
comparison 1-morphism between two 2-fibre products of one cospan of categories fibred in groupoids
is an equivalence of the underlying categories, and an equivalence of categories over the site
which commutes strictly with the structure functors is an equivalence over the site.

Nothing here carries a `@[stacks …]` attribute: the statement is a prerequisite of the chart
construction of Stacks 06M3 and not the whole content of any tag.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.IsHomLift

universe v₁ v₂ u₁ u₂

/-- A morphism lies over every morphism of the base that its image is equal to. This is the
constructor `CategoryTheory.Functor.IsHomLift.map` with the morphism of the base presented as an
arbitrary morphism together with an equation, so that it can be used where that morphism is not
syntactically the image. -/
theorem of_map_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
    (p : 𝒟 ⥤ 𝒞) {a b : 𝒟} (φ : a ⟶ b) (f : p.obj a ⟶ p.obj b) (h : p.map φ = f) :
    p.IsHomLift f φ := h ▸ IsHomLift.map p φ

end CategoryTheory.IsHomLift

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of the full subcategory cut out by a property of the objects of an algebraic stack
lies over the morphism of the site that it lies over in the ambient stack: the structure functor
of the full subcategory is the ambient one restricted along the inclusion. -/
theorem isHomLift_fullSubcategoryBased {A A' : BigFppfOver B S hS} (f : A ⟶ A')
    {a b : P.FullSubcategory} (φ : a ⟶ b) (h : 𝒳.val.val.p.IsHomLift f φ.hom) :
    (fullSubcategoryBased 𝒳 P).p.IsHomLift f φ :=
  have := h
  IsHomLift.of_fac' _ f φ
    (IsHomLift.domain_eq 𝒳.val.val.p f φ.hom) (IsHomLift.codomain_eq 𝒳.val.val.p f φ.hom)
    (IsHomLift.fac' 𝒳.val.val.p f φ.hom)

/-- The 1-morphism of categories over the big fppf site of `S` from the category of elements of a
subfunctor `V ⊆ U` to the category of elements of `U`: it sends the pair `(A, s)` to `(A, s)`,
forgetting that the section `s` lies in `V`. -/
def chartSubfunctorMap (V : Subfunctor U) :
    (fibredCategory B S hS V.toFunctor).val.obj ⥤ (fibredCategory B S hS U).val.obj where
  obj z := ⟨z.base, Discrete.mk z.fiber.as.1⟩
  map {z z'} v := ⟨v.base, Discrete.eqToHom (congrArg Subtype.val (Discrete.eq_of_hom v.fiber))⟩
  map_id z := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    apply Discrete.hom_eq
  map_comp v v' := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    apply Discrete.hom_eq

/-- `AlgebraicGeometry.Stack.chartSubfunctorMap` sends a section of `V` over `A` to the same
section, read in `U`. -/
@[simp] theorem chartSubfunctorMap_obj (V : Subfunctor U)
    (z : (fibredCategory B S hS V.toFunctor).val.obj) :
    (chartSubfunctorMap V).obj z = ⟨z.base, Discrete.mk z.fiber.as.1⟩ := rfl

/-- `AlgebraicGeometry.Stack.chartSubfunctorMap` sends a morphism of `El V` to a morphism of
`El U` over the same morphism of the site. -/
@[simp] theorem chartSubfunctorMap_map_base (V : Subfunctor U)
    {z z' : (fibredCategory B S hS V.toFunctor).val.obj} (v : z ⟶ z') :
    ((chartSubfunctorMap V).map v).base = v.base := rfl

/-- `AlgebraicGeometry.Stack.chartSubfunctorMap` commutes strictly with the structure
functors. -/
theorem chartSubfunctorMap_comp (V : Subfunctor U) :
    chartSubfunctorMap (B := B) (S := S) (hS := hS) V ⋙ (fibredCategory B S hS U).val.p =
      (fibredCategory B S hS V.toFunctor).val.p := rfl

variable (𝒳 P) in
/-- The 2-fibre product of a chart `El U ⟶ 𝒳` of an algebraic stack with the inclusion of the
full subcategory cut out by a property of its objects, as a category. -/
abbrev chartBaseChange (c : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val) :=
  TwoFibreProductOver (fibredCategory B S hS U).val.p (fullSubcategoryBased 𝒳 P).p
    𝒳.val.val.p c.toFunctor (fullSubcategoryBasedInclusion 𝒳 P).toFunctor

variable (𝒳 P) in
/-- The structure functor to the big fppf site of `S` of
`AlgebraicGeometry.Stack.chartBaseChange`. -/
abbrev chartBaseChangeProjection (c : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val) :
    chartBaseChange 𝒳 P c ⥤ BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor (fibredCategory B S hS U).val.p
    (fullSubcategoryBased 𝒳 P).p 𝒳.val.val.p c.toFunctor
    (fullSubcategoryBasedInclusion 𝒳 P).toFunctor

section Comparison

variable {c : (fibredCategory B S hS U).val ⥤ᵇ 𝒳.val.val} {V : Subfunctor U}
  (hV : ∀ (A : BigFppfOver B S hS) (s : U.obj (Opposite.op A)),
    s ∈ V.obj (Opposite.op A) ↔ P (c.toFunctor.obj ⟨A, Discrete.mk s⟩))

include hV

/-- The object of `El U ×_𝒳 𝒲` attached to a section of the subfunctor `V`: the section read in
`U`, the object of `𝒲` the chart attaches to it — which lies in the full subcategory exactly
because the section lies in `V` — and the identity comparison isomorphism. -/
abbrev chartLocusObj (z : (fibredCategory B S hS V.toFunctor).val.obj) :
    chartBaseChange 𝒳 P c where
  base := z.base
  x := (chartSubfunctorMap V).obj z
  y := ⟨c.toFunctor.obj ((chartSubfunctorMap V).obj z),
    (hV z.base z.fiber.as.1).1 z.fiber.as.2⟩
  hx := rfl
  hy := c.w_obj _
  iso := Iso.refl _
  vertical := IsHomLift.id (c.w_obj _)

/-- The morphism of `El U ×_𝒳 𝒲` attached to a morphism of `El V`: the morphism read in `El U`
in the first component and its image under the chart in the second. -/
abbrev chartLocusMap {z z' : (fibredCategory B S hS V.toFunctor).val.obj} (v : z ⟶ z') :
    chartLocusObj hV z ⟶ chartLocusObj hV z' where
  hbase := v.base
  a := (chartSubfunctorMap V).map v
  b := ObjectProperty.homMk (c.toFunctor.map ((chartSubfunctorMap V).map v))
  ha := IsHomLift.of_map_eq (fibredCategory B S hS U).val.p ((chartSubfunctorMap V).map v)
    v.base rfl
  hb :=
    haveI h1 : (fibredCategory B S hS U).val.p.IsHomLift v.base ((chartSubfunctorMap V).map v) :=
      IsHomLift.of_map_eq (fibredCategory B S hS U).val.p ((chartSubfunctorMap V).map v)
        v.base rfl
    isHomLift_fullSubcategoryBased v.base _
      (BasedFunctor.preserves_isHomLift c v.base ((chartSubfunctorMap V).map v))
  w := by
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- **The comparison functor from the category of elements of the subfunctor to the base
change.** For a subfunctor `V ⊆ U` whose sections over `A` are exactly the sections of `U` at
which the property `P` holds after applying the chart, this is the functor
`El V ⥤ El U ×_𝒳 𝒲`. -/
def chartLocusFunctor :
    (fibredCategory B S hS V.toFunctor).val.obj ⥤ chartBaseChange 𝒳 P c where
  obj z := chartLocusObj hV z
  map v := chartLocusMap hV v
  map_id z := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact (chartSubfunctorMap V).map_id z
    · refine ObjectProperty.hom_ext (P := P) ?_
      change c.toFunctor.map ((chartSubfunctorMap V).map (𝟙 z)) = 𝟙 _
      rw [(chartSubfunctorMap V).map_id, c.toFunctor.map_id]
  map_comp v v' := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact (chartSubfunctorMap V).map_comp v v'
    · refine ObjectProperty.hom_ext (P := P) ?_
      change c.toFunctor.map ((chartSubfunctorMap V).map (v ≫ v')) =
        c.toFunctor.map ((chartSubfunctorMap V).map v) ≫
          c.toFunctor.map ((chartSubfunctorMap V).map v')
      rw [(chartSubfunctorMap V).map_comp, c.toFunctor.map_comp]

/-- The comparison functor sends a section of `V` to `AlgebraicGeometry.Stack.chartLocusObj` of
it. -/
@[simp] theorem chartLocusFunctor_obj (z : (fibredCategory B S hS V.toFunctor).val.obj) :
    (chartLocusFunctor hV).obj z = chartLocusObj hV z := rfl

/-- The comparison functor sends a morphism of `El V` to `AlgebraicGeometry.Stack.chartLocusMap`
of it. -/
@[simp] theorem chartLocusFunctor_map
    {z z' : (fibredCategory B S hS V.toFunctor).val.obj} (v : z ⟶ z') :
    (chartLocusFunctor hV).map v = chartLocusMap hV v := rfl

/-- The comparison functor commutes strictly with the structure functors: both read off the base
of a section. -/
theorem chartLocusFunctor_comp :
    chartLocusFunctor hV ⋙ chartBaseChangeProjection 𝒳 P c =
      (fibredCategory B S hS V.toFunctor).val.p := rfl

/-- The comparison functor is faithful: a morphism of a category of elements is determined by the
morphism of the site it lies over, and the comparison functor preserves that morphism. -/
instance faithful_chartLocusFunctor : (chartLocusFunctor hV).Faithful where
  map_injective {z z'} f g h := by
    have hb : f.base = g.base := congrArg TwoFibreProductOver.Hom.hbase h
    exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ hb (by apply Discrete.hom_eq)

/-- The comparison functor is full: a morphism of the base change has a first component in
`El U`, whose base morphism and whose identification of sections lift to a morphism of `El V`,
and a morphism of the base change is determined by its first component because the inclusion of
a full subcategory is faithful. -/
instance full_chartLocusFunctor : (chartLocusFunctor hV).Full where
  map_surjective {z z'} Ψ := by
    have : (fullSubcategoryBasedInclusion 𝒳 P).toFunctor.Faithful := ObjectProperty.faithful_ι P
    have heq : z.fiber.as = V.toFunctor.map Ψ.a.base.op z'.fiber.as :=
      Subtype.ext (Discrete.eq_of_hom Ψ.a.fiber)
    refine ⟨⟨Ψ.a.base, Discrete.eqToHom heq⟩, ?_⟩
    refine TwoFibreProductOver.hom_ext_of_faithful ?_
    exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl (by apply Discrete.hom_eq)

variable (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)

include hP

/-- **Every object of the base change is vertically isomorphic to one in the image of the
comparison functor.** An object of `El U ×_𝒳 𝒲` over `A` is a section `s` of `U` over `A`, an
object of `𝒲` and a vertical isomorphism from `c(A, s)` to it; the property `P` is inherited
along that isomorphism, so `s` lies in `V`, and the comparison isomorphism itself exhibits the
object as vertically isomorphic to the image of `s`. -/
theorem essSurj_chartLocusFunctor (T : chartBaseChange 𝒳 P c) :
    ∃ (z : (fibredCategory B S hS V.toFunctor).val.obj) (e : chartLocusObj hV z ≅ T),
      (chartBaseChangeProjection 𝒳 P c).IsHomLift
        (𝟙 ((chartBaseChangeProjection 𝒳 P c).obj T)) e.hom := by
  obtain ⟨base, ⟨xb, ⟨sx⟩⟩, y, hx, hy, iso, vert⟩ := T
  subst hx
  have hPc : P (c.toFunctor.obj ⟨xb, Discrete.mk sx⟩) := hP iso.hom y.property
  have hsx : sx ∈ V.obj (Opposite.op xb) := (hV xb sx).2 hPc
  have hvert : 𝒳.val.val.p.IsHomLift (𝟙 xb) iso.hom := vert
  have hvertinv : 𝒳.val.val.p.IsHomLift (𝟙 xb) iso.inv :=
    IsHomLift.lift_id_inv 𝒳.val.val.p xb iso
  refine ⟨⟨xb, Discrete.mk ⟨sx, hsx⟩⟩,
    { hom :=
        { hbase := 𝟙 xb
          a := 𝟙 _
          b := ObjectProperty.homMk iso.hom
          ha := IsHomLift.id rfl
          hb := isHomLift_fullSubcategoryBased (𝟙 xb) _ hvert
          w := congrArg (fun m => m ≫ iso.hom) (c.toFunctor.map_id _) }
      inv :=
        { hbase := 𝟙 xb
          a := 𝟙 _
          b := ObjectProperty.homMk iso.inv
          ha := IsHomLift.id rfl
          hb := isHomLift_fullSubcategoryBased (𝟙 xb) _ hvertinv
          w := (congrArg (fun m => m ≫ 𝟙 (c.toFunctor.obj ⟨xb, Discrete.mk sx⟩))
            (c.toFunctor.map_id _)).trans ((Category.id_comp _).trans iso.hom_inv_id.symm) }
      hom_inv_id := by
        refine TwoFibreProductOver.Hom.ext' ?_ ?_
        · exact Category.id_comp _
        · refine ObjectProperty.hom_ext (P := P) ?_
          exact iso.hom_inv_id
      inv_hom_id := by
        refine TwoFibreProductOver.Hom.ext' ?_ ?_
        · exact Category.id_comp _
        · refine ObjectProperty.hom_ext (P := P) ?_
          exact iso.inv_hom_id },
    ?_⟩
  exact IsHomLift.of_map_eq _ _ _ rfl

/-- **The base change of a full-subcategory inclusion along a chart by a presheaf is the category
of elements of the subfunctor cutting out the locus.**

For a property `P` of the objects of an algebraic stack inherited along morphisms, a 1-morphism
`c` from the category of elements of a presheaf `U` on the big fppf site of `S`, and a subfunctor
`V ⊆ U` whose sections over `A` are exactly the sections `s` with `P (c (A, s))`, the 2-fibre
product of `c` with the inclusion of the full subcategory cut out by `P` is equivalent, over that
site, to the category of elements of `V`.

The comparison is `AlgebraicGeometry.Stack.chartLocusFunctor`, which is fully faithful and, by
`AlgebraicGeometry.Stack.essSurj_chartLocusFunctor`, essentially surjective by vertical
isomorphisms; `CategoryTheory.Functor.isFibredEquivalenceOver_of_fullyFaithful` turns that into
an equivalence in the 2-category of categories over the site. -/
theorem nonempty_equivalenceOver_chartBaseChange :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (chartBaseChangeProjection 𝒳 P c)
      (presheafOfCategories (V.toFunctor ⋙ typeToCat)).p) := by
  have h : Functor.IsFibredEquivalenceOver (fibredCategory B S hS V.toFunctor).val.p
      (chartBaseChangeProjection 𝒳 P c) (chartLocusFunctor hV) :=
    chartLocusFunctor_comp hV ▸
      Functor.isFibredEquivalenceOver_of_fullyFaithful (chartLocusFunctor hV)
        (essSurj_chartLocusFunctor hV hP)
  exact ⟨(equivalenceOver_of_isFibredEquivalenceOver h).symm⟩

end Comparison

/-! ### An arbitrary 2-fibre product square -/

variable (𝒳) in
/-- The full subcategory cut out by a property of the objects of an algebraic stack inherited
along morphisms, as an object of the 2-category of categories fibred in groupoids over the big
fppf site of `S`. -/
abbrev fullSubcategoryFibered (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
    (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP)

variable (𝒳) in
/-- The inclusion of `AlgebraicGeometry.Stack.fullSubcategoryFibered`, as a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. -/
abbrev fullSubcategoryFiberedInclusion (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a) :
    fullSubcategoryFibered 𝒳 hP ⟶ 𝒳.val :=
  Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P)

/-- Two 2-fibre products of one cospan of categories fibred in groupoids over the big fppf site
are equivalent over the site. -/
private theorem nonempty_equivalenceOver_of_isTwoFibreProduct_of_isTwoFibreProduct
    {𝒳' 𝒴' 𝒵' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳' ⟶ 𝒵'} {g : 𝒴' ⟶ 𝒵'} (Q R : Bicategory.TwoCommSq f g)
    (hQ : Bicategory.IsTwoFibreProduct Q) (hR : Bicategory.IsTwoFibreProduct R) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver Q.pt.val.p R.pt.val.p) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    Q.pt.isFiberedInGroupoids R.pt.isFiberedInGroupoids
    (Quotient.out (hR.from Q)).hom.hom.toFunctor (Quotient.out (hR.from Q)).hom.hom.w
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQ hR (Quotient.out (hR.from Q)))

/-- **The base change of a full-subcategory inclusion along a chart, at an arbitrary 2-fibre
product square.** In the situation of
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange`, the apex of *any* 2-fibre
product square over the cospan formed by the chart and the inclusion of the full subcategory is
equivalent, over the big fppf site of `S`, to the category of elements of the subfunctor cutting
out the locus.

This is the shape in which
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_fppf` (**Stacks 04XD**)
consumes its `eV` argument: a comparison 1-morphism from the given square to the canonical 2-fibre
product is an equivalence of the underlying categories by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, and **Stacks 003Z (2)** upgrades
that to an equivalence over the site. -/
theorem nonempty_equivalenceOver_chartBaseChange_of_isTwoFibreProduct
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (cm : fibredCategory B S hS U ⟶ 𝒳.val) {V : Subfunctor U}
    (hV : ∀ (A : BigFppfOver B S hS) (s : U.obj (Opposite.op A)),
      s ∈ V.obj (Opposite.op A) ↔ P (cm.hom.toFunctor.obj ⟨A, Discrete.mk s⟩))
    (Q : Bicategory.TwoCommSq cm (fullSubcategoryFiberedInclusion 𝒳 hP))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (V.toFunctor ⋙ typeToCat)).p) := by
  obtain ⟨e0⟩ := nonempty_equivalenceOver_chartBaseChange hV hP
  obtain ⟨e1⟩ := nonempty_equivalenceOver_of_isTwoFibreProduct_of_isTwoFibreProduct Q _ hQ
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cm
      (fullSubcategoryFiberedInclusion 𝒳 hP))
  exact ⟨e1.trans e0⟩

/-- **The base change of an open-substack inclusion along a chart of the target, read off the
chart of the source.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over
the big fppf site of `S`, let `b : 𝒵 ⟶ 𝒴` be a chart of the target, and suppose the base change
`𝒵 ×_𝒴 𝒳` is realised by the category of elements of a presheaf `U`, i.e. the square with apex
`El U` and legs `q`, `cm` is a 2-fibre product over the cospan `(b, f)`. Let `𝒲 ⊆ 𝒳` be the full
subcategory cut out by a property `P` of the objects of `𝒳` inherited along morphisms, and let
`V ⊆ U` cut out the locus of `P` on the chart. Then the apex of any 2-fibre product square over
the cospan `(b, 𝒲 ⟶ 𝒳 ⟶ 𝒴)` — that is, `𝒵 ×_𝒴 𝒲` — is equivalent, over the big fppf site of
`S`, to the category of elements of `V`.

This is the comparison `𝒵 ×_𝒴 𝒲 ≅ (𝒵 ×_𝒴 𝒳) ×_𝒳 𝒲 ≅ El V`: the pasting of the two inner squares
is a 2-fibre product of the outer cospan by **Stacks 02XD** in the form
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`, so the given square is comparable to the
iterated one, and
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_of_isTwoFibreProduct` identifies
the iterated apex with `El V`. -/
theorem nonempty_equivalenceOver_chartBaseChange_comp_of_isTwoFibreProduct
    (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    {𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳.val ⟶ 𝒴) (b : 𝒵 ⟶ 𝒴) (q : fibredCategory B S hS U ⟶ 𝒵)
    (cm : fibredCategory B S hS U ⟶ 𝒳.val) (ι : q ≫ b ≅ cm ≫ f)
    (hD : Bicategory.IsTwoFibreProduct
      (⟨fibredCategory B S hS U, q, cm, ι⟩ : Bicategory.TwoCommSq b f))
    {V : Subfunctor U}
    (hV : ∀ (A : BigFppfOver B S hS) (s : U.obj (Opposite.op A)),
      s ∈ V.obj (Opposite.op A) ↔ P (cm.hom.toFunctor.obj ⟨A, Discrete.mk s⟩))
    (Q : Bicategory.TwoCommSq b (fullSubcategoryFiberedInclusion 𝒳 hP ≫ f))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (V.toFunctor ⋙ typeToCat)).p) := by
  obtain ⟨e0⟩ := nonempty_equivalenceOver_chartBaseChange hV hP
  obtain ⟨e1⟩ := nonempty_equivalenceOver_of_isTwoFibreProduct_of_isTwoFibreProduct Q _ hQ
    (Bicategory.isTwoFibreProduct_pasteSnd _ hD _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cm
        (fullSubcategoryFiberedInclusion 𝒳 hP)))
  exact ⟨e1.trans e0⟩

/-! ### The open substack cut out by a set of points -/

/-- **The base change along a chart of the inclusion of the full subcategory cut out by a set of
points.** Let `𝒳` be an algebraic stack over `S`, let `Ω` be a set of points of `|𝒳|`
(**Stacks 04XG**), let `𝒲 ⊆ 𝒳` be the full subcategory cut out by
`AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` — the open substack attached to `Ω` when `Ω` is open,
by `AlgebraicGeometry.Stack.pointsWithinOpenSubstack` — and let `c` be a chart of `𝒳` by the
category of elements of a presheaf `U`. Then the apex of any 2-fibre product square over the
cospan `(c, 𝒲 ⟶ 𝒳)` is equivalent, over the big fppf site of `S`, to the category of elements of
the subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` of `U` cut out by the inverse image
of `Ω`, which is an open subspace of `U` when `Ω` is open and `U` is an algebraic space by
`AlgebraicGeometry.Stack.isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage`
(**Stacks 03BZ**).

This is the comparison `V ×_𝒴 𝒲 ≅ (V ×_𝒴 𝒳) ×_𝒳 𝒲` that the chart construction of
**Stacks 06M3** needs: with `U = V ×_𝒴 𝒳` the chart of `𝒳` induced by a chart `V ⟶ 𝒴`, the right
side is the open subspace of `U` this produces, so that **Stacks 04XD** can be applied to
`𝒲 ⟶ 𝒴` along `V ⟶ 𝒴` with the open immersion of that open subspace into `U` for its morphism of
representing presheaves.

The identification of the locus on the chart is
`AlgebraicGeometry.Stack.mem_openSubspaceOfPoints_spacePointMap_preimage_iff`. -/
theorem nonempty_equivalenceOver_chartBaseChange_pointsWithin
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (cm : fibredCategory B S hS U ⟶ 𝒳.val)
    (Q : Bicategory.TwoCommSq cm
      (fullSubcategoryFiberedInclusion 𝒳 (fun f => pointsWithin_of_hom 𝒳 Ω f)))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories ((Space.openSubspaceOfPoints B S hS U
        (spacePointMap B S hS U 𝒳.val cm.hom ⁻¹' Ω)).toFunctor ⋙ typeToCat)).p) :=
  nonempty_equivalenceOver_chartBaseChange_of_isTwoFibreProduct
    (fun f => pointsWithin_of_hom 𝒳 Ω f) cm
    (fun _ s => mem_openSubspaceOfPoints_spacePointMap_preimage_iff B S hS U Ω cm.hom s) Q hQ

/-- **`𝒵 ×_𝒴 𝒲 ≅ (𝒵 ×_𝒴 𝒳) ×_𝒳 𝒲` for `𝒲` the full subcategory cut out by a set of points.**
In the situation of
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_chartBaseChange_comp_of_isTwoFibreProduct` at
the property `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω`, the base change of the inclusion of that
full subcategory along a chart `b : 𝒵 ⟶ 𝒴` of the target is the category of elements of the
subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` of the chart `U = 𝒵 ×_𝒴 𝒳` of `𝒳` cut
out by the inverse image of `Ω`.

This is the statement that the chart construction of **Stacks 06M3** consumes **Stacks 04XD** at:
with `Ω` open and `U` an algebraic space the subfunctor is an open subspace of `U` by
`AlgebraicGeometry.Stack.isOpenSubspace_openSubspaceOfPoints_spacePointMap_preimage`
(**Stacks 03BZ**), so the morphism of representing presheaves induced by the projection of the
square is the open immersion of that open subspace into `U`. -/
theorem nonempty_equivalenceOver_chartBaseChange_comp_pointsWithin
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    {𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (fm : 𝒳.val ⟶ 𝒴) (b : 𝒵 ⟶ 𝒴) (q : fibredCategory B S hS U ⟶ 𝒵)
    (cm : fibredCategory B S hS U ⟶ 𝒳.val) (ι : q ≫ b ≅ cm ≫ fm)
    (hD : Bicategory.IsTwoFibreProduct
      (⟨fibredCategory B S hS U, q, cm, ι⟩ : Bicategory.TwoCommSq b fm))
    (Q : Bicategory.TwoCommSq b
      (fullSubcategoryFiberedInclusion 𝒳 (fun f => pointsWithin_of_hom 𝒳 Ω f) ≫ fm))
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories ((Space.openSubspaceOfPoints B S hS U
        (spacePointMap B S hS U 𝒳.val cm.hom ⁻¹' Ω)).toFunctor ⋙ typeToCat)).p) :=
  nonempty_equivalenceOver_chartBaseChange_comp_of_isTwoFibreProduct
    (fun f => pointsWithin_of_hom 𝒳 Ω f) fm b q cm ι hD
    (fun _ s => mem_openSubspaceOfPoints_spacePointMap_preimage_iff B S hS U Ω cm.hom s) Q hQ

end AlgebraicGeometry.Stack

end
