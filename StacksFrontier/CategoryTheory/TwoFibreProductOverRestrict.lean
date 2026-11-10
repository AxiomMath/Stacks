module

public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# Reindexing and restricting the base change of a 2-fibre product along a point

Let `C` be a category, let `X` be an object of it and let `𝒳`, `𝒴` be categories over the slice
`C/X` with a 1-morphism `G : 𝒳 ⥤ 𝒴` over `C/X`. A *point of `𝒴` with values in `A`*, for
`a : A ⟶ X`, is a 1-morphism `y : C/A ⥤ 𝒴` over `CategoryTheory.Over.map a`; the base change of
`G` along it is the first projection of the 2-fibre product `C/A ×_{y, 𝒴, G} 𝒳` over `C/X`. This
file proves the two comparisons of such base changes that a descent argument for a relative
property of `G` needs, both as equivalences *over the first factor*
(`StacksRepresentableCFG.EquivalenceOver`), which is the shape the representability predicates of
Stacks 02ZW and the relative properties of Stacks 03YK quantify over.

The first is **reindexing**: a 2-isomorphism of the point — a natural isomorphism of the two
1-morphisms all of whose components are vertical — induces an equivalence of the two base changes.
The underlying functors are `CategoryTheory.TwoFibreProductOver.reindex` and
`CategoryTheory.TwoFibreProductOver.reindexSymm`, which commute strictly with the first projection
and are mutually inverse only on *objects*; the unit and the counit are therefore built by hand,
from isomorphisms of the 2-fibre product whose two components are identities, the cancellation
`α ∘ α⁻¹ = id` being absorbed into the comparison isomorphism.

The second is **restriction**: for `m : A' ⟶ A`, a presheaf `F` on `C/A` representing the base
change of `G` along `y` has its restriction `m^{-1}F` along `CategoryTheory.Over.map m`
representing the base change of `G` along the restricted point `Over.map m ⋙ y`. Together with
`CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap`, which exhibits the relocalization of
a restriction as a base change along a representable morphism, this is the locality step of any
argument of the shape "the relative property holds after restriction to each member of a covering,
hence it holds over the base".

The proof of the second is a chain of three identifications, through the 2-fibre product
`C/A' ×_{Over.map m, C/A} El F` over `C/X`:

1. the second factor of that product is `El F`, which an equivalence over `C/X` replaces by the
   2-fibre product `C/A ×_{y, 𝒴, G} 𝒳` — this is
   `CategoryTheory.TwoFibreProductOver.precomposeSnd` along the forward 1-morphism of the given
   representing equivalence;
2. the middle factor `C/A` then cancels, by
   `CategoryTheory.TwoFibreProductOver.cancelMiddleEquivalenceOver`, leaving
   `C/A' ×_{Over.map m ⋙ y, 𝒴, G} 𝒳`;
3. and `C/A' ×_{Over.map m, C/A} El F` is the category of elements of `m^{-1}F`, which is the
   content of `CategoryTheory.PresheafOfCategories.toBaseChangeElements` below.

## Main definitions

* `CategoryTheory.PresheafOfCategories.restrictElements`: the 1-morphism `El (m^{-1}F) ⥤ El F`
  of categories of elements over `Over.map m`.
* `CategoryTheory.PresheafOfCategories.descendRestrictElements`: the descent of a 1-morphism into
  `El F` lying over `Over.map m` to a 1-morphism into `El (m^{-1}F)`.
* `CategoryTheory.PresheafOfCategories.toBaseChangeElements`: the comparison from
  `El (m^{-1}F)` to the 2-fibre product `C/A' ×_{Over.map m, C/A} El F`.

## Main results

* `CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`: reindexing along a 2-isomorphism of
  the first leg is an equivalence over the first factor.
* `CategoryTheory.PresheafOfCategories.descendRestrictElementsIso` and
  `CategoryTheory.PresheafOfCategories.isEquivalence_descendRestrictElements`: the descent
  recovers the given 1-morphism after restriction, and is an equivalence as soon as that
  1-morphism is one and `Over.map m` is fully faithful.
* `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_toBaseChangeElements`: the
  category of elements of `m^{-1}F` is the base change of `El F` along `Over.map m`.
* `CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_relocalizeRestrict`: the
  restriction of a representing presheaf represents the restricted base change.

## Implementation notes

`CategoryTheory.PresheafOfCategories.toBaseChangeElements` is built with the universal property
`CategoryTheory.TwoFibreProductOver.lift`, so neither its functoriality nor its commutation with
the first projection has to be checked: both legs are functors already at hand and the 2-cell
filling the square is the identity, the only transport being
`CategoryTheory.Over.mapComp_eq` — the slice functors of `m` and `a` compose to the slice functor
of `m ≫ a` only up to the associativity of `C`. That it is an *equivalence* is then checked as
fullness, faithfulness and essential surjectivity; the backward 1-morphism, the unit and the
counit are supplied by
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, which is why only a
`Nonempty` is asserted. Essential surjectivity is the step with content, and it is where no
transport appears: the comparison isomorphism of an object of the 2-fibre product is used to
*restrict* the element that the object names, rather than to transport it along an equality.

`CategoryTheory.PresheafOfCategories.descendRestrictElements` is what makes a representation of
the restricted base change *computable*: a section of `m^{-1}F` over `V` is by definition a
section of `F` over `Over.map m` of `V`, so a 1-morphism over `Over.map m` into `El F` is already
a 1-morphism into `El (m^{-1}F)`, with no choice made. The identifications of bases that the
construction consumes are read through
`CategoryTheory.PresheafOfCategories.elementsFiberEquiv`, which is exactly how
`CategoryTheory.PresheafOfCategories.sectionOfObj` reads a section off an equivalence, so the
section named by an object of the source is literally the section named by its image.

Two shapes recur in the proofs about categories of elements. Their morphisms are compared
through `CategoryTheory.PresheafOfCategories.elements_hom_ext'` rather than
`CategoryTheory.PresheafOfCategories.elements_hom_ext`: the `base` field of a morphism is a
projection of `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom`, which the category instance of
`CategoryTheory.PresheafOfCategories.presheafOfCategories` reaches only through unfolding that no
rewrite performs, while its image under the projection functor is an ordinary functor
application. And the comparison with the given 1-morphism is a natural *isomorphism* rather than
an equality of functors, because an equality is checked through `eqToHom`s between objects of a
category of elements, whose `base` fields no rewrite reaches either.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Reindex

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F F' : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

attribute [local implicit_reducible] fst

/-- The unit of `CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`: reindexing along `α`
and then along `α⁻¹` returns an object with the same two components, the comparison isomorphism
having been composed with `α⁻¹ ∘ α`. The two components of the unit are therefore identities. -/
noncomputable def reindexUnit (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    𝟭 (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) ≅
      reindex (G := G) α hα ⋙ reindexSymm (G := G) α hα := by
  refine NatIso.ofComponents (fun P => ?_) (fun {P Q} φ => ?_)
  · refine isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
      (IsHomLift.id P.hx) (IsHomLift.id P.hy) ?_
    change F.map (𝟙 P.x) ≫ (α.hom.app P.x ≫ α.inv.app P.x ≫ P.iso.hom) =
      P.iso.hom ≫ G.map (𝟙 P.y)
    simp
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ φ.a
      simp
    · change φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b
      simp

/-- The counit of `CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`. -/
noncomputable def reindexCounit (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    reindexSymm (G := G) α hα ⋙ reindex (G := G) α hα ≅
      𝟭 (TwoFibreProductOver p𝒳 p𝒴 p𝒮 F' G) := by
  refine NatIso.ofComponents (fun P => ?_) (fun {P Q} φ => ?_)
  · refine isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
      (IsHomLift.id P.hx) (IsHomLift.id P.hy) ?_
    change F'.map (𝟙 P.x) ≫ P.iso.hom =
      (α.inv.app P.x ≫ α.hom.app P.x ≫ P.iso.hom) ≫ G.map (𝟙 P.y)
    simp
  · refine Hom.ext' ?_ ?_
    · change φ.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ φ.a
      simp
    · change φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b
      simp

/-- **Reindexing a 2-fibre product along a 2-isomorphism of its first leg is an equivalence over
the first factor.** For `α : F ≅ F'` a natural isomorphism of 1-morphisms `𝒳 ⥤ 𝒮` over `𝒞` all of
whose components are vertical, the first projections of `𝒳 ×_{F, 𝒮, G} 𝒴` and of
`𝒳 ×_{F', 𝒮, G} 𝒴` are equivalent as categories over `𝒳`. -/
noncomputable def reindexEquivalenceOver (α : F ≅ F')
    (hα : ∀ x : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) :
    StacksRepresentableCFG.EquivalenceOver (fst p𝒳 p𝒴 p𝒮 F G) (fst p𝒳 p𝒴 p𝒮 F' G) where
  hom := ⟨reindex (G := G) α hα, reindex_comp_fst α hα⟩
  inv := ⟨reindexSymm (G := G) α hα, reindexSymm_comp_fst α hα⟩
  unitIso := reindexUnit (G := G) α hα
  counitIso := reindexCounit (G := G) α hα
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 R.x = eqToHom rfl ≫ 𝟙 R.x ≫ eqToHom rfl
    simp
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun R => ?_)
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    change 𝟙 R.x = eqToHom rfl ≫ 𝟙 R.x ≫ eqToHom rfl
    simp

end Reindex

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.PresheafOfCategories

universe v v₂ v₃ u u₂ u₃

variable {C : Type u} [Category.{v} C] {X A A' : C} (a : A ⟶ X) (m : A' ⟶ A)
  (F : (Over A)ᵒᵖ ⥤ Type v)

/-- The underlying morphism of the isomorphism of categories of elements attached to an
isomorphism of the bases is that isomorphism. -/
@[simp] theorem elementsIsoOfBaseIso_hom_base {C' : Type u₂} [Category.{v} C']
    {G : C'ᵒᵖ ⥤ Type v} {Z W : (presheafOfCategories (G ⋙ typeToCat)).obj} (e : Z.base ≅ W.base)
    (h : Z.fiber.as = G.map (Quiver.Hom.op e.hom) W.fiber.as) :
    (elementsIsoOfBaseIso e h).hom.base = e.hom := rfl

/-- The 1-morphism `El (m^{-1}F) ⥤ El F` of categories of elements over
`CategoryTheory.Over.map m`: a section of the restriction of `F` over `V` *is* a section of `F`
over `Over.map m` of `V`, and a morphism of the restriction is the corresponding morphism of
`F`. -/
def restrictElements :
    (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (F ⋙ typeToCat)).obj where
  obj Z := ⟨(Over.map m).obj Z.base, Discrete.mk Z.fiber.as⟩
  map {_ _} u := ⟨(Over.map m).map u.base, ⟨u.fiber.eq⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `CategoryTheory.PresheafOfCategories.restrictElements` is a 1-morphism over
`CategoryTheory.Over.map m`. -/
@[simp] theorem restrictElements_comp :
    restrictElements m F ⋙ discreteProjection F =
      discreteProjection ((OverShriek.relocalizeRestrict m).obj F) ⋙ Over.map m := rfl

/-! #### Descent of a 1-morphism over `Over.map m` into the category of elements -/

section Descend

variable {D : Type u₂} [Category.{v₂} D]

/-- `CategoryTheory.PresheafOfCategories.elements_hom_ext` with the morphism of bases presented
as the image under the projection of the category of elements. That is the form rewriting can
reach: the projection of a morphism is an application of a functor, whereas its `base` field is an
application of a projection of `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom`, which the
category instance of `CategoryTheory.PresheafOfCategories.presheafOfCategories` reaches only
through unfolding that no rewrite performs. -/
lemma elements_hom_ext' {G : Cᵒᵖ ⥤ Type v}
    {Z W : (presheafOfCategories (G ⋙ typeToCat)).obj} (u w : Z ⟶ W)
    (h : (discreteProjection G).map u = (discreteProjection G).map w) : u = w :=
  elements_hom_ext u w h

/-- `CategoryTheory.PresheafOfCategories.restrictElements` is faithful as soon as
`CategoryTheory.Over.map m` is: a morphism of a category of elements is determined by the
morphism of bases it carries, and the restriction keeps that morphism of bases. -/
theorem faithful_restrictElements [(Over.map m).Faithful] : (restrictElements m F).Faithful :=
  ⟨fun {_ _ u u'} h =>
    elements_hom_ext u u' ((Over.map m).map_injective (congrArg (fun w => w.base) h))⟩

/-- `CategoryTheory.PresheafOfCategories.restrictElements` is full as soon as
`CategoryTheory.Over.map m` is: a morphism of bases in the image of `Over.map m` comes from one
of `C/A'`, and the equation between sections it has to satisfy is unchanged. -/
theorem full_restrictElements [(Over.map m).Full] : (restrictElements m F).Full := by
  refine ⟨fun {Z W} v => ?_⟩
  obtain ⟨b, hb⟩ := (Over.map m).map_surjective v.base
  refine ⟨⟨b, Discrete.eqToHom ?_⟩, elements_hom_ext _ _ ?_⟩
  · change Z.fiber.as = F.map ((Over.map m).map b).op W.fiber.as
    rw [hb]
    exact v.fiber.eq
  · change (Over.map m).map b = v.base
    exact hb

/-- The section named by an object of the category of elements of `F`, read over an object of the
base identified with its own, is the restriction of the section it names along the
identification. -/
lemma elementsFiberEquiv_eq_map_eqToHom {G : Cᵒᵖ ⥤ Type v}
    (Z : (presheafOfCategories (G ⋙ typeToCat)).obj) {W : C} (h : Z.base = W) :
    elementsFiberEquiv G W ⟨Z, h⟩ = G.map (eqToHom h.symm).op Z.fiber.as := by
  subst h
  change Z.fiber.as = G.map (eqToHom rfl).op Z.fiber.as
  simp

/-- **The descent of a 1-morphism into `El F` lying over `CategoryTheory.Over.map m` to a
1-morphism into `El (m^{-1}F)`.** A section of `F` over `Over.map m` of `V` *is* a section of
`m^{-1}F` over `V`, so a 1-morphism `L` whose composite with the projection of `El F` is
`J` followed by `Over.map m` is the same thing as a 1-morphism into `El (m^{-1}F)` over `J`.

No transport appears in the value: the section named by `L z` is read off through
`CategoryTheory.PresheafOfCategories.elementsFiberEquiv` at the identification of the base that
`hL` supplies, which is exactly how
`CategoryTheory.PresheafOfCategories.sectionOfObj` reads a section off an equivalence. -/
def descendRestrictElements (J : D ⥤ Over A')
    (L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hL : L ⋙ discreteProjection F = J ⋙ Over.map m) :
    D ⥤ (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj where
  obj z := ⟨J.obj z, Discrete.mk (elementsFiberEquiv F ((Over.map m).obj (J.obj z))
    ⟨L.obj z, Functor.congr_obj hL z⟩)⟩
  map {z w} u := ⟨J.map u, Discrete.eqToHom
    (elementsFiberEquiv_map_of_isHomLift F ((Over.map m).map (J.map u))
      ⟨L.obj w, Functor.congr_obj hL w⟩ ⟨L.obj z, Functor.congr_obj hL z⟩ (L.map u)
      (isHomLift_map_of_comp hL ((Over.map m).map (J.map u)) u
        (IsHomLift.map (p := J ⋙ Over.map m) u)))⟩
  map_id z := elements_hom_ext _ _ (J.map_id z)
  map_comp u v := elements_hom_ext _ _ (J.map_comp u v)

/-- The descent is strictly a 1-morphism over `J`. -/
@[simp] theorem descendRestrictElements_comp (J : D ⥤ Over A')
    (L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hL : L ⋙ discreteProjection F = J ⋙ Over.map m) :
    descendRestrictElements m F J L hL ⋙
      discreteProjection ((OverShriek.relocalizeRestrict m).obj F) = J := rfl

/-- The base of `L z` is the image under `CategoryTheory.Over.map m` of the base of `J z`, which
is what the descent uses to read off a section. -/
theorem descendRestrictElements_base_eq (J : D ⥤ Over A')
    (L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hL : L ⋙ discreteProjection F = J ⋙ Over.map m) (z : D) :
    (L.obj z).base = (Over.map m).obj (J.obj z) :=
  Functor.congr_obj hL z

/-- **The descent recovers the given 1-morphism after restriction.** Composing the descent with
`CategoryTheory.PresheafOfCategories.restrictElements` returns `L` up to an isomorphism which
is the identity on sections, the two objects having the same section over identified bases.

The comparison is stated as a natural isomorphism rather than an equality of functors, even
though the two functors agree objectwise on the nose: an equality of functors is checked through
`eqToHom`s between objects of a category of elements, whose `base` fields no rewrite reaches,
whereas the isomorphism is `CategoryTheory.PresheafOfCategories.elementsIsoOfBaseIso`, whose base
component is given by `CategoryTheory.PresheafOfCategories.elementsIsoOfBaseIso_hom_base`. -/
noncomputable def descendRestrictElementsIso (J : D ⥤ Over A')
    (L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hL : L ⋙ discreteProjection F = J ⋙ Over.map m) :
    descendRestrictElements m F J L hL ⋙ restrictElements m F ≅ L := by
  refine NatIso.ofComponents (fun z => elementsIsoOfBaseIso
    (eqToIso (descendRestrictElements_base_eq m F J L hL z).symm) ?_) (fun {z w} u => ?_)
  · exact elementsFiberEquiv_eq_map_eqToHom (L.obj z)
      (descendRestrictElements_base_eq m F J L hL z)
  · have hu : (discreteProjection F).map (L.map u) =
        eqToHom (descendRestrictElements_base_eq m F J L hL z) ≫ (Over.map m).map (J.map u) ≫
          eqToHom (descendRestrictElements_base_eq m F J L hL w).symm := Functor.congr_hom hL u
    have key : (Over.map m).map (J.map u) ≫
          eqToHom (descendRestrictElements_base_eq m F J L hL w).symm =
        eqToHom (descendRestrictElements_base_eq m F J L hL z).symm ≫
          (discreteProjection F).map (L.map u) := by
      rw [hu]
      simp
    exact elements_hom_ext' _ _ key

/-- **The descent of an equivalence is an equivalence.** For `m` such that
`CategoryTheory.Over.map m` is fully faithful — in particular for `m` an isomorphism — the
descent of a 1-morphism which is an equivalence of the underlying categories is again one.

`CategoryTheory.PresheafOfCategories.restrictElements` is fully faithful under that hypothesis,
and the descent composed with it is the given equivalence, so full faithfulness of the descent is
cancellation and essential surjectivity is transport of an isomorphism through the fully faithful
`restrictElements`. -/
theorem isEquivalence_descendRestrictElements [(Over.map m).Full] [(Over.map m).Faithful]
    (J : D ⥤ Over A') (L : D ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hL : L ⋙ discreteProjection F = J ⋙ Over.map m)
    (hLe : L.IsEquivalence) : (descendRestrictElements m F J L hL).IsEquivalence := by
  have _ := faithful_restrictElements m F
  have _ := full_restrictElements m F
  have _ := hLe
  have hcomp : (descendRestrictElements m F J L hL ⋙ restrictElements m F).IsEquivalence :=
    Functor.isEquivalence_of_iso (descendRestrictElementsIso m F J L hL).symm
  have _ : (descendRestrictElements m F J L hL).Faithful :=
    Functor.Faithful.of_comp (descendRestrictElements m F J L hL) (restrictElements m F)
  have _ : (descendRestrictElements m F J L hL).Full :=
    Functor.Full.of_comp_faithful (descendRestrictElements m F J L hL) (restrictElements m F)
  have hess : (descendRestrictElements m F J L hL).EssSurj := by
    refine ⟨fun Y => ?_⟩
    obtain ⟨z, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := descendRestrictElements m F J L hL ⋙
      restrictElements m F) ((restrictElements m F).obj Y)
    exact ⟨z, ⟨(Functor.FullyFaithful.ofFullyFaithful (restrictElements m F)).preimageIso i⟩⟩
  have _ := hess
  exact Functor.IsEquivalence.mk

end Descend

/-- The comparison from the category of elements of `m^{-1}F` to the 2-fibre product
`C/A' ×_{Over.map m, C/A} El F` over `C/X`: a section `s` of `F` over `Over.map m` of `V` is the
triple `(V, s, id)`. -/
noncomputable def toBaseChangeElements :
    (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver (Over.map (m ≫ a))
        (discreteProjection F ⋙ Over.map a) (Over.map a) (Over.map m)
        (discreteProjection F) :=
  TwoFibreProductOver.lift _ _ _ _ _
    (discreteProjection ((OverShriek.relocalizeRestrict m).obj F) ⋙ Over.map (m ≫ a))
    (discreteProjection ((OverShriek.relocalizeRestrict m).obj F)) (restrictElements m F)
    rfl
    (by rw [← Functor.assoc, restrictElements_comp, Functor.assoc, ← Over.mapComp_eq])
    (Iso.refl _)
    (fun w => CategoryTheory.IsHomLift.id
      (Functor.congr_obj (Over.mapComp_eq m a).symm
        ((discreteProjection ((OverShriek.relocalizeRestrict m).obj F)).obj w)))

/-- The comparison isomorphism of the image of an object under
`CategoryTheory.PresheafOfCategories.toBaseChangeElements` is the identity. -/
@[simp] theorem toBaseChangeElements_obj_iso
    (Z : (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj) :
    ((toBaseChangeElements a m F).obj Z).iso = Iso.refl ((Over.map m).obj Z.base) := rfl

/-- The first component of the image of an object under
`CategoryTheory.PresheafOfCategories.toBaseChangeElements` is its base. -/
@[simp] theorem toBaseChangeElements_obj_x
    (Z : (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj) :
    ((toBaseChangeElements a m F).obj Z).x = Z.base := rfl

/-- The second component of the image of an object under
`CategoryTheory.PresheafOfCategories.toBaseChangeElements` is the section it names, read over
`Over.map m` of its base. -/
@[simp] theorem toBaseChangeElements_obj_y
    (Z : (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj) :
    ((toBaseChangeElements a m F).obj Z).y =
      ⟨(Over.map m).obj Z.base, Discrete.mk Z.fiber.as⟩ := rfl

/-- The first component of the image of a morphism under
`CategoryTheory.PresheafOfCategories.toBaseChangeElements` is its base. -/
@[simp] theorem toBaseChangeElements_map_a
    {Z Z' : (presheafOfCategories (((OverShriek.relocalizeRestrict m).obj F) ⋙ typeToCat)).obj}
    (u : Z ⟶ Z') : ((toBaseChangeElements a m F).map u).a = u.base := rfl

/-- The comparison is faithful: a morphism of a category of elements is determined by the morphism
of the base it lies over, and the comparison keeps that base. -/
instance faithful_toBaseChangeElements : (toBaseChangeElements a m F).Faithful where
  map_injective {Z Z'} u u' h := by
    refine elements_hom_ext u u' ?_
    exact congrArg TwoFibreProductOver.Hom.a h

/-- The comparison is full: the comparison square of a morphism of the 2-fibre product says that
its second component lies over `Over.map m` of its first, which is exactly the equation a morphism
of the category of elements of `m^{-1}F` has to satisfy. -/
instance full_toBaseChangeElements : (toBaseChangeElements a m F).Full where
  map_surjective {Z Z'} φ := by
    have h : (Over.map m).map φ.a ≫ 𝟙 ((Over.map m).obj Z'.base) =
        𝟙 ((Over.map m).obj Z.base) ≫ φ.b.base := φ.w
    have hw : (Over.map m).map φ.a = φ.b.base := by simpa using h
    refine ⟨⟨φ.a, ⟨?_⟩⟩, ?_⟩
    · have hb : Z.fiber.as = F.map φ.b.base.op Z'.fiber.as := φ.b.fiber.eq
      rw [hb, ← hw]
      rfl
    · refine TwoFibreProductOver.Hom.ext' rfl ?_
      exact elements_hom_ext _ _ hw

/-- The comparison is essentially surjective: an object of the 2-fibre product carries a section
of `F` over the target of its comparison isomorphism, and restricting that section along the
comparison isomorphism produces a section of `m^{-1}F` whose image is isomorphic to the given
object. No transport appears, because the comparison isomorphism is *used* rather than
inverted. -/
instance essSurj_toBaseChangeElements : (toBaseChangeElements a m F).EssSurj where
  mem_essImage P := by
    obtain ⟨hj, hjb⟩ : ∃ hj : (⟨(Over.map m).obj P.x,
        Discrete.mk (F.map P.iso.hom.op P.y.fiber.as)⟩ :
          (presheafOfCategories (F ⋙ typeToCat)).obj) ≅ P.y,
        (discreteProjection F).map hj.hom = P.iso.hom :=
      ⟨elementsIsoOfBaseIso P.iso rfl, rfl⟩
    refine ⟨⟨P.x, Discrete.mk (F.map P.iso.hom.op P.y.fiber.as)⟩, ⟨?_⟩⟩
    refine TwoFibreProductOver.isoMkVertical (U := P.base) (Iso.refl P.x) hj
      (CategoryTheory.IsHomLift.id P.hx) ?_ ?_
    · refine CategoryTheory.IsHomLift.of_fac' _ (𝟙 P.base) hj.hom
        ((Functor.congr_obj (Over.mapComp_eq m a) P.x).symm.trans P.hx) P.hy ?_
      have hv := P.vertical
      have hfac := CategoryTheory.IsHomLift.fac' (Over.map a) (𝟙 P.base) P.iso.hom
      change (Over.map a).map ((discreteProjection F).map hj.hom) = _
      rw [hjb]
      exact hfac
    · change (Over.map m).map (𝟙 P.x) ≫ P.iso.hom =
        𝟙 _ ≫ (discreteProjection F).map hj.hom
      rw [hjb]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      change P.iso.hom = 𝟙 ((Over.map m).obj P.x) ≫ P.iso.hom
      rw [Category.id_comp]

/-- The projection of the category of elements of `F` to `C/X` is fibered in groupoids. -/
private theorem isFiberedInGroupoids_discreteProjection_comp_overMap :
    (discreteProjection F ⋙ Over.map a).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp _ _
    (isFiberedInSetoids_discreteProjection F).isFiberedInGroupoids
    (Functor.IsFiberedInGroupoids.over_map a)

/-- The first projection of the base change of `El F` along `Over.map m` is fibered in
groupoids. -/
private theorem isFiberedInGroupoids_fst_discreteProjection :
    (TwoFibreProductOver.fst (Over.map (m ≫ a)) (discreteProjection F ⋙ Over.map a)
      (Over.map a) (Over.map m) (discreteProjection F)).IsFiberedInGroupoids :=
  isFiberedInGroupoids_fst_overMap_of (m ≫ a)
    (isFiberedInGroupoids_discreteProjection_comp_overMap a F)
    (Functor.IsFiberedInGroupoids.over_map a) (Over.mapComp_eq m a).symm rfl

/-- **The category of elements of `m^{-1}F` is the base change of the category of elements of `F`
along `CategoryTheory.Over.map m`.** -/
theorem nonempty_equivalenceOver_toBaseChangeElements :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (discreteProjection ((OverShriek.relocalizeRestrict m).obj F))
      (TwoFibreProductOver.fst (Over.map (m ≫ a)) (discreteProjection F ⋙ Over.map a)
        (Over.map a) (Over.map m) (discreteProjection F))) := by
  have h₁ : (discreteProjection ((OverShriek.relocalizeRestrict m).obj F)).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids
  exact StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁
    (isFiberedInGroupoids_fst_discreteProjection a m F)
    (toBaseChangeElements a m F) rfl
    ⟨faithful_toBaseChangeElements a m F, full_toBaseChangeElements a m F,
      essSurj_toBaseChangeElements a m F⟩

section Restrict

variable {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  {p𝒳 : 𝒳 ⥤ Over X} {p𝒴 : 𝒴 ⥤ Over X}

/-- **The restriction of a representing presheaf represents the restricted base change.** Let
`y : C/A ⥤ 𝒴` be a point of `𝒴` with values in `A` and let `F` be a presheaf on `C/A` which
represents, over `C/A`, the base change of `G : 𝒳 ⥤ 𝒴` along `y`. Then for `m : A' ⟶ A` the
restriction of `F` along `CategoryTheory.Over.map m` represents, over `C/A'`, the base change of
`G` along the restricted point `Over.map m ⋙ y`. -/
theorem nonempty_equivalenceOver_relocalizeRestrict
    (y : Over A ⥤ 𝒴) (Gf : 𝒳 ⥤ 𝒴)
    (hy : y ⋙ p𝒴 = Over.map a) (hG : Gf ⋙ p𝒴 = p𝒳)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (E : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map a) p𝒳 p𝒴 y Gf) (discreteProjection F)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (m ≫ a)) p𝒳 p𝒴 (Over.map m ⋙ y) Gf)
      (discreteProjection ((OverShriek.relocalizeRestrict m).obj F))) := by
  have hp𝒜 := isFiberedInGroupoids_discreteProjection_comp_overMap a F
  have hp𝒜' : (TwoFibreProductOver.structureFunctor (Over.map a) p𝒳 p𝒴 y Gf
      ).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map a) h𝒳 h𝒴 hy hG
  have hA : E.hom.functor ⋙ (discreteProjection F ⋙ Over.map a) =
      TwoFibreProductOver.structureFunctor (Over.map a) p𝒳 p𝒴 y Gf := by
    rw [← Functor.assoc, E.hom.w, TwoFibreProductOver.fst_comp_eq]
  have _ : Functor.IsEquivalence E.hom.functor :=
    Equivalence.isEquivalence_functor E.toEquivalence
  have hEq := TwoFibreProductOver.isEquivalence_precomposeSnd
    (pT := Over.map (m ≫ a)) (pℬ := Over.map a)
    (G := Over.map m) (F := discreteProjection F) (a := E.hom.functor)
    (Functor.IsFiberedInGroupoids.over_map (m ≫ a)) hp𝒜' hp𝒜 hA rfl
  have key : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (m ≫ a))
        (TwoFibreProductOver.structureFunctor (Over.map a) p𝒳 p𝒴 y Gf) (Over.map a)
        (Over.map m) (E.hom.functor ⋙ discreteProjection F))
      (TwoFibreProductOver.fst (Over.map (m ≫ a)) (discreteProjection F ⋙ Over.map a)
        (Over.map a) (Over.map m) (discreteProjection F))) :=
    StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (isFiberedInGroupoids_fst_overMap_of (m ≫ a) hp𝒜'
        (Functor.IsFiberedInGroupoids.over_map a) (Over.mapComp_eq m a).symm hA)
      (isFiberedInGroupoids_fst_discreteProjection a m F)
      _ (TwoFibreProductOver.precomposeSnd_comp_fst _ _ _ hA) hEq
  rw [E.hom.w] at key
  obtain ⟨k⟩ := key
  obtain ⟨d⟩ := nonempty_equivalenceOver_toBaseChangeElements a m F
  exact ⟨(TwoFibreProductOver.cancelMiddleEquivalenceOver (Over.map (m ≫ a)) p𝒳 p𝒴
    (Over.map a) (Over.map m) Gf y (Over.mapComp_eq m a).symm hy).symm.trans
      (k.trans d.symm)⟩

end Restrict

end CategoryTheory.PresheafOfCategories

end
