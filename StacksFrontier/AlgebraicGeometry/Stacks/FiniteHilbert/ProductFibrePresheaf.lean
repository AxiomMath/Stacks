module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreCover
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.VertHomPresheafGlue
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom

/-!
# The fibre presheaf of Stacks 05YH is the space of sections of the Isom space

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `P = (q : Z ⟶ U, x)` be an object of `ℋ_d(𝒳)`, let `y` be an object of `𝒴` over `U` and let
`y|_Z ⟶ y` be a restriction of `y` along the cover. The fibre computation of Stacks 05YH takes
place over the 2-Yoneda universal family of the object `(P, y)` of `ℋ_d(𝒳) × 𝒴`, and the source
identifies that fibre with the restriction of scalars `Res_{Z/U}(I)` of the Isom space
`I = Isom_𝒴(y|_Z, F x)`.

This file performs the *presheaf* half of that identification, which involves no finite Hilbert
category at all. The presheaf whose category of elements the fibre should be is the one whose
sections over a test object `T / U` are the vertical morphisms between the restrictions of `y|_Z`
and of `F x` to `T ×_U Z`; it is the restriction along the family of covers of the presheaf of
vertical morphisms of Stacks 045G, and it is identified here with the space of sections over `U`
of the relocalization of `I`. Nothing about algebraic spaces, Isom presheaves or spaces of
sections is left in the remaining gap: what remains is the statement that the fibre of the
1-morphism of Equation 05WD is the category of elements of that presheaf of vertical morphisms.

## Main definitions

* `AlgebraicGeometry.Stack.productCoverVertHomPresheaf`: the presheaf on the big fppf site of `Z`
  of vertical morphisms from the chosen restrictions of `y|_Z` to the chosen restrictions of
  `F x`; by Stacks 045G it is the Isom presheaf `Isom_𝒴(y|_Z, F x)`.
* `AlgebraicGeometry.Stack.productFibrePresheaf`: its restriction along the family of covers —
  **the fibre presheaf of Stacks 05YH**.
* `AlgebraicGeometry.Stack.FibreIsVertHomElements`: the statement that every fibre of the
  1-morphism of Equation 05WD over a 2-Yoneda universal family is the category of elements of
  that presheaf.

## Main results

* `AlgebraicGeometry.Stack.productFibrePresheaf_eq_vertHomPresheaf`: the fibre presheaf is the
  presheaf of vertical morphisms of the two reindexed families, on the nose.
* `AlgebraicGeometry.Stack.nonempty_natIso_productFibrePresheaf_sectionSpace`: the fibre presheaf
  is isomorphic, after a universe lift, to the space of sections over `U` of the relocalization
  of a presheaf representing the Isom space.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_productFibrePresheaf_sectionSpace`: hence
  their categories of elements are equivalent over the big fppf site of `U`.
* `AlgebraicGeometry.Stack.productObj_iso_hom_eq`: the comparison isomorphism of an object of the
  product `ℋ_d(𝒳) × 𝒴` is an `eqToHom`.
* `AlgebraicGeometry.Stack.fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom`:
  the fibre identification of Stacks 05YH follows from
  `AlgebraicGeometry.Stack.FibreIsVertHomElements`, the diagonal hypothesis and Stacks 05YF.

## What of Stacks 05YH is and is not proved

Proved: the identification of the fibre presheaf with the space of sections, from the Isom space
of `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover` — which is where the
hypothesis of Stacks 05YH on the diagonal of `𝒴` enters, through Stacks 045G.

No declaration here carries the tag of Stacks 05YH. What this file leaves to be proved is one
statement, with no algebraic space in it: for every object `P` of `ℋ_d(𝒳)`, every object `y` of
`𝒴` over its base and every restriction of `y` to the cover, the 2-fibre product of
`AlgebraicGeometry.Stack.forgetToProduct` with the 2-Yoneda universal family of `(P, y)` is
equivalent, over the big fppf site of the base, to the category of elements of
`AlgebraicGeometry.Stack.productFibrePresheaf`. That is the content of
`AlgebraicGeometry.Stack.FibreIsVertHomElements`, and
`AlgebraicGeometry.Stack.fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom`
turns it into the fibre identification which
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres` needs. It
must not be carried as a hypothesis of a tagged statement: together with Stacks 05YF it is
jointly equivalent to the conclusion of Stacks 05YH, which is why
`AlgebraicGeometry.Stack.fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom`
carries no tag.

That statement **is** proved, in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreEquivalence`, where the fibre is
computed and Stacks 05YH is concluded; this file is the half of the computation that does not
mention a finite Hilbert category.

## Implementation notes

The two families whose vertical morphisms are taken are the *chosen-pullback* 1-morphisms
`CategoryTheory.Functor.pullbackSliceFunctor` of the two objects of the fibre of `𝒴` over `Z`,
and not the cleavage-free families that the finite Hilbert category provides: it is for those
that `CategoryTheory.Functor.vertHomPresheafIsoIsomPresheaf` identifies the presheaf of vertical
morphisms with the Isom presheaf, on the nose. The passage to a cleavage-free family is
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfNatIso`, which needs only
a vertical 2-isomorphism of families and is available for whoever proves the remaining
statement.

The direction of the vertical morphisms is the one Stacks 045G fixes, from the restriction of
`y|_Z` to the restriction of `F x`; the opposite convention is reached by
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafSymmIso`.

The restriction `y|_Z` of `y` along the cover is an **argument**, together with the equality
identifying its base with `Z`: representability asserts only that such a restriction exists, and
a definition choosing one by `Classical.choice` would produce an object about which nothing
further could be said. The same convention is followed for the presheaf `I` representing the Isom
space, for the presentation `w` of its relocalization and for the identification `hw` of the
values of `w`.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertTargetProduct
  absoluteHilbertTargetProductProjection finiteHilbertCategory absoluteHilbertCategory
  absoluteHilbertProjection finiteHilbertProjection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

section VertHom

variable [𝒴.toBasedCategory.p.IsFibered] (P : AbsoluteHilbert.Object B S hS d 𝒳)
  (yZ : 𝒴.toBasedCategory.obj) (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z)

/-- The chosen-pullback 1-morphism of the restriction `y|_Z` of `y` to the cover, as a family of
objects of `𝒴` indexed by the big fppf site of `Z`. -/
noncomputable abbrev coverTargetSlice : Over P.Z.left ⥤ 𝒴.toBasedCategory.obj :=
  Over.iteratedSliceBackward P.Z ⋙
    Functor.pullbackSliceFunctor 𝒴.toBasedCategory.p (Functor.Fiber.mk hyZ)

/-- The chosen-pullback 1-morphism of the image under `F` of the object of `𝒳` carried by `P`,
as a family of objects of `𝒴` indexed by the big fppf site of `Z`. -/
noncomputable abbrev coverSourceSlice : Over P.Z.left ⥤ 𝒴.toBasedCategory.obj :=
  Over.iteratedSliceBackward P.Z ⋙
    Functor.pullbackSliceFunctor 𝒴.toBasedCategory.p
      (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))

/-- **The presheaf of vertical morphisms from the restrictions of `y|_Z` to the restrictions of
`F x`**, on the big fppf site of the cover `Z`. By Stacks 045G it is the Isom presheaf
`Isom_𝒴(y|_Z, F x)`. -/
noncomputable def productCoverVertHomPresheaf : (Over P.Z.left)ᵒᵖ ⥤ Type v₂ :=
  VertHom.presheaf 𝒴.isStackInGroupoids.isFiberedInGroupoids
    (Functor.backward_pullbackSliceFunctor_comp 𝒴.toBasedCategory.p P.Z
      (Functor.Fiber.mk hyZ))
    (Functor.backward_pullbackSliceFunctor_comp 𝒴.toBasedCategory.p P.Z
      (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P)))

/-- **The presheaf of vertical morphisms is the Isom presheaf**, Stacks 045G read at the two
objects of the fibre of `𝒴` over the cover which the fibre computation of Stacks 05YH
compares. -/
noncomputable def productCoverVertHomPresheafIso :
    productCoverVertHomPresheaf (F := F) P yZ hyZ ≅
      (Over.iteratedSliceBackward P.Z).op ⋙ 𝒴.toBasedCategory.p.isomPresheaf
        (Functor.Fiber.mk hyZ)
        (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P)) :=
  Functor.vertHomPresheafIsoIsomPresheaf 𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk hyZ)
    (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))
    𝒴.isStackInGroupoids.isFiberedInGroupoids

end VertHom

/-! ### The fibre presheaf and the space of sections -/

section Fibre

variable [𝒴.toBasedCategory.p.IsFibered] (P : AbsoluteHilbert.Object B S hS d 𝒳)
  (y : 𝒴.toBasedCategory.obj) (hy : 𝒴.toBasedCategory.p.obj y = P.U)
  (yZ : 𝒴.toBasedCategory.obj) (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z)

/-- **The fibre presheaf of Stacks 05YH**: the presheaf on the big fppf site of `U` whose
sections over a test object `T` are the vertical morphisms from the restriction of `y|_Z` to the
restriction of `F x`, both taken to the cover `T ×_U Z` of the member of the universal family at
`T`. -/
noncomputable def productFibrePresheaf : (Over P.U.left)ᵒᵖ ⥤ Type v₂ :=
  (productFamilyCover P y hy).op ⋙ productCoverVertHomPresheaf (F := F) P yZ hyZ

/-- **The fibre presheaf is a presheaf of vertical morphisms**, namely the one of the two
families of objects of `𝒴` obtained by restricting `y|_Z` and `F x` along the family of covers.
This is
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_comp_op`, and it is what makes
the fibre presheaf accessible to
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfNatIso`. -/
theorem productFibrePresheaf_eq_vertHomPresheaf
    (h₁ : (productFamilyCover P y hy ⋙ coverTargetSlice P yZ hyZ) ⋙
      𝒴.toBasedCategory.p = productFamilyCover P y hy ⋙ Over.map P.Z.hom)
    (h₂ : (productFamilyCover P y hy ⋙ coverSourceSlice (F := F) P) ⋙
      𝒴.toBasedCategory.p = productFamilyCover P y hy ⋙ Over.map P.Z.hom) :
    productFibrePresheaf (F := F) P y hy yZ hyZ =
      VertHom.presheaf 𝒴.isStackInGroupoids.isFiberedInGroupoids h₁ h₂ :=
  VertHom.presheaf_comp_op (productFamilyCover P y hy)
    𝒴.isStackInGroupoids.isFiberedInGroupoids _ _ h₁ h₂

variable (I : (BigFppfOver B P.Z.left.1 P.Z.left.2)ᵒᵖ ⥤ Type u)
  (w : (OverShriek.relocalizePresheafFunctor P.q.left).obj I ⟶
    yoneda.obj (Over.mk P.q.left : BigFppfOver B (B.inclusion.obj P.U.left) P.U.left.property))
  (hw : ∀ (T : BigFppfOver B (B.inclusion.obj P.U.left) P.U.left.property)
    (s : ((OverShriek.relocalizePresheafFunctor P.q.left).obj I).obj (op T)),
    (w.app (op T) s).left = s.val.fst)

/-- **The space of sections over `U` of the relocalization of a presheaf on the big fppf site of
`Z` is its restriction along the family of covers.** This is
`AlgebraicGeometry.Stack.productFamilySectionEquiv`, read as an isomorphism of presheaves. -/
noncomputable def sectionSpaceIsoCoverPullback :
    Space.sectionSpace B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left)
        ((OverShriek.relocalizePresheafFunctor P.q.left).obj I) w ≅
      (productFamilyCover P y hy).op ⋙ I :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (productFamilySectionEquiv P y hy I w hw T.unop))
    (by
      intro T T' f
      ext s
      exact productFamilySectionEquiv_map P y hy I w hw f.unop s)

include hw in
/-- **The fibre presheaf of Stacks 05YH is the space of sections over `U` of the relocalization
of the Isom space.** The Isom space is a presheaf `I` on the big fppf site of the cover
isomorphic, after a universe lift, to `Isom_𝒴(y|_Z, F x)`; the fibre presheaf is the restriction
of that Isom presheaf along the family of covers
(`AlgebraicGeometry.Stack.productCoverVertHomPresheafIso`), and the restriction of `I` along the
family of covers is the space of sections
(`AlgebraicGeometry.Stack.sectionSpaceIsoCoverPullback`). -/
theorem nonempty_natIso_productFibrePresheaf_sectionSpace
    (hI : Nonempty (I ⋙ uliftFunctor.{v₂, u} ≅
      ((Over.iteratedSliceBackward P.Z).op ⋙ 𝒴.toBasedCategory.p.isomPresheaf
          (Functor.Fiber.mk hyZ)
          (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))) ⋙
        uliftFunctor.{u, v₂})) :
    Nonempty (productFibrePresheaf (F := F) P y hy yZ hyZ ⋙ uliftFunctor.{u, v₂} ≅
      Space.sectionSpace B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left)
          ((OverShriek.relocalizePresheafFunctor P.q.left).obj I) w ⋙
        uliftFunctor.{v₂, u}) := by
  obtain ⟨i⟩ := hI
  refine ⟨?_⟩
  refine (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (productFamilyCover P y hy).op
    (productCoverVertHomPresheafIso (F := F) P yZ hyZ)) uliftFunctor.{u, v₂}).trans ?_
  refine (eqToIso (CategoryTheory.Functor.assoc _ _ _)).trans ?_
  refine (Functor.isoWhiskerLeft (productFamilyCover P y hy).op i.symm).trans ?_
  refine (eqToIso (CategoryTheory.Functor.assoc _ _ _).symm).trans ?_
  exact Functor.isoWhiskerRight
    (sectionSpaceIsoCoverPullback P y hy I w hw).symm uliftFunctor.{v₂, u}

include hw in
/-- **The category of elements of the fibre presheaf is equivalent, over the big fppf site of
`U`, to the category of elements of the space of sections.** The category of elements of a
presheaf of sets determines the presheaf, so this is
`AlgebraicGeometry.Stack.nonempty_natIso_productFibrePresheaf_sectionSpace` read through
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_iff`. -/
theorem nonempty_equivalenceOver_productFibrePresheaf_sectionSpace
    (hI : Nonempty (I ⋙ uliftFunctor.{v₂, u} ≅
      ((Over.iteratedSliceBackward P.Z).op ⋙ 𝒴.toBasedCategory.p.isomPresheaf
          (Functor.Fiber.mk hyZ)
          (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))) ⋙
        uliftFunctor.{u, v₂})) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (productFibrePresheaf (F := F) P y hy yZ hyZ ⋙ typeToCat)).p
      (presheafOfCategories (Space.sectionSpace B (B.inclusion.obj P.U.left)
        P.U.left.property (Over.mk P.q.left)
        ((OverShriek.relocalizePresheafFunctor P.q.left).obj I) w ⋙ typeToCat)).p) :=
  (PresheafOfCategories.nonempty_equivalenceOver_iff _ _).2
    (nonempty_natIso_productFibrePresheaf_sectionSpace P y hy yZ hyZ I w hw hI)

end Fibre

/-! ### The remaining statement of Stacks 05YH -/

/-- The comparison isomorphism of an object of the product `ℋ_d(𝒳) × 𝒴` is an `eqToHom`: the
structure functor of the product is the identity of the site, so a vertical morphism of the
product is a vertical morphism of the site. -/
theorem productObj_iso_hom_eq (X : (absoluteHilbertTargetProduct
    (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj) :
    X.iso.hom = eqToHom (X.hx.trans X.hy.symm) := by
  have hv := X.vertical
  have h := IsHomLift.fac' (𝟭 (BigFppfOver B S hS)) (𝟙 X.base) X.iso.hom
  simp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map] at h
  rw [h]
  simp

variable (B S hS d 𝒳 𝒴 F) in
/-- **The one statement of Stacks 05YH which the library does not prove**: for an object `P` of
`ℋ_d(𝒳)`, an object `y` of `𝒴` over the base of `P` and a restriction `y|_Z ⟶ y` of `y` along the
cover, the 2-fibre product of the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD with the
2-Yoneda universal family of `(P, y)` is equivalent, over the big fppf site of the base, to the
category of elements of the fibre presheaf
`AlgebraicGeometry.Stack.productFibrePresheaf`.

An object of that 2-fibre product over a test object `T / U` is an object of `ℋ_d(𝒳/𝒴)`
restricting to `(P, y)`, that is a choice of identification of `F x` with `y|_Z` after base
change to `T ×_U Z`; a section of the fibre presheaf over `T` is exactly such an
identification. No algebraic space occurs in the statement.

This must **not** be carried as a hypothesis of a statement tagged with Stacks 05YH: together
with Stacks 05YF it is jointly equivalent to the conclusion, and would leave the hypothesis of
Stacks 05YH on the diagonal of `𝒴` unused. -/
abbrev FibreIsVertHomElements [𝒴.toBasedCategory.p.IsFibered] : Prop :=
  ∀ (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
    (hy : 𝒴.toBasedCategory.p.obj y = P.U) (yZ : 𝒴.toBasedCategory.obj) (φ : yZ ⟶ y),
    𝒴.toBasedCategory.p.IsHomLift P.q φ →
    ∀ hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map P.U.hom)
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p
          (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
            (𝒴 := 𝒴)).p
          (productFamily P y hy)
          (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
            (F := F)).toFunctor)
        (presheafOfCategories (productFibrePresheaf (F := F) P y hy yZ hyZ ⋙ typeToCat)).p)

/-- **The fibre identification of Stacks 05YH follows from the statement about vertical
morphisms.** Given `AlgebraicGeometry.Stack.FibreIsVertHomElements`, the diagonal hypothesis of
Stacks 05YH and Stacks 05YF, every fibre of the 1-morphism of Equation 05WD over a 2-Yoneda
universal family is representable by an algebraic space: the fibre presheaf is the space of
sections over the base of the relocalization of the Isom space
(`AlgebraicGeometry.Stack.nonempty_equivalenceOver_productFibrePresheaf_sectionSpace`), and that
space of sections is an algebraic space by Stacks 05YF
(`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf`).

Composing with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres` would give
Stacks 05YH; no tag is claimed here, because the hypothesis
`AlgebraicGeometry.Stack.FibreIsVertHomElements` is not a legitimate carried input. -/
theorem fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom
    [𝒴.toBasedCategory.p.IsFibered]
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴)))
    (hfib : FibreIsVertHomElements B S hS d 𝒳 𝒴 F) :
    FibresOverObjUniversalFamiliesAlgebraic
      (isFiberedInGroupoids_absoluteHilbertTargetProductProjection
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) := by
  intro X
  obtain ⟨base, Px, yy, hx, hy, iso, hv⟩ := X
  cases hx
  obtain rfl : iso = eqToIso hy.symm := by
    exact Iso.ext (productObj_iso_hom_eq
      (⟨_, Px, yy, rfl, hy, iso, hv⟩ : (absoluteHilbertTargetProduct
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj))
  obtain ⟨yZ, φ, hφ, hyZ, I, hI, hiso, halg⟩ :=
    exists_isAlgebraicSpace_restrictionOfScalars_isomPresheaf (F := F) hΔ Px yy hy
  exact ⟨_, halg, ⟨(hfib Px yy hy yZ φ hφ hyZ).some.trans
    (nonempty_equivalenceOver_productFibrePresheaf_sectionSpace Px yy hy yZ hyZ I
      (OverShriek.relocalizeToYoneda Px.q.left I) (fun _ _ => rfl) hiso).some⟩⟩

end AlgebraicGeometry.Stack

end
