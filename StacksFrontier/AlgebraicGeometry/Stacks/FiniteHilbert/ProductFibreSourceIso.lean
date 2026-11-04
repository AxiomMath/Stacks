module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibrePresheaf

/-!
# The objects of `𝒴` carried by the universal family are the chosen restrictions of `F x`

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `P = (q : Z ⟶ U, x)` be an object of `ℋ_d(𝒳)` and let `y` be an object of `𝒴` over `U`. The
member of the 2-Yoneda universal family of `(P, y)` at a test object `T / U` carries an object of
`𝒳` over the cover `T ×_U Z`, namely a restriction of `x`; its image under `F` is therefore a
restriction of `F x`, and this file identifies it with the *chosen* restriction of `F x` to
`T ×_U Z`.

Both are strongly cartesian lifts, to objects over `T ×_U Z`, of one and the same morphism of the
big fppf site, so they are canonically isomorphic by a vertical isomorphism, and the
identification is natural in the test object because both sides are determined by their
composites with a strongly cartesian morphism to `F x`.

The point of the identification is that the fibre presheaf
`AlgebraicGeometry.Stack.productFibrePresheaf` is spelled with the chosen restrictions — that is
what makes it the Isom presheaf of Stacks 045G on the nose — while the fibre of the 1-morphism of
Equation 05WD produces the restrictions that the finite Hilbert category carries. Combined with
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfNatIso` and
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafSymmIso`, this file replaces the
chosen restrictions of `F x` by the cleavage-free ones and reverses the direction of the vertical
morphisms, giving the shape in which the fibre is to be computed.

## Main definitions

* `AlgebraicGeometry.Stack.productSourceFunctor`: the functor remembering only the object of `𝒳`
  carried by an object of the product `ℋ_d(𝒳) × 𝒴`.
* `AlgebraicGeometry.Stack.productFamilySource`: the family of objects of `𝒴` obtained by applying
  `F` to the objects of `𝒳` carried by the universal family.
* `AlgebraicGeometry.Stack.productFamilySourceIso`: the vertical identification of a member of
  that family with the chosen restriction of `F x`.
* `AlgebraicGeometry.Stack.productFamilySourceNatIso`: the same, as a 2-isomorphism of families.
* `AlgebraicGeometry.Stack.productFibrePresheafSource`: the fibre presheaf in its cleavage-free
  shape — the presheaf of vertical morphisms from `F x|_{T ×_U Z}` to the chosen restriction of
  `y|_Z`.

## Main results

* `AlgebraicGeometry.Stack.productSourceFunctor_comp` and
  `AlgebraicGeometry.Stack.productFamilySource_comp`: the two families are 1-morphisms over the
  site.
* `AlgebraicGeometry.Stack.productFamilySourceIso_over`: the identification is vertical.
* `AlgebraicGeometry.Stack.productFibrePresheafSourceIso`: the cleavage-free fibre presheaf is
  isomorphic to `AlgebraicGeometry.Stack.productFibrePresheaf`.
* `AlgebraicGeometry.Stack.fibreIsVertHomElements_of_source`: the cleavage-free form of the
  statement about vertical morphisms, `AlgebraicGeometry.Stack.FibreIsVertHomSourceElements`,
  implies the form stated with the Isom presheaf; and, composed with the previous file,
  the fibre identification of Stacks 05YH.

## What is and is not proved

Proved, in full, with no carried hypothesis: the identification of the two shapes of the fibre
presheaf. No tag is claimed: the file states no result of the Stacks project, it is a step of the
fibre computation of Stacks 05YH and is the analogue, for the 1-morphism of Equation 05WD, of
`AlgebraicGeometry.Stack.familySourceNatIso` in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace`.

`AlgebraicGeometry.Stack.FibreIsVertHomSourceElements` is the fibre computation itself, stated so
that it can be consumed before being proved; it must not be carried as a hypothesis of a tagged
statement, because together with Stacks 05YF it is jointly equivalent to the conclusion of
Stacks 05YH. It **is** proved, in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreEquivalence`, as
`AlgebraicGeometry.Stack.fibreIsVertHomSourceElements`, and Stacks 05YH is concluded there.

## Implementation notes

The chosen restriction of `F x` is the value of
`CategoryTheory.Functor.pullbackSliceFunctor`, whose strongly cartesian morphism to `F x` is
`CategoryTheory.Functor.IsPreFibered.pullbackMap`; the strong cartesianness of the morphism
coming from the universal family is the fibredness in groupoids of `𝒴`, applied to the image
under `F` of the morphism of `𝒳`, which lies over the cover component because `F` is a
1-morphism over the site.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertTargetProduct
  absoluteHilbertTargetProductProjection finiteHilbertCategory absoluteHilbertCategory
  absoluteHilbertProjection finiteHilbertProjection productCoverFunctor
  CategoryTheory.Over.iteratedSliceBackward CategoryTheory.Over.homMk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The functor remembering only the object of `𝒳` carried by an object of the product
`ℋ_d(𝒳) × 𝒴`. -/
def productSourceFunctor :
    (absoluteHilbertTargetProduct
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj ⥤
      𝒳.toBasedCategory.obj where
  obj W := W.x.x
  map φ := φ.a.a
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [local implicit_reducible] productSourceFunctor

/-- The image under `F` of the object of `𝒳` carried by an object of the product lies over the
cover of that object: the two families of objects of `𝒴` and of the site are compatible. -/
theorem productSourceFunctor_comp :
    (productSourceFunctor (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) ⋙
        F.toFunctor) ⋙ 𝒴.toBasedCategory.p =
      productCoverFunctor (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) := by
  refine CategoryTheory.Functor.ext
    (fun W => (BasedFunctor.w_obj F W.x.x).trans W.x.x_over) ?_
  intro W W' φ
  have ha := φ.a.a_over
  have h : 𝒴.toBasedCategory.p.IsHomLift φ.a.cover.g (F.toFunctor.map φ.a.a) :=
    BasedFunctor.preserves_isHomLift F _ _
  exact IsHomLift.fac' 𝒴.toBasedCategory.p φ.a.cover.g (F.toFunctor.map φ.a.a)

variable (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
  (hy : 𝒴.toBasedCategory.p.obj y = P.U)

/-- The family of objects of `𝒴` obtained by applying `F` to the objects of `𝒳` carried by the
2-Yoneda universal family of `(P, y)`. -/
noncomputable abbrev productFamilySource : Over P.U.left ⥤ 𝒴.toBasedCategory.obj :=
  productFamily P y hy ⋙ productSourceFunctor ⋙ F.toFunctor

/-- `AlgebraicGeometry.Stack.productFamilySource` is a 1-morphism over the big fppf site: its
member at a test object lies over the corresponding member of the family of covers. -/
theorem productFamilySource_comp :
    productFamilySource (F := F) P y hy ⋙ 𝒴.toBasedCategory.p =
      productFamilyCover P y hy ⋙ Over.map P.Z.hom := by
  rw [productFamilyCover_base, ← productSourceFunctor_comp (F := F)]
  rfl

/-- The image under `F` of the morphism of `𝒳` underlying the chosen morphism out of a member of
the universal family is strongly cartesian over the cover component. -/
theorem productFamilySourceArrow_isStronglyCartesian (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsStronglyCartesian (productFamilyArrowHilbert P y hy T).cover.g
      (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a) := by
  have ha := (productFamilyArrowHilbert P y hy T).a_over
  have h : 𝒴.toBasedCategory.p.IsHomLift (productFamilyArrowHilbert P y hy T).cover.g
      (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a) :=
    BasedFunctor.preserves_isHomLift F (productFamilyArrowHilbert P y hy T).cover.g
      (productFamilyArrowHilbert P y hy T).a
  exact 𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift
    (productFamilyArrowHilbert P y hy T).cover.g
    (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a)


section Iso

variable [𝒴.toBasedCategory.p.IsFibered]

/-- The chosen strongly cartesian morphism from the chosen restriction of `F x` to `F x`. -/
noncomputable abbrev coverSourceArrow (A : Over P.Z.left) :
    (coverSourceSlice (F := F) P).obj A ⟶ F.obj P.x :=
  Functor.IsPreFibered.pullbackMap
    (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P)).2
    ((Over.iteratedSliceBackward P.Z).obj A).hom

/-- The chosen morphism out of a chosen restriction of `F x` is strongly cartesian. -/
theorem coverSourceArrow_isStronglyCartesian (A : Over P.Z.left) :
    𝒴.toBasedCategory.p.IsStronglyCartesian
      ((Over.iteratedSliceBackward P.Z).obj A).hom (coverSourceArrow (F := F) P A) := by
  have h : 𝒴.toBasedCategory.p.IsCartesian
      ((Over.iteratedSliceBackward P.Z).obj A).hom (coverSourceArrow (F := F) P A) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  exact Functor.IsFibered.isStronglyCartesian_of_isCartesian 𝒴.toBasedCategory.p
    ((Over.iteratedSliceBackward P.Z).obj A).hom (coverSourceArrow (F := F) P A)

/-- The chosen morphisms out of the chosen restrictions of `F x` are compatible with the
transition morphisms of the family of chosen restrictions. -/
theorem coverSourceArrow_naturality {A A' : Over P.Z.left} (h : A ⟶ A') :
    (coverSourceSlice (F := F) P).map h ≫ coverSourceArrow (F := F) P A' =
      coverSourceArrow (F := F) P A :=
  Functor.pullbackFiberMap_fac 𝒴.toBasedCategory.p _ ((Over.iteratedSliceBackward P.Z).map h)

/-- **The image under `F` of the object of `𝒳` carried by a member of the universal family is
the chosen restriction of `F x` to the corresponding member of the family of covers**: both are
strongly cartesian lifts of one and the same morphism of the site. -/
noncomputable def productFamilySourceIso (T : Over P.U.left) :
    (productFamilySource (F := F) P y hy).obj T ≅
      (coverSourceSlice (F := F) P).obj ((productFamilyCover P y hy).obj T) :=
  have _h₁ := coverSourceArrow_isStronglyCartesian (F := F) P ((productFamilyCover P y hy).obj T)
  have _h₂ := productFamilySourceArrow_isStronglyCartesian (F := F) P y hy T
  Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒴.toBasedCategory.p
    (g := eqToIso (productFamilyCover_base_obj P y hy T).symm)
    (productFamilyCover_arrow P y hy T)
    (coverSourceArrow (F := F) P ((productFamilyCover P y hy).obj T))
    (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a)

/-- `AlgebraicGeometry.Stack.productFamilySourceIso` is vertical. -/
theorem productFamilySourceIso_over (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map P.Z.hom).obj ((productFamilyCover P y hy).obj T)))
      (productFamilySourceIso (F := F) P y hy T).hom := by
  have h₁ := coverSourceArrow_isStronglyCartesian (F := F) P ((productFamilyCover P y hy).obj T)
  have h₂ := productFamilySourceArrow_isStronglyCartesian (F := F) P y hy T
  have h : 𝒴.toBasedCategory.p.IsHomLift
      (eqToHom (productFamilyCover_base_obj P y hy T).symm)
      (productFamilySourceIso (F := F) P y hy T).hom :=
    Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift 𝒴.toBasedCategory.p
      (g := eqToIso (productFamilyCover_base_obj P y hy T).symm)
      (productFamilyCover_arrow P y hy T)
      (coverSourceArrow (F := F) P ((productFamilyCover P y hy).obj T))
      (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a)
  have hd := IsHomLift.domain_eq 𝒴.toBasedCategory.p
    (eqToHom (productFamilyCover_base_obj P y hy T).symm)
    (productFamilySourceIso (F := F) P y hy T).hom
  have hc := IsHomLift.codomain_eq 𝒴.toBasedCategory.p
    (eqToHom (productFamilyCover_base_obj P y hy T).symm)
    (productFamilySourceIso (F := F) P y hy T).hom
  refine IsHomLift.of_fac' _ _ _
    (hd.trans (productFamilyCover_base_obj P y hy T).symm) hc ?_
  rw [IsHomLift.fac' _ (eqToHom (productFamilyCover_base_obj P y hy T).symm)
    (productFamilySourceIso (F := F) P y hy T).hom]
  simp

/-- `AlgebraicGeometry.Stack.productFamilySourceIso` is compatible with the chosen morphisms to
`F x`. -/
theorem productFamilySourceIso_fac (T : Over P.U.left) :
    (productFamilySourceIso (F := F) P y hy T).hom ≫
        coverSourceArrow (F := F) P ((productFamilyCover P y hy).obj T) =
      F.toFunctor.map (productFamilyArrowHilbert P y hy T).a := by
  have h₁ := coverSourceArrow_isStronglyCartesian (F := F) P ((productFamilyCover P y hy).obj T)
  have h₂ := productFamilySourceArrow_isStronglyCartesian (F := F) P y hy T
  have h₃ : 𝒴.toBasedCategory.p.IsHomLift (productFamilyArrowHilbert P y hy T).cover.g
      (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a) := h₂.toIsHomLift
  dsimp only [productFamilySourceIso, Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p
    ((Over.iteratedSliceBackward P.Z).obj ((productFamilyCover P y hy).obj T)).hom
    (coverSourceArrow (F := F) P ((productFamilyCover P y hy).obj T))
    (productFamilyCover_arrow P y hy T)
    (F.toFunctor.map (productFamilyArrowHilbert P y hy T).a)

/-- **The objects of `𝒴` carried by the universal family are the chosen restrictions of `F x`
reindexed along the family of covers.** The components are
`AlgebraicGeometry.Stack.productFamilySourceIso`; naturality holds because both sides are
morphisms to a strongly cartesian lift over one morphism of the site. -/
noncomputable def productFamilySourceNatIso :
    productFamilySource (F := F) P y hy ≅
      productFamilyCover P y hy ⋙ coverSourceSlice (F := F) P :=
  NatIso.ofComponents (productFamilySourceIso (F := F) P y hy) (by
    intro T T' f
    change F.toFunctor.map ((productFamily P y hy).map f).a.a ≫
        (productFamilySourceIso (F := F) P y hy T').hom =
      (productFamilySourceIso (F := F) P y hy T).hom ≫
        (coverSourceSlice (F := F) P).map ((productFamilyCover P y hy).map f)
    have hsc := coverSourceArrow_isStronglyCartesian (F := F) P
      ((productFamilyCover P y hy).obj T')
    have hi := productFamilySourceIso_over (F := F) P y hy T
    have hi' := productFamilySourceIso_over (F := F) P y hy T'
    have hr : 𝒴.toBasedCategory.p.IsHomLift
        ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f))
        ((coverSourceSlice (F := F) P).map ((productFamilyCover P y hy).map f)) :=
      Functor.isHomLift_map_of_comp_eq (Functor.backward_pullbackSliceFunctor_comp
        𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk
          (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))) _ _
    have haa := ((productFamily P y hy).map f).a.a_over
    have ha : 𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.g
        (F.toFunctor.map ((productFamily P y hy).map f).a.a) :=
      BasedFunctor.preserves_isHomLift F ((productFamily P y hy).map f).a.cover.g
        ((productFamily P y hy).map f).a.a
    have hl' : 𝒴.toBasedCategory.p.IsHomLift
        ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f))
        (F.toFunctor.map ((productFamily P y hy).map f).a.a) := by
      refine IsHomLift.of_fac' _ _ _
        (((BasedFunctor.w_obj F ((productFamily P y hy).obj T).x.x).trans
          ((productFamily P y hy).obj T).x.x_over).trans
          (productFamilyCover_base_obj P y hy T).symm)
        (((BasedFunctor.w_obj F ((productFamily P y hy).obj T').x.x).trans
          ((productFamily P y hy).obj T').x.x_over).trans
          (productFamilyCover_base_obj P y hy T').symm) ?_
      rw [IsHomLift.fac' _ ((productFamily P y hy).map f).a.cover.g
        (F.toFunctor.map ((productFamily P y hy).map f).a.a)]
      have h : (Over.map P.Z.hom).map ((productFamilyCover P y hy).map f) =
          eqToHom (productFamilyCover_base_obj P y hy T) ≫
            ((productFamily P y hy).map f).a.cover.g ≫
            eqToHom (productFamilyCover_base_obj P y hy T').symm :=
        CategoryTheory.Functor.congr_hom (productFamilyCover_base P y hy) f
      rw [h]
      simp
    have hh₁ : 𝒴.toBasedCategory.p.IsHomLift
        ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f))
        (F.toFunctor.map ((productFamily P y hy).map f).a.a ≫
          (productFamilySourceIso (F := F) P y hy T').hom) :=
      IsHomLift.comp_lift_id_right 𝒴.toBasedCategory.p _ _ _
    have hh₂ : 𝒴.toBasedCategory.p.IsHomLift
        ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f))
        ((productFamilySourceIso (F := F) P y hy T).hom ≫
          (coverSourceSlice (F := F) P).map ((productFamilyCover P y hy).map f)) :=
      IsHomLift.comp_lift_id_left 𝒴.toBasedCategory.p _ _ _
    refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p
      ((Over.iteratedSliceBackward P.Z).obj ((productFamilyCover P y hy).obj T')).hom
      (coverSourceArrow (F := F) P ((productFamilyCover P y hy).obj T'))
      ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f)) ?_
    rw [Category.assoc, productFamilySourceIso_fac, Category.assoc,
      coverSourceArrow_naturality, productFamilySourceIso_fac, ← F.toFunctor.map_comp]
    exact congrArg (fun g => F.toFunctor.map g.a)
      (productFamilyArrowHilbert_naturality P y hy f))

/-! ### The fibre presheaf in its cleavage-free shape -/

section Cleavage

variable (yZ : 𝒴.toBasedCategory.obj) (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z)

/-- The family of chosen restrictions of `y|_Z` along the family of covers is a 1-morphism over
the big fppf site. -/
theorem productFamilyCoverTargetSlice_comp :
    (productFamilyCover P y hy ⋙ coverTargetSlice P yZ hyZ) ⋙ 𝒴.toBasedCategory.p =
      productFamilyCover P y hy ⋙ Over.map P.Z.hom := by
  rw [CategoryTheory.Functor.assoc,
    Functor.backward_pullbackSliceFunctor_comp 𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk hyZ)]

/-- The family of chosen restrictions of `F x` along the family of covers is a 1-morphism over
the big fppf site. -/
theorem productFamilyCoverSourceSlice_comp :
    (productFamilyCover P y hy ⋙ coverSourceSlice (F := F) P) ⋙ 𝒴.toBasedCategory.p =
      productFamilyCover P y hy ⋙ Over.map P.Z.hom := by
  rw [CategoryTheory.Functor.assoc,
    Functor.backward_pullbackSliceFunctor_comp 𝒴.toBasedCategory.p P.Z
      (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))]

/-- **The fibre presheaf of Stacks 05YH in its cleavage-free shape**: the presheaf on the big
fppf site of `U` whose sections over a test object `T` are the vertical morphisms from the image
under `F` of the object of `𝒳` carried by the member of the universal family at `T` to the chosen
restriction of `y|_Z` to the cover `T ×_U Z`.

This is the shape in which the fibre of the 1-morphism of Equation 05WD presents itself: an
object of the fibre over `T` carries an identification of `F x|_{T ×_U Z}` with the restriction
of `y`, and nothing of the chosen cleavage of `𝒴` occurs on the source side. -/
noncomputable def productFibrePresheafSource : (Over P.U.left)ᵒᵖ ⥤ Type v₂ :=
  VertHom.presheaf 𝒴.isStackInGroupoids.isFiberedInGroupoids
    (productFamilySource_comp (F := F) P y hy)
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ)

/-- **The cleavage-free fibre presheaf is isomorphic to the fibre presheaf.** Replacing the
chosen restrictions of `F x` by the images under `F` of the objects of `𝒳` carried by the
universal family is
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafIsoOfNatIso` applied to
`AlgebraicGeometry.Stack.productFamilySourceNatIso`, and reversing the direction of the vertical
morphisms is
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafSymmIso`. -/
noncomputable def productFibrePresheafSourceIso :
    productFibrePresheafSource (F := F) P y hy yZ hyZ ≅
      productFibrePresheaf (F := F) P y hy yZ hyZ := by
  refine (VertHom.presheafSymmIso 𝒴.isStackInGroupoids.isFiberedInGroupoids
    (productFamilySource_comp (F := F) P y hy)
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ)).trans ?_
  refine (VertHom.presheafIsoOfNatIso 𝒴.isStackInGroupoids.isFiberedInGroupoids
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ)
    (productFamilySource_comp (F := F) P y hy)
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ)
    (productFamilyCoverSourceSlice_comp (F := F) P y hy)
    (Iso.refl _) (productFamilySourceNatIso (F := F) P y hy)
    (fun a => IsHomLift.id (CategoryTheory.Functor.congr_obj
      (productFamilyCoverTargetSlice_comp P y hy yZ hyZ) a))
    (fun a => productFamilySourceIso_over (F := F) P y hy a)).trans ?_
  exact (eqToIso (productFibrePresheaf_eq_vertHomPresheaf (F := F) P y hy yZ hyZ
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ)
    (productFamilyCoverSourceSlice_comp (F := F) P y hy))).symm

end Cleavage

end Iso

/-! ### The remaining statement, in its cleavage-free shape -/

variable (B S hS d 𝒳 𝒴 F) in
/-- **The one statement of Stacks 05YH which the library does not prove, in its cleavage-free
shape**: for an object `P = (q : Z ⟶ U, x)` of `ℋ_d(𝒳)`, an object `y` of `𝒴` over `U` and a
restriction `y|_Z ⟶ y` of `y` along the cover, the 2-fibre product of the 1-morphism
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD with the 2-Yoneda universal family of `(P, y)` is
equivalent, over the big fppf site of `U`, to the category of elements of
`AlgebraicGeometry.Stack.productFibrePresheafSource`.

A section of that presheaf over a test object `T / U` is a vertical isomorphism from
`F x|_{T ×_U Z}` — the image under `F` of the object of `𝒳` that the member of the universal
family at `T` carries over its cover `T ×_U Z` — to the restriction of `y|_Z` to `T ×_U Z`; an
object of the 2-fibre product over `T` is an object of `ℋ_d(𝒳/𝒴)` restricting to `(P, y)`, which
is exactly such an isomorphism. No algebraic space, no Isom presheaf and no chosen cleavage on
the source side occur in the statement.

This must **not** be carried as a hypothesis of a statement tagged with Stacks 05YH: together
with Stacks 05YF it is jointly equivalent to the conclusion. -/
abbrev FibreIsVertHomSourceElements [𝒴.toBasedCategory.p.IsFibered] : Prop :=
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
        (presheafOfCategories
          (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).p)

/-- **The cleavage-free form of the remaining statement implies the form stated with the Isom
presheaf.** The two fibre presheaves are isomorphic by
`AlgebraicGeometry.Stack.productFibrePresheafSourceIso`, and isomorphic presheaves of sets have
equivalent categories of elements over the base. -/
theorem fibreIsVertHomElements_of_source [𝒴.toBasedCategory.p.IsFibered]
    (h : FibreIsVertHomSourceElements B S hS d 𝒳 𝒴 F) :
    FibreIsVertHomElements B S hS d 𝒳 𝒴 F := by
  intro P y hy yZ φ hφ hyZ
  exact ⟨(h P y hy yZ φ hφ hyZ).some.trans
    (PresheafOfCategories.equivalenceOverOfIso
      (productFibrePresheafSourceIso (F := F) P y hy yZ hyZ))⟩

/-- **The fibre identification of Stacks 05YH follows from the cleavage-free statement about
vertical morphisms.** This is
`AlgebraicGeometry.Stack.fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom`
read through `AlgebraicGeometry.Stack.fibreIsVertHomElements_of_source`; composing it with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres` would give
Stacks 05YH. No tag is claimed: the hypothesis
`AlgebraicGeometry.Stack.FibreIsVertHomSourceElements` is not a legitimate carried input. -/
theorem fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHomSource
    [𝒴.toBasedCategory.p.IsFibered]
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴)))
    (hfib : FibreIsVertHomSourceElements B S hS d 𝒳 𝒴 F) :
    FibresOverObjUniversalFamiliesAlgebraic
      (isFiberedInGroupoids_absoluteHilbertTargetProductProjection
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) :=
  fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHom hΔ
    (fibreIsVertHomElements_of_source hfib)

end AlgebraicGeometry.Stack

end
