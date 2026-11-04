module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreSourceIso
public import StacksFrontier.AlgebraicGeometry.Stacks.ReindexedSectionRepresentation

/-!
# The 1-morphism of Equation 05WD is representable by algebraic spaces (Stacks 05YH)

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. Stacks 05YH asserts that the 1-morphism

`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`

of Equation 05WD is representable by algebraic spaces as soon as the diagonal `𝒴 ⟶ 𝒴 × 𝒴` is
representable by algebraic spaces. This file proves it by computing the fibre.

Fix an object `P = (q : Z ⟶ U, x)` of `ℋ_d(𝒳)`, an object `y` of `𝒴` over `U` and a restriction
`φ : y|_Z ⟶ y` of `y` along the cover. An object of the fibre of Equation 05WD over the 2-Yoneda
universal family of `(P, y)`, at a test object `T / U`, is an object of `ℋ_d(𝒳/𝒴)` together with
a vertical identification of its image in the product with the member of the universal family at
`T`; up to that identification its data is the cover `T ×_U Z`, the restriction of `x` to it, the
restriction of `y` to `T`, and an identification `α` of the image under `F` of the first with the
second. Such an `α` is the same thing as a vertical morphism from `F x|_{T ×_U Z}` to the
restriction of `y|_Z` to `T ×_U Z`, because the restriction of `y` to `T` and the restriction of
`y|_Z` to `T ×_U Z` are both restrictions of `y` along the two edges of one cartesian square; so
the fibre is the category of elements of
`AlgebraicGeometry.Stack.productFibrePresheafSource`, which is identified with the space of
sections over `U` of the relocalization of the Isom space `Isom_𝒴(y|_Z, F x)`.

## Main definitions

* `AlgebraicGeometry.Stack.coverTargetArrow`: the chosen strongly cartesian morphism from a
  chosen restriction of `y|_Z` to `y|_Z`.
* `AlgebraicGeometry.Stack.productFamilyTargetArrow`: the morphism, over the cover of the member
  of the universal family at `T`, from the chosen restriction of `y|_Z` to `T ×_U Z` to the
  object of `𝒴` carried by that member.
* `AlgebraicGeometry.Stack.fibreObject` and `AlgebraicGeometry.Stack.fibreMap`: the object and
  the morphism of `ℋ_d(𝒳/𝒴)` attached to a section of the fibre presheaf and to a restriction
  relation between two sections.
* `AlgebraicGeometry.Stack.productFibre`: the fibre itself, the 2-fibre product of the
  1-morphism of Equation 05WD with the universal family.
* `AlgebraicGeometry.Stack.productFibreFunctor`: the comparison 1-morphism from the category of
  elements of the fibre presheaf to the fibre.
* `AlgebraicGeometry.Stack.fibreObjSection`: the section of the fibre presheaf named by an object
  of the fibre.

## Main results

* `AlgebraicGeometry.Stack.productFamilyTargetArrow_fac` and
  `AlgebraicGeometry.Stack.productFamilyTargetArrow_naturality`: the defining equation of the
  restriction morphism and its naturality in the test object.
* `AlgebraicGeometry.Stack.productFibreFunctor_faithful`,
  `AlgebraicGeometry.Stack.productFibreFunctor_full` and
  `AlgebraicGeometry.Stack.hasVerticalPreimages_productFibreFunctor`: the comparison 1-morphism
  is fully faithful and admits vertical preimages.
* `AlgebraicGeometry.Stack.fibreEquivalenceOver`: **the fibre computation**, the fibre is
  equivalent over the big fppf site of `U` to the category of elements of the fibre presheaf.
* `AlgebraicGeometry.Stack.fibreIsVertHomSourceElements` and
  `AlgebraicGeometry.Stack.fibres_absoluteHilbertTargetProduct_forgetToProduct`: the fibre
  computation for every object of the product, and the resulting representability of every fibre
  by an algebraic space.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpacesForgetToProduct_of_diagonal`: the
  1-morphism of Equation 05WD is representable by algebraic spaces when the diagonal of `𝒴` is.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertTargetProduct
  absoluteHilbertTargetProductProjection finiteHilbertCategory absoluteHilbertCategory
  absoluteHilbertProjection finiteHilbertProjection productCoverFunctor productSourceFunctor
  CategoryTheory.Over.iteratedSliceBackward CategoryTheory.Over.homMk
  forgetToProduct forgetRelativeStructure forgetTarget
  CategoryTheory.TwoFibreProductOver.lift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  [𝒴.toBasedCategory.p.IsFibered]
  (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
  (hy : 𝒴.toBasedCategory.p.obj y = P.U) (yZ : 𝒴.toBasedCategory.obj)
  (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z)

/-- The chosen strongly cartesian morphism from a chosen restriction of `y|_Z` to `y|_Z`. -/
noncomputable abbrev coverTargetArrow (A : Over P.Z.left) :
    (coverTargetSlice P yZ hyZ).obj A ⟶ yZ :=
  Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk hyZ).2
    ((Over.iteratedSliceBackward P.Z).obj A).hom

/-- The chosen morphism out of a chosen restriction of `y|_Z` lies over the structure morphism of
the test object. -/
theorem coverTargetArrow_over (A : Over P.Z.left) :
    𝒴.toBasedCategory.p.IsHomLift ((Over.iteratedSliceBackward P.Z).obj A).hom
      (coverTargetArrow P yZ hyZ A) :=
  (Functor.IsPreFibered.pullbackMap.IsCartesian (Functor.Fiber.mk hyZ).2
    ((Over.iteratedSliceBackward P.Z).obj A).hom).toIsHomLift

/-- The chosen morphisms out of the chosen restrictions of `y|_Z` are compatible with the
transition morphisms of the family of chosen restrictions. -/
theorem coverTargetArrow_naturality {A A' : Over P.Z.left} (h : A ⟶ A') :
    (coverTargetSlice P yZ hyZ).map h ≫ coverTargetArrow P yZ hyZ A' =
      coverTargetArrow P yZ hyZ A :=
  Functor.pullbackFiberMap_fac 𝒴.toBasedCategory.p _ ((Over.iteratedSliceBackward P.Z).map h)

/-- The chosen morphism out of the chosen restriction of `y|_Z` to the cover of the member of the
universal family at a test object lies over the cover component of the chosen morphism out of
that member. -/
theorem coverTargetArrow_over_cover (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsHomLift (productFamilyArrowHilbert P y hy T).cover.g
      (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T)) := by
  have h := coverTargetArrow_over P yZ hyZ ((productFamilyCover P y hy).obj T)
  refine IsHomLift.of_fac' _ _ _
    ((CategoryTheory.Functor.congr_obj (Functor.backward_pullbackSliceFunctor_comp
        𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk hyZ))
      ((productFamilyCover P y hy).obj T)).trans
      (productFamilyCover_base_obj P y hy T)) hyZ ?_
  rw [IsHomLift.fac' _ ((Over.iteratedSliceBackward P.Z).obj
    ((productFamilyCover P y hy).obj T)).hom
    (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T)),
    productFamilyCover_arrow P y hy T]
  simp

/-- The `𝒴`-component of a morphism of a 2-fibre product lies over the image of its
`𝒳`-component in the base. -/
private theorem isHomLift_map_a_b {𝒞 𝒳' 𝒴' 𝒮 : Type*} [Category 𝒞] [Category 𝒳'] [Category 𝒴']
    [Category 𝒮] {p𝒳 : 𝒳' ⥤ 𝒞} {p𝒴 : 𝒴' ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {G₁ : 𝒳' ⥤ 𝒮} {G₂ : 𝒴' ⥤ 𝒮}
    {X X' : TwoFibreProductOver p𝒳 p𝒴 p𝒮 G₁ G₂} (f : X.Hom X') :
    p𝒴.IsHomLift (p𝒳.map f.a) f.b := by
  have ha := f.ha
  rw [IsHomLift.fac' p𝒳 f.hbase f.a, IsHomLift.lift_eqToHom_comp_iff]
  exact (IsHomLift.lift_comp_eqToHom_iff _ _ _ _).2 f.hb

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The morphism of `𝒴` underlying the chosen morphism out of a member of the universal family
lies over the base component of the morphism of `ℋ_d(𝒳)` underlying it. -/
theorem productFamilyArrowTarget_over_cover_f (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsHomLift (productFamilyArrowHilbert P y hy T).cover.f
      (productFamilyArrow P y hy T).b :=
  isHomLift_map_a_b (productFamilyArrow P y hy T)

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The morphism of `𝒴` underlying the chosen morphism out of a member of the universal family
is strongly cartesian over the base component. -/
theorem productFamilyArrowTarget_isStronglyCartesian (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsStronglyCartesian (productFamilyArrowHilbert P y hy T).cover.f
      (productFamilyArrow P y hy T).b :=
  have _h := productFamilyArrowTarget_over_cover_f P y hy T
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift
    (productFamilyArrowHilbert P y hy T).cover.f (productFamilyArrow P y hy T).b

variable (φ : yZ ⟶ y) (hφ : 𝒴.toBasedCategory.p.IsHomLift P.q φ)

include hφ in
/-- The composite of the chosen morphism out of the chosen restriction of `y|_Z` with the
restriction `y|_Z ⟶ y` lies over the lower edge of the cartesian square of the chosen morphism
out of the member of the universal family. -/
theorem isHomLift_coverTargetArrow_comp (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsHomLift
      ((productFamilyArrowHilbert P y hy T).cover.g ≫ P.q)
      (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ) := by
  have h₁ := coverTargetArrow_over_cover P y hy yZ hyZ T
  have h₂ := hφ
  infer_instance

include hφ in
/-- **The restriction of `y|_Z` to the cover of a member of the universal family maps to the
object of `𝒴` that the member carries.** The morphism is the unique one over the cover, supplied
by the strong cartesianness of the morphism of `𝒴` underlying the chosen morphism out of the
member. -/
noncomputable def productFamilyTargetArrow (T : Over P.U.left) :
    (coverTargetSlice P yZ hyZ).obj ((productFamilyCover P y hy).obj T) ⟶
      ((productFamily P y hy).obj T).y := by
  have h₁ : 𝒴.toBasedCategory.p.IsStronglyCartesian
      (productFamilyArrowHilbert P y hy T).cover.f (productFamilyArrow P y hy T).b :=
    productFamilyArrowTarget_isStronglyCartesian P y hy T
  have h₂ : 𝒴.toBasedCategory.p.IsHomLift (productFamilyArrowHilbert P y hy T).cover.g
      (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T)) :=
    coverTargetArrow_over_cover P y hy yZ hyZ T
  have h₃ : 𝒴.toBasedCategory.p.IsHomLift P.q φ := hφ
  have h₄ : 𝒴.toBasedCategory.p.IsHomLift
      ((productFamilyArrowHilbert P y hy T).cover.g ≫ P.q)
      (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ) := inferInstance
  exact @Functor.IsStronglyCartesian.map _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
    (productFamilyArrowHilbert P y hy T).cover.f (productFamilyArrow P y hy T).b h₁ _ _
    ((productFamily P y hy).obj T).x.q
    ((productFamilyArrowHilbert P y hy T).cover.g ≫ P.q)
    (productFamilyArrowHilbert P y hy T).cover.square.w
    (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ) h₄

include hφ in
/-- The defining equation of `AlgebraicGeometry.Stack.productFamilyTargetArrow`. -/
theorem productFamilyTargetArrow_fac (T : Over P.U.left) :
    productFamilyTargetArrow P y hy yZ hyZ φ hφ T ≫ (productFamilyArrow P y hy T).b =
      coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ := by
  exact @Functor.IsStronglyCartesian.fac _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
    (productFamilyArrowHilbert P y hy T).cover.f (productFamilyArrow P y hy T).b
    (productFamilyArrowTarget_isStronglyCartesian P y hy T) _ _
    ((productFamily P y hy).obj T).x.q ((productFamilyArrowHilbert P y hy T).cover.g ≫ P.q)
    (productFamilyArrowHilbert P y hy T).cover.square.w
    (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ)
    (isHomLift_coverTargetArrow_comp P y hy yZ hyZ φ hφ T)

include hφ in
/-- `AlgebraicGeometry.Stack.productFamilyTargetArrow` lies over the cover of the member of the
universal family. -/
theorem productFamilyTargetArrow_over (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).obj T).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ T) := by
  exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
    (productFamilyArrowHilbert P y hy T).cover.f (productFamilyArrow P y hy T).b
    (productFamilyArrowTarget_isStronglyCartesian P y hy T) _ _
    ((productFamily P y hy).obj T).x.q ((productFamilyArrowHilbert P y hy T).cover.g ≫ P.q)
    (productFamilyArrowHilbert P y hy T).cover.square.w
    (coverTargetArrow P yZ hyZ ((productFamilyCover P y hy).obj T) ≫ φ)
    (isHomLift_coverTargetArrow_comp P y hy yZ hyZ φ hφ T)

/-- `AlgebraicGeometry.Stack.productFamilyTargetArrow` is strongly cartesian over the cover of the
member of the universal family at the test object. -/
private theorem isStronglyCartesian_productFamilyTargetArrow (T : Over P.U.left) :
    𝒴.toBasedCategory.p.IsStronglyCartesian ((productFamily P y hy).obj T).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ T) :=
  have _h := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ T
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift
    ((productFamily P y hy).obj T).x.q (productFamilyTargetArrow P y hy yZ hyZ φ hφ T)

/-! ### The object of `ℋ_d(𝒳/𝒴)` attached to a section of the fibre presheaf -/

/-- A section of the fibre presheaf over a test object is vertical over the cover of the member
of the universal family there. -/
theorem isHomLift_productFibrePresheafSource_val (T : Over P.U.left)
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T)) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 ((productFamily P y hy).obj T).x.Z) ψ.1 := by
  have hψ := ψ.2
  refine IsHomLift.of_fac' _ _ _
    (((BasedFunctor.w_obj F ((productFamily P y hy).obj T).x.x).trans
      ((productFamily P y hy).obj T).x.x_over))
    ((CategoryTheory.Functor.congr_obj (Functor.backward_pullbackSliceFunctor_comp
        𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk hyZ))
      ((productFamilyCover P y hy).obj T)).trans
      (productFamilyCover_base_obj P y hy T)) ?_
  rw [IsHomLift.fac' 𝒴.toBasedCategory.p
    (𝟙 ((productFamilyCover P y hy ⋙ Over.map P.Z.hom).obj T)) ψ.1]
  simp

include hφ in
/-- **The object of `ℋ_d(𝒳/𝒴)` attached to a section of the fibre presheaf.** Its cover, its
object of `𝒳` and its object of `𝒴` are those of the member of the universal family at the test
object, and its identification is the section followed by
`AlgebraicGeometry.Stack.productFamilyTargetArrow`. -/
noncomputable def fibreObject (T : Over P.U.left)
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T)) :
    FiniteHilbert.Object B S hS 𝒳 𝒴 F d where
  U := ((productFamily P y hy).obj T).x.U
  Z := ((productFamily P y hy).obj T).x.Z
  q := ((productFamily P y hy).obj T).x.q
  finiteLocallyFree := ((productFamily P y hy).obj T).x.finiteLocallyFree
  y := ((productFamily P y hy).obj T).y
  y_over := (((productFamily P y hy).obj T).hy).trans (((productFamily P y hy).obj T).hx).symm
  x := ((productFamily P y hy).obj T).x.x
  x_over := ((productFamily P y hy).obj T).x.x_over
  α := ψ.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T
  α_over := by
    have h₁ := isHomLift_productFibrePresheafSource_val P y hy yZ hyZ T ψ
    have h₂ := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ T
    exact IsHomLift.comp_lift_id_left 𝒴.toBasedCategory.p
      ((productFamily P y hy).obj T).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ T) ψ.1

attribute [local implicit_reducible] fibreObject

include hφ in
/-- The vertical morphism of the product from the member of the universal family at a test
object to the image under the 1-morphism of Equation 05WD of the object attached to a section of
the fibre presheaf. Both components are identities: the two objects of the product differ only in
the spelling of their base. -/
noncomputable def fibreObjectHom (T : Over P.U.left)
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T)) :
    (productFamily P y hy).obj T ⟶
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor.obj (fibreObject P y hy yZ hyZ φ hφ T ψ) where
  hbase := eqToHom (((productFamily P y hy).obj T).hx).symm
  a := 𝟙 ((productFamily P y hy).obj T).x
  b := 𝟙 ((productFamily P y hy).obj T).y
  ha := IsHomLift.id_lift_eqToHom_domain (((productFamily P y hy).obj T).hx).symm
    ((productFamily P y hy).obj T).hx
  hb := IsHomLift.id_lift_eqToHom_domain (((productFamily P y hy).obj T).hx).symm
    ((productFamily P y hy).obj T).hy
  w := by
    have e1 := productObj_iso_hom_eq ((productFamily P y hy).obj T)
    have e2 := productObj_iso_hom_eq ((forgetToProduct (B := B) (S := S) (hS := hS)
      (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor.obj
      (fibreObject P y hy yZ hyZ φ hφ T ψ))
    rw [e1, e2]
    simp

attribute [local implicit_reducible] fibreObjectHom

include hφ in
/-- `AlgebraicGeometry.Stack.fibreObjectHom` is an isomorphism. -/
theorem isIso_fibreObjectHom (T : Over P.U.left)
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T)) :
    IsIso (fibreObjectHom P y hy yZ hyZ φ hφ T ψ) := by
  have h₁ : IsIso (fibreObjectHom P y hy yZ hyZ φ hφ T ψ).hbase := by
    show IsIso (eqToHom (((productFamily P y hy).obj T).hx).symm)
    infer_instance
  have h₂ : IsIso (fibreObjectHom P y hy yZ hyZ φ hφ T ψ).a := by
    show IsIso (𝟙 ((productFamily P y hy).obj T).x)
    infer_instance
  have h₃ : IsIso (fibreObjectHom P y hy yZ hyZ φ hφ T ψ).b := by
    show IsIso (𝟙 ((productFamily P y hy).obj T).y)
    infer_instance
  exact isIso_twoFibreProductOver_hom (fibreObjectHom P y hy yZ hyZ φ hφ T ψ)

include hφ in
/-- The image under the 1-morphism of Equation 05WD of the object attached to a section of the
fibre presheaf is the member of the universal family, up to a vertical isomorphism of the
product. -/
noncomputable def fibreObjectIso (T : Over P.U.left)
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T)) :
    (productFamily P y hy).obj T ≅
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor.obj (fibreObject P y hy yZ hyZ φ hφ T ψ) :=
  have _h := isIso_fibreObjectHom P y hy yZ hyZ φ hφ T ψ
  asIso (fibreObjectHom P y hy yZ hyZ φ hφ T ψ)

/-! ### Naturality of the restriction morphism -/

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The morphism of `𝒴` underlying a transition morphism of the universal family lies over the
base component of the morphism of `ℋ_d(𝒳)` underlying it. -/
theorem productFamilyMapTarget_over_cover_f {T T' : Over P.U.left} (f : T ⟶ T') :
    𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.f
      ((productFamily P y hy).map f).b :=
  isHomLift_map_a_b ((productFamily P y hy).map f)

/-- The transition morphism of the family of chosen restrictions of `y|_Z` lies over the cover
component of the transition morphism of the universal family. -/
theorem coverTargetSlice_map_over_cover {T T' : Over P.U.left} (f : T ⟶ T') :
    𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.g
      ((coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f)) := by
  have h : 𝒴.toBasedCategory.p.IsHomLift
      ((Over.map P.Z.hom).map ((productFamilyCover P y hy).map f))
      ((coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f)) :=
    Functor.isHomLift_map_of_comp_eq (Functor.backward_pullbackSliceFunctor_comp
      𝒴.toBasedCategory.p P.Z (Functor.Fiber.mk hyZ)) _ _
  have hc : (Over.map P.Z.hom).map ((productFamilyCover P y hy).map f) =
      eqToHom (productFamilyCover_base_obj P y hy T) ≫
        ((productFamily P y hy).map f).a.cover.g ≫
        eqToHom (productFamilyCover_base_obj P y hy T').symm :=
    CategoryTheory.Functor.congr_hom (productFamilyCover_base P y hy) f
  rwa [hc, IsHomLift.lift_eqToHom_comp_iff, IsHomLift.lift_comp_eqToHom_iff] at h

include hφ in
/-- **`AlgebraicGeometry.Stack.productFamilyTargetArrow` is natural in the test object.** -/
theorem productFamilyTargetArrow_naturality {T T' : Over P.U.left} (f : T ⟶ T') :
    (coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f) ≫
        productFamilyTargetArrow P y hy yZ hyZ φ hφ T' =
      productFamilyTargetArrow P y hy yZ hyZ φ hφ T ≫ ((productFamily P y hy).map f).b := by
  have hsc : 𝒴.toBasedCategory.p.IsStronglyCartesian
      (productFamilyArrowHilbert P y hy T').cover.f (productFamilyArrow P y hy T').b :=
    productFamilyArrowTarget_isStronglyCartesian P y hy T'
  have hL₁ := coverTargetSlice_map_over_cover P y hy yZ hyZ f
  have hL₂ := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ T'
  have hR₁ := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ T
  have hR₂ := productFamilyMapTarget_over_cover_f P y hy f
  have hLl : 𝒴.toBasedCategory.p.IsHomLift
      (((productFamily P y hy).map f).a.cover.g ≫ ((productFamily P y hy).obj T').x.q)
      ((coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f) ≫
        productFamilyTargetArrow P y hy yZ hyZ φ hφ T') := inferInstance
  have hRl : 𝒴.toBasedCategory.p.IsHomLift
      (((productFamily P y hy).obj T).x.q ≫ ((productFamily P y hy).map f).a.cover.f)
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ T ≫
        ((productFamily P y hy).map f).b) := inferInstance
  rw [← ((productFamily P y hy).map f).a.cover.square.w] at hRl
  have hbnat : ((productFamily P y hy).map f).b ≫ (productFamilyArrow P y hy T').b =
      (productFamilyArrow P y hy T).b :=
    congrArg (fun g => g.b) (objUniversalArrow_naturality
      isFiberedInGroupoids_absoluteHilbertTargetProductProjection (productPoint P y hy) f)
  refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p
    (productFamilyArrowHilbert P y hy T').cover.f (productFamilyArrow P y hy T').b
    (((productFamily P y hy).map f).a.cover.g ≫
      ((productFamily P y hy).obj T').x.q) ?_
  simp only [Category.assoc]
  rw [productFamilyTargetArrow_fac, hbnat, productFamilyTargetArrow_fac,
    ← coverTargetArrow_naturality P yZ hyZ ((productFamilyCover P y hy).map f)]
  exact (Category.assoc _ _ _).symm

/-! ### The morphism of `ℋ_d(𝒳/𝒴)` attached to a restriction relation between sections -/

include hφ in
/-- **The morphism of `ℋ_d(𝒳/𝒴)` attached to a morphism of test objects and a restriction
relation between sections of the fibre presheaf.** Its four components are those of the
transition morphism of the universal family. -/
noncomputable def fibreMap {T T' : Over P.U.left} (f : T ⟶ T')
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T))
    (ψ' : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T'))
    (hψ : ψ = (productFibrePresheafSource (F := F) P y hy yZ hyZ).map f.op ψ') :
    fibreObject P y hy yZ hyZ φ hφ T ψ ⟶ fibreObject P y hy yZ hyZ φ hφ T' ψ' where
  f := ((productFamily P y hy).map f).a.cover.f
  g := ((productFamily P y hy).map f).a.cover.g
  square := ((productFamily P y hy).map f).a.cover.square
  b := ((productFamily P y hy).map f).b
  b_over := productFamilyMapTarget_over_cover_f P y hy f
  a := ((productFamily P y hy).map f).a.a
  a_over := ((productFamily P y hy).map f).a.a_over
  compatible := by
    have hfac : ψ.1 ≫
        (coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f) =
        F.toFunctor.map ((productFamily P y hy).map f).a.a ≫ ψ'.1 := by
      rw [hψ]
      exact VertHom.restrict_fac 𝒴.isStackInGroupoids.isFiberedInGroupoids
        (productFamilySource_comp (F := F) P y hy)
        (productFamilyCoverTargetSlice_comp P y hy yZ hyZ) f ψ'
    change F.toFunctor.map ((productFamily P y hy).map f).a.a ≫
        (ψ'.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T') =
      (ψ.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T) ≫
        ((productFamily P y hy).map f).b
    simp only [Category.assoc]
    rw [← productFamilyTargetArrow_naturality P y hy yZ hyZ φ hφ f, ← Category.assoc, ← hfac]
    exact Category.assoc _ _ _

/-! ### The comparison 1-morphism -/

attribute [local implicit_reducible] fibreObjectIso fibreMap CategoryTheory.asIso

/-- The 2-fibre product of the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD with the
2-Yoneda universal family of the object `(P, y)` of the product — the fibre of Stacks 05YH. -/
noncomputable abbrev productFibre :=
  TwoFibreProductOver (Over.map P.U.hom)
    (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
    (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).p
    (productFamily P y hy)
    (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor

include hφ in
/-- **The comparison 1-morphism from the category of elements of the fibre presheaf to the fibre
of the 1-morphism of Equation 05WD.** A section of the fibre presheaf over a test object is sent
to the object of `ℋ_d(𝒳/𝒴)` it names, together with the vertical isomorphism identifying the
image of that object in the product with the member of the universal family. -/
noncomputable def productFibreFunctor :
    (presheafOfCategories
        (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).obj ⥤
      productFibre (F := F) P y hy where
  obj E :=
    { base := ((productFamily P y hy).obj E.base).base
      x := E.base
      y := fibreObject P y hy yZ hyZ φ hφ E.base E.fiber.as
      hx := (objUniversalFamily_base_obj
        isFiberedInGroupoids_absoluteHilbertTargetProductProjection
        (productPoint P y hy) E.base).symm
      hy := ((productFamily P y hy).obj E.base).hx
      iso := fibreObjectIso P y hy yZ hyZ φ hφ E.base E.fiber.as
      vertical := by
        refine IsHomLift.of_fac' _ _ _ rfl ((productFamily P y hy).obj E.base).hx ?_
        change eqToHom (((productFamily P y hy).obj E.base).hx).symm = _
        simp only [Category.id_comp]
        exact (eqToHom_trans _ _).symm }
  map {E E'} u :=
    TwoFibreProductOver.Hom.mk' u.base
      (fibreMap P y hy yZ hyZ φ hφ u.base E.fiber.as E'.fiber.as (Discrete.eq_of_hom u.fiber))
      (by
        have h1 : eqToHom (((productFamily P y hy).obj E.base).hx).symm ≫
              (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
                (d := d)).p.map (fibreMap P y hy yZ hyZ φ hφ u.base E.fiber.as E'.fiber.as
                  (Discrete.eq_of_hom u.fiber)) ≫
              eqToHom ((productFamily P y hy).obj E'.base).hx =
            ((productFamily P y hy).map u.base).hbase :=
          (((productFamily P y hy).map u.base).hbase_eq).symm
        have h2 : ((productFamily P y hy).map u.base).hbase =
            eqToHom (objUniversalFamily_base_obj
              isFiberedInGroupoids_absoluteHilbertTargetProductProjection
              (productPoint P y hy) E.base) ≫
            (Over.map P.U.hom).map u.base ≫
            eqToHom (objUniversalFamily_base_obj
              isFiberedInGroupoids_absoluteHilbertTargetProductProjection
              (productPoint P y hy) E'.base).symm :=
          CategoryTheory.Functor.congr_hom (objUniversalFamily_comp
            isFiberedInGroupoids_absoluteHilbertTargetProductProjection
            (productPoint P y hy)) u.base
        exact h1.trans h2)
      (TwoFibreProductOver.Hom.ext'
        (by
          change ((productFamily P y hy).map u.base).a ≫
              𝟙 ((productFamily P y hy).obj E'.base).x =
            𝟙 ((productFamily P y hy).obj E.base).x ≫
              ((productFamily P y hy).map u.base).a
          simp)
        (by
          change ((productFamily P y hy).map u.base).b ≫
              𝟙 ((productFamily P y hy).obj E'.base).y =
            𝟙 ((productFamily P y hy).obj E.base).y ≫
              ((productFamily P y hy).map u.base).b
          simp))
  map_id E := by
    refine TwoFibreProductOver.Hom.ext' rfl ?_
    refine FiniteHilbert.Hom.ext ?_ ?_ ?_ ?_
    · change ((productFamily P y hy).map (𝟙 E.base)).a.cover.f = _
      rw [(productFamily P y hy).map_id]
      rfl
    · change ((productFamily P y hy).map (𝟙 E.base)).a.cover.g = _
      rw [(productFamily P y hy).map_id]
      rfl
    · change ((productFamily P y hy).map (𝟙 E.base)).b = _
      rw [(productFamily P y hy).map_id]
      rfl
    · change ((productFamily P y hy).map (𝟙 E.base)).a.a = _
      rw [(productFamily P y hy).map_id]
      rfl
  map_comp {E E' E''} u v := by
    refine TwoFibreProductOver.Hom.ext' rfl ?_
    refine FiniteHilbert.Hom.ext ?_ ?_ ?_ ?_
    · change ((productFamily P y hy).map (u.base ≫ v.base)).a.cover.f = _
      rw [(productFamily P y hy).map_comp]
      rfl
    · change ((productFamily P y hy).map (u.base ≫ v.base)).a.cover.g = _
      rw [(productFamily P y hy).map_comp]
      rfl
    · change ((productFamily P y hy).map (u.base ≫ v.base)).b = _
      rw [(productFamily P y hy).map_comp]
      rfl
    · change ((productFamily P y hy).map (u.base ≫ v.base)).a.a = _
      rw [(productFamily P y hy).map_comp]
      rfl

/-! ### The comparison 1-morphism is fully faithful -/

include hφ in
/-- **The comparison 1-morphism is faithful.** -/
theorem productFibreFunctor_faithful :
    (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).Faithful :=
  ⟨fun {_E _E'} {u v} h =>
    PresheafOfCategories.elements_hom_ext u v (congrArg TwoFibreProductOver.Hom.a h)⟩

include hφ in
/-- For a morphism `χ` of the fibre between two objects in the image of the comparison
1-morphism, the transition morphism of the universal family along `χ.a` has the components of the
morphism of `ℋ_d(𝒳/𝒴)` carried by `χ`. -/
theorem productFibreFunctor_hom_components {E E' :
    (presheafOfCategories
      (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).obj}
    (χ : (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).obj E ⟶
      (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).obj E') :
    ((productFamily P y hy).map χ.a).a =
        (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)).toFunctor.map χ.b ∧
      ((productFamily P y hy).map χ.a).b = χ.b.b := by
  constructor
  · have h : ((productFamily P y hy).map χ.a).a ≫ 𝟙 ((productFamily P y hy).obj E'.base).x =
        𝟙 ((productFamily P y hy).obj E.base).x ≫
          (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
            (F := F)).toFunctor.map χ.b :=
      congrArg TwoFibreProductOver.Hom.a χ.w
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  · have h : ((productFamily P y hy).map χ.a).b ≫ 𝟙 ((productFamily P y hy).obj E'.base).y =
        𝟙 ((productFamily P y hy).obj E.base).y ≫ χ.b.b :=
      congrArg TwoFibreProductOver.Hom.b χ.w
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

include hφ in
/-- **A compatibility of the two identifications is a restriction relation between the two
sections of the fibre presheaf.** -/
theorem productFibrePresheafSource_restrict_of_compatible {T T' : Over P.U.left} (f : T ⟶ T')
    (ψ : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T))
    (ψ' : (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op T'))
    (h : (ψ.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T) ≫
        ((productFamily P y hy).map f).b =
      F.toFunctor.map ((productFamily P y hy).map f).a.a ≫
        (ψ'.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T')) :
    ψ = (productFibrePresheafSource (F := F) P y hy yZ hyZ).map f.op ψ' := by
  have hν' := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ T'
  have hsc := isStronglyCartesian_productFamilyTargetArrow P y hy yZ hyZ φ hφ T'
  have hv₁ := isHomLift_productFibrePresheafSource_val P y hy yZ hyZ T ψ
  have hv₂ := isHomLift_productFibrePresheafSource_val P y hy yZ hyZ T' ψ'
  have hcg := coverTargetSlice_map_over_cover P y hy yZ hyZ f
  have haao : 𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.g
      (F.toFunctor.map ((productFamily P y hy).map f).a.a) := by
    have := ((productFamily P y hy).map f).a.a_over
    exact BasedFunctor.preserves_isHomLift F ((productFamily P y hy).map f).a.cover.g
      ((productFamily P y hy).map f).a.a
  have hl₁ : 𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.g
      (ψ.1 ≫ (productFamilyCover P y hy ⋙ coverTargetSlice P yZ hyZ).map f) :=
    IsHomLift.comp_lift_id_left 𝒴.toBasedCategory.p
      ((productFamily P y hy).map f).a.cover.g
      ((coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f)) ψ.1
  have hl₂ : 𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).map f).a.cover.g
      ((productFamilySource (F := F) P y hy).map f ≫ ψ'.1) :=
    IsHomLift.comp_lift_id_right 𝒴.toBasedCategory.p
      ((productFamily P y hy).map f).a.cover.g
      (F.toFunctor.map ((productFamily P y hy).map f).a.a) ψ'.1
  refine VertHom.restrict_uniq 𝒴.isStackInGroupoids.isFiberedInGroupoids
    (productFamilySource_comp (F := F) P y hy)
    (productFamilyCoverTargetSlice_comp P y hy yZ hyZ) f ψ' ψ ?_
  refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p
    ((productFamily P y hy).obj T').x.q
    (productFamilyTargetArrow P y hy yZ hyZ φ hφ T')
    ((productFamily P y hy).map f).a.cover.g ?_
  calc (ψ.1 ≫ (productFamilyCover P y hy ⋙ coverTargetSlice P yZ hyZ).map f) ≫
        productFamilyTargetArrow P y hy yZ hyZ φ hφ T'
      = ψ.1 ≫ ((coverTargetSlice P yZ hyZ).map ((productFamilyCover P y hy).map f) ≫
          productFamilyTargetArrow P y hy yZ hyZ φ hφ T') := Category.assoc _ _ _
    _ = ψ.1 ≫ (productFamilyTargetArrow P y hy yZ hyZ φ hφ T ≫
          ((productFamily P y hy).map f).b) := by
        rw [productFamilyTargetArrow_naturality P y hy yZ hyZ φ hφ f]
    _ = (ψ.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T) ≫
          ((productFamily P y hy).map f).b := (Category.assoc _ _ _).symm
    _ = F.toFunctor.map ((productFamily P y hy).map f).a.a ≫
          (ψ'.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ T') := h
    _ = ((productFamilySource (F := F) P y hy).map f ≫ ψ'.1) ≫
          productFamilyTargetArrow P y hy yZ hyZ φ hφ T' := (Category.assoc _ _ _).symm

include hφ in
/-- A morphism of the fibre between two objects in the image of the comparison 1-morphism
witnesses the restriction relation between the two sections of the fibre presheaf. -/
theorem productFibreFunctor_restrict_of_hom {E E' :
    (presheafOfCategories
      (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).obj}
    (χ : (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).obj E ⟶
      (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).obj E') :
    E.fiber.as =
      (productFibrePresheafSource (F := F) P y hy yZ hyZ).map χ.a.op E'.fiber.as := by
  obtain ⟨hwa, hwb⟩ := productFibreFunctor_hom_components P y hy yZ hyZ φ hφ χ
  have haa : ((productFamily P y hy).map χ.a).a.a = χ.b.a :=
    congrArg (fun t => t.a) hwa
  have hcomp := χ.b.compatible
  change F.toFunctor.map χ.b.a ≫
      (E'.fiber.as.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ E'.base) =
    (E.fiber.as.1 ≫ productFamilyTargetArrow P y hy yZ hyZ φ hφ E.base) ≫ χ.b.b at hcomp
  rw [← haa, ← hwb] at hcomp
  exact productFibrePresheafSource_restrict_of_compatible (T := E.base) (T' := E'.base)
    P y hy yZ hyZ φ hφ χ.a E.fiber.as E'.fiber.as hcomp.symm

include hφ in
/-- **The comparison 1-morphism is full**: every morphism of the fibre between two objects in its
image is the image of a morphism of the category of elements. -/
theorem productFibreFunctor_full : (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).Full := by
  refine ⟨fun {E E'} χ => ?_⟩
  obtain ⟨hwa, hwb⟩ := productFibreFunctor_hom_components P y hy yZ hyZ φ hφ χ
  refine ⟨⟨χ.a, eqToHom (congrArg Discrete.mk
    (productFibreFunctor_restrict_of_hom P y hy yZ hyZ φ hφ χ))⟩,
    TwoFibreProductOver.Hom.ext' rfl (FiniteHilbert.Hom.ext ?_ ?_ hwb ?_)⟩
  · exact congrArg (fun t => t.cover.f) hwa
  · exact congrArg (fun t => t.cover.g) hwa
  · exact congrArg (fun t => t.a) hwa

/-! ### Vertical preimages -/

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The functor remembering only the object of `𝒳` carried by an object of `ℋ_d(𝒳)`. -/
def absoluteHilbertSourceFunctor :
    AbsoluteHilbert.Object B S hS d 𝒳 ⥤ 𝒳.toBasedCategory.obj where
  obj Q := Q.x
  map ψ := ψ.a
  map_id _ := rfl
  map_comp _ _ := rfl

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The functor remembering only the cover of an object of `ℋ_d(𝒳)`. -/
def absoluteHilbertCoverFunctor :
    AbsoluteHilbert.Object B S hS d 𝒳 ⥤ BigFppfOver B S hS where
  obj Q := Q.Z
  map ψ := ψ.cover.g
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [local implicit_reducible] absoluteHilbertSourceFunctor absoluteHilbertCoverFunctor

variable (R : productFibre (F := F) P y hy)

/-- The morphism of `ℋ_d(𝒳)` underlying the inverse of the comparison isomorphism of an object
of the fibre. -/
noncomputable abbrev fibreObjComparison : (forgetToProduct (B := B) (S := S) (hS := hS)
    (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor.obj R.y ⟶
      (productFamily P y hy).obj R.x :=
  R.iso.inv

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The inverse of the comparison isomorphism of an object of the fibre is vertical. -/
theorem fibreObjComparison_vertical :
    (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := 𝒴)).p.IsHomLift (𝟙 R.base) R.iso.inv := by
  have hv := R.vertical
  exact IsHomLift.lift_id_inv (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS)
    (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).p R.base R.iso

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The `ℋ_d(𝒳)`-component of the inverse of the comparison isomorphism of an object of the
fibre is vertical. -/
theorem fibreObjComparison_a_vertical :
    (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p.IsHomLift
      (𝟙 R.base) R.iso.inv.a := by
  have hv := fibreObjComparison_vertical (F := F) P y hy R
  have ha := R.iso.inv.ha
  have hfac : (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
      (𝒴 := 𝒴)).p.map R.iso.inv = eqToHom (IsHomLift.domain_eq _ (𝟙 R.base) R.iso.inv) ≫
        𝟙 R.base ≫ eqToHom (IsHomLift.codomain_eq _ (𝟙 R.base) R.iso.inv).symm :=
    IsHomLift.fac' _ (𝟙 R.base) R.iso.inv
  have hb : R.iso.inv.hbase = eqToHom (IsHomLift.domain_eq
      (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
        (𝒴 := 𝒴)).p (𝟙 R.base) R.iso.inv) ≫ 𝟙 R.base ≫
      eqToHom (IsHomLift.codomain_eq (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS)
        (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).p (𝟙 R.base) R.iso.inv).symm := hfac
  exact (IsHomLift.lift_comp_eqToHom_iff _ _ _ _).1
    ((IsHomLift.lift_eqToHom_comp_iff _ _ _ _).1 (hb ▸ ha))

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The inverse of the comparison isomorphism of an object of the fibre is an isomorphism. -/
theorem isIso_fibreObjComparison : IsIso R.iso.inv :=
  ⟨R.iso.hom, R.iso.inv_hom_id, R.iso.hom_inv_id⟩

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- Its `ℋ_d(𝒳)`-component is an isomorphism. -/
theorem isIso_fibreObjComparison_a : IsIso R.iso.inv.a := by
  have h := isIso_fibreObjComparison (F := F) P y hy R
  exact inferInstanceAs (IsIso ((TwoFibreProductOver.fst
    (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
    𝒴.toBasedCategory.p (𝟭 (BigFppfOver B S hS))
    (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
    𝒴.toBasedCategory.p).map R.iso.inv))

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- Its `𝒳`-component is an isomorphism. -/
theorem isIso_fibreObjComparison_a_a : IsIso R.iso.inv.a.a := by
  have h := isIso_fibreObjComparison_a (F := F) P y hy R
  exact inferInstanceAs (IsIso ((absoluteHilbertSourceFunctor (B := B) (S := S) (hS := hS)
    (d := d) (𝒳 := 𝒳)).map R.iso.inv.a))

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- Its cover component is an isomorphism. -/
theorem isIso_fibreObjComparison_a_cover_g : IsIso R.iso.inv.a.cover.g := by
  have h := isIso_fibreObjComparison_a (F := F) P y hy R
  exact inferInstanceAs (IsIso ((absoluteHilbertCoverFunctor (B := B) (S := S) (hS := hS)
    (d := d) (𝒳 := 𝒳)).map R.iso.inv.a))

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- The `𝒴`-component of the inverse of the comparison isomorphism lies over the base component
of its `ℋ_d(𝒳)`-component. -/
theorem isHomLift_fibreObjComparison_b :
    𝒴.toBasedCategory.p.IsHomLift R.iso.inv.a.cover.f R.iso.inv.b :=
  isHomLift_map_a_b R.iso.inv

/-- The identification of `F x` with the restriction of `y` carried by the object of
`ℋ_d(𝒳/𝒴)` of an object of the fibre, transported to the member of the universal family by the
inverse of the comparison isomorphism. -/
noncomputable def fibreObjAlpha :
    F.obj ((productFamily P y hy).obj R.x).x.x ⟶ ((productFamily P y hy).obj R.x).y :=
  have _h := isIso_fibreObjComparison_a_a (F := F) P y hy R
  F.toFunctor.map (CategoryTheory.inv R.iso.inv.a.a) ≫ R.y.α ≫ R.iso.inv.b

attribute [local implicit_reducible] fibreObjAlpha

omit [𝒴.toBasedCategory.p.IsFibered] in
/-- `AlgebraicGeometry.Stack.fibreObjAlpha` lies over the cover of the member of the universal
family. -/
theorem isHomLift_fibreObjAlpha :
    𝒴.toBasedCategory.p.IsHomLift ((productFamily P y hy).obj R.x).x.q
      (fibreObjAlpha (F := F) P y hy R) := by
  have hia := isIso_fibreObjComparison_a_a (F := F) P y hy R
  have hig := isIso_fibreObjComparison_a_cover_g (F := F) P y hy R
  have haa := R.iso.inv.a.a_over
  have h1 : 𝒳.toBasedCategory.p.IsHomLift (CategoryTheory.inv R.iso.inv.a.cover.g)
      (CategoryTheory.inv R.iso.inv.a.a) :=
    IsHomLift.inv 𝒳.toBasedCategory.p R.iso.inv.a.cover.g R.iso.inv.a.a
  have h1' : 𝒴.toBasedCategory.p.IsHomLift (CategoryTheory.inv R.iso.inv.a.cover.g)
      (F.toFunctor.map (CategoryTheory.inv R.iso.inv.a.a)) :=
    BasedFunctor.preserves_isHomLift F (CategoryTheory.inv R.iso.inv.a.cover.g)
      (CategoryTheory.inv R.iso.inv.a.a)
  have h2 := R.y.α_over
  have h3 := isHomLift_fibreObjComparison_b (F := F) P y hy R
  have hc1 : 𝒴.toBasedCategory.p.IsHomLift (R.y.q ≫ R.iso.inv.a.cover.f)
      (R.y.α ≫ R.iso.inv.b) :=
    IsHomLift.comp 𝒴.toBasedCategory.p R.y.q R.iso.inv.a.cover.f R.y.α R.iso.inv.b
  have hc : 𝒴.toBasedCategory.p.IsHomLift (CategoryTheory.inv R.iso.inv.a.cover.g ≫
      R.y.q ≫ R.iso.inv.a.cover.f) (fibreObjAlpha (F := F) P y hy R) :=
    IsHomLift.comp 𝒴.toBasedCategory.p (CategoryTheory.inv R.iso.inv.a.cover.g)
      (R.y.q ≫ R.iso.inv.a.cover.f) (F.toFunctor.map (CategoryTheory.inv R.iso.inv.a.a))
      (R.y.α ≫ R.iso.inv.b)
  have hsq : R.iso.inv.a.cover.g ≫ ((productFamily P y hy).obj R.x).x.q =
      R.y.q ≫ R.iso.inv.a.cover.f := R.iso.inv.a.cover.square.w
  have heq : CategoryTheory.inv R.iso.inv.a.cover.g ≫ R.y.q ≫ R.iso.inv.a.cover.f =
      ((productFamily P y hy).obj R.x).x.q := by
    rw [← hsq, IsIso.inv_hom_id_assoc]
  rwa [heq] at hc

/-- The section of the fibre presheaf named by an object of the fibre: the unique vertical
morphism whose composite with the restriction morphism is
`AlgebraicGeometry.Stack.fibreObjAlpha`. -/
noncomputable def fibreObjSectionVal :
    (productFamilySource (F := F) P y hy).obj R.x ⟶
      (coverTargetSlice P yZ hyZ).obj ((productFamilyCover P y hy).obj R.x) := by
  have hν := productFamilyTargetArrow_over P y hy yZ hyZ φ hφ R.x
  have h₁ : 𝒴.toBasedCategory.p.IsStronglyCartesian ((productFamily P y hy).obj R.x).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x) :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift
      ((productFamily P y hy).obj R.x).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x)
  have h₂ := isHomLift_fibreObjAlpha (F := F) P y hy R
  exact @Functor.IsStronglyCartesian.map _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
    ((productFamily P y hy).obj R.x).x.q
    (productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x) h₁ _ _
    (𝟙 ((productFamily P y hy).obj R.x).x.Z) ((productFamily P y hy).obj R.x).x.q
    (Category.id_comp _).symm (fibreObjAlpha (F := F) P y hy R) h₂

attribute [local implicit_reducible] fibreObjSectionVal

/-- The defining equation of `AlgebraicGeometry.Stack.fibreObjSectionVal`. -/
theorem fibreObjSectionVal_fac :
    fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R ≫
        productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x =
      fibreObjAlpha (F := F) P y hy R := by
  have h₁ := isStronglyCartesian_productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x
  have h₂ := isHomLift_fibreObjAlpha (F := F) P y hy R
  exact @Functor.IsStronglyCartesian.fac _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
    ((productFamily P y hy).obj R.x).x.q
    (productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x) h₁ _ _
    (𝟙 ((productFamily P y hy).obj R.x).x.Z) ((productFamily P y hy).obj R.x).x.q
    (Category.id_comp _).symm (fibreObjAlpha (F := F) P y hy R) h₂

/-- `AlgebraicGeometry.Stack.fibreObjSectionVal` is vertical, in the spelling the fibre presheaf
asks for. -/
theorem isHomLift_fibreObjSectionVal :
    𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((productFamilyCover P y hy ⋙ Over.map P.Z.hom).obj R.x))
      (fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R) := by
  have h₁ := isStronglyCartesian_productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x
  have h₂ := isHomLift_fibreObjAlpha (F := F) P y hy R
  have h : 𝒴.toBasedCategory.p.IsHomLift (𝟙 ((productFamily P y hy).obj R.x).x.Z)
      (fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R) :=
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ 𝒴.toBasedCategory.p _ _ _ _
      ((productFamily P y hy).obj R.x).x.q
      (productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x) h₁ _ _
      (𝟙 ((productFamily P y hy).obj R.x).x.Z) ((productFamily P y hy).obj R.x).x.q
      (Category.id_comp _).symm (fibreObjAlpha (F := F) P y hy R) h₂
  show 𝒴.toBasedCategory.p.IsHomLift
    (𝟙 ((Over.map P.Z.hom).obj ((productFamilyCover P y hy).obj R.x)))
    (fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R)
  rw [productFamilyCover_base_obj P y hy R.x]
  exact h

/-- The section of the fibre presheaf named by an object of the fibre. -/
noncomputable def fibreObjSection :
    (productFibrePresheafSource (F := F) P y hy yZ hyZ).obj (op R.x) :=
  ⟨fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R,
    isHomLift_fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R⟩

/-- The morphism of `ℋ_d(𝒳/𝒴)` from the object of `ℋ_d(𝒳/𝒴)` carried by an object of the fibre to
the one named by the section it names. -/
noncomputable def fibreObjMap :
    R.y ⟶ fibreObject P y hy yZ hyZ φ hφ R.x
      (fibreObjSection (F := F) P y hy yZ hyZ φ hφ R) where
  f := R.iso.inv.a.cover.f
  g := R.iso.inv.a.cover.g
  square := R.iso.inv.a.cover.square
  b := R.iso.inv.b
  b_over := isHomLift_fibreObjComparison_b (F := F) P y hy R
  a := R.iso.inv.a.a
  a_over := R.iso.inv.a.a_over
  compatible := by
    have hia := isIso_fibreObjComparison_a_a (F := F) P y hy R
    change F.toFunctor.map R.iso.inv.a.a ≫
        (fibreObjSectionVal (F := F) P y hy yZ hyZ φ hφ R ≫
          productFamilyTargetArrow P y hy yZ hyZ φ hφ R.x) = R.y.α ≫ R.iso.inv.b
    rw [fibreObjSectionVal_fac]
    change F.toFunctor.map R.iso.inv.a.a ≫
        (F.toFunctor.map (CategoryTheory.inv R.iso.inv.a.a) ≫ R.y.α ≫ R.iso.inv.b) =
      R.y.α ≫ R.iso.inv.b
    rw [← Category.assoc, ← F.toFunctor.map_comp, IsIso.hom_inv_id, F.toFunctor.map_id,
      Category.id_comp]

/-- The vertical morphism of the fibre from an object of the fibre to the object named by the
section of the fibre presheaf it names. -/
noncomputable def fibreObjHom :
    R ⟶ (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ).obj
      ⟨R.x, Discrete.mk (fibreObjSection (F := F) P y hy yZ hyZ φ hφ R)⟩ where
  hbase := eqToHom (R.hx.symm.trans (objUniversalFamily_base_obj
    isFiberedInGroupoids_absoluteHilbertTargetProductProjection (productPoint P y hy) R.x).symm)
  a := 𝟙 R.x
  b := fibreObjMap (F := F) P y hy yZ hyZ φ hφ R
  ha := IsHomLift.id_lift_eqToHom_domain _ R.hx
  hb := by
    have hd := fibreObjComparison_a_vertical (F := F) P y hy R
    have hfa : R.iso.inv.a.cover.f =
        eqToHom (IsHomLift.domain_eq (absoluteHilbertCategory (B := B) (S := S) (hS := hS)
          (d := d) (𝒳 := 𝒳)).p (𝟙 R.base) R.iso.inv.a) ≫ 𝟙 R.base ≫
          eqToHom (IsHomLift.codomain_eq (absoluteHilbertCategory (B := B) (S := S) (hS := hS)
            (d := d) (𝒳 := 𝒳)).p (𝟙 R.base) R.iso.inv.a).symm :=
      IsHomLift.fac' (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d)
        (𝒳 := 𝒳)).p (𝟙 R.base) R.iso.inv.a
    refine IsHomLift.of_fac' _ _ _ R.hy ((productFamily P y hy).obj R.x).hx ?_
    refine hfa.trans ?_
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  w := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · have h : R.iso.hom.a ≫ R.iso.inv.a = 𝟙 ((productFamily P y hy).obj R.x).x :=
        congrArg TwoFibreProductOver.Hom.a R.iso.hom_inv_id
      change ((productFamily P y hy).map (𝟙 R.x)).a ≫ 𝟙 ((productFamily P y hy).obj R.x).x =
        R.iso.hom.a ≫ R.iso.inv.a
      rw [h, (productFamily P y hy).map_id]
      simp only [Category.comp_id]
      rfl
    · have h : R.iso.hom.b ≫ R.iso.inv.b = 𝟙 ((productFamily P y hy).obj R.x).y :=
        congrArg TwoFibreProductOver.Hom.b R.iso.hom_inv_id
      change ((productFamily P y hy).map (𝟙 R.x)).b ≫ 𝟙 ((productFamily P y hy).obj R.x).y =
        R.iso.hom.b ≫ R.iso.inv.b
      rw [h, (productFamily P y hy).map_id]
      simp only [Category.comp_id]
      rfl

attribute [local implicit_reducible] fibreObjMap fibreObjHom

/-- `AlgebraicGeometry.Stack.fibreObjMap` is an isomorphism. -/
theorem isIso_fibreObjMap : IsIso (fibreObjMap (F := F) P y hy yZ hyZ φ hφ R) := by
  have hia := isIso_fibreObjComparison_a (F := F) P y hy R
  have hif : IsIso R.iso.inv.a.cover.f := inferInstanceAs (IsIso
    ((absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p.map R.iso.inv.a))
  have hl : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsHomLift R.iso.inv.a.cover.f (fibreObjMap (F := F) P y hy yZ hyZ φ hφ R) :=
    IsHomLift.map _ (fibreObjMap (F := F) P y hy yZ hyZ φ hφ R)
  have hsc := isFiberedInGroupoids_finiteHilbertProjection
    (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)
    |>.isStronglyCartesian_homLift R.iso.inv.a.cover.f
      (fibreObjMap (F := F) P y hy yZ hyZ φ hφ R)
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    R.iso.inv.a.cover.f (fibreObjMap (F := F) P y hy yZ hyZ φ hφ R)

/-- `AlgebraicGeometry.Stack.fibreObjHom` is an isomorphism. -/
theorem isIso_fibreObjHom : IsIso (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R) := by
  have h₁ : IsIso (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R).hbase := by
    show IsIso (eqToHom (R.hx.symm.trans (objUniversalFamily_base_obj
      isFiberedInGroupoids_absoluteHilbertTargetProductProjection
      (productPoint P y hy) R.x).symm))
    infer_instance
  have h₂ : IsIso (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R).a := by
    show IsIso (𝟙 R.x)
    infer_instance
  have h₃ : IsIso (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R).b :=
    isIso_fibreObjMap (F := F) P y hy yZ hyZ φ hφ R
  exact isIso_twoFibreProductOver_hom (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R)

/-- **The comparison 1-morphism admits vertical preimages**: every object of the fibre is
vertically isomorphic to the one attached to the section of the fibre presheaf it names. -/
theorem hasVerticalPreimages_productFibreFunctor :
    Functor.HasVerticalPreimages
      (presheafOfCategories
        (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).p
      (TwoFibreProductOver.fst (Over.map P.U.hom)
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
          (𝒴 := 𝒴)).p
        (productFamily P y hy)
        (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)).toFunctor)
      (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ) := by
  intro R
  have hi := isIso_fibreObjHom (F := F) P y hy yZ hyZ φ hφ R
  refine ⟨⟨R.x, Discrete.mk (fibreObjSection (F := F) P y hy yZ hyZ φ hφ R)⟩, rfl,
    asIso (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R), ?_⟩
  exact IsHomLift.map _ (fibreObjHom (F := F) P y hy yZ hyZ φ hφ R)

/-- **The fibre of the 1-morphism of Equation 05WD over the 2-Yoneda universal family of
`(P, y)` is the category of elements of the fibre presheaf**, through the comparison 1-morphism
`AlgebraicGeometry.Stack.productFibreFunctor`. -/
noncomputable def fibreEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories
        (productFibrePresheafSource (F := F) P y hy yZ hyZ ⋙ typeToCat)).p
      (TwoFibreProductOver.fst (Over.map P.U.hom)
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p
        (absoluteHilbertTargetProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)
          (𝒴 := 𝒴)).p
        (productFamily P y hy)
        (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)).toFunctor) := by
  have h1 := productFibreFunctor_faithful (F := F) P y hy yZ hyZ φ hφ
  have h2 := productFibreFunctor_full (F := F) P y hy yZ hyZ φ hφ
  exact equivalenceOverOfVerticalPreimages (productFibreFunctor (F := F) P y hy yZ hyZ φ hφ) rfl
    (hasVerticalPreimages_productFibreFunctor (F := F) P y hy yZ hyZ φ hφ)

/-! ### Stacks 05YH -/

/-- **The fibre computation of Stacks 05YH**, in its cleavage-free shape: for every object `P` of
`ℋ_d(𝒳)`, every object `y` of `𝒴` over its base and every restriction of `y` to the cover, the
2-fibre product of the 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD with the 2-Yoneda
universal family of `(P, y)` is equivalent, over the big fppf site of the base, to the category
of elements of `AlgebraicGeometry.Stack.productFibrePresheafSource`. -/
theorem fibreIsVertHomSourceElements : FibreIsVertHomSourceElements B S hS d 𝒳 𝒴 F := by
  intro P' y' hy' yZ' φ' hφ' hyZ'
  exact ⟨(fibreEquivalenceOver (F := F) P' y' hy' yZ' hyZ' φ' hφ').symm⟩

/-- **The fibre identification of Stacks 05YH.** For every object `X` of `ℋ_d(𝒳) × 𝒴`, the
2-fibre product of the 1-morphism of Equation 05WD with the 2-Yoneda universal family of `X` is
representable by an algebraic space over the base of `X`, provided the diagonal of `𝒴` is
representable by algebraic spaces. -/
theorem fibres_absoluteHilbertTargetProduct_forgetToProduct
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴))) :
    FibresOverObjUniversalFamiliesAlgebraic
      (isFiberedInGroupoids_absoluteHilbertTargetProductProjection
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))
      (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) :=
  fibres_absoluteHilbertTargetProduct_forgetToProduct_of_fibreIsVertHomSource hΔ
    fibreIsVertHomSourceElements

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf
site of a scheme `S` and let `d` be a natural number. If the diagonal `𝒴 ⟶ 𝒴 × 𝒴` is
representable by algebraic spaces then the 1-morphism

`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`

of Equation 05WD is representable by algebraic spaces, in the sense of Stacks 02ZW. -/
@[stacks 05YH]
theorem isRepresentableByAlgebraicSpacesForgetToProduct_of_diagonal
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴))) :
    IsRepresentableByAlgebraicSpacesForgetToProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) :=
  isRepresentableByAlgebraicSpacesForgetToProduct_of_fibres
    (fibres_absoluteHilbertTargetProduct_forgetToProduct hΔ)

end AlgebraicGeometry.Stack

end
