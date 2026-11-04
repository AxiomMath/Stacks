module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductMorphismRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelocalizedSectionsFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalFamilyArrow

/-!
# The family of covers of the 2-Yoneda universal family of a point of `ℋ_d(𝒳) × 𝒴`

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `P = (q : Z ⟶ U, x)` be an object of the absolute finite Hilbert category `ℋ_d(𝒳)` and let
`y` be an object of `𝒴` over `U`; together they are an object of the product `ℋ_d(𝒳) × 𝒴` and so
carry a scheme-valued point of the product, the 2-Yoneda universal family of that object.

The fibre computation of Stacks 05YH is performed over that point, and the first thing it needs
is the family of covers underlying it: the member of the family at a test object `T / U` is an
object of `ℋ_d(𝒳) × 𝒴` whose cover is `T ×_U Z`, and the fibre over it will be identified with
the sections over `T` of the Isom space of the pair `(y|_Z, F x)` pulled back to `T ×_U Z`. This
file builds that family of covers as a functor into the big fppf site of `Z`, and identifies the
cover of each member with the fibre product `T ×_U Z`, as a binary product in the slice over `U`
and hence as a product of representable presheaves.

## Main definitions

* `AlgebraicGeometry.Stack.productPoint`: the object of `ℋ_d(𝒳) × 𝒴` attached to an object of
  `ℋ_d(𝒳)` and an object of `𝒴` over its base.
* `AlgebraicGeometry.Stack.productFamily`: the 2-Yoneda universal family of that object.
* `AlgebraicGeometry.Stack.productFamilyCover`: the family of covers, as a functor from the big
  fppf site of `U` to the big fppf site of `Z`.
* `AlgebraicGeometry.Stack.productFamilyProduct`: the cover of a member of the family, read as a
  test object over `U`, together with its two projections to `T` and to `Z`.
* `AlgebraicGeometry.Stack.productFamilyProductIso`: the presheaf represented by that cover is
  the product of the presheaves represented by `T` and by `Z`.

## Main results

* `AlgebraicGeometry.Stack.productFamilyCover_base`: the family of covers is the family of covers
  of the universal family.
* `AlgebraicGeometry.Stack.productFamilyProduct_isPullback`: the cover of a member of the family
  is the fibre product of the test object with `Z` over `U`.
* `AlgebraicGeometry.Stack.productFamilyProductIso_snd` and
  `AlgebraicGeometry.Stack.productFamilyProductIso_map`: the second projection of that
  identification and its naturality in the test object.
* `AlgebraicGeometry.Stack.productFamilySectionEquiv` and
  `AlgebraicGeometry.Stack.productFamilySectionEquiv_map`: **the identification the fibre
  computation consumes** — the sections over a test object `T` of the relocalization of a
  presheaf on the big fppf site of `Z` are its values at the member of the family of covers at
  `T`, naturally in `T`.

## What is and is not proved

Proved, in full, with no carried hypothesis: the identification of the covers of the universal
family with the fibre products `T ×_U Z`, in the shape in which
`AlgebraicGeometry.Stack.relocalizeSectionsEquiv` consumes it, and the resulting identification
of the space of sections of a relocalized presheaf with the restriction of that presheaf along
the family of covers.

No tag is claimed. The file states no result of the Stacks project: it is the bookkeeping of the
fibre computation of Stacks 05YH, and is the analogue, for the 1-morphism of Equation 05WD, of
the family-of-covers bookkeeping performed inside
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace` for the 1-morphism of
Stacks 05XN.

## Implementation notes

The object of `ℋ_d(𝒳) × 𝒴` is built from an object of `ℋ_d(𝒳)` and an object of `𝒴` over its
base rather than taken as given: an object of the product carries its base as a separate field
together with two equalities identifying it with the bases of the components, and every statement
made at a general object of the product would have to transport along them. The comparison
isomorphism of the product is an `eqToIso`, because the structure functor of the product is the
identity of the site and a vertical morphism of the site is an `eqToHom`.

`CategoryTheory.BasedCategory.ofFunctor` and the three finite Hilbert categories are made
`implicit_reducible` locally, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductMorphism`.

## References

* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertTargetProduct
  absoluteHilbertTargetProductProjection finiteHilbertCategory absoluteHilbertCategory
  objUniversalFamily objUniversalArrow CategoryTheory.Over.iteratedSliceBackward
  CategoryTheory.Over.homMk CategoryTheory.TwoFibreProductOver.structureFunctor
  absoluteHilbertProjection finiteHilbertProjection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}

/-- The object of the product `ℋ_d(𝒳) × 𝒴` attached to an object `P` of `ℋ_d(𝒳)` and an object
`y` of `𝒴` over the base of `P`. Its comparison isomorphism is an `eqToIso`: the structure
functor of the product is the identity of the site. -/
def productPoint (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
    (hy : 𝒴.toBasedCategory.p.obj y = P.U) :
    (absoluteHilbertTargetProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj where
  base := P.U
  x := P
  y := y
  hx := rfl
  hy := hy
  iso := eqToIso hy.symm
  vertical := IsHomLift.of_fac' (𝟭 (BigFppfOver B S hS)) (𝟙 P.U) (eqToHom hy.symm) rfl hy (by
    simp)

attribute [local implicit_reducible] productPoint

/-- The base of `AlgebraicGeometry.Stack.productPoint` is the base of the object of
`ℋ_d(𝒳)`. -/
theorem productPoint_base (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
    (hy : 𝒴.toBasedCategory.p.obj y = P.U) :
    (absoluteHilbertTargetProduct
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).p.obj
      (productPoint P y hy) = P.U :=
  rfl

variable (P : AbsoluteHilbert.Object B S hS d 𝒳) (y : 𝒴.toBasedCategory.obj)
  (hy : 𝒴.toBasedCategory.p.obj y = P.U)

/-- The 2-Yoneda universal family of `AlgebraicGeometry.Stack.productPoint`: the scheme-valued
point of `ℋ_d(𝒳) × 𝒴` over the base of `P` attached to it by the 2-Yoneda lemma. -/
noncomputable abbrev productFamily :
    Over P.U.left ⥤ (absoluteHilbertTargetProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj :=
  objUniversalFamily isFiberedInGroupoids_absoluteHilbertTargetProductProjection
    (productPoint P y hy)

/-- The chosen strongly cartesian morphism from a member of
`AlgebraicGeometry.Stack.productFamily` to the object it is the family of. -/
noncomputable abbrev productFamilyArrow (T : Over P.U.left) :
    (productFamily P y hy).obj T ⟶ productPoint P y hy :=
  objUniversalArrow isFiberedInGroupoids_absoluteHilbertTargetProductProjection
    (productPoint P y hy) T

/-- The morphism of `ℋ_d(𝒳)` underlying the chosen morphism out of a member of the universal
family. -/
noncomputable abbrev productFamilyArrowHilbert (T : Over P.U.left) :
    ((productFamily P y hy).obj T).x ⟶ P :=
  (productFamilyArrow P y hy T).a

/-- The chosen morphisms out of the universal family are compatible with its transition
morphisms, in their `ℋ_d(𝒳)`-components. -/
theorem productFamilyArrowHilbert_naturality {T T' : Over P.U.left} (f : T ⟶ T') :
    ((productFamily P y hy).map f).a ≫ productFamilyArrowHilbert P y hy T' =
      productFamilyArrowHilbert P y hy T :=
  congrArg (fun g => g.a) (objUniversalArrow_naturality
    isFiberedInGroupoids_absoluteHilbertTargetProductProjection (productPoint P y hy) f)

/-- The family of covers underlying the universal family of
`AlgebraicGeometry.Stack.productPoint`, as a family of test objects over the cover `Z`: a test
object `T / U` is sent to the cover of the member of the universal family at `T`, regarded over
`Z` through the chosen morphism. -/
noncomputable def productFamilyCover : Over P.U.left ⥤ Over P.Z.left where
  obj T := Over.mk (productFamilyArrowHilbert P y hy T).cover.g.left
  map {T T'} f := Over.homMk ((productFamily P y hy).map f).a.cover.g.left
    (congrArg (fun g => g.cover.g.left) (productFamilyArrowHilbert_naturality P y hy f))
  map_id T := by
    refine Over.OverMorphism.ext ?_
    change ((productFamily P y hy).map (𝟙 T)).a.cover.g.left = _
    rw [(productFamily P y hy).map_id]
    rfl
  map_comp f g := by
    refine Over.OverMorphism.ext ?_
    change ((productFamily P y hy).map (f ≫ g)).a.cover.g.left = _
    rw [(productFamily P y hy).map_comp]
    rfl

attribute [local implicit_reducible] productFamilyCover

/-- The functor remembering only the cover of an object of the product `ℋ_d(𝒳) × 𝒴`. -/
def productCoverFunctor :
    (absoluteHilbertTargetProduct
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj ⥤
      BigFppfOver B S hS where
  obj W := W.x.Z
  map φ := φ.a.cover.g
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [local implicit_reducible] productCoverFunctor

/-- The base object of the object of `ℋ_d(𝒳)` carried by a member of the universal family is the
image of the test object. -/
theorem productFamily_base_obj (T : Over P.U.left) :
    ((productFamily P y hy).obj T).x.U = (Over.map P.U.hom).obj T :=
  (((productFamily P y hy).obj T).hx).trans
    (objUniversalFamily_base_obj isFiberedInGroupoids_absoluteHilbertTargetProductProjection
      (productPoint P y hy) T)

/-- The `ℋ_d(𝒳)`-component of a morphism of `ℋ_d(𝒳) × 𝒴` lies over its base morphism, up to the
equalities identifying the bases. -/
private theorem p_map_a_eq_of_hbase_eq
    {W W' : (absoluteHilbertTargetProduct
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).obj} (φ : W ⟶ W')
    {k : W.base ⟶ W'.base} (hk : φ.hbase = k) :
    (absoluteHilbertCategory
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p.map φ.a =
      eqToHom W.hx ≫ k ≫ eqToHom W'.hx.symm := by
  subst hk
  simp [φ.hbase_eq]

/-- The base component of the chosen morphism of `ℋ_d(𝒳)` out of a member of the universal
family is the structure morphism of the test object. -/
theorem productFamilyArrowHilbert_cover_f (T : Over P.U.left) :
    (productFamilyArrowHilbert P y hy T).cover.f =
      eqToHom (productFamily_base_obj P y hy T) ≫
        ((Over.iteratedSliceBackward P.U).obj T).hom := by
  exact p_map_a_eq_of_hbase_eq (productFamilyArrow P y hy T)
    (objUniversalArrow_base isFiberedInGroupoids_absoluteHilbertTargetProductProjection
      (productPoint P y hy) T) |>.trans (by simp; rfl)

/-- The image in the site of `S` of a member of the family of covers is the cover of the
corresponding member of the universal family. -/
theorem productFamilyCover_base_obj (T : Over P.U.left) :
    (Over.map P.Z.hom).obj ((productFamilyCover P y hy).obj T) =
      ((productFamily P y hy).obj T).x.Z := by
  show Over.mk ((productFamilyArrowHilbert P y hy T).cover.g.left ≫ P.Z.hom) = _
  rw [(productFamilyArrowHilbert P y hy T).cover.g.w]
  rfl

/-- The family of covers is the family of covers of the universal family. -/
theorem productFamilyCover_base :
    productFamilyCover P y hy ⋙ Over.map P.Z.hom =
      productFamily P y hy ⋙ productCoverFunctor := by
  refine CategoryTheory.Functor.ext (productFamilyCover_base_obj P y hy) ?_
  intro T T' f
  refine Over.OverMorphism.ext ?_
  simp
  rfl

/-- The cover component of the chosen morphism out of a member of the universal family is the
structure morphism of the corresponding member of the family of covers. -/
theorem productFamilyCover_arrow (T : Over P.U.left) :
    (productFamilyArrowHilbert P y hy T).cover.g =
      eqToHom (productFamilyCover_base_obj P y hy T).symm ≫
        ((Over.iteratedSliceBackward P.Z).obj ((productFamilyCover P y hy).obj T)).hom := by
  refine Over.OverMorphism.ext ?_
  show (productFamilyArrowHilbert P y hy T).cover.g.left =
    (eqToHom (productFamilyCover_base_obj P y hy T).symm).left ≫
      (productFamilyArrowHilbert P y hy T).cover.g.left
  simp

/-- The base component of the transition morphism of the universal family is the transition
morphism of the test objects. -/
theorem productFamilyMap_cover_f {T T' : Over P.U.left} (f : T ⟶ T') :
    ((productFamily P y hy).map f).a.cover.f =
      eqToHom (productFamily_base_obj P y hy T) ≫ (Over.map P.U.hom).map f ≫
        eqToHom (productFamily_base_obj P y hy T').symm := by
  exact (p_map_a_eq_of_hbase_eq ((productFamily P y hy).map f)
    (CategoryTheory.Functor.congr_hom (objUniversalFamily_comp
      isFiberedInGroupoids_absoluteHilbertTargetProductProjection (productPoint P y hy)) f)).trans
    (by simp; rfl)

/-- The cover of a member of the universal family presents the fibre product of the test object
with `Z` over `U`. -/
theorem productFamilyProduct_isPullback (T : Over P.U.left) :
    IsPullback (productFamilyArrowHilbert P y hy T).cover.g.left
      (((productFamily P y hy).obj T).x.q.left ≫
        eqToHom (congrArg Over.left (productFamily_base_obj P y hy T)))
      P.q.left T.hom := by
  have h := (productFamilyArrowHilbert P y hy T).cover.square.map (Over.forget _)
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (eqToIso (congrArg Over.left (productFamily_base_obj P y hy T))) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · have hf := congrArg (fun g => g.left) (productFamilyArrowHilbert_cover_f P y hy T)
    change (productFamilyArrowHilbert P y hy T).cover.f.left =
      (eqToHom (productFamily_base_obj P y hy T)).left ≫ T.hom at hf
    show (productFamilyArrowHilbert P y hy T).cover.f.left ≫ 𝟙 P.U.left =
      eqToHom (congrArg Over.left (productFamily_base_obj P y hy T)) ≫ T.hom
    simpa only [Over.eqToHom_left, Category.comp_id] using hf

/-- The fibre product `T ×_U Z`, as a test object over `U`. -/
noncomputable def productFamilyProduct (T : Over P.U.left) : Over P.U.left :=
  Over.mk ((productFamilyArrowHilbert P y hy T).cover.g.left ≫ P.q.left)

/-- The first projection of `AlgebraicGeometry.Stack.productFamilyProduct`. -/
noncomputable def productFamilyProductFst (T : Over P.U.left) :
    productFamilyProduct P y hy T ⟶ T :=
  Over.homMk (((productFamily P y hy).obj T).x.q.left ≫
    eqToHom (congrArg Over.left (productFamily_base_obj P y hy T)))
    (productFamilyProduct_isPullback P y hy T).w.symm

/-- The second projection of `AlgebraicGeometry.Stack.productFamilyProduct`. -/
noncomputable def productFamilyProductSnd (T : Over P.U.left) :
    productFamilyProduct P y hy T ⟶ Over.mk P.q.left :=
  Over.homMk (productFamilyArrowHilbert P y hy T).cover.g.left rfl

attribute [local implicit_reducible] productFamilyProduct productFamilyProductFst
  productFamilyProductSnd

/-- `AlgebraicGeometry.Stack.productFamilyProduct` is the binary product of `T` and `Z` in the
slice over `U`. -/
noncomputable def productFamilyProductLimit (T : Over P.U.left) :
    IsLimit (BinaryFan.mk (productFamilyProductFst P y hy T)
      (productFamilyProductSnd P y hy T)) :=
  overBinaryFanIsLimit P.q.left T (productFamilyProduct P y hy T)
    (productFamilyProductFst P y hy T) (productFamilyProductSnd P y hy T)
    (productFamilyProduct_isPullback P y hy T)

/-- The presheaf represented by `AlgebraicGeometry.Stack.productFamilyProduct` is the product of
the two representable presheaves. -/
noncomputable def productFamilyProductIso (T : Over P.U.left) :
    yoneda.obj (productFamilyProduct P y hy T) ≅
      yoneda.obj T ⨯ yoneda.obj (Over.mk P.q.left) :=
  yonedaBinaryProductIso (productFamilyProductFst P y hy T) (productFamilyProductSnd P y hy T)
    (productFamilyProductLimit P y hy T)

/-- The first projection of `AlgebraicGeometry.Stack.productFamilyProductIso`. -/
theorem productFamilyProductIso_fst (T : Over P.U.left) :
    (productFamilyProductIso P y hy T).hom ≫ prod.fst =
      yoneda.map (productFamilyProductFst P y hy T) :=
  yonedaBinaryProductIso_fst _ _ _

/-- The second projection of `AlgebraicGeometry.Stack.productFamilyProductIso`. -/
theorem productFamilyProductIso_snd (T : Over P.U.left) :
    (productFamilyProductIso P y hy T).hom ≫ prod.snd =
      yoneda.map (productFamilyProductSnd P y hy T) :=
  yonedaBinaryProductIso_snd _ _ _

/-- The transition morphism of the family of fibre products. -/
noncomputable def productFamilyProductMap {T T' : Over P.U.left} (f : T ⟶ T') :
    productFamilyProduct P y hy T ⟶ productFamilyProduct P y hy T' :=
  Over.homMk ((productFamily P y hy).map f).a.cover.g.left (by
    have h := congrArg (fun g => g.cover.g.left)
      (productFamilyArrowHilbert_naturality P y hy f)
    change ((productFamily P y hy).map f).a.cover.g.left ≫
      ((productFamilyArrowHilbert P y hy T').cover.g.left ≫ P.q.left) =
      (productFamilyArrowHilbert P y hy T).cover.g.left ≫ P.q.left
    change ((productFamily P y hy).map f).a.cover.g.left ≫
      (productFamilyArrowHilbert P y hy T').cover.g.left =
      (productFamilyArrowHilbert P y hy T).cover.g.left at h
    rw [← Category.assoc, h])

attribute [local implicit_reducible] productFamilyProductMap

/-- The transition morphisms of the family of fibre products are over `Z`. -/
theorem productFamilyProductMap_snd {T T' : Over P.U.left} (f : T ⟶ T') :
    productFamilyProductMap P y hy f ≫ productFamilyProductSnd P y hy T' =
      productFamilyProductSnd P y hy T :=
  Over.OverMorphism.ext (congrArg (fun g => g.cover.g.left)
    (productFamilyArrowHilbert_naturality P y hy f))

/-- The transition morphisms of the family of fibre products are compatible with the first
projections. -/
theorem productFamilyProductMap_fst {T T' : Over P.U.left} (f : T ⟶ T') :
    productFamilyProductMap P y hy f ≫ productFamilyProductFst P y hy T' =
      productFamilyProductFst P y hy T ≫ f := by
  have hf := congrArg (fun g => g.left) (productFamilyMap_cover_f P y hy f)
  have hs := congrArg (fun g => g.left) ((productFamily P y hy).map f).a.cover.square.w
  refine Over.OverMorphism.ext ?_
  show ((productFamily P y hy).map f).a.cover.g.left ≫
      (((productFamily P y hy).obj T').x.q.left ≫
        eqToHom (congrArg Over.left (productFamily_base_obj P y hy T'))) =
    ((((productFamily P y hy).obj T).x.q.left ≫
      eqToHom (congrArg Over.left (productFamily_base_obj P y hy T)))) ≫ f.left
  change ((productFamily P y hy).map f).a.cover.g.left ≫
    ((productFamily P y hy).obj T').x.q.left =
    ((productFamily P y hy).obj T).x.q.left ≫ ((productFamily P y hy).map f).a.cover.f.left at hs
  change ((productFamily P y hy).map f).a.cover.f.left =
    (eqToHom (productFamily_base_obj P y hy T)).left ≫ f.left ≫
      (eqToHom (productFamily_base_obj P y hy T').symm).left at hf
  rw [← Category.assoc, hs, Category.assoc, hf]
  simp

/-- `AlgebraicGeometry.Stack.productFamilyProductIso` is natural in the test object. -/
theorem productFamilyProductIso_map {T T' : Over P.U.left} (f : T ⟶ T') :
    (productFamilyProductIso P y hy T).hom ≫ prod.map (yoneda.map f) (𝟙 _) =
      yoneda.map (productFamilyProductMap P y hy f) ≫
        (productFamilyProductIso P y hy T').hom := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, ← Category.assoc, productFamilyProductIso_fst,
      Category.assoc, productFamilyProductIso_fst, ← yoneda.map_comp, ← yoneda.map_comp,
      productFamilyProductMap_fst]
  · rw [Category.assoc, prod.map_snd, Category.comp_id, productFamilyProductIso_snd,
      Category.assoc, productFamilyProductIso_snd, ← yoneda.map_comp,
      productFamilyProductMap_snd]

/-! ### The sections of a relocalized presheaf over the cover -/

section Sections

variable (W : (BigFppfOver B (B.inclusion.obj P.Z.left) P.Z.left.property)ᵒᵖ ⥤ Type u)
  (w : (OverShriek.relocalizePresheafFunctor P.q.left).obj W ⟶
    yoneda.obj (Over.mk P.q.left : BigFppfOver B (B.inclusion.obj P.U.left) P.U.left.property))
  (hw : ∀ (T : BigFppfOver B (B.inclusion.obj P.U.left) P.U.left.property)
    (s : ((OverShriek.relocalizePresheafFunctor P.q.left).obj W).obj (op T)),
    (w.app (op T) s).left = s.val.fst)

/-- **The sections over `T` of the relocalization of a presheaf on the big fppf site of `Z` are
its values at the members of the family of covers.** A section over `T` is a morphism
`T ×_U Z ⟶ W` over `Z`, and the cover of the member of the universal family at `T` is `T ×_U Z`
by `AlgebraicGeometry.Stack.productFamilyProduct_isPullback`. -/
noncomputable def productFamilySectionEquiv (T : Over P.U.left) :
    (Space.sectionSpace B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left)
      ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w).obj (op T) ≃
      W.obj (op ((productFamilyCover P y hy).obj T)) :=
  (Space.sectionSpaceEquiv B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left) T
    ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w).trans
    (relocalizeSectionsEquiv P.q.left W w hw T (productFamilyProduct P y hy T)
      (productFamilyProductSnd P y hy T) (productFamilyProductIso P y hy T)
      (productFamilyProductIso_snd P y hy T))

/-- `AlgebraicGeometry.Stack.productFamilySectionEquiv` is natural in the test object. -/
theorem productFamilySectionEquiv_map {T T' : Over P.U.left} (f : T ⟶ T')
    (s : (Space.sectionSpace B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left)
      ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w).obj (op T')) :
    productFamilySectionEquiv P y hy W w hw T
      ((Space.sectionSpace B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left)
        ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w).map f.op s) =
      W.map ((productFamilyCover P y hy).map f).op
        (productFamilySectionEquiv P y hy W w hw T' s) := by
  have hs := Space.sectionSpaceEquiv_map B (B.inclusion.obj P.U.left) P.U.left.property
    (Over.mk P.q.left) T' T ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w f s
  have hh := relocalizeSectionsEquiv_map P.q.left W w hw f (productFamilyProductMap P y hy f)
    (productFamilyProductSnd P y hy T') (productFamilyProductSnd P y hy T)
    (productFamilyProductMap_snd P y hy f)
    (productFamilyProductIso P y hy T') (productFamilyProductIso P y hy T)
    (productFamilyProductIso_snd P y hy T') (productFamilyProductIso_snd P y hy T)
    (productFamilyProductIso_map P y hy f)
    (Space.sectionSpaceEquiv B (B.inclusion.obj P.U.left) P.U.left.property (Over.mk P.q.left) T'
      ((OverShriek.relocalizePresheafFunctor P.q.left).obj W) w s)
  change _ = W.map ((productFamilyCover P y hy).map f).op _ at hh
  refine Eq.trans ?_ hh
  exact congrArg (relocalizeSectionsEquiv P.q.left W w hw T (productFamilyProduct P y hy T)
    (productFamilyProductSnd P y hy T) (productFamilyProductIso P y hy T)
    (productFamilyProductIso_snd P y hy T)) (Subtype.ext hs)

end Sections

end AlgebraicGeometry.Stack

end
