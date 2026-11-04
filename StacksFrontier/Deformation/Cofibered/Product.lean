module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Applications.TwoFibreProductBaseChangeSmooth
public import StacksFrontier.Deformation.Applications.TwoFibreProductDeformation
public import StacksFrontier.Deformation.Examples.BaseCategoryOverItself
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Products of categories cofibered in groupoids over the base category

The product of two categories cofibered in groupoids `𝓕` and `𝓖` over `𝒞_Λ` is their `2`-fibre
product `𝓕 ×_{𝒞_Λ} 𝓖` taken over `𝒞_Λ` itself: the base category is read, through the identity
functor, as a category cofibered in groupoids over itself, and the two morphisms to it are the
structure morphisms of `𝓕` and of `𝓖`.

An object of `𝓕 ×_{𝒞_Λ} 𝓖` is a quadruple `(U, x, y, φ)` with `x` over `U` in `𝓕`, `y` over `U` in
`𝓖`, and `φ : 𝓕.p x ≅ 𝓖.p y` vertical over `U`. Over the identity functor a vertical arrow is the
canonical identification (`Deformation.cofiberedProduct_iso_hom`), so an object of the product is a
pair of objects over one object of `𝒞_Λ` (`Deformation.cofiberedProductObj_eq`), and a morphism is
a pair of arrows over one arrow of `𝒞_Λ` (`Deformation.cofiberedProductHom`).

## Main definitions

* `Deformation.cofiberedProduct`: the product `𝓕 ×_{𝒞_Λ} 𝓖` of two categories cofibered in
  groupoids over `𝒞_Λ`, namely their `2`-fibre product over `𝒞_Λ`.
* `Deformation.cofiberedProductObj`, `Deformation.cofiberedProductHom`: an object of the product
  from a pair of objects over one object of `𝒞_Λ`, and a morphism of the product from a pair of
  arrows over one arrow of `𝒞_Λ`.
* `Deformation.cofiberedProductFst`, `Deformation.cofiberedProductSnd`: the two projections, as
  morphisms over `𝒞_Λ`.
* `Deformation.cofiberedProductLift`: the morphism over `𝒞_Λ` into the product determined by a
  pair of morphisms over `𝒞_Λ`.

## Main results

* `Deformation.isCofiberedInGroupoids_cofiberedProduct`: the product of two categories cofibered
  in groupoids is cofibered in groupoids.
* `Deformation.cofiberedProductLift_comp_fst`, `Deformation.cofiberedProductLift_comp_snd`: the
  two projections recover the two morphisms the lift was built from.
* `Deformation.twoFibreProductBasedCategory_comp_baseProjection`: the `2`-fibre product of `𝓗₁`
  and `𝓗₂` over `𝒞_Λ`, formed from morphisms `p₁ : 𝓗₁ → 𝓖` and `p₂ : 𝓗₂ → 𝓖` followed by the
  structure morphism of `𝓖`, is the product `𝓗₁ ×_{𝒞_Λ} 𝓗₂`.
* `Deformation.isDeformationCategory_cofiberedProduct`: the product of two deformation categories
  is a deformation category, given that `𝒞_Λ` is a deformation category over itself.
* `Deformation.isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id`: the product of
  two deformation categories is a deformation category.

## References

* [Stacks Project, Tag 06GK](https://stacks.math.columbia.edu/tag/06GK)
* [Stacks Project, Tag 0DZJ](https://stacks.math.columbia.edu/tag/0DZJ)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The product of two categories cofibered in groupoids over `𝒞_Λ` -/

section Product

variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- The *product* of two categories cofibered in groupoids `𝓕` and `𝓖` over `𝒞_Λ` is their
`2`-fibre product `𝓕 ×_{𝒞_Λ} 𝓖`, taken over `𝒞_Λ` itself: the `2`-fibre product of the two
structure morphisms of `𝓕` and `𝓖` into the base category read through the identity functor as a
category cofibered in groupoids over itself. -/
@[stacks 0DZJ "the product of two categories cofibered in groupoids over 𝒞_Λ is their 2-fibre \
product over 𝒞_Λ",
  stacks 06GK "(14) products of categories cofibered in groupoids"]
public def cofiberedProduct (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    BasedCategory (ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  twoFibreProductBasedCategory (baseProjection 𝓕.p) (baseProjection 𝓖.p)

/-- The comparison isomorphism carried by an object of the product is the canonical identification
of the two base objects. -/
public theorem cofiberedProduct_iso_hom
    (P : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p) :
    P.iso.hom = eqToHom P.hx ≫ eqToHom P.hy.symm := by
  let _ := P.vertical
  simpa using IsHomLift.fac' (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) (𝟙 P.base) P.iso.hom

/-- A pair of arrows lying over one arrow of `𝒞_Λ` makes the comparison square of the product
commute. -/
public theorem cofiberedProduct_w
    {P Q : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p}
    (hbase : P.base ⟶ Q.base) (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (ha : 𝓕.p.IsHomLift hbase a) (hb : 𝓖.p.IsHomLift hbase b) :
    𝓕.p.map a ≫ Q.iso.hom = P.iso.hom ≫ 𝓖.p.map b := by
  let _ := ha
  let _ := hb
  rw [cofiberedProduct_iso_hom Q, cofiberedProduct_iso_hom P,
    IsHomLift.fac' 𝓕.p hbase a, IsHomLift.fac' 𝓖.p hbase b]
  simp

/-- An object of the product `𝓕 ×_{𝒞_Λ} 𝓖`: a pair of an object of `𝓕` and an object of `𝓖`
lying over one object `U` of `𝒞_Λ`. The comparison isomorphism is the canonical identification
of the two base objects. -/
public def cofiberedProductObj (U : ArtinianLocalAlgCat.{u, w, w} Λ k) (x : 𝓕.obj) (y : 𝓖.obj)
    (hx : 𝓕.p.obj x = U) (hy : 𝓖.p.obj y = U) :
    TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p where
  base := U
  x := x
  y := y
  hx := hx
  hy := hy
  iso := eqToIso (hx.trans hy.symm)
  vertical := IsHomLift.of_fac' _ (𝟙 U) _ hx hy (by simp)

/-- Every object of the product is of the form `Deformation.cofiberedProductObj`. -/
public theorem cofiberedProductObj_eq (U : ArtinianLocalAlgCat.{u, w, w} Λ k) (x : 𝓕.obj)
    (y : 𝓖.obj) (hx : 𝓕.p.obj x = U) (hy : 𝓖.p.obj y = U) (iso : 𝓕.p.obj x ≅ 𝓖.p.obj y)
    (vertical : (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)).IsHomLift (𝟙 U) iso.hom) :
    cofiberedProductObj (𝓕 := 𝓕) (𝓖 := 𝓖) U x y hx hy =
      { base := U, x := x, y := y, hx := hx, hy := hy, iso := iso, vertical := vertical } := by
  obtain rfl : eqToIso (hx.trans hy.symm) = iso := Iso.ext <| by
    rw [cofiberedProduct_iso_hom (𝓕 := 𝓕) (𝓖 := 𝓖)
      { base := U, x := x, y := y, hx := hx, hy := hy, iso := iso, vertical := vertical }]
    simp
  rfl

/-- A morphism of the product `𝓕 ×_{𝒞_Λ} 𝓖`: a pair of an arrow of `𝓕` and an arrow of `𝓖`
lying over one arrow of `𝒞_Λ`. -/
public def cofiberedProductHom
    {P Q : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p}
    (hbase : P.base ⟶ Q.base) (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (ha : 𝓕.p.IsHomLift hbase a) (hb : 𝓖.p.IsHomLift hbase b) : P ⟶ Q where
  hbase := hbase
  a := a
  b := b
  ha := ha
  hb := hb
  w := cofiberedProduct_w hbase a b ha hb

/-- The base arrow of `Deformation.cofiberedProductHom hbase a b ha hb` is `hbase`. -/
@[simp]
public theorem cofiberedProductHom_hbase
    {P Q : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p}
    (hbase : P.base ⟶ Q.base) (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (ha : 𝓕.p.IsHomLift hbase a) (hb : 𝓖.p.IsHomLift hbase b) :
    (cofiberedProductHom hbase a b ha hb).hbase = hbase := rfl

/-- The arrow of `𝓕` of `Deformation.cofiberedProductHom hbase a b ha hb` is `a`. -/
@[simp]
public theorem cofiberedProductHom_a
    {P Q : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p}
    (hbase : P.base ⟶ Q.base) (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (ha : 𝓕.p.IsHomLift hbase a) (hb : 𝓖.p.IsHomLift hbase b) :
    (cofiberedProductHom hbase a b ha hb).a = a := rfl

/-- The arrow of `𝓖` of `Deformation.cofiberedProductHom hbase a b ha hb` is `b`. -/
@[simp]
public theorem cofiberedProductHom_b
    {P Q : TwoFibreProductOver 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p}
    (hbase : P.base ⟶ Q.base) (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (ha : 𝓕.p.IsHomLift hbase a) (hb : 𝓖.p.IsHomLift hbase b) :
    (cofiberedProductHom hbase a b ha hb).b = b := rfl

/-- The first projection `𝓕 ×_{𝒞_Λ} 𝓖 → 𝓕` of the product, as a morphism over `𝒞_Λ`. -/
public def cofiberedProductFst (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    BasedFunctor (cofiberedProduct 𝓕 𝓖) 𝓕 where
  toFunctor := TwoFibreProductOver.fst 𝓕.p 𝓖.p (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p
  w := TwoFibreProductOver.fst_comp_eq

/-- The second projection `𝓕 ×_{𝒞_Λ} 𝓖 → 𝓖` of the product, as a morphism over `𝒞_Λ`. -/
public def cofiberedProductSnd (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)) :
    BasedFunctor (cofiberedProduct 𝓕 𝓖) 𝓖 :=
  twoFibreProductSnd (baseProjection 𝓕.p) (baseProjection 𝓖.p)

/-- The morphism over `𝒞_Λ` from `𝓗` to the product `𝓕 ×_{𝒞_Λ} 𝓖` determined by a pair of
morphisms over `𝒞_Λ` from `𝓗` to `𝓕` and to `𝓖`. -/
public def cofiberedProductLift (φ : BasedFunctor 𝓗 𝓕) (ψ : BasedFunctor 𝓗 𝓖) :
    BasedFunctor 𝓗 (cofiberedProduct 𝓕 𝓖) where
  toFunctor :=
    { obj := fun h ↦
        cofiberedProductObj (𝓗.p.obj h) (φ.obj h) (ψ.obj h) (φ.w_obj h) (ψ.w_obj h)
      map := fun {_ _} f ↦
        cofiberedProductHom (𝓗.p.map f) (φ.map f) (ψ.map f)
          (BasedFunctor.preserves_isHomLift φ (𝓗.p.map f) f)
          (BasedFunctor.preserves_isHomLift ψ (𝓗.p.map f) f)
      map_id := fun h ↦
        TwoFibreProductOver.Hom.ext' (φ.toFunctor.map_id h) (ψ.toFunctor.map_id h)
      map_comp := fun f g ↦
        TwoFibreProductOver.Hom.ext' (φ.toFunctor.map_comp f g) (ψ.toFunctor.map_comp f g) }
  w := rfl

/-- The first projection of the lift of a pair of morphisms over `𝒞_Λ` is the first of them. -/
@[simp]
public theorem cofiberedProductLift_comp_fst (φ : BasedFunctor 𝓗 𝓕) (ψ : BasedFunctor 𝓗 𝓖) :
    BasedFunctor.comp (cofiberedProductLift φ ψ) (cofiberedProductFst 𝓕 𝓖) = φ :=
  BasedCategory.BasedFunctor.ext' rfl

/-- The second projection of the lift of a pair of morphisms over `𝒞_Λ` is the second of
them. -/
@[simp]
public theorem cofiberedProductLift_comp_snd (φ : BasedFunctor 𝓗 𝓕) (ψ : BasedFunctor 𝓗 𝓖) :
    BasedFunctor.comp (cofiberedProductLift φ ψ) (cofiberedProductSnd 𝓕 𝓖) = ψ :=
  BasedCategory.BasedFunctor.ext' rfl

/-- The product of two categories cofibered in groupoids over `𝒞_Λ` is again cofibered in
groupoids. -/
@[stacks 0DZJ "the product of two categories cofibered in groupoids is cofibered in groupoids",
  stacks 06GK "(14) the product is again a category cofibered in groupoids"]
public theorem isCofiberedInGroupoids_cofiberedProduct
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p) :
    IsCofiberedInGroupoids (cofiberedProduct 𝓕 𝓖).p :=
  isCofiberedInGroupoids_twoFibreProductBasedCategory (baseProjection 𝓕.p)
    (baseProjection 𝓖.p) h𝓕 h𝓖 isCofiberedInGroupoids_id

/-- A morphism over `𝒞_Λ` followed by the structure morphism of its target is the structure
morphism of its source. -/
public theorem comp_baseProjection (φ : BasedFunctor 𝓗 𝓕) :
    BasedFunctor.comp φ (baseProjection 𝓕.p) = baseProjection 𝓗.p :=
  BasedCategory.BasedFunctor.ext' φ.w

/-- Given morphisms `p₁ : 𝓗 → 𝓕` and `p₂ : 𝓖 → 𝓕` of categories cofibered in groupoids over `𝒞_Λ`,
the `2`-fibre product of `𝓗` and `𝓖` formed over `𝒞_Λ` — that is, over the two composites of `p₁`
and `p₂` with the structure morphism of `𝓕` — is the product `𝓗 ×_{𝒞_Λ} 𝓖`. -/
@[stacks 0DZJ "the 2-fibre product over 𝒞_Λ along the structure morphisms is the product"]
public theorem twoFibreProductBasedCategory_comp_baseProjection
    (p₁ : BasedFunctor 𝓗 𝓕) (p₂ : BasedFunctor 𝓖 𝓕) :
    twoFibreProductBasedCategory (BasedFunctor.comp p₁ (baseProjection 𝓕.p))
        (BasedFunctor.comp p₂ (baseProjection 𝓕.p)) = cofiberedProduct 𝓗 𝓖 := by
  rw [comp_baseProjection p₁, comp_baseProjection p₂]
  rfl

/-- The product of two deformation categories over `𝒞_Λ` is a deformation category, given that
`𝒞_Λ` is one over itself. -/
public theorem isDeformationCategory_cofiberedProduct
    (hΛ : IsDeformationCategory.{u, w, w} (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)))
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p) :
    IsDeformationCategory.{u, w, w} (cofiberedProduct 𝓕 𝓖).p :=
  isDeformationCategory_twoFibreProductOver 𝓕.p 𝓖.p
    (𝟭 (ArtinianLocalAlgCat.{u, w, w} Λ k)) 𝓕.p 𝓖.p rfl rfl h𝓕 h𝓖 hΛ

/-- The product of two deformation categories over `𝒞_Λ` is a deformation category. -/
public theorem isDeformationCategory_cofiberedProduct_of_isDeformationCategory_id
    (h𝓕 : IsDeformationCategory.{u, w, w} 𝓕.p)
    (h𝓖 : IsDeformationCategory.{u, w, w} 𝓖.p) :
    IsDeformationCategory.{u, w, w} (cofiberedProduct 𝓕 𝓖).p :=
  isDeformationCategory_cofiberedProduct (isDeformationCategory_id Λ k) h𝓕 h𝓖

end Product

end Deformation

end
