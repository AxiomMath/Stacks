module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.Deformation.Cofibered.Product
public import StacksFrontier.Deformation.Smooth.FullVertical

/-!
# Changing the target of a 2-fibre product, and the factors of a product, over `𝒞_Λ`

Two `1`-morphisms of categories cofibered in groupoids over `𝒞_Λ`, both smooth: changing the
target of a `2`-fibre product along a fully faithful `1`-morphism, and replacing the two factors
of a product by two others.

## Main definitions

* `Deformation.mapBaseBasedFunctor`: postcomposition of both legs of a `2`-fibre product over
  `𝒞_Λ` with a `1`-morphism over `𝒞_Λ`.
* `Deformation.cofiberedProductMap`: the morphism of products over `𝒞_Λ` induced by a morphism on
  each factor.

## Main results

* `Deformation.isSmooth_mapBaseBasedFunctor`: `Deformation.mapBaseBasedFunctor` is smooth when
  the `1`-morphism is fully faithful.
* `Deformation.isSmooth_cofiberedProductMap`: `Deformation.cofiberedProductMap` of two full
  morphisms whose targets receive vertical arrows from their images is smooth.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0DZJ](https://stacks.math.columbia.edu/tag/0DZJ)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Changing the target of a 2-fibre product -/

section MapBase

variable {𝓣 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓐 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓑 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓓 : BasedCategory.{v₄, u₄} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- Postcomposition of both legs of a `2`-fibre product over `𝒞_Λ` with a `1`-morphism
`b : 𝓑 ⟶ 𝓓` over `𝒞_Λ`, as a `1`-morphism over `𝒞_Λ`. -/
def mapBaseBasedFunctor (G : BasedFunctor 𝓣 𝓑) (F : BasedFunctor 𝓐 𝓑) (b : BasedFunctor 𝓑 𝓓) :
    BasedFunctor (twoFibreProductBasedCategory G F)
      (twoFibreProductBasedCategory (BasedFunctor.comp G b) (BasedFunctor.comp F b)) where
  toFunctor := TwoFibreProductOver.mapBase G.toFunctor F.toFunctor b.toFunctor b.w
  w := rfl

/-- **Changing the target of a `2`-fibre product along a fully faithful `1`-morphism over `𝒞_Λ`
is smooth.** -/
theorem isSmooth_mapBaseBasedFunctor (G : BasedFunctor 𝓣 𝓑) (F : BasedFunctor 𝓐 𝓑)
    (b : BasedFunctor 𝓑 𝓓) [b.toFunctor.Full] [b.toFunctor.Faithful] :
    IsSmooth (mapBaseBasedFunctor G F b) := by
  have hequiv :
      (TwoFibreProductOver.mapBase G.toFunctor F.toFunctor b.toFunctor b.w).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_mapBase (pT := 𝓣.p) (p𝒜 := 𝓐.p) b.w
  have hfull : (mapBaseBasedFunctor G F b).toFunctor.Full :=
    (inferInstance :
      (TwoFibreProductOver.mapBase G.toFunctor F.toFunctor b.toFunctor b.w).Full)
  refine isSmooth_of_full_of_exists_vertical _ (fun R => ?_)
  have hmap : b.toFunctor.mapIso
      ((Functor.FullyFaithful.ofFullyFaithful b.toFunctor).preimageIso R.iso) = R.iso :=
    Iso.ext ((Functor.FullyFaithful.ofFullyFaithful b.toFunctor).map_preimage R.iso.hom)
  have hvert : 𝓑.p.IsHomLift (𝟙 R.base)
      ((Functor.FullyFaithful.ofFullyFaithful b.toFunctor).preimageIso R.iso).hom := by
    refine (BasedFunctor.isHomLift_iff b (𝟙 R.base) _).mp ?_
    rw [show b.toFunctor.map
        ((Functor.FullyFaithful.ofFullyFaithful b.toFunctor).preimageIso R.iso).hom =
      R.iso.hom from congrArg Iso.hom hmap]
    exact R.vertical
  have hobj : (mapBaseBasedFunctor G F b).obj ⟨R.base, R.x, R.y, R.hx, R.hy,
      (Functor.FullyFaithful.ofFullyFaithful b.toFunctor).preimageIso R.iso, hvert⟩ = R :=
    TwoFibreProductOver.obj_ext (p𝒳 := 𝓣.p) (p𝒴 := 𝓐.p) (p𝒮 := 𝓓.p)
      (F := (BasedFunctor.comp G b).toFunctor) (G := (BasedFunctor.comp F b).toFunctor)
      (base := R.base) (x := R.x) (y := R.y) (hx := R.hx) (hy := R.hy) hmap
  exact ⟨⟨R.base, R.x, R.y, R.hx, R.hy,
    (Functor.FullyFaithful.ofFullyFaithful b.toFunctor).preimageIso R.iso, hvert⟩,
    eqToHom hobj, IsHomLift.eqToHom_codomain_lift_id hobj rfl⟩

end MapBase

/-! ### Changing the two factors of a product -/

section Product

variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓕' : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓖' : BasedCategory.{v₄, u₄} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- The morphism of products over `𝒞_Λ` induced by a morphism on each factor. -/
def cofiberedProductMap (φ : BasedFunctor 𝓕 𝓕') (ψ : BasedFunctor 𝓖 𝓖') :
    BasedFunctor (cofiberedProduct 𝓕 𝓖) (cofiberedProduct 𝓕' 𝓖') :=
  cofiberedProductLift (BasedFunctor.comp (cofiberedProductFst 𝓕 𝓖) φ)
    (BasedFunctor.comp (cofiberedProductSnd 𝓕 𝓖) ψ)

/-- **A product of two full morphisms over `𝒞_Λ` whose factors receive vertical arrows from the
images is smooth.** -/
theorem isSmooth_cofiberedProductMap (φ : BasedFunctor 𝓕 𝓕') (ψ : BasedFunctor 𝓖 𝓖')
    [φ.toFunctor.Full] [ψ.toFunctor.Full]
    (hφ : ∀ x' : 𝓕'.obj, ∃ (x : 𝓕.obj) (a : φ.obj x ⟶ x'),
      𝓕'.p.IsHomLift (𝟙 (𝓕'.p.obj x')) a)
    (hψ : ∀ y' : 𝓖'.obj, ∃ (y : 𝓖.obj) (b : ψ.obj y ⟶ y'),
      𝓖'.p.IsHomLift (𝟙 (𝓖'.p.obj y')) b) :
    IsSmooth (cofiberedProductMap φ ψ) := by
  have hfull : (cofiberedProductMap φ ψ).toFunctor.Full := ⟨fun {_ _} m =>
    ⟨cofiberedProductHom m.hbase (φ.toFunctor.preimage m.a) (ψ.toFunctor.preimage m.b)
      ((BasedFunctor.isHomLift_iff φ m.hbase _).mp
        (cast (congrArg (fun t => 𝓕'.p.IsHomLift m.hbase t)
          (φ.toFunctor.map_preimage m.a).symm) m.ha))
      ((BasedFunctor.isHomLift_iff ψ m.hbase _).mp
        (cast (congrArg (fun t => 𝓖'.p.IsHomLift m.hbase t)
          (ψ.toFunctor.map_preimage m.b).symm) m.hb)),
      TwoFibreProductOver.Hom.ext' (φ.toFunctor.map_preimage m.a)
        (ψ.toFunctor.map_preimage m.b)⟩⟩
  refine isSmooth_of_full_of_exists_vertical _ (fun R => ?_)
  obtain ⟨x, a, ha⟩ := hφ R.x
  obtain ⟨y, b, hb⟩ := hψ R.y
  have hx : 𝓕.p.obj x = R.base :=
    (BasedFunctor.w_obj φ x).symm.trans
      ((IsHomLift.domain_eq 𝓕'.p (𝟙 (𝓕'.p.obj R.x)) a).trans R.hx)
  have hy : 𝓖.p.obj y = R.base :=
    (BasedFunctor.w_obj ψ y).symm.trans
      ((IsHomLift.domain_eq 𝓖'.p (𝟙 (𝓖'.p.obj R.y)) b).trans R.hy)
  have haR : 𝓕'.p.IsHomLift (𝟙 R.base) a :=
    (congrArg (fun U => 𝓕'.p.IsHomLift (𝟙 U) a) R.hx).mp ha
  have hbR : 𝓖'.p.IsHomLift (𝟙 R.base) b :=
    (congrArg (fun U => 𝓖'.p.IsHomLift (𝟙 U) b) R.hy).mp hb
  exact ⟨cofiberedProductObj R.base x y hx hy, _, IsHomLift.map (cofiberedProduct 𝓕' 𝓖').p
    (cofiberedProductHom
      (P := (cofiberedProductMap φ ψ).obj (cofiberedProductObj R.base x y hx hy)) (Q := R)
      (𝟙 R.base) a b haR hbR)⟩

end Product

end Deformation

end
