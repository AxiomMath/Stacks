module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.MapRelative
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.SpecialFibreThin

/-!
# Automorphisms of the pushforwards to the square-zero extensions

Let `φ : 𝒢 → ℱ` be a morphism of categories cofibered in groupoids over `𝒞_Λ` satisfying (RS),
and let `x₀` be an object of `𝒢`. For a finite-dimensional vector space `M` over the residue
field, write `x₀[M]` for the chosen pushforward of `x₀` to the square-zero extension `k ⊕ M`
of the base of `x₀`. Then `φ` is surjective on the automorphisms of `x₀[M]` for *every* `M` as
soon as it is surjective on the automorphisms of `x₀[k]`, the dual-number pushforward.

## Main definitions

* `Deformation.coordinateProd`, `Deformation.coordinateFst`, `Deformation.coordinateSnd`: the
  product of two coordinate modules and its two projections.

## Main results

* `Deformation.isPullback_squareZeroAlg_prod`: **the square-zero extension by a product is the
  fibre product of the two square-zero extensions over the residue field.**
* `Deformation.isPullback_map_of_satisfiesRS`: the image of a fibre square under a morphism
  over the base is a fibre square, when the target satisfies (RS).
* `Deformation.surjective_mapFiberAut_squareZeroUnder_of_linearEquiv`: transport of the
  conclusion along a linear equivalence of coordinate modules.
* `Deformation.surjective_mapFiberAut_squareZeroUnder_of_subsingleton`: the conclusion for the
  zero coordinate module.
* `Deformation.surjective_mapFiberAut_squareZeroUnder_prod`: the conclusion for a product of
  two coordinate modules.
* `Deformation.surjective_mapFiberAut_squareZeroUnder`: **the conclusion for every coordinate
  module**, from the rank-one case.

## References

* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uG vG uF vF u₁ v₁

/-! ### The square-zero extension by a product of coordinate modules -/

section Prod

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The product of two coordinate modules. -/
public noncomputable abbrev coordinateProd (k : Type w) [Field k]
    (M N : FGModuleCat.{max v w} k) : FGModuleCat.{max v w} k :=
  FGModuleCat.of k (↥M × ↥N)

/-- The first projection of a product of coordinate modules. -/
public noncomputable abbrev coordinateFst (k : Type w) [Field k]
    (M N : FGModuleCat.{max v w} k) : coordinateProd.{v, w} k M N ⟶ M :=
  FGModuleCat.ofHom (LinearMap.fst k ↥M ↥N)

/-- The second projection of a product of coordinate modules. -/
public noncomputable abbrev coordinateSnd (k : Type w) [Field k]
    (M N : FGModuleCat.{max v w} k) : coordinateProd.{v, w} k M N ⟶ N :=
  FGModuleCat.ofHom (LinearMap.snd k ↥M ↥N)

/-- The reduction of a square-zero extension to the residue field is surjective. -/
public theorem surjective_squareZeroAlgRed (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M : FGModuleCat.{max v w} k) :
    Function.Surjective ((squareZeroAlgRed.{u, v, w} A M).right).hom :=
  fun c => ⟨TrivSqZeroExt.inl c.down, rfl⟩

/-- **The square-zero extension by a product is a fibre product.** The two projections exhibit
the square-zero extension by `M × N` as the fibre product of the square-zero extensions by `M`
and by `N` over the residue field. -/
public theorem isPullback_squareZeroAlg_prod (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (M N : FGModuleCat.{max v w} k) :
    IsPullback ((squareZeroAlgFunctor.{u, v, w} A).map (coordinateFst.{v, w} k M N)).right
      ((squareZeroAlgFunctor.{u, v, w} A).map (coordinateSnd.{v, w} k M N)).right
      (squareZeroAlgRed.{u, v, w} A M).right (squareZeroAlgRed.{u, v, w} A N).right := by
  refine isPullback_of_carrier _ _ _ _ ?_ (Or.inl (surjective_squareZeroAlgRed A M)) ?_ ?_
  · exact (congrArg Under.Hom.right
      (squareZeroAlgFunctor_map_red.{u, v, w} A (coordinateFst.{v, w} k M N))).trans
      (congrArg Under.Hom.right
        (squareZeroAlgFunctor_map_red.{u, v, w} A (coordinateSnd.{v, w} k M N))).symm
  · intro z z' h1 h2
    refine TrivSqZeroExt.ext ?_ (Prod.ext ?_ ?_)
    · exact ((squareZeroAlgFunctor_map_fst.{u, v, w} A (coordinateFst.{v, w} k M N) z).symm.trans
        (congrArg TrivSqZeroExt.fst h1)).trans
        (squareZeroAlgFunctor_map_fst.{u, v, w} A (coordinateFst.{v, w} k M N) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateFst.{v, w} k M N) z).symm.trans
        (congrArg TrivSqZeroExt.snd h1)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateFst.{v, w} k M N) z')
    · exact ((squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateSnd.{v, w} k M N) z).symm.trans
        (congrArg TrivSqZeroExt.snd h2)).trans
        (squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateSnd.{v, w} k M N) z')
  · intro a b hab
    have hfst : TrivSqZeroExt.fst a = TrivSqZeroExt.fst b :=
      congrArg ULift.down (hab : ULift.up (TrivSqZeroExt.fst a) = ULift.up (TrivSqZeroExt.fst b))
    refine ⟨((TrivSqZeroExt.fst a, (TrivSqZeroExt.snd a, TrivSqZeroExt.snd b)) :
        TrivSqZeroExt k (↥M × ↥N)), TrivSqZeroExt.ext ?_ ?_, TrivSqZeroExt.ext ?_ ?_⟩
    · exact squareZeroAlgFunctor_map_fst.{u, v, w} A (coordinateFst.{v, w} k M N) _
    · exact squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateFst.{v, w} k M N) _
    · exact (squareZeroAlgFunctor_map_fst.{u, v, w} A (coordinateSnd.{v, w} k M N) _).trans hfst
    · exact squareZeroAlgFunctor_map_snd.{u, v, w} A (coordinateSnd.{v, w} k M N) _

/-- **The square-zero extension by a subsingleton coordinate module is the residue field.** -/
public theorem isIso_squareZeroAlgRed_of_subsingleton
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (M : FGModuleCat.{max v w} k)
    (hM : Subsingleton ↥M) : IsIso ((squareZeroAlgRed.{u, v, w} A M).right) := by
  refine ArtinianLocalAlgCat.isIso_of_bijective_hom _
    ⟨fun z z' hzz => ?_, surjective_squareZeroAlgRed A M⟩
  exact TrivSqZeroExt.ext (congrArg ULift.down hzz) (@Subsingleton.elim _ hM _ _)

end Prod

/-! ### The image of a fibre square under a morphism over the base -/

section Image

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, v, w} Λ k)}

/-- A commutative square in a category satisfying (RS) is a pullback as soon as its image is, when
the second leg lies over a surjection. -/
private theorem isPullback_of_satisfiesRS_of_map
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : SatisfiesRS p) {z x₁ x₂ x : F} {c₁ : z ⟶ x₁} {c₂ : z ⟶ x₂} {f₁ : x₁ ⟶ x}
    {f₂ : x₂ ⟶ x} {A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k} {g₂ : A₂ ⟶ A}
    (hf₂ : p.IsHomLift g₂ f₂) (hcomm : c₁ ≫ f₁ = c₂ ≫ f₂) (hg₂ : Function.Surjective g₂.hom)
    (h : IsPullback (p.map c₁) (p.map c₂) (p.map f₁) (p.map f₂)) : IsPullback c₁ c₂ f₁ f₂ := by
  have hsurj : Function.Surjective (p.map f₂).hom := by
    rw [IsHomLift.fac' p g₂ f₂]
    exact (surjective_hom_eqToHom _).comp (hg₂.comp (surjective_hom_eqToHom _))
  obtain ⟨hlim⟩ := isLimit_of_map_isLimit hp f₁ f₂ (PullbackCone.mk c₁ c₂ hcomm) hsurj ⟨h.isLimit⟩
  exact IsPullback.of_isLimit hlim

/-- **The image of a fibre square under a morphism over the base is a fibre square**, when the
target category satisfies (RS) and the base square is a fibre square whose second leg is
surjective. -/
public theorem isPullback_map_of_satisfiesRS (φ : BasedFunctor 𝓖 𝓕) (hrsF : SatisfiesRS 𝓕.p)
    {D A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k} {π₁ : D ⟶ A₁} {π₂ : D ⟶ A₂}
    {g₁ : A₁ ⟶ A} {g₂ : A₂ ⟶ A}
    {z : 𝓖.p.Fiber D} {x₁ : 𝓖.p.Fiber A₁} {x₂ : 𝓖.p.Fiber A₂} {x : 𝓖.p.Fiber A}
    {c₁ : z.1 ⟶ x₁.1} {c₂ : z.1 ⟶ x₂.1} {f₁ : x₁.1 ⟶ x.1} {f₂ : x₂.1 ⟶ x.1}
    (hc₁ : 𝓖.p.IsHomLift π₁ c₁) (hc₂ : 𝓖.p.IsHomLift π₂ c₂)
    (hf₁ : 𝓖.p.IsHomLift g₁ f₁) (hf₂ : 𝓖.p.IsHomLift g₂ f₂)
    (hcomm : c₁ ≫ f₁ = c₂ ≫ f₂)
    (hbase : IsPullback π₁ π₂ g₁ g₂) (hg₂ : Function.Surjective g₂.hom) :
    IsPullback (φ.map c₁) (φ.map c₂) (φ.map f₁) (φ.map f₂) := by
  have hf₂B := isHomLift_basedFunctor_map φ g₂ f₂ hf₂
  have hcommB : φ.map c₁ ≫ φ.map f₁ = φ.map c₂ ≫ φ.map f₂ := by
    rw [← φ.toFunctor.map_comp, ← φ.toFunctor.map_comp, hcomm]
  have hbaseB := isPullback_map_of_isHomLift (z := fiberObj φ z) (x₁ := fiberObj φ x₁)
    (x₂ := fiberObj φ x₂) (x := fiberObj φ x) (isHomLift_basedFunctor_map φ π₁ c₁ hc₁)
    (isHomLift_basedFunctor_map φ π₂ c₂ hc₂) (isHomLift_basedFunctor_map φ g₁ f₁ hf₁)
    (isHomLift_basedFunctor_map φ g₂ f₂ hf₂) hbase
  exact isPullback_of_satisfiesRS_of_map hrsF hf₂B hcommB hg₂ hbaseB

end Image

/-! ### Surjectivity on the automorphisms of the square-zero pushforwards -/

section SquareZero

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- If `M ≃ₗ[k] N`, surjectivity on the automorphisms of the pushforward of `x₀` to the
square-zero extension by `M` gives surjectivity on those of the pushforward to the square-zero
extension by `N`. -/
public theorem surjective_mapFiberAut_squareZeroUnder_of_linearEquiv (φ : BasedFunctor 𝓖 𝓕)
    (hcofG : IsCofiberedInGroupoids 𝓖.p) (hcofF : IsCofiberedInGroupoids 𝓕.p)
    {x₀ : 𝓖.obj} (P : ChosenPushforwardsAt 𝓖.p x₀) {M N : FGModuleCat.{max v w} k}
    (e : ↥M ≃ₗ[k] ↥N)
    (h : Function.Surjective (mapFiberAut φ
      (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)))) :
    Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ N))) := by
  let eM : M ≅ N :=
    { hom := FGModuleCat.ofHom e.toLinearMap
      inv := FGModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => e.symm_apply_apply t
      inv_hom_id := by
        apply FGModuleCat.hom_ext; exact LinearMap.ext fun t => e.apply_symm_apply t }
  let eU : squareZeroUnder.{u, v, w} 𝓖.p x₀ M ≅ squareZeroUnder.{u, v, w} 𝓖.p x₀ N :=
    (squareZeroAlgFunctor.{u, v, w} (𝓖.p.obj x₀)).mapIso eM
  let eR : (squareZeroUnder.{u, v, w} 𝓖.p x₀ M).right ≅
      (squareZeroUnder.{u, v, w} 𝓖.p x₀ N).right :=
    { hom := eU.hom.right
      inv := eU.inv.right
      hom_inv_id := congrArg Under.Hom.right eU.hom_inv_id
      inv_hom_id := congrArg Under.Hom.right eU.inv_hom_id }
  have hiM := P.inclusion_cocartesian (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)
  have hiN := P.inclusion_cocartesian (squareZeroUnder.{u, v, w} 𝓖.p x₀ N)
  have hwM : 𝓖.p.IsHomLift (squareZeroUnder.{u, v, w} 𝓖.p x₀ M).hom
      (P.inclusion (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)) := inferInstance
  have hwN : 𝓖.p.IsHomLift
      ((squareZeroUnder.{u, v, w} 𝓖.p x₀ M).hom ≫ eR.hom)
      (P.inclusion (squareZeroUnder.{u, v, w} 𝓖.p x₀ N)) := by
    have hw : (squareZeroUnder.{u, v, w} 𝓖.p x₀ M).hom ≫ eR.hom =
        (squareZeroUnder.{u, v, w} 𝓖.p x₀ N).hom := eU.hom.w
    rw [hw]
    exact inferInstance
  exact surjective_mapFiberAut_of_pushforward φ hcofG hcofF
    (squareZeroUnder.{u, v, w} 𝓖.p x₀ M).hom eR
    (P.inclusion (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)) hwM
    (P.inclusion (squareZeroUnder.{u, v, w} 𝓖.p x₀ N)) hwN h

/-- For a subsingleton coordinate module `M`, the morphism is surjective on the automorphisms of
the pushforward of `x₀` to the square-zero extension by `M`. -/
public theorem surjective_mapFiberAut_squareZeroUnder_of_subsingleton (φ : BasedFunctor 𝓖 𝓕)
    (hcofF : IsCofiberedInGroupoids 𝓕.p)
    (hthinF : Quiver.IsThin (𝓕.p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    {x₀ : 𝓖.obj} (P : ChosenPushforwardsAt 𝓖.p x₀) (M : FGModuleCat.{max v w} k)
    (hM : Subsingleton ↥M) :
    Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M))) := by
  have hiso := isIso_squareZeroAlgRed_of_subsingleton.{u, v, w} (𝓖.p.obj x₀) M hM
  have hthinSpecial : Quiver.IsThin
      (𝓕.p.Fiber (specialFibreUnder.{u, v, w, uG, vG} (p := 𝓖.p) (x := x₀)).right) :=
    isThin_fiber_of_iso hcofF
      (specialFibreUnderRightIso.{u, v, w, uG, vG} (p := 𝓖.p) x₀) hthinF
  have hthin : Quiver.IsThin
      (𝓕.p.Fiber (squareZeroUnder.{u, v, w} 𝓖.p x₀ M).right) :=
    isThin_fiber_of_iso hcofF
      (asIso ((squareZeroAlgRed.{u, v, w} (𝓖.p.obj x₀) M).right)).symm hthinSpecial
  intro b
  have hsub := hthin (fiberObj φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)))
    (fiberObj φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M)))
  refine ⟨1, ?_⟩
  rw [map_one]
  exact Aut.ext (Subsingleton.elim _ _)

/-- For coordinate modules `M` and `N`, surjectivity on the automorphisms of the two
pushforwards gives surjectivity on the automorphisms of the pushforward to the square-zero
extension by `M × N`. -/
public theorem surjective_mapFiberAut_squareZeroUnder_prod (φ : BasedFunctor 𝓖 𝓕)
    (hrsG : SatisfiesRS 𝓖.p) (hrsF : SatisfiesRS 𝓕.p)
    (hthinG : Quiver.IsThin (𝓖.p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    {x₀ : 𝓖.obj} (P : ChosenPushforwardsAt 𝓖.p x₀) (M N : FGModuleCat.{max v w} k)
    (hM : Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M))))
    (hN : Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ N)))) :
    Function.Surjective (mapFiberAut φ
      (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ (coordinateProd.{v, w} k M N)))) := by
  set A := 𝓖.p.obj x₀ with hA
  set c₁ := P.map (squareZeroUnderMap.{u, v, w} 𝓖.p x₀ (coordinateFst.{v, w} k M N)) with hc₁def
  set c₂ := P.map (squareZeroUnderMap.{u, v, w} 𝓖.p x₀ (coordinateSnd.{v, w} k M N)) with hc₂def
  set f₁ := P.map (squareZeroUnderRed.{u, v, w} 𝓖.p x₀ M) with hf₁def
  set f₂ := P.map (squareZeroUnderRed.{u, v, w} 𝓖.p x₀ N) with hf₂def
  have hc₁ : 𝓖.p.IsHomLift
      ((squareZeroUnderMap.{u, v, w} 𝓖.p x₀ (coordinateFst.{v, w} k M N)).right) c₁ :=
    P.map_isHomLift _
  have hc₂ : 𝓖.p.IsHomLift
      ((squareZeroUnderMap.{u, v, w} 𝓖.p x₀ (coordinateSnd.{v, w} k M N)).right) c₂ :=
    P.map_isHomLift _
  have hf₁ : 𝓖.p.IsHomLift ((squareZeroUnderRed.{u, v, w} 𝓖.p x₀ M).right) f₁ :=
    P.map_isHomLift _
  have hf₂ : 𝓖.p.IsHomLift ((squareZeroUnderRed.{u, v, w} 𝓖.p x₀ N).right) f₂ :=
    P.map_isHomLift _
  have hcomm : c₁ ≫ f₁ = c₂ ≫ f₂ := by
    rw [hc₁def, hf₁def, hc₂def, hf₂def, ← P.map_comp, ← P.map_comp]
    exact congrArg P.map
      ((squareZeroAlgFunctor_map_red.{u, v, w} A (coordinateFst.{v, w} k M N)).trans
        (squareZeroAlgFunctor_map_red.{u, v, w} A (coordinateSnd.{v, w} k M N)).symm)
  have hbase := isPullback_squareZeroAlg_prod.{u, v, w} A M N
  have hg₂ : Function.Surjective ((squareZeroUnderRed.{u, v, w} 𝓖.p x₀ N).right).hom :=
    surjective_squareZeroAlgRed.{u, v, w} A N
  have hsq : IsPullback c₁ c₂ f₁ f₂ := isPullback_of_satisfiesRS_of_map hrsG hf₂ hcomm hg₂
    (isPullback_map_of_isHomLift hc₁ hc₂ hf₁ hf₂ hbase)
  have hsqB : IsPullback (φ.map c₁) (φ.map c₂) (φ.map f₁) (φ.map f₂) :=
    isPullback_map_of_satisfiesRS φ hrsF hc₁ hc₂ hf₁ hf₂ hcomm hbase hg₂
  have hthin : Quiver.IsThin
      (𝓖.p.Fiber (specialFibreUnder.{u, v, w, uG, vG} (p := 𝓖.p) (x := x₀)).right) :=
    isThin_fiber_specialFibreUnder_right.{u, v, w, uG, vG} (p := 𝓖.p) x₀ hrsG.1 hthinG
  exact surjective_mapFiberAut_of_fibreSquare φ hrsG.1 hrsF.1 hc₁ hc₂ hf₁ hf₂ hsq hsqB
    hbase hthin hM hN

/-- If a morphism over `𝒞_Λ` between categories
cofibered in groupoids satisfying (RS) is surjective on the automorphisms of the dual-number
pushforward of `x₀`, then it is surjective on the automorphisms of the pushforward of `x₀` to
the square-zero extension by every finite-dimensional coordinate module. -/
public theorem surjective_mapFiberAut_squareZeroUnder (φ : BasedFunctor 𝓖 𝓕)
    (hrsG : SatisfiesRS 𝓖.p) (hrsF : SatisfiesRS 𝓕.p)
    (hthinG : Quiver.IsThin (𝓖.p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    (hthinF : Quiver.IsThin (𝓕.p.Fiber (residueFieldObject.{u, v, w} Λ k)))
    {x₀ : 𝓖.obj} (P : ChosenPushforwardsAt 𝓖.p x₀)
    (hline : Function.Surjective (mapFiberAut φ
      (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ (FGModuleCat.of k (ULift.{v} k))))))
    (M : FGModuleCat.{max v w} k) :
    Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ M))) := by
  classical
  have hone : Module.finrank k (ULift.{v} k) = 1 :=
    (ULift.moduleEquiv (R := k) (M := k)).finrank_eq.trans (Module.finrank_self k)
  have hzero : ∀ N : FGModuleCat.{max v w} k, Module.finrank k ↥N = 0 →
      Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ N))) := fun N h =>
    surjective_mapFiberAut_squareZeroUnder_of_subsingleton φ hrsF.1 hthinF P N
      ((Module.finrank_eq_zero_iff_of_free (R := k) (M := ↥N)).1 h)
  suffices h : ∀ n : ℕ, ∀ N : FGModuleCat.{max v w} k, Module.finrank k ↥N ≤ n →
      Function.Surjective (mapFiberAut φ (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ N))) from
    h (Module.finrank k ↥M) M le_rfl
  intro n
  induction n with
  | zero =>
    exact fun N hN => hzero N (Nat.le_zero.1 hN)
  | succ n ih =>
    intro N hN
    by_cases hN0 : Module.finrank k ↥N = 0
    · exact hzero N hN0
    · obtain ⟨t, ht⟩ : ∃ t : ↥N, t ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hN0 ((Module.finrank_eq_zero_iff_of_free (R := k) (M := ↥N)).2
          ⟨fun a b => (hcon a).trans (hcon b).symm⟩)
      obtain ⟨q, hq⟩ := Submodule.exists_isCompl (k ∙ t)
      have hline' : Module.finrank k ↥(k ∙ t) = 1 := finrank_span_singleton ht
      have hsum : Module.finrank k ↥(k ∙ t) + Module.finrank k ↥q = Module.finrank k ↥N :=
        Submodule.finrank_add_eq_of_isCompl hq
      have hqle : Module.finrank k ↥q ≤ n := by omega
      have hP : Function.Surjective (mapFiberAut φ
          (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ (FGModuleCat.of k ↥(k ∙ t))))) :=
        surjective_mapFiberAut_squareZeroUnder_of_linearEquiv φ hrsG.1 hrsF.1 P
          (LinearEquiv.ofFinrankEq (ULift.{v} k) ↥(k ∙ t) (hone.trans hline'.symm)) hline
      have hQ : Function.Surjective (mapFiberAut φ
          (P.obj (squareZeroUnder.{u, v, w} 𝓖.p x₀ (FGModuleCat.of k ↥q)))) :=
        ih (FGModuleCat.of k ↥q) hqle
      refine surjective_mapFiberAut_squareZeroUnder_of_linearEquiv φ hrsG.1 hrsF.1 P
        (M := coordinateProd.{v, w} k (FGModuleCat.of k ↥(k ∙ t)) (FGModuleCat.of k ↥q))
        (N := N) (Submodule.prodEquivOfIsCompl (k ∙ t) q hq) ?_
      exact surjective_mapFiberAut_squareZeroUnder_prod φ hrsG hrsF hthinG P
        (FGModuleCat.of k ↥(k ∙ t)) (FGModuleCat.of k ↥q) hP hQ

end SquareZero

end Deformation

end
