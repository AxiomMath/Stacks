module

public import Mathlib.Algebra.Exact.Basic
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the tangent row of the six-term sequence of a 2-fibre product

Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over `𝒞_Λ` and let
`𝒲 = ℋ ×_ℱ 𝒢`. Part (2) of Tag 06L5 asserts a six-term exact sequence

`0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`.

This file treats the tail of that sequence: the three maps

`Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`,

read at an arbitrary coordinate module `M` (so at the rank-one module they are the tangent
spaces and the infinitesimal automorphism group of the source), and exactness at the two
interior terms `T𝒲` and `Tℋ ⊕ T𝒢`. The boundary map is `Deformation.boundaryFun`; its
`k`-linear form is `Deformation.boundaryLinearMap`, with exactness at `T𝒲` proved as
`Deformation.exact_boundaryLinearMap_tangentProjPair`.

## Main definitions

* `Deformation.tangentModuleAt` and `Deformation.tangentMapAt`: the tangent module `T𝓕(M)` of a
  deformation category and the `k`-linear map induced on it by a `1`-morphism. These package
  `Deformation.associatedTangentSpaceModuleStructure` and
  `Deformation.associatedTangentLiftMap` with the (S2) condition supplied by Tag 07WV.
* `Deformation.tangentClassAt`: the class of an object of the fibre over `k[M]`, read in the
  tangent module. Every element of the tangent module is one
  (`Deformation.tangentClassAt_surjective`), and two of them agree exactly when the objects are
  isomorphic in the fibre (`Deformation.tangentClassAt_eq_iff`).
* `Deformation.productFst`, `Deformation.productSnd`, `Deformation.firstLegBased`,
  `Deformation.secondLegBased`: the two projections of the `2`-fibre product and the two outer
  legs, as `1`-morphisms over `𝒞_Λ`.
* `Deformation.tangentProjPair`: the map `c : T𝒲 → Tℋ ⊕ T𝒢`, the pair of the maps induced by
  the two projections.
* `Deformation.tangentLegDiff`: the map `d : Tℋ ⊕ T𝒢 → Tℱ`, the difference of the maps induced
  by `f` and by `g`. The signs are the ones the source defers: a map into a direct sum is a
  pair, a map out of one is a difference.

## Main results

* `Deformation.exact_tangentProjPair_tangentLegDiff`: **part (2) of Tag 06L5, exactness at
  `Tℋ ⊕ T𝒢`**. An element of `Tℋ ⊕ T𝒢` killed by `d` is a pair of classes of objects `y` of
  `ℋ(k[M])` and `z` of `𝒢(k[M])` whose images under `f` and `g` are isomorphic in `ℱ(k[M])`;
  any vertical isomorphism between them makes the quadruple `(k[M], y, z, φ)` an object of
  `𝒲(k[M])` projecting to the given pair. Conversely the comparison isomorphism carried by an
  object of `𝒲(k[M])` is exactly a fibrewise isomorphism between its two images, so `d ∘ c = 0`.
* `Deformation.exact_boundaryFun_tangentProjPair`: exactness at `T𝒲` for the boundary map read
  as a map of **sets** on the infinitesimal automorphism group of `x'₀`; the form for the
  `k`-linear boundary map is `Deformation.exact_boundaryLinearMap_tangentProjPair`.
* `Deformation.infinitesimalAutomorphismsAlongSplitPair_eq_top_of_isThin`: over a thin fibre
  every automorphism of a chosen pushforward along a split inclusion is infinitesimal.

## Implementation notes

The two direct summands `Tℋ` and `T𝒢` live in different type universes, since `ℋ` and `𝒢` do;
`Prod` is universe-polymorphic in both arguments, so the direct sum is their product and no
universe lift is needed.

The `2`-fibre product is taken over the two legs' own projections `f ⋙ pF` and `g ⋙ pF`, which
makes the two outer legs `1`-morphisms over `𝒞_Λ` by `rfl`; the general form, with projections
`pH` and `pG` and equalities `f ⋙ pF = pH`, follows by substituting those equalities.

Exactness is `Function.Exact`: the kernel of each map is the image of the previous one. The
boundary map is only a map of sets here, since `Function.Exact` needs no more than a zero in the
target.

The source's `Inf` is taken relative to a chosen splitting of the inclusion `k ⟶ k[M]`, so that
splitting is a hypothesis of `Deformation.exact_boundaryFun_tangentProjPair`. The basepoint is
required to lie over the residue field, which makes the fibre containing `x₀` thin.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/

@[expose] public section

namespace Deformation

/-! ### Classes in the tangent module -/

section TangentClass
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

private theorem cast_cancel_symm {α β : Type u₁} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by
  cases h; rfl

/-- Condition (S2) for the functor of isomorphism classes of a deformation category
(Stacks Tag 07WV). -/
public theorem tangentConditionS2
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) :
    SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)) :=
  Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 h𝓕

/-- The tangent module `T𝓕(M)` of a deformation category at a coordinate module `M`: the value
at `M` of the canonical linear lift of the associated square-zero functor. At the rank-one
module this is the tangent space of Tag 06I9 with the vector-space structure of Tag 06IH. -/
@[sga "3 XI 1.9" "partial", sga "7 VI 1.18" "clause (1), partial"]
public noncomputable abbrev tangentModuleAt
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (M : FGModuleCat.{max v w} k) :
    ModuleCat.{u₁} k :=
  (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕)).functor.obj M

/-- The class of an object of the fibre over the square-zero extension by `M`, read in the
tangent module. -/
public noncomputable def tangentClassAt
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (M : FGModuleCat.{max v w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) :=
  cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕) M).symm
    (classOf 𝓕 h𝓕.predeformation.cofibered x)

/-- The class in the tangent module is the transported isomorphism class. -/
public theorem tangentClassAt_eq
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (M : FGModuleCat.{max v w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    tangentClassAt.{u, v, w} 𝓕 h𝓕 M x =
      cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
          (tangentConditionS2.{u, v, w} h𝓕) M).symm
        (classOf 𝓕 h𝓕.predeformation.cofibered x) := rfl

/-- Every element of the tangent module is the class of an object of the fibre. -/
public theorem tangentClassAt_surjective
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (M : FGModuleCat.{max v w} k) :
    Function.Surjective (tangentClassAt.{u, v, w} 𝓕 h𝓕 M) := by
  intro t
  obtain ⟨x, hx⟩ := classOf_surjective 𝓕 h𝓕.predeformation.cofibered
    ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)
    (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕) M) t)
  refine ⟨x, ?_⟩
  rw [tangentClassAt_eq, hx, cast_cancel_symm]

/-- Two objects of the fibre over `k[M]` have the same class in the tangent module exactly when
they are isomorphic in that fibre. -/
public theorem tangentClassAt_eq_iff
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (M : FGModuleCat.{max v w} k)
    (x y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    tangentClassAt.{u, v, w} 𝓕 h𝓕 M x = tangentClassAt.{u, v, w} 𝓕 h𝓕 M y ↔
      IsIsomorphic x y := by
  rw [tangentClassAt_eq, tangentClassAt_eq,
    ← classOf_eq_iff 𝓕 h𝓕.predeformation.cofibered x y]
  refine ⟨fun h => ?_, fun h => congrArg _ h⟩
  have h2 := congrArg (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) M)) h
  rwa [cast_symm_cancel, cast_symm_cancel] at h2

/-- The `k`-linear map on tangent modules induced by a `1`-morphism of deformation categories.
At the rank-one module this is the differential of Tag 06IJ. -/
public noncomputable def tangentMapAt
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{max v w} k) :
    ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) →ₗ[k] ↥(tangentModuleAt.{u, v, w} 𝓖 h𝓖 M) :=
  associatedTangentLiftMap.{u, v, w} 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) (tangentConditionS2.{u, v, w} h𝓖) φ M

/-- The induced map sends the class of an object of the fibre to the class of its image. -/
public theorem tangentMapAt_tangentClassAt
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{max v w} k)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) :
    tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M (tangentClassAt.{u, v, w} 𝓕 h𝓕 M x) =
      tangentClassAt.{u, v, w} 𝓖 h𝓖 M
        ((fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj x) :=
  associatedTangentLiftMap_classOf.{u, v, w} 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) (tangentConditionS2.{u, v, w} h𝓖) φ M x

end TangentClass

/-! ### The tangent row of the six-term sequence -/

section TangentRow
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

/-- The `2`-fibre product `𝒲 = ℋ ×_ℱ 𝒢`, as a based category over `𝒞_Λ`. The two outer legs
are taken over their own projections `f ⋙ pF` and `g ⋙ pF`. -/
public abbrev productBased (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) :=
  BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g)

/-- The first projection `𝒲 → ℋ`, as a `1`-morphism over `𝒞_Λ`. -/
public def productFst (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) :
    productBased.{u, v, w} pF f g ⥤ᵇ BasedCategory.ofFunctor (f ⋙ pF) where
  toFunctor := TwoFibreProductOver.fst (f ⋙ pF) (g ⋙ pF) pF f g
  w := TwoFibreProductOver.fst_comp_eq

/-- The second projection `𝒲 → 𝒢`, as a `1`-morphism over `𝒞_Λ`. -/
public def productSnd (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) :
    productBased.{u, v, w} pF f g ⥤ᵇ BasedCategory.ofFunctor (g ⋙ pF) where
  toFunctor := TwoFibreProductOver.snd (f ⋙ pF) (g ⋙ pF) pF f g
  w := TwoFibreProductOver.snd_comp_eq

/-- The first outer leg `f : ℋ → ℱ`, as a `1`-morphism over `𝒞_Λ`. -/
public def firstLegBased (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) :
    BasedCategory.ofFunctor (f ⋙ pF) ⥤ᵇ BasedCategory.ofFunctor pF where
  toFunctor := f
  w := rfl

/-- The second outer leg `g : 𝒢 → ℱ`, as a `1`-morphism over `𝒞_Λ`. -/
public def secondLegBased (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (g : G ⥤ F) :
    BasedCategory.ofFunctor (g ⋙ pF) ⥤ᵇ BasedCategory.ofFunctor pF where
  toFunctor := g
  w := rfl

variable (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)

/-- The `2`-fibre product of the two legs is a deformation category (part (1) of
Stacks Tag 06L5). -/
public theorem isDeformationCategory_productBased
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) :
    IsDeformationCategory.{u, v, w}
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) :=
  isDeformationCategory_twoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g rfl rfl hH hG hF

/-- The comparison isomorphism carried by an object of the fibre of the `2`-fibre product over
`U` is vertical over `U`. -/
public theorem isHomLift_fibre_iso
    {U : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (W : (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).Fiber U) :
    pF.IsHomLift (𝟙 U) W.1.iso.hom := by
  obtain ⟨W, hW⟩ := W
  subst hW
  exact W.vertical

/-- `c`, the map `T𝒲 → Tℋ ⊕ T𝒢` of the six-term sequence: the pair of the maps induced on
tangent modules by the two projections of the `2`-fibre product. -/
public noncomputable def tangentProjPair
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k) :
    ↥(tangentModuleAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M) →ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M) ×
        ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (g ⋙ pF)) hG M) :=
  LinearMap.prod
    (tangentMapAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
      (productFst.{u, v, w} pF f g) M)
    (tangentMapAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
      (productSnd.{u, v, w} pF f g) M)

/-- The first component of `c` is the map induced by the first projection. -/
public theorem tangentProjPair_apply_fst
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k)
    (t : ↥(tangentModuleAt.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M)) :
    (tangentProjPair.{u, v, w} pF f g hH hG hF M t).1 =
      tangentMapAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
        (productFst.{u, v, w} pF f g) M t := rfl

/-- The second component of `c` is the map induced by the second projection. -/
public theorem tangentProjPair_apply_snd
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k)
    (t : ↥(tangentModuleAt.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M)) :
    (tangentProjPair.{u, v, w} pF f g hH hG hF M t).2 =
      tangentMapAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
        (productSnd.{u, v, w} pF f g) M t := rfl

/-- `d`, the map `Tℋ ⊕ T𝒢 → Tℱ` of the six-term sequence: the difference of the maps induced on
tangent modules by the two outer legs. The sign is the one the source defers: a map out of a
direct sum is a difference. -/
public noncomputable def tangentLegDiff
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k) :
    (↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M) ×
        ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (g ⋙ pF)) hG M)) →ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor pF) hF M) :=
  (tangentMapAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M).comp
      (LinearMap.fst k _ _) -
    (tangentMapAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M).comp
      (LinearMap.snd k _ _)

/-- `d` is the difference of the two maps induced by the outer legs. -/
public theorem tangentLegDiff_apply
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k)
    (b : ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M) ×
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (g ⋙ pF)) hG M)) :
    tangentLegDiff.{u, v, w} pF f g hH hG hF M b =
      tangentMapAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M b.1 -
        tangentMapAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M b.2 := rfl

/-- In the tangent row `T𝒲 → Tℋ ⊕ T𝒢 → Tℱ` of the six-term sequence of the `2`-fibre product
`𝒲 = ℋ ×_ℱ 𝒢`, the kernel of the difference of the two outer legs is the image of the pair of
the two projections. -/
@[stacks 06L5 "part (2), the tangent row `T𝒲 → Tℋ ⊕ T𝒢 → Tℱ` of the six-term exact sequence \
and its exactness at `Tℋ ⊕ T𝒢`"]
public theorem exact_tangentProjPair_tangentLegDiff
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) (M : FGModuleCat.{max v w} k) :
    Function.Exact (tangentProjPair.{u, v, w} pF f g hH hG hF M)
      (tangentLegDiff.{u, v, w} pF f g hH hG hF M) := by
  intro b
  constructor
  · -- An element killed by `d` comes from `T𝒲`.
    intro hb
    obtain ⟨y, hy⟩ := tangentClassAt_surjective.{u, v, w}
      (BasedCategory.ofFunctor (f ⋙ pF)) hH M b.1
    obtain ⟨z, hz⟩ := tangentClassAt_surjective.{u, v, w}
      (BasedCategory.ofFunctor (g ⋙ pF)) hG M b.2
    have hfy := tangentMapAt_tangentClassAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M y
    have hgz := tangentMapAt_tangentClassAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M z
    have hb' : tangentMapAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M b.1 -
        tangentMapAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M b.2 = 0 := hb
    have hdiff : tangentMapAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M b.1 =
        tangentMapAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M b.2 := sub_eq_zero.mp hb'
    rw [← hy, ← hz, hfy, hgz] at hdiff
    obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u, v, w} (BasedCategory.ofFunctor pF) hF M _ _).mp hdiff
    refine ⟨tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
      ⟨{ base := (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M
         x := y.1
         y := z.1
         hx := y.2
         hy := z.2
         iso := Fiber.fiberInclusion.mapIso e
         vertical := e.hom.2 }, rfl⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · rw [tangentProjPair_apply_fst.{u, v, w}]
      exact (tangentMapAt_tangentClassAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
        (productFst.{u, v, w} pF f g) M _).trans hy
    · rw [tangentProjPair_apply_snd.{u, v, w}]
      exact (tangentMapAt_tangentClassAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
        (productSnd.{u, v, w} pF f g) M _).trans hz
  · -- The composite vanishes.
    rintro ⟨t, rfl⟩
    obtain ⟨W, hW⟩ := tangentClassAt_surjective.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M t
    subst hW
    rw [tangentLegDiff_apply.{u, v, w}, tangentProjPair_apply_fst.{u, v, w},
      tangentProjPair_apply_snd.{u, v, w},
      tangentMapAt_tangentClassAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
      (productFst.{u, v, w} pF f g) M W,
      tangentMapAt_tangentClassAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
      (productSnd.{u, v, w} pF f g) M W,
      tangentMapAt_tangentClassAt.{u, v, w} hH hF (firstLegBased.{u, v, w} pF f) M _,
      tangentMapAt_tangentClassAt.{u, v, w} hG hF (secondLegBased.{u, v, w} pF g) M _,
      sub_eq_zero, tangentClassAt_eq_iff.{u, v, w} (BasedCategory.ofFunctor pF) hF M _ _]
    have hv := isHomLift_fibre_iso.{u, v, w} pF f g W
    refine ⟨{ hom := ⟨W.1.iso.hom, hv⟩
              inv := ⟨W.1.iso.inv, ?_⟩
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · let := hv
      exact inferInstanceAs (pF.IsHomLift (𝟙 _) W.1.iso.inv)
    · apply Fiber.hom_ext
      exact W.1.iso.hom_inv_id
    · apply Fiber.hom_ext
      exact W.1.iso.inv_hom_id

end TangentRow

/-! ### The zero of the tangent module, on chosen pushforwards -/

section PushforwardZero
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F]

-- The re-based square-zero extension has to unfold for `(squareZeroCrossUnder A M).right` to be
-- recognized as the square-zero extension by `M`.
attribute [local implicit_reducible] squareZeroCrossUnder

/-- The structure arrow of the re-based square-zero extension by `M` is unchanged by the zero
coordinate map: it is a morphism of objects under `A` from the extension to itself, and such a
morphism is by definition compatible with the two structure arrows, which are the same one. -/
public theorem squareZeroCrossUnder_hom_comp_map_zero
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (M : FGModuleCat.{max v w} k) :
    (squareZeroCrossUnder.{u, v, w} A M).hom ≫
        (squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M) =
      (squareZeroCrossUnder.{u, v, w} A M).hom :=
  Under.w (squareZeroCrossUnderMap.{u, v, w} A (0 : M ⟶ M))

/-- The class of the chosen pushforward of an object `x` to the re-based square-zero extension
by `M` is the zero of the tangent module. -/
public theorem tangentClassAt_pushforward_eq_zero
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (x : 𝓕.obj)
    (P : ChosenPushforwardsAt 𝓕.p x) (M : FGModuleCat.{max v w} k) :
    tangentClassAt.{u, v, w} 𝓕 h𝓕 M
      (P.obj (squareZeroCrossUnder.{u, v, w} (𝓕.p.obj x) M)) = 0 := by
  have hinst : 𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (0 : M ⟶ M))
      (P.map (squareZeroCrossUnderMap.{u, v, w} (𝓕.p.obj x) (0 : M ⟶ M))) :=
    P.map_isHomLift (squareZeroCrossUnderMap.{u, v, w} (𝓕.p.obj x) (0 : M ⟶ M))
  let := hinst
  exact associatedTangentLift_classOf_eq_zero.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) M _ _
    (P.map (squareZeroCrossUnderMap.{u, v, w} (𝓕.p.obj x) (0 : M ⟶ M)))

end PushforwardZero

/-! ### Vertical isomorphisms as isomorphisms of a fibre -/

section FiberIso
open CategoryTheory CategoryTheory.Functor
universe u₁ v₁ u₂ v₂

/-- A vertical isomorphism of the total category is an isomorphism of the fibre. -/
public def fiberIsoOfVertical {X : Type u₁} [Category.{v₁} X] {C : Type u₂} [Category.{v₂} C]
    {p : X ⥤ C} {A : C} (a b : p.Fiber A) (φ : a.1 ≅ b.1)
    (h : p.IsHomLift (𝟙 A) φ.hom) : a ≅ b where
  hom := ⟨φ.hom, h⟩
  inv := ⟨φ.inv, by have := h; infer_instance⟩
  hom_inv_id := by apply Functor.Fiber.hom_ext; exact φ.hom_inv_id
  inv_hom_id := by apply Functor.Fiber.hom_ext; exact φ.inv_hom_id

@[simp]
public theorem fiberIsoOfVertical_hom {X : Type u₁} [Category.{v₁} X] {C : Type u₂}
    [Category.{v₂} C] {p : X ⥤ C} {A : C} (a b : p.Fiber A) (φ : a.1 ≅ b.1)
    (h : p.IsHomLift (𝟙 A) φ.hom) :
    Functor.Fiber.fiberInclusion.map (fiberIsoOfVertical a b φ h).hom = φ.hom := rfl

@[simp]
public theorem fiberIsoOfVertical_inv {X : Type u₁} [Category.{v₁} X] {C : Type u₂}
    [Category.{v₂} C] {p : X ⥤ C} {A : C} (a b : p.Fiber A) (φ : a.1 ≅ b.1)
    (h : p.IsHomLift (𝟙 A) φ.hom) :
    Functor.Fiber.fiberInclusion.map (fiberIsoOfVertical a b φ h).inv = φ.inv := rfl

@[simp]
public theorem fiberIsoOfVertical_mapIso_hom {X : Type u₁} [Category.{v₁} X] {C : Type u₂}
    [Category.{v₂} C] {p : X ⥤ C} {A : C} (a b : p.Fiber A) (φ : a.1 ≅ b.1)
    (h : p.IsHomLift (𝟙 A) φ.hom) :
    (Functor.Fiber.fiberInclusion.mapIso (fiberIsoOfVertical a b φ h)).hom = φ.hom := rfl

@[simp]
public theorem fiberIsoOfVertical_mapIso_inv {X : Type u₁} [Category.{v₁} X] {C : Type u₂}
    [Category.{v₂} C] {p : X ⥤ C} {A : C} (a b : p.Fiber A) (φ : a.1 ≅ b.1)
    (h : p.IsHomLift (𝟙 A) φ.hom) :
    (Functor.Fiber.fiberInclusion.mapIso (fiberIsoOfVertical a b φ h)).inv = φ.inv := rfl

end FiberIso

/-! ### Over a thin fibre every automorphism of a pushforward is infinitesimal -/

section AllInfinitesimal
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂

/-- If the fibre over `A₀` is thin, then every automorphism of a chosen pushforward of `x₀`
along a split inclusion `A₀ → Aε` is infinitesimal. -/
public theorem infinitesimalAutomorphismsAlongSplitPair_eq_top_of_isThin
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} {A₀ Aε : C} {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hge : g ≫ e = 𝟙 A₀)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (hthin : Quiver.IsThin (p.Fiber A₀)) :
    infinitesimalAutomorphismsAlongSplitPair hp g e hge i hi = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun a => ?_
  rw [mem_infinitesimalAutomorphismsAlongSplitPair_iff]
  have hrl : p.IsHomLift e (canonicalRetraction hp g e hge i hi).1 :=
    (canonicalRetraction hp g e hge i hi).2.1
  have hrf : i ≫ (canonicalRetraction hp g e hge i hi).1 = 𝟙 x₀.1 :=
    (canonicalRetraction hp g e hge i hi).2.2
  have hal : p.IsHomLift (𝟙 Aε) a.hom.val := a.hom.2
  have hcoc := isStronglyCocartesian_of_isCofiberedInGroupoids hp g i hi
  have hi' := hi
  have hcompl : p.IsHomLift e (a.hom.val ≫ (canonicalRetraction hp g e hge i hi).1) :=
    inferInstance
  have hendo : p.IsHomLift (𝟙 A₀)
      (i ≫ a.hom.val ≫ (canonicalRetraction hp g e hge i hi).1) := by
    have h : p.IsHomLift (g ≫ e)
      (i ≫ a.hom.val ≫ (canonicalRetraction hp g e hge i hi).1) := inferInstance
    rwa [hge] at h
  have hsub := hthin x₀ x₀
  have hendoeq : i ≫ a.hom.val ≫ (canonicalRetraction hp g e hge i hi).1 = 𝟙 x₀.1 :=
    congrArg Subtype.val
      (Subsingleton.elim
        (⟨i ≫ a.hom.val ≫ (canonicalRetraction hp g e hge i hi).1, hendo⟩ : x₀ ⟶ x₀) (𝟙 x₀))
  exact Functor.IsStronglyCocartesian.ext p g i e (hendoeq.trans hrf.symm)

/-- The special fibre of a predeformation category is thin: there is a unique morphism between
any two of its objects. -/
public theorem isThin_specialFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory.{u, v, w} p) :
    Quiver.IsThin (p.Fiber (residueFieldObject.{u, v, w} Λ k)) := by
  obtain ⟨-, hu⟩ := (CategoryTheory.equiv_punit_iff_unique _).mp hp.specialFiber
  intro A B
  obtain ⟨uu⟩ := hu A B
  exact uu.instSubsingleton

end AllInfinitesimal

/-! ### The boundary map lands in the kernel at `T𝒲` -/

section BoundaryKernel
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- The boundary map `δ : Aut(x'₀) → T𝒲` of the six-term sequence lands in the kernel of the
map `c : T𝒲 → Tℋ ⊕ T𝒢`. -/
@[stacks 06L5 "part (2), that the boundary map of the six-term exact sequence lands in the \
kernel of `T𝒲 → Tℋ ⊕ T𝒢`"]
public theorem tangentProjPair_boundaryFun_eq_zero
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    tangentProjPair.{u, v, w} pF f g hH hG hF M
        (boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
          (tangentConditionS2.{u, v, w}
            (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) M α) = 0 := by
  refine Prod.ext ?_ ?_
  · rw [tangentProjPair_apply_fst.{u, v, w}]
    refine (tangentMapAt_tangentClassAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
      (productFst.{u, v, w} pF f g) M
      ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α,
        rfl⟩).trans ?_
    exact tangentClassAt_pushforward_eq_zero.{u, v, w}
      (BasedCategory.ofFunctor (f ⋙ pF)) hH y₀ PH M
  · rw [tangentProjPair_apply_snd.{u, v, w}]
    refine (tangentMapAt_tangentClassAt.{u, v, w}
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
      (productSnd.{u, v, w} pF f g) M
      ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α,
        rfl⟩).trans ?_
    exact tangentClassAt_pushforward_eq_zero.{u, v, w}
      (BasedCategory.ofFunctor (g ⋙ pF)) hG z₀ PG M

/-- A fibre object of `f ⋙ pF` with vanishing class in the tangent module is isomorphic to the
chosen pushforward by a vertical isomorphism, whose image under `f` is vertical over `pF`. -/
private theorem exists_vertical_iso_pushforward_of_tangentClassAt_eq_zero
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF)) {y₀ : H}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (M : FGModuleCat.{max v w} k)
    (a : (f ⋙ pF).Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (h : tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M a = 0) :
    ∃ c : a.1 ≅ (PH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).1,
      (f ⋙ pF).IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) c.hom ∧
        pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
          (f.map c.hom) ∧
        pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
          (f.map c.inv) := by
  obtain ⟨i⟩ := (tangentClassAt_eq_iff.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M _ _).mp
    (h.trans (tangentClassAt_pushforward_eq_zero.{u, v, w}
      (BasedCategory.ofFunctor (f ⋙ pF)) hH y₀ PH M).symm)
  have h1 : (f ⋙ pF).IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    i.hom.val := i.hom.2
  have h2 : (f ⋙ pF).IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    i.inv.val := i.inv.2
  exact ⟨⟨i.hom.val, i.inv.val, congrArg Subtype.val i.hom_inv_id,
      congrArg Subtype.val i.inv_hom_id⟩, i.hom.2,
    Functor.isHomLift_map_of_comp_eq (rfl : f ⋙ pF = f ⋙ pF) _ i.hom.val,
    Functor.isHomLift_map_of_comp_eq (rfl : f ⋙ pF = f ⋙ pF) _ i.inv.val⟩

/-- Every element of the kernel of `c` is in the image of the boundary map: it is the class of
`(k[M], y'₀, z'₀, c' ∘ α ∘ b')` for an automorphism `α` of `x'₀`. -/
public theorem exists_aut_boundaryObject_tangentClassAt_eq
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (W : (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).Fiber
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (hker : tangentProjPair.{u, v, w} pF f g hH hG hF M
      (tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M W) = 0) :
    ∃ α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)),
      tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
          ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α,
            rfl⟩ =
        tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M W := by
  -- The class of each projection of `W` vanishes, hence equals that of the chosen pushforward.
  have h1 : tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (f ⋙ pF)) hH M
      ((fiberFunctor (productFst.{u, v, w} pF f g)
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj W) = 0 := by
    have hc := congrArg Prod.fst hker
    rw [tangentProjPair_apply_fst.{u, v, w},
      tangentMapAt_tangentClassAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hH
        (productFst.{u, v, w} pF f g) M W] at hc
    exact hc
  have h2 : tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (g ⋙ pF)) hG M
      ((fiberFunctor (productSnd.{u, v, w} pF f g)
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj W) = 0 := by
    have hc := congrArg Prod.snd hker
    rw [tangentProjPair_apply_snd.{u, v, w},
      tangentMapAt_tangentClassAt.{u, v, w}
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) hG
        (productSnd.{u, v, w} pF f g) M W] at hc
    exact hc
  obtain ⟨iI, hiI0, hiI1, hiI2⟩ := exists_vertical_iso_pushforward_of_tangentClassAt_eq_zero
    pF f hH PH M ⟨W.1.x, _⟩ h1
  obtain ⟨jI, hjI0, hjI1, hjI2⟩ := exists_vertical_iso_pushforward_of_tangentClassAt_eq_zero
    pF g hG PG M ⟨W.1.y, _⟩ h2
  -- The comparison isomorphisms of the source are vertical, and so is that of `W`.
  have hb1 := (isHomLift_boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).1
  have hb2 := (isHomLift_boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).2
  have hc1 := (isHomLift_boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF
    hF.predeformation.cofibered M).1
  have hc2 := (isHomLift_boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF
    hF.predeformation.cofibered M).2
  have hWv := isHomLift_fibre_iso.{u, v, w} pF f g W
  have hWv' : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      W.1.iso.inv := by have := hWv; infer_instance
  have hWv' : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      W.1.iso.inv := by have := hWv; infer_instance
  have hv : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      ((boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).hom ≫
        f.map iI.inv ≫ W.1.iso.hom ≫ g.map jI.hom ≫
          (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF
            hF.predeformation.cofibered M).inv) := inferInstance
  refine ⟨fiberIsoOfVertical _ _
    ⟨(boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).hom ≫
        f.map iI.inv ≫ W.1.iso.hom ≫ g.map jI.hom ≫
          (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hF.predeformation.cofibered M).inv,
      (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hF.predeformation.cofibered M).hom ≫
        g.map jI.inv ≫ W.1.iso.inv ≫ f.map iI.hom ≫
          (boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).inv,
      by simp, by simp⟩
    hv, ?_⟩
  refine (tangentClassAt_eq_iff.{u, v, w} (productBased.{u, v, w} pF f g)
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M _ _).mpr
    ⟨(fiberIsoOfVertical W _
      (TwoFibreProductOver.isoMkVertical iI jI hiI0 hjI0 ?_) ?_).symm⟩
  · change f.map iI.hom ≫
        (boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).inv ≫
          (((boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).hom ≫
              f.map iI.inv ≫ W.1.iso.hom ≫ g.map jI.hom ≫
                (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF
                  hF.predeformation.cofibered M).inv) ≫
            (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF
              hF.predeformation.cofibered M).hom) =
      W.1.iso.hom ≫ g.map jI.hom
    simp
  · exact TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 _) hiI0

/-- Exactness at `T𝒲` for the boundary map read as a map of sets: in the row
`Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢` of the six-term sequence of `𝒲 = ℋ ×_ℱ 𝒢`, the kernel of the pair of
the two projections is the image of the boundary map on the infinitesimal automorphisms of
`x'₀ = f(y'₀)`, taken relative to the splitting `e` of `k ⟶ k[M]`. -/
public theorem exact_boundaryFun_tangentProjPair
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    (hy₀ : (f ⋙ pF).obj y₀ = residueFieldObject.{u, v, w} Λ k)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (e : (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M ⟶ (f ⋙ pF).obj y₀)
    (hsplit : (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom ≫ e =
      𝟙 ((f ⋙ pF).obj y₀)) :
    Function.Exact
      (fun α : infinitesimalAutomorphismsAlongSplitPair
          (x₀ := (⟨f.obj y₀, rfl⟩ : pF.Fiber ((f ⋙ pF).obj y₀)))
          (xε := PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
          hF.predeformation.cofibered
          (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom e hsplit
          (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
          (PF.inclusion_cocartesian _).toIsHomLift =>
        boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
          (tangentConditionS2.{u, v, w}
            (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) M α.1)
      (tangentProjPair.{u, v, w} pF f g hH hG hF M) := by
  intro t
  constructor
  · intro ht
    obtain ⟨W, hW⟩ := tangentClassAt_surjective.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M t
    subst hW
    obtain ⟨α, hα⟩ := exists_aut_boundaryObject_tangentClassAt_eq.{u, v, w}
      pF f g hH hG hF hzy hcmp PH PG PF M W ht
    have hthin : Quiver.IsThin (pF.Fiber ((f ⋙ pF).obj y₀)) := by
      rw [hy₀]
      exact isThin_specialFiber.{u, v, w} hF.predeformation
    refine ⟨⟨α, ?_⟩, hα⟩
    rw [infinitesimalAutomorphismsAlongSplitPair_eq_top_of_isThin
      (x₀ := (⟨f.obj y₀, rfl⟩ : pF.Fiber ((f ⋙ pF).obj y₀)))
      (xε := PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
      hF.predeformation.cofibered
      (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M).hom e hsplit
      (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))
      (PF.inclusion_cocartesian _).toIsHomLift hthin]
    exact Subgroup.mem_top α
  · rintro ⟨α, rfl⟩
    exact tangentProjPair_boundaryFun_eq_zero.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M α.1

end BoundaryKernel

end Deformation

end

