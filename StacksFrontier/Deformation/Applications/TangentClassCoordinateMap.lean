module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact

/-!
# Classes of objects of a fibre under a map of coordinate modules

The tangent module `T𝓕(M)` of a deformation category is a value of the canonical linear lift of
the associated square-zero functor, so it is functorial in the coordinate module `M`: a map
`φ : M ⟶ N` of finite-dimensional `k`-vector spaces induces a `k`-linear map
`T𝓕(M) ⟶ T𝓕(N)`. This file names that map and computes it on classes of objects of a fibre.

The computation is the missing handle on the vector-space structure of
[Stacks Project, Tag 06IH]. That structure is produced by the product conditions of
[Stacks Project, Tag 06I6], so neither the addition nor the scalar action of `T𝓕(M)` is given by
a formula on classes: `Deformation.tangentClassAt` ships with
`Deformation.tangentClassAt_eq_iff` and `Deformation.tangentClassAt_surjective` and nothing about
sums. What the lift *does* provide is additivity in the map of coordinate modules, and
`Deformation.exists_linearFunctorLift_sum` says that this is enough: a sum of two elements of
`T𝓕(M)` is the image of a single element of `T𝓕(M × M)` under `p₁ + p₂`. Combining the two gives
`Deformation.tangentClassAt_add_of_isHomLift`, which computes a *sum* of classes of objects of
the fibre over `k[M]` from one object of the fibre over `k[M × M]` and three pushforwards of it.

## Main definitions

* `Deformation.tangentModuleMapAt`: the `k`-linear map `T𝓕(M) ⟶ T𝓕(N)` induced by a map
  `M ⟶ N` of coordinate modules.

## Main results

* `Deformation.tangentModuleMapAt_tangentClassAt`: the induced map sends the class of an object
  of the fibre over `k[M]` to the class of any pushforward of it along `k[M] ⟶ k[N]`. This is
  `Deformation.map_classOf` transported across the equality of carriers
  `Deformation.associatedTangentLift_carrier`.
* `Deformation.tangentModuleMapAt_add`: the induced map is additive in the map of coordinate
  modules, because the lift is an additive functor. With
  `Deformation.tangentModuleMapAt_id`, `Deformation.tangentModuleMapAt_zero` and
  `Deformation.tangentModuleMapAt_comp` these are the functoriality the rest of the file uses.
* `Deformation.tangentClassAt_add_of_isHomLift`: **a sum of two classes of objects of the fibre
  over `k[M]`, computed from the fibre over `k[M × M]`.** If one object of the fibre over `k[M]`
  is a pushforward of `z` along `k[φ]`, a second along `k[ψ]` and a third along `k[φ + ψ]`, then
  the class of the third is the sum of the classes of the first two.
* `Deformation.tangentClassAt_smul_of_isHomLift`: the scalar counterpart — the class of a
  pushforward of `x` along `k[c • 𝟙 M]` is `c` times the class of `x`. This one needs no larger
  coordinate module, so it is the cheaper half of the `k`-linearity of a map out of the tangent
  module.
* `Deformation.exists_tangentModuleMapAt_eq_add`: **every** sum of two tangent vectors arises
  that way — a sum in `T𝓕(N)` is the image under `p₁ + p₂` of a single element of `T𝓕(W)`
  for `N` a direct summand of `W` twice over. So the previous lemma is not only correct but
  exhaustive: nothing abstract stands between it and additivity of a map out of the tangent
  module, only the geometric identification of the three pushforwards.

## Implementation notes

The carrier of `T𝓕(M)` is *equal* to the set of isomorphism classes over `k[M]` rather than
isomorphic to it — `Deformation.associatedTangentLift_carrier`, which is `congrArg` applied to
the `forget_comp` field of the lift — so every statement here is a transport along an equality of
types. `Deformation.moduleFunctor_map_cast` is the compatibility of that transport with the
action of the two functors on morphisms, and it is what carries a computation performed with
`Deformation.isomorphismClasses` over to the module-valued lift.

## References

* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 07W5](https://stacks.math.columbia.edu/tag/07W5)
-/

@[expose] public section

namespace Deformation

section CoordinateMap

open CategoryTheory CategoryTheory.Functor

universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
  (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p)

/-- **The `k`-linear map on tangent modules induced by a map of coordinate modules.** The tangent
module is the value at `M` of the canonical linear lift of the associated square-zero functor, so
a map `φ : M ⟶ N` of finite-dimensional `k`-vector spaces induces a `k`-linear map
`T𝓕(M) ⟶ T𝓕(N)`. At `φ = a • 𝟙` this is the scalar action of
[Stacks Project, Tag 06IH]. -/
noncomputable def tangentModuleMapAt {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N) :
    ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) →ₗ[k] ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 N) :=
  ((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕)).functor.map φ).hom

/-- The induced map is the action of the linear lift on the morphism. -/
theorem tangentModuleMapAt_eq {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 φ =
      ((associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
        (tangentConditionS2.{u, v, w} h𝓕)).functor.map φ).hom := rfl

/-- **The induced map sends the class of an object of the fibre to the class of a pushforward.**
For `φ : M ⟶ N`, an object `x` of the fibre over `k[M]`, an object `y` of the fibre over `k[N]`
and an arrow `a : x ⟶ y` lying over `k[φ]`, the class of `y` is the image of the class of `x`.

This is `Deformation.map_classOf` — which pins the action of the functor of isomorphism classes
on a base morphism, independently of any choice of pushforwards — transported along the equality
of carriers `Deformation.associatedTangentLift_carrier`. -/
theorem tangentModuleMapAt_tangentClassAt {M N : FGModuleCat.{max v w} k} (φ : M ⟶ N)
    (x : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj N))
    (a : x.1 ⟶ y.1)
    (ha : 𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ) a) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 φ (tangentClassAt.{u, v, w} 𝓕 h𝓕 M x) =
      tangentClassAt.{u, v, w} 𝓕 h𝓕 N y := by
  rw [tangentClassAt_eq, tangentClassAt_eq,
    ← map_classOf 𝓕 h𝓕.predeformation.cofibered
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ) x y a]
  refine (Equiv.cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
    (tangentConditionS2.{u, v, w} h𝓕) N)).injective ?_
  rw [Equiv.cast_apply, Equiv.cast_apply, cast_symm_cancel, tangentModuleMapAt_eq]
  have hmc := moduleFunctor_map_cast k
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕)).functor
    (squareZeroExtensionArtinian.{u, w, max v w} Λ k ⋙
      isomorphismClasses 𝓕 h𝓕.predeformation.cofibered)
    (associatedTangentSpaceModuleStructure.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕)).forget_comp φ
    (cast (associatedTangentLift_carrier.{u, v, w} 𝓕 h𝓕.predeformation
      (tangentConditionS2.{u, v, w} h𝓕) M).symm (classOf 𝓕 h𝓕.predeformation.cofibered x))
  rwa [cast_symm_cancel] at hmc

/-- **The induced map is additive in the map of coordinate modules**, because the canonical
linear lift is an additive functor. This is the half of the vector-space structure of
[Stacks Project, Tag 06IH] that *is* given by a formula. -/
theorem tangentModuleMapAt_add {M N : FGModuleCat.{max v w} k} (φ ψ : M ⟶ N)
    (t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (φ + ψ) t =
      tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 φ t + tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 ψ t := by
  simp only [tangentModuleMapAt_eq, CategoryTheory.Functor.map_add]
  rfl

/-- The identity of a coordinate module induces the identity of the tangent module. -/
theorem tangentModuleMapAt_id {M : FGModuleCat.{max v w} k}
    (t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (𝟙 M) t = t := by
  rw [tangentModuleMapAt_eq, CategoryTheory.Functor.map_id]
  rfl

/-- The zero map of coordinate modules induces the zero map of tangent modules. -/
theorem tangentModuleMapAt_zero {M N : FGModuleCat.{max v w} k}
    (t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (0 : M ⟶ N) t = 0 := by
  rw [tangentModuleMapAt_eq, CategoryTheory.Functor.map_zero]
  rfl

/-- The induced maps compose. -/
theorem tangentModuleMapAt_comp {M N O : FGModuleCat.{max v w} k} (φ : M ⟶ N) (ψ : N ⟶ O)
    (t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (φ ≫ ψ) t =
      tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 ψ (tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 φ t) := by
  simp only [tangentModuleMapAt_eq, CategoryTheory.Functor.map_comp]
  rfl

/-- **The scalar action of [Stacks Project, Tag 06IH] is the induced map of the scaling of the
coordinate module.** The canonical linear lift is a `k`-linear functor, so it sends `c • 𝟙 M` to
`c • 𝟙`. At the rank-one module this is
`Deformation.associatedTangentSpace_smul_eq_map`, read on the lift rather than on the
set-valued functor. -/
theorem tangentModuleMapAt_smul {M : FGModuleCat.{max v w} k} (c : k)
    (t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M)) :
    tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (c • 𝟙 M) t = c • t := by
  rw [tangentModuleMapAt_eq, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The scalar multiple of a class of an object of a fibre.** If `y` is a pushforward of `x`
along `k[c • 𝟙 M]`, then the class of `y` is `c` times the class of `x`.

This is the scalar counterpart of `Deformation.tangentClassAt_add_of_isHomLift`, and it is
cheaper: a scaling of the coordinate module is a single endomorphism of `M`, so no larger
coordinate module and no second pushforward is needed. -/
theorem tangentClassAt_smul_of_isHomLift {M : FGModuleCat.{max v w} k} (c : k)
    (x y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (a : x.1 ⟶ y.1)
    (ha : 𝓕.p.IsHomLift
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (c • 𝟙 M)) a) :
    tangentClassAt.{u, v, w} 𝓕 h𝓕 M y = c • tangentClassAt.{u, v, w} 𝓕 h𝓕 M x := by
  rw [← tangentModuleMapAt_tangentClassAt.{u, v, w} 𝓕 h𝓕 (c • 𝟙 M) x y a ha]
  exact tangentModuleMapAt_smul.{u, v, w} 𝓕 h𝓕 c _

/-- **A sum of two tangent vectors is realized over a doubled coordinate module.** If `N` sits
inside `W` as a direct summand twice over, by sections `i₁`, `i₂` of projections `p₁`, `p₂`, then
for any two elements `s`, `t` of `T𝓕(N)` there is a single element `ζ` of `T𝓕(W)` whose images
under `p₁`, `p₂` and `p₁ + p₂` are `s`, `t` and `s + t`.

This is `Deformation.exists_linearFunctorLift_sum` for the canonical linear lift of the
associated square-zero functor, proved here directly in the tangent module: `ζ` is
`i₁ s + i₂ t`, and each conclusion is linearity of the induced maps together with the four
splitting relations. Combined with `Deformation.tangentModuleMapAt_tangentClassAt` it says that
the sum of any two classes of objects of the fibre over `k[N]` is computed by
`Deformation.tangentClassAt_add_of_isHomLift`, so that lemma is not only correct but
exhaustive.

The four splitting relations are hypotheses rather than a biproduct decomposition of `W`, for
the reason recorded in
`StacksFrontier/Deformation/LiftsOfObjects/Action/LinearLiftSum.lean`: at the concrete rank-two
module they hold by `rfl`. -/
theorem exists_tangentModuleMapAt_eq_add {N W : FGModuleCat.{max v w} k}
    (p₁ p₂ : W ⟶ N) (i₁ i₂ : N ⟶ W)
    (h₁₁ : i₁ ≫ p₁ = 𝟙 N) (h₂₁ : i₂ ≫ p₁ = 0)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₂ : i₂ ≫ p₂ = 𝟙 N)
    (s t : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 N)) :
    ∃ ζ : ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 W),
      tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 p₁ ζ = s ∧
        tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 p₂ ζ = t ∧
          tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 (p₁ + p₂) ζ = s + t := by
  -- the image of `ζ` under a projection, computed by the splitting relations
  have hproj : ∀ (q : W ⟶ N) (α β : N ⟶ N), i₁ ≫ q = α → i₂ ≫ q = β →
      tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 q
          (tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 i₁ s + tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 i₂ t) =
        tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 α s + tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 β t := by
    intro q α β hα hβ
    rw [_root_.map_add, ← tangentModuleMapAt_comp, ← tangentModuleMapAt_comp, hα, hβ]
  refine ⟨tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 i₁ s + tangentModuleMapAt.{u, v, w} 𝓕 h𝓕 i₂ t,
    ?_, ?_, ?_⟩
  · rw [hproj p₁ (𝟙 N) 0 h₁₁ h₂₁, tangentModuleMapAt_id, tangentModuleMapAt_zero, add_zero]
  · rw [hproj p₂ 0 (𝟙 N) h₁₂ h₂₂, tangentModuleMapAt_id, tangentModuleMapAt_zero, zero_add]
  · rw [hproj (p₁ + p₂) (𝟙 N) (𝟙 N)
      (by rw [Preadditive.comp_add, h₁₁, h₁₂, add_zero])
      (by rw [Preadditive.comp_add, h₂₁, h₂₂, zero_add]),
      tangentModuleMapAt_id, tangentModuleMapAt_id]

/-- **A sum of two classes of objects of a fibre, computed over the doubled coordinate module.**
Let `φ, ψ : M ⟶ N` be maps of coordinate modules, let `z` be an object of the fibre over `k[M]`,
and let `xφ`, `xψ` and `xs` be objects of the fibre over `k[N]` admitting arrows from `z` over
`k[φ]`, over `k[ψ]` and over `k[φ + ψ]` respectively. Then

`cls xs = cls xφ + cls xψ`

in the tangent module `T𝓕(N)`.

This is the only handle the addition of [Stacks Project, Tag 06IH] offers on classes of objects
of a fibre: that addition is produced by the product conditions of [Stacks Project, Tag 06I6] and
has no formula, so a sum of two classes has to be *realized* by a single object over a larger
coordinate module. The case the applications use is `M = N × N` with `φ` and `ψ` the two
projections, where `Deformation.exists_linearFunctorLift_sum` guarantees that every pair of
elements of `T𝓕(N)` arises this way. -/
theorem tangentClassAt_add_of_isHomLift {M N : FGModuleCat.{max v w} k} (φ ψ : M ⟶ N)
    (z : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (xφ xψ xs : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj N))
    (aφ : z.1 ⟶ xφ.1)
    (haφ : 𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map φ) aφ)
    (aψ : z.1 ⟶ xψ.1)
    (haψ : 𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map ψ) aψ)
    (as : z.1 ⟶ xs.1)
    (has : 𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).map (φ + ψ)) as) :
    tangentClassAt.{u, v, w} 𝓕 h𝓕 N xs =
      tangentClassAt.{u, v, w} 𝓕 h𝓕 N xφ + tangentClassAt.{u, v, w} 𝓕 h𝓕 N xψ := by
  rw [← tangentModuleMapAt_tangentClassAt.{u, v, w} 𝓕 h𝓕 φ z xφ aφ haφ,
    ← tangentModuleMapAt_tangentClassAt.{u, v, w} 𝓕 h𝓕 ψ z xψ aψ haψ,
    ← tangentModuleMapAt_tangentClassAt.{u, v, w} 𝓕 h𝓕 (φ + ψ) z xs as has]
  exact tangentModuleMapAt_add.{u, v, w} 𝓕 h𝓕 φ ψ _

end CoordinateMap

end Deformation

end
