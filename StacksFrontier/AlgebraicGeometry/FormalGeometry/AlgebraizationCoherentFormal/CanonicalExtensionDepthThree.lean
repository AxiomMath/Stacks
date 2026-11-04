module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.RegularSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksCore.Tactic.StacksAttribute

/-!
# Canonical extension of a coherent formal module of depth three along the distance function

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, its closed subschemes `Y = V(I)` and `Z = V(𝔞)`, and the open complement
`U = X ∖ Z`.  Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`.  [Stacks, Tag 0EJI] asserts that
`(ℱₙ)` extends canonically to `X` in the sense of [Stacks, Tag 0EIP] as soon as

1. `A` has a dualizing complex and `cd(A, I) = 1`, and
2. `(ℱₙ)` is pro-isomorphic to an inverse system `(ℱ''ₙ)` of coherent `𝒪_U`-modules with
   `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` for every `y ∈ U ∩ Y`.

The route is the Mittag-Leffler criterion
`Stacks.Algebraization.canonicallyExtends_of_finite_limit_images` of [Stacks, Tag 0EHH], which
produces the canonical extension from three conditions on
`M = limₙ H⁰(U, ℱₙ)`: (a) the inverse system `(H⁰(U, ℱₙ))` has Mittag-Leffler, (b) the limit
topology on `M` is its `I`-adic topology, and (c) every projection `M → H⁰(U, ℱₙ)` has finite
image.

What is proved here is condition (c); the tag itself is
`Stacks.Algebraization.canonicallyExtends_of_cd_one_of_proIso_depthThree` in
`CanonicalExtensionCdOneDepthThree.lean`, which supplies (a) and (b) as well.  A
pro-isomorphism of inverse systems of `𝒪_U`-modules becomes, after applying global sections,
a pro-isomorphism of inverse systems of `A`-modules; the composite `ψₙ ∘ φ_{βₙ}` of its two
structure maps is a transition map of `(H⁰(U, ℱₙ))`, so the image of the limit projection at
`n` — which factors through every transition map into level `n` — is contained in the image of
`H⁰(U, ℱ''_{βₙ})`.  That image is finite, and a submodule of a finite module over a Noetherian
ring is finite.  This is `Stacks.Algebraization.finite_range_limitProjection_of_proIso`.

## Main definitions

* `Stacks.Algebraization.depthOfStalkOnOpen` — the depth of the stalk of an `𝒪_U`-module at a
  point of `U`, over the local ring there.
* `Stacks.Algebraization.proIsoComp` — a pro-isomorphism of `ℕᵒᵖ`-indexed systems pushed forward
  along a functor.

## Main results

* `Stacks.Algebraization.finite_range_limitProjection_of_proIso` — condition (c) of
  [Stacks, Tag 0EHH] for a system pro-isomorphic to one with finite global sections.

## Implementation notes

Pro-isomorphism is `InverseSequence.ProIso`, the explicit up-to-refinement description of an
isomorphism of pro-objects: reindexings `α, β ≥ id` together with maps `φₘ : Xₐₘ ⟶ Yₘ` and
`ψₘ : Y_{βₘ} ⟶ Xₘ`, natural in `m`, whose two composites are transition maps.  That is the form
in which the notion is available over an arbitrary category, and it is what makes the
factorisation of a transition map through the other system usable.

`Stacks.Algebraization.globalSectionsSystem S F` is by construction
`F.obj ⋙ openSectionsFunctor S`, so the functor applied to the structure maps of the
pro-isomorphism lands in the very system whose limit projections condition (c) is about; no
comparison is needed.

The depth of a stalk is taken over the local ring of `U` at the point, with the module
structure on the stalk of the sheaf of modules supplied by the instance
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`, as in
`Stacks.Algebraization.depth_stalk_depthTwoImprovedSystem` for [Stacks, Tag 0EJF].  Depth and
the distance function both take values in `ℕ∞`, so the source's inequality is read there; the
infinite values are retained, and at a point of a connected component of `Y` missing `Z` the
distance is `∞` and the inequality holds, which is what the source intends.

A point of `U ∩ Y` is a point `y` of `U` together with a point `z` of `Y` with the same image
in `X`, the idiom of `Stacks.Algebraization.SatisfiesDepthInequalities`; `δ^Y_Z` is evaluated at
`z` and the depth at `y`.  Both `U ⟶ X` and `Y ⟶ X` are monomorphisms, so neither point is
extra data.

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP), the conclusion.
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH), the criterion used.
* [Stacks Project, Tag 0EH7](https://stacks.math.columbia.edu/tag/0EH7)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The depth of the stalk of an `𝒪_U`-module at a point of `U`, taken over the local ring of
`U` at that point and its maximal ideal. -/
public noncomputable def depthOfStalkOnOpen (N : S.U.toScheme.Modules) (y : S.U.toScheme) :
    ℕ∞ :=
  letI : Module (S.U.toScheme.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.U.toScheme.presheaf) N.val y
  Module.depth (S.U.toScheme.presheaf.stalk y)
    (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk y))
    (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf y)

/-- A pro-isomorphism of inverse systems indexed by `ℕᵒᵖ` is carried by any functor to a
pro-isomorphism of the composed systems: the reindexings are unchanged and the structure maps
are the images of the given ones. -/
public def proIsoComp {C : Type*} [Category C] {D : Type*} [Category D]
    {X Y : ℕᵒᵖ ⥤ C} (e : InverseSequence.ProIso X Y) (H : C ⥤ D) :
    InverseSequence.ProIso (X ⋙ H) (Y ⋙ H) where
  α := e.α
  β := e.β
  αmono := e.αmono
  βmono := e.βmono
  αle := e.αle
  βle := e.βle
  φ m := H.map (e.φ m)
  ψ m := H.map (e.ψ m)
  φnat h := by
    change H.map (InverseSequence.tr X (e.αmono h)) ≫ H.map (e.φ _) =
      H.map (e.φ _) ≫ H.map (InverseSequence.tr Y h)
    rw [← H.map_comp, ← H.map_comp, e.φnat h]
  ψnat h := by
    change H.map (InverseSequence.tr Y (e.βmono h)) ≫ H.map (e.ψ _) =
      H.map (e.ψ _) ≫ H.map (InverseSequence.tr X h)
    rw [← H.map_comp, ← H.map_comp, e.ψnat h]
  ψφ m := by
    change H.map (e.φ (e.β m)) ≫ H.map (e.ψ m) = H.map (InverseSequence.tr X _)
    rw [← H.map_comp, e.ψφ m]
  φψ m := by
    change H.map (e.ψ (e.α m)) ≫ H.map (e.φ m) = H.map (InverseSequence.tr Y _)
    rw [← H.map_comp, e.φψ m]

variable (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **Condition (c) of [Stacks, Tag 0EHH] from a pro-isomorphism.**  If the diagram of `(ℱₙ)` is
pro-isomorphic to an inverse system `(ℱ''ₙ)` of `𝒪_U`-modules whose global sections are finite
`A`-modules, then every projection `limₙ H⁰(U, ℱₙ) → H⁰(U, ℱₙ)` has finite image.

The transition map of `(H⁰(U, ℱₙ))` from level `α(βₙ)` to level `n` factors through
`H⁰(U, ℱ''_{βₙ})`, and the limit projection at `n` factors through that transition map. -/
public theorem finite_range_limitProjection_of_proIso
    (G : ℕᵒᵖ ⥤ S.U.toScheme.Modules) (e : InverseSequence.ProIso F.obj G)
    (hfin : ∀ n : ℕ, Module.Finite S.A ((openSectionsFunctor S).obj (G.obj (op n))))
    (n : ℕ) :
    Module.Finite S.A
      (LinearMap.range (limit.π (globalSectionsSystem S F) (op n)).hom) := by
  have e' : InverseSequence.ProIso (globalSectionsSystem S F)
      (G ⋙ openSectionsFunctor S) := proIsoComp e (openSectionsFunctor S)
  have hk : n ≤ e'.α (e'.β n) := (e'.βle n).trans (e'.αle (e'.β n))
  have hψφ : e'.φ (e'.β n) ≫ e'.ψ n =
      (globalSectionsSystem S F).map (homOfLE hk).op := e'.ψφ n
  have hsplit : limit.π (globalSectionsSystem S F) (op n) =
      (limit.π (globalSectionsSystem S F) (op (e'.α (e'.β n))) ≫ e'.φ (e'.β n)) ≫ e'.ψ n := by
    rw [Category.assoc, hψφ]
    exact (limit.w (globalSectionsSystem S F) (homOfLE hk).op).symm
  have hle : LinearMap.range (limit.π (globalSectionsSystem S F) (op n)).hom ≤
      LinearMap.range (e'.ψ n).hom := by
    rw [hsplit]
    simp only [ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  have : Module.Finite S.A ((G ⋙ openSectionsFunctor S).obj (op (e'.β n))) := hfin (e'.β n)
  have : Module.Finite S.A (LinearMap.range (e'.ψ n).hom) :=
    Module.Finite.of_surjective (e'.ψ n).hom.rangeRestrict
      (LinearMap.surjective_rangeRestrict _)
  refine Module.Finite.iff_fg.mpr ?_
  have hmap := (IsNoetherian.noetherian
      ((LinearMap.range (limit.π (globalSectionsSystem S F) (op n)).hom).comap
        (LinearMap.range (e'.ψ n).hom).subtype)).map
      (LinearMap.range (e'.ψ n).hom).subtype
  rwa [Submodule.map_comap_subtype, inf_of_le_right hle] at hmap

end Stacks.Algebraization

end
