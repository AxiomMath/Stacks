module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Local

/-!
# Comparison with Mathlib's functoriality of `Proj`, and transitivity of the transitions

The transition morphisms of `StacksFrontier.AlgebraicGeometry.RelativeProj.Local` are built by
glueing, out of `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`, which is defined for *any*
graded ring homomorphism on its exact domain of definition. Mathlib's
`AlgebraicGeometry.Proj.map` is defined only under the hypothesis `ℬ₊ ≤ 𝒜₊.map ψ`, but comes with
a developed API, in particular `AlgebraicGeometry.Proj.map_comp` and
`AlgebraicGeometry.Proj.map_id`.

This file shows the two agree whenever Mathlib's hypothesis holds, shows that the hypothesis
*does* hold for the restriction maps of a quasi-coherent graded algebra, and reads off
transitivity of the transition morphisms. Transitivity is the second of the two functoriality
laws that Tag 01NP asks for, and is what a functor `S.AffineZariskiSite ⥤ Scheme` with value
`Proj Γ(U, 𝒜)` would need.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.hom_ext_of_mapDomain_eq_top`: two morphisms out of
  `Proj ℬ` agree as soon as they agree on each `D₊(ψ f)`, when `ψ` is everywhere defined.
* `Stacks.AlgebraicGeometry.RelativeProj.irrelevant_le_map_of_isLocalizationAway`: Mathlib's
  hypothesis holds for a graded ring map exhibiting `B` as a localization of `A` away from a
  degree-zero element.
* `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`: the glued morphism agrees with
  `AlgebraicGeometry.Proj.map`.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition_comp` and
  `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.resMap_comp`: **Tag 01NP**, transitivity
  of the transition morphisms.

## Implementation notes

The comparison is proved on the standard affine cover and nowhere touches the structure sheaf:
`Stacks.AlgebraicGeometry.RelativeProj.ι_mapHomOfTop` describes the glued morphism on `D₊(ψ f)`
as `Spec` of `HomogeneousLocalization.Away.map ψ f`, and
`AlgebraicGeometry.Proj.awayι_comp_map` describes Mathlib's morphism there by the *same* ring
map. This sidesteps the obstruction that stopped the bundled `ProjMapData` of Tag 01MY: the
sheaf-level comparison needs the pointwise localization formula of
`AlgebraicGeometry.Proj.comapStructureSheafFun`, which a glued morphism does not provide, whereas
the equality of *scheme* morphisms needs only the local identity.

`transition_comp` carries both the `mapDomain = ⊤` hypotheses and Mathlib's `ℬ₊ ≤ 𝒜₊.map ψ`
hypotheses as explicit arguments rather than deriving the former from the latter. Deriving them
would make the statement shorter but force every caller to produce the proof in exactly the
derived form; as `Prop` arguments they are proof-irrelevant, so an explicit argument costs
nothing and matches whatever the caller has. The final `congr 1` is what absorbs that
irrelevance: `AlgebraicGeometry.Proj.map` takes the hypothesis as an explicit argument whose
*type* changes when the graded ring map is rewritten, so `rw` with
`GradedAlgebra.res_comp` cannot be used directly on the goal.

## References

* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)

## Not done here

The identity law of Tag 01NP is `GradedAlgebra.transition_id` in
`StacksFrontier.AlgebraicGeometry.RelativeProj.Local`; the two together are the functoriality
needed for a functor into `Scheme`, but that functor is not assembled, because the relative
glueing datum it feeds also needs the squares to be cartesian, which is not proved. The
isomorphisms `θ` on the twists `𝒪(n)` of Tags 01NO and 01NP are not constructed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u w w' w''

section Compare

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- Two morphisms out of `Proj ℬ` agree as soon as they agree on each standard open `D₊(ψ f)`
for `f` homogeneous of positive degree, provided those cover `Proj ℬ`. -/
public theorem hom_ext_of_mapDomain_eq_top (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤)
    {Y : Scheme.{u}} (p q : AlgebraicGeometry.Proj ℬ ⟶ Y)
    (H : ∀ (d : ℕ), 0 < d → ∀ f : A, f ∈ 𝒜 d →
      (Proj.basicOpen ℬ (ψ f)).ι ≫ p = (Proj.basicOpen ℬ (ψ f)).ι ≫ q) :
    p = q := by
  have key : (mapDomain 𝒜 ℬ ψ).ι ≫ p = (mapDomain 𝒜 ℬ ψ).ι ≫ q := by
    refine mapDomain_hom_ext 𝒜 ℬ ψ _ _ fun d hd f hf => ?_
    rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι]
    exact H d hd f hf
  rw [← Category.id_comp p, ← Category.id_comp q, ← topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom]
  simp only [Category.assoc, key]

/-- **Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for a localization away from a
degree-zero element.** A homogeneous element of `B` of positive degree is a unit multiple of the
image of a homogeneous element of `A` of the same degree. -/
public theorem irrelevant_le_map_of_isLocalizationAway (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0)
    [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
  have hu : IsUnit (ψ g) := isUnit_of_isLocalizationAway 𝒜 ℬ ψ g halg
  refine irrelevant_le_map_of_mem_span 𝒜 ℬ ψ fun d hd b hb => ?_
  obtain ⟨a, k, ha, hak⟩ := exists_mem_graded_mul_pow 𝒜 ℬ ψ hg halg hb
  have hmem : ψ a ∈ Ideal.span (ψ '' ⋃ n > 0, (𝒜 n : Set A)) :=
    Ideal.subset_span ⟨a, Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, ha⟩⟩, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Bˣ, (v : B) = ψ g ^ k := ⟨(hu.pow k).unit, IsUnit.unit_spec _⟩
  have hb' : ψ a * ((v⁻¹ : Bˣ) : B) = b := by
    rw [hak, ← hv, mul_assoc, Units.mul_inv, mul_one]
  rw [← hb']
  exact Ideal.mul_mem_right _ _ hmem

end Compare

section CompareMathlib

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The glued morphism is Mathlib's.** When `ψ` satisfies Mathlib's hypothesis
`ℬ₊ ≤ 𝒜₊.map ψ`, the morphism obtained by glueing the maps of degree-zero localizations agrees
with `AlgebraicGeometry.Proj.map`.

The `SetLike` carriers are confined to `Type u` here, unlike everywhere else in this
development: `AlgebraicGeometry.Proj.map` itself declares them in the ring's universe, so
stating the equation at independent carrier universes does not elaborate. -/
public theorem mapHomOfTop_eq_map (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    mapHomOfTop 𝒜 ℬ ψ hdom = Proj.map ψ hψ := by
  refine hom_ext_of_mapDomain_eq_top 𝒜 ℬ ψ hdom _ _ fun d hd f hf => ?_
  have hι : (Proj.basicOpen ℬ (ψ f)).ι =
      (Proj.basicOpenIsoSpec ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd).hom ≫
        Proj.awayι ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  have h1 : (Proj.basicOpen ℬ (ψ f)).ι ≫ Proj.map ψ hψ =
      Proj.basicOpenToSpec ℬ (ψ f) ≫ Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
        Proj.awayι 𝒜 f hf hd := by
    rw [hι, Proj.basicOpenIsoSpec_hom, Category.assoc, Proj.awayι_comp_map ψ hψ hd f hf]
  rw [ι_mapHomOfTop 𝒜 ℬ ψ hdom hd hf, h1, mapAwayHom]

end CompareMathlib

namespace GradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for the restriction map of a
quasi-coherent graded algebra along a basic open inclusion of affine opens. -/
public theorem irrelevant_le_map_res (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    HomogeneousIdeal.irrelevant (𝒜.grading (U.basicOpen f)) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading U)).map (𝒜.res (S.basicOpen_le f)) := by
  let := 𝒜.algebra (U := U.basicOpen f) (V := U) (S.basicOpen_le f)
  have := 𝒜.isLocalization U f
  exact irrelevant_le_map_of_isLocalizationAway _ _ _ (𝒜.str_mem U f)
    (𝒜.algebraMap_eq (U := U.basicOpen f) (V := U) (S.basicOpen_le f))

/-- The transition morphism is Mathlib's `AlgebraicGeometry.Proj.map`, whenever Mathlib's
hypothesis is available. -/
public theorem transition_eq_map {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (hdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res h) = ⊤)
    (hi : HomogeneousIdeal.irrelevant (𝒜.grading U) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading V)).map (𝒜.res h)) :
    𝒜.transition h hdom = Proj.map (𝒜.res h) hi :=
  mapHomOfTop_eq_map (𝒜.grading V) (𝒜.grading U) (𝒜.res h) hi hdom

/-- The transition morphism along a basic open inclusion is Mathlib's
`AlgebraicGeometry.Proj.map`. -/
public theorem resMap_eq_map (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    𝒜.resMap U f = Proj.map (𝒜.res (S.basicOpen_le f)) (𝒜.irrelevant_le_map_res U f) :=
  𝒜.transition_eq_map (U := U.basicOpen f) (V := U) (S.basicOpen_le f) _ _

/-- **Tag 01NP.** The transition morphisms compose: the transition for a composite inclusion of
affine opens is the composite of the transitions. -/
public theorem transition_comp {U V W : S.AffineZariskiSite} (hUV : U.toOpens ≤ V.toOpens)
    (hVW : V.toOpens ≤ W.toOpens)
    (hiUV : HomogeneousIdeal.irrelevant (𝒜.grading U) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading V)).map (𝒜.res hUV))
    (hiVW : HomogeneousIdeal.irrelevant (𝒜.grading V) ≤
      (HomogeneousIdeal.irrelevant (𝒜.grading W)).map (𝒜.res hVW))
    (hUVdom : mapDomain (𝒜.grading V) (𝒜.grading U) (𝒜.res hUV) = ⊤)
    (hVWdom : mapDomain (𝒜.grading W) (𝒜.grading V) (𝒜.res hVW) = ⊤)
    (hUWdom : mapDomain (𝒜.grading W) (𝒜.grading U) (𝒜.res (hUV.trans hVW)) = ⊤) :
    𝒜.transition hUV hUVdom ≫ 𝒜.transition hVW hVWdom =
      𝒜.transition (hUV.trans hVW) hUWdom := by
  rw [𝒜.transition_eq_map hUV hUVdom hiUV, 𝒜.transition_eq_map hVW hVWdom hiVW,
    𝒜.transition_eq_map (hUV.trans hVW) hUWdom
      (by rw [𝒜.res_comp hUV hVW]; exact irrelevant_le_map_comp hiVW hiUV),
    ← Proj.map_comp (𝒜.res hVW) (𝒜.res hUV) hiVW hiUV]
  congr 1
  exact (𝒜.res_comp hUV hVW).symm

/-- **Tag 01NP** for basic open inclusions, where no hypothesis is needed. -/
public theorem resMap_comp (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens))
    (g : Γ(S, (U.basicOpen f).toOpens))
    (hUWdom : mapDomain (𝒜.grading U) (𝒜.grading ((U.basicOpen f).basicOpen g))
      (𝒜.res ((S.basicOpen_le g).trans (S.basicOpen_le f))) = ⊤) :
    𝒜.resMap (U.basicOpen f) g ≫ 𝒜.resMap U f =
      𝒜.transition ((S.basicOpen_le g).trans (S.basicOpen_le f)) hUWdom :=
  𝒜.transition_comp (U := (U.basicOpen f).basicOpen g) (V := U.basicOpen f) (W := U)
    (S.basicOpen_le g) (S.basicOpen_le f) (𝒜.irrelevant_le_map_res (U.basicOpen f) g)
    (𝒜.irrelevant_le_map_res U f) _ _ hUWdom

end GradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProj

end
