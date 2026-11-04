module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.Fibre
public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Pointwise
public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Legs
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist

/-!
# The two comparison maps on twists agree as morphisms

`StacksFrontier/AlgebraicGeometry/ProjThetaCompare/Fibre.lean` identifies the two constructions of
Tag 01MY's comparison map `θ n` **on sections, pointwise**: the one indexed by the domain of
definition `U(ψ) ⊆ Proj ℬ`
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`) and the one indexed by
`AlgebraicGeometry.Proj.map ψ` (`Stacks.ProjTwistComparison.twistMap`). This file lifts that
identification to an **equality of morphisms**.

## The route

An equality of morphisms *out of an inverse image* cannot be read on sections, the inverse image
being a sheafification of a tensor product. The equality is therefore stated and proved on the
other side of the pullback--pushforward adjunction, where
`StacksFrontier/AlgebraicGeometry/ProjTwistCocycle/Transpose.lean` has already computed the
transpose of the `U(ψ)`-indexed comparison: for a section `p` of the inclusion of the domain of
definition, `Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose` is that transpose, and
`…ProjTwistCocycle.twistTranspose_app_val` evaluates it on a section at a point as a single
application of Tag 01MY's fibre comparison. The transpose of the `Proj.map`-indexed comparison is
`Stacks.ProjTwistComparison.pushforwardTwistMap`, whose sections are
`Stacks.ProjTwistComparison.sectionsMap`, likewise a single application of a fibre comparison.
So the equality of the two transposes is pointwise exactly
`Stacks.AlgebraicGeometry.ProjThetaCompare.twistFibreMap_apply_eq`, and nothing else is needed.

Both transposes are morphisms into a direct image, but along two morphisms of schemes which are
only propositionally equal — `p ≫ mapHom 𝒜 ℬ ψ` and `AlgebraicGeometry.Proj.map ψ` — so the
congruence isomorphism `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` appears in the
statement. It is a presheaf restriction along an equality of opens, hence a reindexing of a
family of homogeneous fractions, and contributes nothing to the pointwise identity.

## Main results

* `Stacks.AlgebraicGeometry.ProjThetaCompare.projMap_eq_of_section`: a section of the inclusion
  of the domain of definition identifies the transition morphism with `AlgebraicGeometry.Proj.map`.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.twistTranspose_eq_pushforwardTwistMap`: **the two
  `θ`'s have the same adjoint transpose**, for an arbitrary homomorphism of nonnegatively graded
  rings whose domain of definition admits a section of its inclusion, and every `n : ℤ`.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.transpose_projInclusionTwistIso_eq`: the same at the
  restriction maps of a quasi-coherent graded algebra — the transpose of Tag 01NO's twist
  isomorphism is `Stacks.ProjTwistComparison.pushforwardTwistMap`.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.pushNested_eq_pushforwardTwistMap`: **Tag 01NO's
  pushed-forward twist comparison is the direct image of
  `Stacks.ProjTwistComparison.pushforwardTwistMap`**, followed by the congruence isomorphism for
  the chart factorization. This is the form the chart-refinement law consumes.

## What is not proved here

No clause of any tag is claimed: an identification of two constructions of one comparison map is
not a labelled assertion of the source.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCocycle
open Stacks.AlgebraicGeometry.PushforwardCocycle
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjThetaCompare

attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### The transition morphism of a graded homomorphism with a section -/

section Graded

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **A section of the inclusion of the domain of definition makes the domain everything.** -/
public theorem mapDomain_eq_top_of_section (ψ : 𝒜 →+*ᵍ ℬ)
    (p : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ ψ).toScheme)
    (hpi : p ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ)) :
    mapDomain 𝒜 ℬ ψ = ⊤ :=
  eq_top_iff.mpr fun y _ => mem_mapDomain_of_section 𝒜 ℬ ψ p hpi y

/-- **A section of the inclusion of the domain of definition identifies the transition morphism
with `AlgebraicGeometry.Proj.map`.** The section is unique, the inclusion of an open being a
monomorphism, so the transition morphism is
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`, and that is `Proj.map` by
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`. -/
public theorem projMap_eq_of_section (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (p : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ ψ).toScheme)
    {g : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜} (hg : p ≫ mapHom 𝒜 ℬ ψ = g)
    (hpi : p ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ)) :
    AlgebraicGeometry.Proj.map ψ hψ = g := by
  have hdom : mapDomain 𝒜 ℬ ψ = ⊤ := mapDomain_eq_top_of_section 𝒜 ℬ ψ p hpi
  have hp : p = (Scheme.topIso _).inv ≫
      ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom := by
    refine (cancel_mono (mapDomain 𝒜 ℬ ψ).ι).mp ?_
    exact hpi.trans (topIso_inv_isoOfEq_hom_ι 𝒜 ℬ ψ hdom).symm
  refine Eq.trans (mapHomOfTop_eq_map 𝒜 ℬ ψ hψ hdom).symm ?_
  refine Eq.trans ?_ hg
  rw [hp, mapHomOfTop, Category.assoc]

end Graded

/-! ### The two transposes agree -/

section Transpose

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The two constructions of Tag 01MY's comparison map on the `n`-th twist have the same adjoint
transpose.**

The left-hand side is the transpose of
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, the comparison indexed by the domain of
definition, computed by
`Stacks.AlgebraicGeometry.ProjTwistCocycle.twistTranspose`; the right-hand side is
`Stacks.ProjTwistComparison.pushforwardTwistMap`, the explicit transpose of the comparison indexed
by `AlgebraicGeometry.Proj.map ψ`, carried along the identification of the two transition
morphisms.

Checked on a section at a point, where both sides are one application of Tag 01MY's fibre
comparison and the two agree by
`Stacks.AlgebraicGeometry.ProjThetaCompare.twistFibreMap_apply_eq`. -/
public theorem twistTranspose_eq_pushforwardTwistMap (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) (n : ℤ)
    (p : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ ψ).toScheme)
    {g : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜} (hg : p ≫ mapHom 𝒜 ℬ ψ = g)
    (hpi : p ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ))
    (hgm : AlgebraicGeometry.Proj.map ψ hψ = g) :
    twistTranspose p (mapHom 𝒜 ℬ ψ) (mapDomain 𝒜 ℬ ψ).ι g hg hpi
        (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ ψ n)
      = Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n ≫
        (Scheme.Modules.pushforwardCongr hgm).hom.app (twistingSheaf ℬ n) := by
  refine hom_ext_val_app fun T a => Subtype.ext (funext fun y => ?_)
  have hm := mem_mapDomain_of_section 𝒜 ℬ ψ p hpi y.1
  have hbp0 : basePoint 𝒜 ℬ ψ ⟨y.1, hm⟩ = g.base y.1 :=
    basePoint_of_section 𝒜 ℬ ψ p g hg hpi y.1 hm
  have hbp : basePoint 𝒜 ℬ ψ ⟨y.1, hm⟩ ∈ T := hbp0 ▸ y.2
  have h2 : ProjectiveSpectrum.comapFun ψ hψ y.1 ∈ T :=
    (basePoint_eq_comapFun 𝒜 ℬ ψ hψ ⟨y.1, hm⟩) ▸ hbp
  refine Eq.trans (twistTranspose_app_val 𝒜 ℬ ψ p g hg hpi n T a y hm hbp) ?_
  refine Eq.trans (twistFibreMap_apply_eq 𝒜 ℬ ψ hψ ⟨y.1, hm⟩ a.1 hbp h2) ?_
  rfl

end Transpose

/-! ### The instance: the restriction maps of a quasi-coherent graded algebra -/

section Instance

variable {S : Scheme.{u}}

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for the restriction map of a
quasi-coherent graded algebra along an inclusion of affine opens of the base. -/
public theorem irrelevant_le_map_res (A : SheafGradedAlgebra S) (U V : S.Opens) (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (A.grading U)₊ ≤ (A.grading V)₊.map (A.res hUV) :=
  Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens
    A.toGradedAlgebra (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) hUV

/-- **The transition morphism of the charts is `AlgebraicGeometry.Proj.map` of the restriction
map.** -/
public theorem projMap_res_eq_projInclusionMap (A : SheafGradedAlgebra S) (U V : S.Opens)
    (hUV : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    AlgebraicGeometry.Proj.map (A.res hUV) (irrelevant_le_map_res A U V hUV hU hV) =
      projInclusionMap A U V hUV hU hV :=
  projMap_eq_of_section (A.grading V) (A.grading U) (A.res hUV)
    (irrelevant_le_map_res A U V hUV hU hV) (projInclusionTopSection A U V hUV hU hV)
    (ProjInclusionTwist.projInclusionTopSection_comp_mapHom A U V hUV hU hV)
    (projInclusionTopSection_ι A U V hUV hU hV)

/-- **The transpose of Tag 01NO's twist isomorphism is
`Stacks.ProjTwistComparison.pushforwardTwistMap`**, carried along the identification of the two
spellings of the transition morphism of the charts.

`Stacks.AlgebraicGeometry.ProjTwistCocycle.transpose_projInclusionTwistIso` computes the transpose
as `twistTranspose`, and
`Stacks.AlgebraicGeometry.ProjThetaCompare.twistTranspose_eq_pushforwardTwistMap` identifies that
with the explicit transpose of the `Proj.map`-indexed comparison. -/
public theorem transpose_projInclusionTwistIso_eq (A : SheafGradedAlgebra S) (U V : S.Opens)
    (hUV : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    transpose (projInclusionMap A U V hUV hU hV) (twistingSheaf (A.grading V) n)
        (ProjInclusionTwist.projInclusionTwistIso A U V hUV hU hV n).hom
      = Stacks.ProjTwistComparison.pushforwardTwistMap (A.res hUV)
            (irrelevant_le_map_res A U V hUV hU hV) n ≫
        (Scheme.Modules.pushforwardCongr
            (projMap_res_eq_projInclusionMap A U V hUV hU hV)).hom.app
          (twistingSheaf (A.grading U) n) :=
  (transpose_projInclusionTwistIso A U V hUV hU hV n).trans
    (twistTranspose_eq_pushforwardTwistMap (A.grading V) (A.grading U) (A.res hUV)
      (irrelevant_le_map_res A U V hUV hU hV) n (projInclusionTopSection A U V hUV hU hV)
      (ProjInclusionTwist.projInclusionTopSection_comp_mapHom A U V hUV hU hV)
      (projInclusionTopSection_ι A U V hUV hU hV)
      (projMap_res_eq_projInclusionMap A U V hUV hU hV))

end Instance

end Stacks.AlgebraicGeometry.ProjThetaCompare

end
