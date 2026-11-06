module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Stacks 04U0: the finite-type form of fppf locality for algebraic spaces

Let `F` be an fppf sheaf of sets on the big fppf site of a scheme `S` and let `{S_i → S}` be a
covering family of the base. If each restriction `h_{S_i} × F` is an algebraic space *of finite
type over `S_i`*, then `F` is an algebraic space. This is Stacks 04U0. Like Stacks 04SK, it
rests on the bootstrap theorem Stacks 04S6, condition (3).

The point of the finite-type hypothesis is purely set-theoretic, exactly as in the source: it
produces étale atlases of the restrictions whose size is bounded by the size of `S`, so that
their disjoint union is again an object of the site and Stacks 02WQ applies.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_isFiniteType` is Stacks 04U0.

## Implementation notes

The source reduces first to a covering by affines indexed by a set of cardinality at most that
of `S`. That refinement is the common part of the proofs of Stacks 04SK and Stacks 04U0,
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_atlas_size_le`. That lemma picks, over each
point of `S`, an affine open `W` of a member `S_i` through a point above it, so there are at
most `2 ^ size (S)` of them, and asks only for an étale atlas of each restriction
`h_W × F_i` of bounded size. This file supplies that atlas, and this is where the finite-type
hypothesis is spent. The restriction to `W` is a base change of `h_{S_i} × F ⟶ h_{S_i}`, so it
is of finite type over the affine `h_W` and hence quasi-compact. Stacks 03H6 then gives it an
*affine* surjective étale atlas `U`. The composite `U ⟶ W ⟶ S_i ⟶ S` is locally of finite type
(Stacks 03XG; `S_i ⟶ S` is locally of finite presentation because the family is an fppf
covering) with `U` quasi-compact, so Stacks 04T7 bounds `size (U)` by `size (S)`.

The appeal to the bootstrap theorem Stacks 04S6, condition (3), happens inside that refinement
lemma.

## References

* [Stacks Project, Tag 04U0](https://stacks.math.columbia.edu/tag/04U0)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_CoveringRestrictionFiniteType :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_CoveringRestrictionFiniteType
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Coproducts of bounded families in the site, with their universal property -/

/-- **A family of objects of the big fppf site over `S`, indexed by a type of the working
universe and of uniformly bounded size, has a coproduct inside the site.**

The underlying scheme is the disjoint union of the underlying schemes of the members, which is
again of size below the cutoff by `AlgebraicGeometry.schemeSize_coproduct_le`, and the structure
morphism is assembled from those of the members. The universal property is inherited from the
disjoint union of schemes because the inclusion of the site into schemes is fully faithful and a
morphism out of the disjoint union commutes with the structure morphisms as soon as its
restrictions do.

`AlgebraicGeometry.BigFppfOver.exists_coproduct_of_size_le` presents the same object by its
disjoint open cover; this is the presentation by the universal property, which is what
`AlgebraicGeometry.isAlgebraicSpace_coproduct` and
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering` consume. -/
theorem BigFppfOver.exists_isColimit_cofan_of_size_le (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {K : Type u} (R : K → BigFppfOver B S hS) {μ : Cardinal.{u}}
    (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hsize : ∀ k, ((BigFppfOver.toScheme B S hS).obj (R k)).size ≤ μ) :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k, R k ⟶ Z), Nonempty (IsColimit (Cofan.mk Z c)) :=
  BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS R
    ((schemeSize_coproduct_le _ μ hℵ hK hsize).trans_lt hμ)

/-! ### Stacks 04U0 -/

/-- The members of a covering family of the base are locally of finite presentation over the
base: an fppf covering family is flat and locally of finite presentation by definition. -/
private lemma locallyOfFinitePresentation_toScheme_map_covering
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS))))
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩) (i : E.I₀) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (E.f i)) := by
  have hfp := B.isFppfCovering_of_isCovering hE
  rw [IsFppfCovering, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map] at hfp
  rw [show (((PreZeroHypercover.map (BigFppfOver.forget B S hS) E).map
      (schemeBelowInclusion B.cutoff)).presieve₀) =
      Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (E.X i))
        (fun i => (BigFppfOver.toScheme B S hS).map (E.f i)) from rfl,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hfp
  exact (hfp.2 i).2

/-- Let `F` be a presheaf of sets on the big fppf site of `S` and let `{S i → S}` be a covering
family of the base, and assume

1. `F` is a sheaf (`hF`);
2. each restriction `h_{S i} × F` is an algebraic space (`hFi`);
3. each restriction is of finite type over its member (`hft`).

Then `F` is an algebraic space.

The refinement of the covering by affines over the points of `S`, Stacks 02WQ and the final
appeal to Stacks 04S6 are `AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_atlas_size_le`.
What this proof adds is the bounded atlas it asks for: the restriction of `h_{S i} × F` to an
affine open `W` of `S i` is of finite type over `W`, hence quasi-compact, hence has an affine
étale atlas (Stacks 03H6), which is locally of finite type over `S` and so of size at most
`size (S)` (Stacks 04T7). -/
@[stacks 04U0]
theorem isAlgebraicSpace_of_isCovering_of_isFiniteType
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS))))
    (hE : BigFppfOver.IsCovering B S hS ⟨Over.mk (𝟙 (B.obj hS)), E⟩)
    (hFi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ F))
    (hft : ∀ i : E.I₀, Space.IsFiniteType B S hS
      (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i))) :
    IsAlgebraicSpace B S hS F := by
  classical
  refine isAlgebraicSpace_of_isCovering_of_atlas_size_le hF E hE hFi (κ := S.size) hS
    (fun i W j hWaff hjoi => ?_)
  -- the restriction to `W` is a base change of `h_{S i} × F ⟶ h_{S i}`
  have sq := IsPullback.of_hasPullback
    (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i)) (yoneda.map j)
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hX : IsAlgebraicSpace B S hS
      (pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i)) (yoneda.map j)) :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS (pullback.fst _ _)
      ((Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback sq.flip
        (Functor.relativelyRepresentable.map yoneda j))
      (hFi i)
  -- so it is of finite type over the affine `W`, hence quasi-compact
  have sq' : IsPullback
      (ObjectProperty.homMk (pullback.fst _ _) : (⟨_, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hFi i⟩)
      (ObjectProperty.homMk (pullback.snd _ _) : (⟨_, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hW⟩)
      (ObjectProperty.homMk prod.fst : (⟨_, hFi i⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨_, isAlgebraicSpace_yoneda B S hS (E.X i)⟩)
      (ObjectProperty.homMk (yoneda.map j) : (⟨_, hW⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨_, isAlgebraicSpace_yoneda B S hS (E.X i)⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  have hqlft : Space.IsLocallyOfFiniteType B S hS (pullback.snd _ _ :
      pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i)) (yoneda.map j) ⟶
        yoneda.obj W) :=
    (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq' (hft i).1
  have hqc : Space.IsQuasiCompactSpace B S hS
      (pullback (prod.fst : yoneda.obj (E.X i) ⨯ F ⟶ yoneda.obj (E.X i)) (yoneda.map j)) :=
    Space.isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj W))
      (pullback.snd _ _)))
      (Space.isQuasiCompact_of_isPullback B S hS sq (hft i).2 _ hW
        (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS W hWaff) (𝟙 _))
  -- an affine surjective étale atlas, Stacks 03H6
  obtain ⟨Y, a, hYaff, hYsurj, hYet⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hX).1 hqc
  refine ⟨Y, a, hYsurj, (Space.isEtale_iff_presheaf_of_yoneda B S hS a).1 hYet, ?_⟩
  -- Stacks 04T7 bounds its size by the size of the base
  have hcompose : Space.IsLocallyOfFiniteType B S hS (a ≫ pullback.snd _ _) :=
    Space.isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS Y) hX hW a _
      (Space.holdsOnEveryEtaleChart_of_isEtale B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (fun _ hg => have := hg; inferInstance) hX hYet)
      hqlft
  have hgmap : Space.IsLocallyOfFiniteType B S hS
      (yoneda.map (yoneda.preimage (a ≫ pullback.snd _ _))) := by
    rwa [Functor.map_preimage]
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (a ≫ pullback.snd _ _))) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
      (yoneda.preimage (a ≫ pullback.snd _ _))).1 hgmap
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (E.f i)) :=
    locallyOfFinitePresentation_toScheme_map_covering E hE i
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y) := by
    have := hYaff
    infer_instance
  exact Scheme.size_le_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ pullback.snd _ _)) ≫
      (BigFppfOver.toScheme B S hS).map j ≫ (BigFppfOver.toScheme B S hS).map (E.f i))

end AlgebraicGeometry

end
