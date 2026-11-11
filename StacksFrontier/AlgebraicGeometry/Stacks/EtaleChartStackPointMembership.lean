module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartOpenSubspaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedNearSubstack

/-!
# The point-set clause of the Stacks 06N3 chart, read on the stack

The family assembly of **Stacks 06N3**,
`AlgebraicGeometry.Stack.exists_etaleChartFamily_of_forall_isFiniteTypePoint`, asks that the
prescribed finite type point `x` of `|𝒳|` lie in the image on points of the chart it is handed.
**Stacks 06N2** does not say that: its point-set conclusion is about a point of `|U|`, namely the
image under the projection `p : F ⟶ U` of a point of the fibre `F = U ×_𝒳 Spec k`, and
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι` states it as
membership of that point of `|U|` in the point set of the open subspace `V ⊆ U`.

This file crosses from the one to the other. It is the one clause that
`AlgebraicGeometry.Stack`
`.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale` of
`StacksFrontier/AlgebraicGeometry/Stacks/EtaleChartOpenSubspaceSiteObject.lean` still carries in its
hypothesis `hchart`, everything about open substacks, schemes of the site, coproducts, index types
and sizes being discharged there.

## The chase

The field-valued point enters with its image on points prescribed: `Spec k ⟶ 𝒳` has range `{x}`,
which is the shape
`AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`
delivers it in at a finite type point and the shape
`AlgebraicGeometry.Stack.exists_point_fibreOverFieldPoint_of_range_eq_singleton` already consumes.
Given a point `xF` of an algebraic space `Fsp` representing `F` whose image `p(xF)` in `|U|` lies
in the point set of `V`, say `p(xF) = ι(y)` for `y ∈ |V|`, the point of `|𝒳|` that `y` is carried
to by the chart on `V` is computed in three steps:

* the point of `|S_U|` named by `ι(y)` is the image of the point of `|S_V|` named by `y` under
  the 1-morphism of **Stacks 0458** induced by `ι`
  (`AlgebraicGeometry.Stack.spacePointMap_algebraicSpaceStackMap`);
* that same point of `|S_U|` is the image under the projection
  `AlgebraicGeometry.Stack.fibreProjection` of the point of `|F|` named by `xF`
  (`AlgebraicGeometry.Stack.pointsMap_fibreProjection_spacePointMap`, the comparison of the two
  readings of the projection);
* and the invertible filler of the cartesian square identifies `p ≫ f` with `q ≫ g` on points
  (`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`), so the image in `|𝒳|` lies in
  the range of `g`, which is `{x}`.

No bijectivity is used: the point of `|S_V|` is produced by
`AlgebraicGeometry.Stack.spacePointMap` out of `y` rather than matched against a given point of
`|S_V|`, so neither injectivity nor surjectivity of the tautological chart is needed here. (It is
needed one step earlier, inside
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι`, to move the
Stacks 06N2 clause down onto the algebraic space.)

## Main results

* `AlgebraicGeometry.Stack`
  `.mem_range_pointsMap_comp_algebraicSpaceStackMap_of_mem_range_pointsMap_ι`:
  **the clause.** A point of `|𝒳|` which is the whole image of the field-valued point lies in the
  image on points of the chart on an open subspace `V ⊆ U`, as soon as some point of a
  representing algebraic space of the fibre has its image under the projection in the point set
  of `V`.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap`: **Stacks 06N2 with
  the point-set clause at the prescribed point of `|𝒳|`** — the conjunction the hypothesis
  `hchart` of
  `AlgebraicGeometry.Stack`
  `.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale` asks for.
* `AlgebraicGeometry.Stack`
  `.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range`:
  the chart of Stacks 06N3 **in the shape the family assembly consumes**, run off the fibre
  hypothesis of Stacks 06N2 and the prescribed image of the field-valued point alone.

## What this does not settle

The hypotheses of the three results are the data of **Stacks 06N2** at the slice of
**Stacks 06MD**: the algebraic space `U` and the 1-morphism `f : U ⟶ 𝒳`, the field-valued point
with its singleton range, a representing algebraic space of the fibre, and the unramifiedness of
the fibre near the point. Producing *those* at a finite type point of a DM algebraic stack is the
body of the source's argument and is not touched here — in particular the identification of the
fibre of the Stacks 06MD slice,
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_fibreOverFieldPoint_zeroLocusOnOpen`, has
still to be fed to `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` through
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt`.

No `@[stacks]` attribute is registered. Nothing below is a step of Stacks 06N2, whose registration
sits on `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale`; and no part of **Stacks 06N3** is
claimed, its registration sitting on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
  (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-! ### The clause -/

/-- **The point-set clause of the Stacks 06N3 chart.** Let `f : U ⟶ 𝒳` be a 1-morphism out of the
algebraic stack of an algebraic space, let `g : Spec k ⟶ 𝒳` be a field-valued point whose image on
points is exactly `{x}`, let `Fsp` be an algebraic space representing the fibre
`F = U ×_𝒳 Spec k` and let `p : Fsp ⟶ U` be the projection of **Stacks 04SW** read on it. If some
point `xF` of `|Fsp|` has `p(xF)` in the point set of an open subspace `V ⊆ U`, in the sense of
**Stacks 02YU**, part (2), then `x` lies in the image on points of the composite of the
1-morphism of **Stacks 0458** induced by `V` with `f`.

This is the clause the family assembly of **Stacks 06N3** consumes and **Stacks 06N2** does not
supply: the latter concludes with the membership of `p(xF)` in the point set of `V`, which is the
hypothesis here. The two are joined by the comparison of the two readings of the projection,
`AlgebraicGeometry.Stack.pointsMap_fibreProjection_spacePointMap`, together with the invertible
filler of the cartesian square, which identifies `p ≫ f` with `q ≫ g` on points; the image of `x`
under nothing at all is then read out of the singleton range of `g`. -/
theorem mem_range_pointsMap_comp_algebraicSpaceStackMap_of_mem_range_pointsMap_ι
    {x : AlgebraicStacks.points B S hS 𝒳}
    (hg : Set.range (AlgebraicStacks.pointsMap B S hS g) = {x})
    (xF : Space.points B S hS Fsp)
    (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V)
    (hmem : Space.pointsMap B S hS Fsp
        (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) xF ∈
      Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) :
    x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f)) := by
  obtain ⟨y, hy⟩ := hmem
  refine ⟨spacePointMap B S hS V.toFunctor (fibredCategory B S hS V.toFunctor)
    (BasedFunctor.id (fibredCategory B S hS V.toFunctor).val) y, ?_⟩
  -- the point of `|S_U|` reached from `y` is the one the projection of the fibre produces
  have hproj : AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι)
        (spacePointMap B S hS V.toFunctor (fibredCategory B S hS V.toFunctor)
          (BasedFunctor.id (fibredCategory B S hS V.toFunctor).val) y) =
      AlgebraicStacks.pointsMap B S hS (fibreProjection B S hS 𝒳 U hU k hk toBase f g)
        (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
          (representingEquivalence B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF) := by
    rw [pointsMap_fibreProjection_spacePointMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF xF,
      ← hy]
    exact (spacePointMap_algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι y).symm
  -- the invertible filler of the cartesian square, read on points
  have hfill : AlgebraicStacks.pointsMap B S hS
        (fibreProjection B S hS 𝒳 U hU k hk toBase f g ≫ f) =
      AlgebraicStacks.pointsMap B S hS
        (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g ≫ g) :=
    AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g).iso.hom
  have hrange : AlgebraicStacks.pointsMap B S hS f
      (AlgebraicStacks.pointsMap B S hS (fibreProjection B S hS 𝒳 U hU k hk toBase f g)
        (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
          (representingEquivalence B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF)) ∈
      Set.range (AlgebraicStacks.pointsMap B S hS g) := by
    have hap := congrFun hfill
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF)
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp,
      Function.comp_apply, Function.comp_apply] at hap
    exact hap ▸ Set.mem_range_self _
  rw [hg, Set.mem_singleton_iff] at hrange
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hproj]
  exact hrange

/-! ### Stacks 06N2 with the clause -/

/-- **Stacks 06N2, with the point-set clause at the prescribed point of `|𝒳|`.** Let `𝒳` be an
algebraic stack, let `U` be an algebraic space with a 1-morphism `f : U ⟶ 𝒳` which is flat and
locally of finite presentation, let `g : Spec k ⟶ 𝒳` be a field-valued point whose image on points
is exactly `{x}`, let `Fsp` be an algebraic space representing the fibre `F = U ×_𝒳 Spec k`, and
suppose `F ⟶ Spec k` is unramified near the point of `|F|` named by `xF ∈ |Fsp|`. Then there is an
open subspace `V ⊆ U`, in the sense of **Stacks 02YU**, part (2), such that the composite of the
1-morphism of **Stacks 0458** induced by `V` with `f` is étale **and has `x` in its image on
points**.

This is exactly the conjunction the hypothesis `hchart` of
`AlgebraicGeometry.Stack`
`.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_isOpenSubspace_isEtale` asks for, so
with this the substantial direction of **Stacks 06N3** reduces to producing the data of
Stacks 06N2 at the Stacks 06MD slice of a smooth chart, at a finite type point.

Nothing is added to `AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι`
beyond
`AlgebraicGeometry.Stack`
`.mem_range_pointsMap_comp_algebraicSpaceStackMap_of_mem_range_pointsMap_ι`. -/
theorem exists_isOpenSubspace_isEtale_mem_range_pointsMap
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    {x : AlgebraicStacks.points B S hS 𝒳}
    (hg : Set.range (AlgebraicStacks.pointsMap B S hS g) = {x})
    (xF : Space.points B S hS Fsp)
    (hx : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF)) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      IsEtale B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f) ∧
        x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hU V.ι ≫ f)) := by
  obtain ⟨V, hV, hmem, het⟩ :=
    exists_isOpenSubspace_isEtale_mem_range_pointsMap_ι.{u, w} B S hS 𝒳 U hU k hk toBase f g
      Fsp eF hflat hfp xF hx
  exact ⟨V, hV, het,
    mem_range_pointsMap_comp_algebraicSpaceStackMap_of_mem_range_pointsMap_ι.{u, w} B S hS 𝒳 U hU
      k hk toBase f g Fsp eF hg xF V hV hmem⟩

/-! ### The chart of Stacks 06N3 in the shape the family assembly consumes -/

/-- **The chart of Stacks 06N3 off the fibre hypothesis of Stacks 06N2, with the point-set clause
at the prescribed point of `|𝒳|`.** Let `ρ : h_{U₀} ≅ U` present the algebraic space `U` as the
functor of points of a scheme `U₀` of the site, let `f : U ⟶ 𝒳` be flat and locally of finite
presentation, let `g : Spec k ⟶ 𝒳` be a field-valued point with image exactly `{x}` on points, let
`Fsp` represent the fibre `F = U ×_𝒳 Spec k`, and suppose `F ⟶ Spec k` is unramified near the
point of `|F|` named by `xF ∈ |Fsp|`. Then there are a scheme `Z` of the site, a morphism
`z : Z ⟶ U₀` of the site with open immersion of schemes underlying it, and a 1-morphism
`Z ⟶ 𝒳` which is relatively étale in the sense of **Stacks 04XB**, whose image on points contains
`x`, and with `size Z ≤ 2 ^ 2 ^ size U₀`.

That is the datum
`AlgebraicGeometry.Stack.exists_etaleChartFamily_of_forall_isFiniteTypePoint` asks for at one
finite type point, with no clause left over. It is
`AlgebraicGeometry.Stack.exists_siteObject_isRelativelyEtale_chart_of_mem_range` at the open
subspace and étaleness of **Stacks 06N2** and at the clause
`AlgebraicGeometry.Stack`
`.mem_range_pointsMap_comp_algebraicSpaceStackMap_of_mem_range_pointsMap_ι` supplies. -/
theorem exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range
    {U₀ : BigFppfOver B S hS} (ρ : yoneda.obj U₀ ≅ U)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    {x : AlgebraicStacks.points B S hS 𝒳}
    (hg : Set.range (AlgebraicStacks.pointsMap B S hS g) = {x})
    (xF : Space.points B S hS Fsp)
    (hx : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor xF)) :
    ∃ (Z : BigFppfOver B S hS) (z : Z ⟶ U₀) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map z) ∧
        IsRelativelyEtale B S hS c.hom ∧
          x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
            ((BigFppfOver.toScheme B S hS).obj Z).size ≤
              (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
                ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  obtain ⟨V, hV, het, hmem⟩ :=
    exists_isOpenSubspace_isEtale_mem_range_pointsMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp eF
      hflat hfp hg xF hx
  exact exists_siteObject_isRelativelyEtale_chart_of_mem_range.{u, w} B S hS hU ρ f hV het x hmem

end AlgebraicGeometry.Stack

end
