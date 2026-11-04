module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityGlobalProjection

/-!
# Every component of the datum is a base change of the glued scheme

Let `𝒰 = {X i ⟶ S}` be a covering family of a scheme `S` for the fpqc topology and let `D` be a
descent datum relative to `𝒰` whose restriction to every affine open of `S` is effective. The
schemes charting the restricted data over the affine opens of `S` glue to a scheme `X` over `S`,
and each component of `D` projects onto `X` (`AlgebraicGeometry.DescentData.globalProj`). Those
projections exhibit every component of `D` as the base change of `X` along the corresponding
member of the family.

## Main definitions

* `AlgebraicGeometry.Scheme.affinePreimageCover`: the open cover of a scheme over `S` by the
  preimages of the affine opens of `S`.

## Main results

* `AlgebraicGeometry.DescentData.fst_comp_globalProj`: the projection onto the glued scheme, read
  on the part of a component lying over an affine open of the base through the chosen fibre
  product, is the projection of the chosen chart followed by that chart's inclusion into the
  glued scheme.
* `AlgebraicGeometry.DescentData.isPullback_globalProj`: every component of the datum is the
  base change of the glued scheme along the corresponding member of the family.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace MorphismOfSchemeFamilies

/-- The open cover of a scheme over `S` by the preimages of the affine opens of `S`. -/
def Scheme.affinePreimageCover {S T : Scheme.{u}} (g : T ⟶ S) : T.OpenCover where
  I₀ := S.affineOpens
  X U := (g ⁻¹ᵁ U.1).toScheme
  f U := (g ⁻¹ᵁ U.1).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨V, hV, hxV, -⟩ :=
      Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) (U := ⊤) (Opens.mem_top (g x))
    exact ⟨⟨V, hV⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

namespace DescentData

variable {S : Scheme.{u}}

section Step7

attribute [local implicit_reducible] MorphismOfSchemeFamilies.ofRestrictBase
  MorphismOfSchemeFamilies.pulledBackDatum

variable {𝒰 : PreZeroHypercover.{u} S}
  (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (D : DescentData 𝒰.f)
  (hD : ∀ U : S.affineOpens, ((MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U.1)).functor.obj D).IsFamilyEffective)
  {X : Scheme.{u}} (p : X ⟶ S)
  (c : ∀ U : S.affineOpens, (affineChart D hD U).base.left ⟶ X)
  (hcres : ∀ {V U : S.affineOpens} (h : V.1 ≤ U.1), res h𝒰 D hD h ≫ c U = c V)

/-- The projection onto the glued scheme, read on the part of the component lying over an
affine open of the base through the chosen fibre product. -/
@[reassoc]
lemma fst_comp_globalProj (U : S.affineOpens) (i : 𝒰.I₀) :
    pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U.1).ι) ≫ globalProj h𝒰 D hD c hcres i =
      (affineChart D hD U).proj i ≫ c U := by
  refine (cancel_epi (restrictBaseObjIso 𝒰 D U.1 i).hom).mp ?_
  rw [← Category.assoc, restrictBaseObjIso_hom_fst]
  exact ι_globalProj h𝒰 D hD c hcres U i

include hcres hD h𝒰 p in
/-- Every component of the datum is the base change of the glued scheme along the corresponding
member of the family. -/
lemma isPullback_globalProj
    (hc : ∀ U : S.affineOpens, IsPullback (affineChart D hD U).base.hom (c U) U.1.ι p)
    (i : 𝒰.I₀) :
    IsPullback (globalProj h𝒰 D hD c hcres i) (D.obj i).hom p (𝒰.f i) := by
  refine (Scheme.isPullback_of_openCover (D.obj i).hom (globalProj h𝒰 D hD c hcres i)
    (𝒰.f i) p (Scheme.affinePreimageCover (𝒰.f i)) fun U ↦ ?_).flip
  have h1 : IsPullback (pullback.snd (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U.1).ι))
      (pullback.fst (D.obj i).hom (((𝒰.f i) ⁻¹ᵁ U.1).ι) ≫ globalProj h𝒰 D hD c hcres i)
      ((((𝒰.f i) ⁻¹ᵁ U.1).ι) ≫ 𝒰.f i) p := by
    rw [fst_comp_globalProj h𝒰 D hD c hcres U i, ← morphismRestrict_ι (𝒰.f i) U.1]
    exact (((affineChart D hD U).isPullback i).flip).paste_vert (hc U)
  exact h1

end Step7

end DescentData

end AlgebraicGeometry

end

end
