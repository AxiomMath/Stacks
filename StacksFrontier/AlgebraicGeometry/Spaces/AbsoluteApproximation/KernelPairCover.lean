module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The kernel pair of an étale neighbourhood is covered by the diagonal and the open part

In the proof of Stacks 07SU one is given an algebraic space `X`, an open subspace `U ⊆ X`, a
closed subspace `Z ⊆ X` with `|X| = |U| ⊔ |Z|`, and an étale morphism `f : V ⟶ X` from a scheme
such that `f⁻¹(Z) ⟶ Z` is an isomorphism (property (6)). The proof asserts that the scheme
`V ×_X V` is the union of the opens `Δ_{V/X}(V)` and `W ×_U W`, where `W = f⁻¹(U)`. This file
proves the statement about points that this amounts to: every point of `V ×_X V` lies on the
diagonal or over `W`.

## Main results

* `AlgebraicGeometry.Space.mem_range_diag_or_mem_range_of_isIso_pullback_fst`: every point of
  the kernel pair `V ×_X V` lies on the diagonal or has its second projection in `W`.

## Implementation notes

A point `x` of `V ×_X V` whose second projection `v` is not in `W` maps to a point of `X` outside
`|U|`, hence in `|Z|`, so `v` comes from `f⁻¹(Z)` and `x` from `K_Z = (V ×_X V) ×_V f⁻¹(Z)`
(Stacks 03H4). The two projections agree on `K_Z`, because both factor through `f⁻¹(Z)`
compatibly with the isomorphism `f⁻¹(Z) ⟶ Z`, so `K_Z ⟶ V ×_X V` factors through the diagonal.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In a cartesian square, a point whose image lies in the image of one leg of the cospan is in the
range of the opposite leg of the square. -/
private theorem mem_range_pointsMap_of_isPullback {W Z W' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z} {h : Z' ⟶ Z} (sq : IsPullback c p' p h)
    (z : points B S hS Z') (a : points B S hS W)
    (ha : pointsMap B S hS W p a = pointsMap B S hS Z' h z) :
    z ∈ Set.range (pointsMap B S hS W' p') := by
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS sq a z ha
  exact ⟨w, hw⟩

/-- **Every point of the kernel pair of an étale neighbourhood lies on the diagonal or over the
open part (proof of Stacks 07SU, property (6)).** Let `f : V ⟶ X` be a morphism from an object of
the site, `U` and `Z` subfunctors of `X` whose points are complementary, with `f⁻¹(Z) ⟶ Z` an
isomorphism, `W ⟶ V` an object of the site with `W = V ×_X U`, and `R` with projections
`s, t : R ⟶ V` and diagonal `d : V ⟶ R` the kernel pair of `f`. Then every point of `R` lies in
the image of `d` or has its image under `t` in the image of `W`. -/
theorem mem_range_diag_or_mem_range_of_isIso_pullback_fst
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W R : BigFppfOver B S hS} (f : yoneda.obj V ⟶ X)
    (U Z : Subfunctor X)
    (hUZ : Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ)
    (hZ : IsIso (pullback.fst Z.ι f))
    (incl : W ⟶ V) (wU : yoneda.obj W ⟶ U.toFunctor) (hW : IsPullback wU (yoneda.map incl) U.ι f)
    (s t : R ⟶ V) (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) (d : V ⟶ R)
    (hds : d ≫ s = 𝟙 _) (hdt : d ≫ t = 𝟙 _)
    (x : (BigFppfOver.toScheme B S hS).obj R) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map d) ∨
      (BigFppfOver.toScheme B S hS).map t x ∈
        Set.range ((BigFppfOver.toScheme B S hS).map incl) := by
  by_cases hv : (BigFppfOver.toScheme B S hS).map t x ∈
      Set.range ((BigFppfOver.toScheme B S hS).map incl)
  · exact Or.inr hv
  left
  obtain ⟨xp, rfl⟩ := surjective_pointsToScheme B S hS R x
  set vp := pointsMap B S hS (yoneda.obj R) (yoneda.map t) xp with hvp
  have hvp' : pointsToScheme B S hS V vp =
      (BigFppfOver.toScheme B S hS).map t (pointsToScheme B S hS R xp) :=
    pointsToScheme_pointsMap_yoneda B S hS t xp
  -- the image of `v` in `X` is not in `U`, hence in `Z`
  have hU : pointsMap B S hS (yoneda.obj V) f vp ∉
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    rintro ⟨a, ha⟩
    have hb := mem_range_pointsMap_of_isPullback hW vp a ha
    rw [range_pointsMap_yoneda_eq_preimage, Set.mem_preimage, hvp'] at hb
    exact hv hb
  have hZmem : pointsMap B S hS (yoneda.obj V) f vp ∈
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    rw [hUZ]; exact hU
  -- so `v` comes from `f⁻¹(Z)`
  obtain ⟨q, hq⟩ : vp ∈ Set.range (pointsMap B S hS _ (pullback.snd Z.ι f)) := by
    obtain ⟨a, ha⟩ := hZmem
    exact mem_range_pointsMap_of_isPullback (IsPullback.of_hasPullback Z.ι f) vp a ha
  -- and `x` from `K_Z = R ×_V f⁻¹(Z)`
  obtain ⟨y, hy⟩ : xp ∈ Set.range (pointsMap B S hS _
      (pullback.fst (yoneda.map t) (pullback.snd Z.ι f))) := by
    exact mem_range_pointsMap_of_isPullback
      (IsPullback.of_hasPullback (yoneda.map t) (pullback.snd Z.ι f)).flip xp q hq
  -- the two projections agree on `K_Z`
  set ψ := pullback.fst (yoneda.map t) (pullback.snd Z.ι f)
  set b := pullback.snd (yoneda.map t) (pullback.snd Z.ι f)
  have hcond : (b ≫ pullback.fst Z.ι f) ≫ Z.ι = (ψ ≫ yoneda.map s) ≫ f := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← pullback.condition,
      Category.assoc, Category.assoc, hR.w]
  have hab : pullback.lift (b ≫ pullback.fst Z.ι f) (ψ ≫ yoneda.map s) hcond = b :=
    (cancel_mono (pullback.fst Z.ι f)).1 (pullback.lift_fst _ _ _)
  have hst : ψ ≫ yoneda.map s = ψ ≫ yoneda.map t := by
    rw [← pullback.lift_snd (b ≫ pullback.fst Z.ι f) (ψ ≫ yoneda.map s) hcond, hab,
      pullback.condition]
  -- hence `K_Z ⟶ R` factors through the diagonal
  have hfac : ψ = (ψ ≫ yoneda.map t) ≫ yoneda.map d := by
    refine hR.hom_ext ?_ ?_
    · rw [Category.assoc, ← yoneda.map_comp, hds, CategoryTheory.Functor.map_id,
        Category.comp_id, hst]
    · rw [Category.assoc, ← yoneda.map_comp, hdt, CategoryTheory.Functor.map_id,
        Category.comp_id]
  have hx : xp ∈ Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map d)) := by
    refine ⟨pointsMap B S hS _ (ψ ≫ yoneda.map t) y, ?_⟩
    rw [← pointsMap_comp_apply, ← hfac, hy]
  rw [range_pointsMap_yoneda_eq_preimage, Set.mem_preimage] at hx
  exact hx

end AlgebraicGeometry.Space

end
