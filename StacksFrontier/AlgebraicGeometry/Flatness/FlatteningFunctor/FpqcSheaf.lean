module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BaseChangeTransition
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness

/-!
# The flatness functor is an fpqc sheaf

For a morphism of schemes `f : X ⟶ S` and a quasi-coherent `𝒪_X`-module `F`, flatness of the
base-changed module `F_T` over a scheme `T` over `S` is local for the fpqc topology on `T`: it
holds over `T` exactly when it holds over every member of an fpqc covering of `T`. Since the
flatness functor of `F` is subterminal, this locality is precisely the sheaf condition for the
fpqc topology on schemes over `S`.

The substance is the descent direction. A member `T' ⟶ T` of an fpqc covering is flat, hence so
is the induced morphism `X ×_S T' ⟶ X ×_S T`, and the members of the covering are jointly
surjective, so every point of `X ×_S T` is hit by a point of some `X ×_S T'`. At such a point,
flatness of `F_{T'}` over `T'` gives flatness over `T` by transitivity of flatness along the
flat morphism `T' ⟶ T`, and then descends along the faithfully flat stalk map of
`X ×_S T' ⟶ X ×_S T`.

## Main results

* `AlgebraicGeometry.FlatnessSituation.isFlatAfterBaseChange_iff_fpqcCover`: flatness of the
  base-changed module is fpqc local on the scheme over the base.
* `AlgebraicGeometry.FlatnessSituation.flatFunctor_isSheaf_fpqc`: the flatness functor is a
  sheaf for the fpqc topology on schemes over the base.

## Implementation notes

An fpqc covering is taken in the form of a `CategoryTheory.Precoverage.ZeroHypercover` for
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, whose index type lives in a universe independent of
the universe of the schemes. The descent step at a point combines
`AlgebraicGeometry.IsFlatOverAt.comp` with
`AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt`, and the comparison between
pulling the module back to `X ×_S T'` in one step and in two is
`AlgebraicGeometry.schemeModulePullbackCompIso`.

## References

* [Stacks Project, Tag 05MY](https://stacks.math.columbia.edu/tag/05MY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u w

namespace AlgebraicGeometry.FlatnessSituation

variable (D : FlatnessSituation.{u}) {T T' : Over D.S}

/-- The comparison isomorphism between pulling the module back to `X ×_S T'` in one step and
pulling it back to `X ×_S T` and then along the transition morphism of the two base changes. -/
private noncomputable def baseChangeModuleTransitionIso (g : T' ⟶ T) :
    (modulePullback (Stacks.BaseChange.transition D.f g).toLRSHom.toShHom).obj
        (D.baseChangeModule T) ≅ D.baseChangeModule T' := by
  simpa only [Stacks.BaseChange.transition_comp_fst, Functor.comp_obj] using
    (schemeModulePullbackCompIso (Stacks.BaseChange.transition D.f g)
      (pullback.fst D.f T.hom)).app D.F

/-- If the base-changed module is flat over `T'` and `T' ⟶ T` is flat, then the base-changed
module over `T` is flat at every point of `X ×_S T` in the image of `X ×_S T'`. -/
private theorem isFlatOverAt_baseChangeModule_of_flat_hom (g : T' ⟶ T) (hg : Flat g.left)
    (h : D.IsFlatAfterBaseChange T') (x' : D.baseChange T') :
    IsFlatOverAt (pullback.snd D.f T.hom).toLRSHom.toShHom (D.baseChangeModule T)
      ((Stacks.BaseChange.transition D.f g).base x') := by
  have hq : Flat (Stacks.BaseChange.transition D.f g) :=
    Stacks.BaseChange.transition_flat D.f g hg
  have hpulled : IsFlatOverAt (pullback.snd D.f T'.hom).toLRSHom.toShHom
      ((modulePullback (Stacks.BaseChange.transition D.f g).toLRSHom.toShHom).obj
        (D.baseChangeModule T)) x' :=
    isFlatOverAt_of_moduleIso _ (D.baseChangeModuleTransitionIso g).symm x' (h x')
  have hover : IsFlatOverAt
      ((pullback.snd D.f T'.hom).toLRSHom.toShHom ≫ g.left.toLRSHom.toShHom)
      ((modulePullback (Stacks.BaseChange.transition D.f g).toLRSHom.toShHom).obj
        (D.baseChangeModule T)) x' :=
    IsFlatOverAt.comp _ _ _ x' hpulled (Flat.stalkMap g.left _)
  refine (isFlatOverAt_iff_modulePullback_isFlatOverAt (Stacks.BaseChange.transition D.f g)
    (pullback.snd D.f T.hom) (D.baseChangeModule T) x' (Flat.stalkMap _ x')).mpr ?_
  have hw : Stacks.BaseChange.transition D.f g ≫ pullback.snd D.f T.hom =
      pullback.snd D.f T'.hom ≫ g.left := (Stacks.BaseChange.transition_isPullback D.f g).w
  rw [hw]
  exact hover

/-- Flatness of the base-changed module is local for the fpqc topology on the scheme over the
base: it holds over `T` exactly when it holds over every member of an fpqc covering of `T`.
This locality is what the fpqc sheaf condition for the flatness functor amounts to. -/
public theorem isFlatAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsFlatAfterBaseChange T ↔
      ∀ i, D.IsFlatAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) := by
  have hmem : 𝒰.toPreZeroHypercover.presieve₀ ∈ Scheme.precoverage (@Flat) T.left :=
    Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.left 𝒰.mem₀
  have hdata := (Scheme.presieve₀_mem_precoverage_iff
    (P := @Flat) 𝒰.toPreZeroHypercover).mp hmem
  have hflat : ∀ i, Flat (𝒰.f i) := hdata.2
  set localHom : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T :=
    fun i ↦ Over.homMk (𝒰.f i) (by simp) with hlocalHom
  refine ⟨fun h i ↦ D.isFlatAfterBaseChange_of_hom (localHom i) h, fun h x ↦ ?_⟩
  obtain ⟨i, y₀, hy₀⟩ := hdata.1 ((pullback.snd D.f T.hom).base x)
  obtain ⟨x', hx'⟩ := Stacks.BaseChange.exists_transition_preimage D.f (localHom i)
    (hflat i) x y₀ hy₀
  rw [← hx']
  exact D.isFlatOverAt_baseChangeModule_of_flat_hom (localHom i) (hflat i) (h i) x'

/-- **Stacks Project, Tag 05MY.** Part (1): the flatness functor of a quasi-coherent module
satisfies the sheaf condition for the fpqc topology on schemes over the base. -/
@[stacks 05MY "flat_functor_fpqc_sheaf"]
public theorem flatFunctor_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.flatFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf ((Scheme.fpqcPrecoverage.toGrothendieck).over D.S) D.flatFunctor
  rw [CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget
    Scheme.fpqcPrecoverage D.S,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨ι, Y, g, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : Scheme.fpqcPrecoverage.ZeroHypercover T.left :=
    ⟨⟨ι, fun i ↦ (Y i).left, fun i ↦ (g i).left⟩, by
      simpa [Precoverage.mem_comap_iff] using hR⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x _
  have hlocal (i : ι) : D.IsFlatAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) := by
    change D.IsFlatAfterBaseChange (Over.mk ((g i).left ≫ T.hom))
    convert (x i).down using 1
    exact CostructuredArrow.obj_ext _ _ rfl (CostructuredArrow.w (g i)).symm
  refine ⟨PLift.up ((D.isFlatAfterBaseChange_iff_fpqcCover T 𝒰).2 hlocal), ?_, ?_⟩
  · intro i; cases x i; rfl
  · intro t _; cases t; rfl

end AlgebraicGeometry.FlatnessSituation
