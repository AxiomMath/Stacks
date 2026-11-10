module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Flatness.BaseChangeTransition
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange

/-!
# The functor of flatness in dimensions at least `n` is an fpqc sheaf

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type and let `n` be a natural number. Flatness in dimensions `≥ n` of the base-changed module
`F_T` over a scheme `T` over `S` is local for the fpqc topology on `T`: it holds over `T`
exactly when it holds over every member of an fpqc covering of `T`. Since the functor `F_n` is
subterminal, this locality is precisely the sheaf condition for the fpqc topology on schemes
over `S`.

The substance is the descent direction. A point `x` of `X_T` at which `F_T` is not flat over
`T` is lifted to a point `x'` of `X_{T'}`, for a member `T' ⟶ T` of the covering through which
the image of `x` in `T` is hit, in such a way that the residue-field transcendence degree over
the base does not change. Flat base change identifies the non-flat loci, so `F_{T'}` is not
flat at `x'` either, and the dimension bound assumed over `T'` transports back to `x`.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.isFlatInDimensionsGEAfterBaseChange_iff_fpqcCover`:
  flatness in dimensions `≥ n` of the base-changed module is fpqc local on the scheme over the
  base.
* `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc`: **Stacks
  05MV**, part (1): the functor `F_n` is a sheaf for the fpqc topology on schemes over the
  base.  The whole of Stacks 05MV, parts (1) and (2) together, is
  `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving`
  in the module
  `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionSheafAndLimitPreserving`

## Implementation notes

An fpqc covering is taken in the form of a `CategoryTheory.Precoverage.ZeroHypercover` for
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, whose index type lives in a universe independent of
the universe of the schemes.

The dimension condition is used through its transcendence-degree form
`AlgebraicGeometry.isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt` (Stacks 0CWF), which is
pointwise and therefore transports along the lift of a point. The lift is
`AlgebraicGeometry.exists_pullback_point_preserving_fibre_dimension_and_trdeg` (Stacks 02FY),
applied to the cartesian square `Stacks.BaseChange.transition_isPullback`; the descent of
non-flatness along it is `AlgebraicGeometry.isFlatOverAt_of_modulePullback` (Stacks 047C), and
the bookkeeping of the two residue-field algebra structures is
`AlgebraicGeometry.trdeg_residueFieldMap_congr`.

## References

* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 0CWF](https://stacks.math.columbia.edu/tag/0CWF)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 047C](https://stacks.math.columbia.edu/tag/047C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u w

namespace AlgebraicGeometry.FlatDimensionSituation

variable (D : FlatDimensionSituation.{u})

/-- If the base-changed module is flat over `T'` at a point `x'` and `T' ⟶ T` is flat, then the
base-changed module over `T` is flat at the image of `x'` in `X ×_S T`. -/
private theorem isFlatOverAt_baseChangeModule_of_flat_hom {T T' : Over D.S} (g : T' ⟶ T)
    (hg : Flat g.left) (x' : ↥(pullback D.f T'.hom))
    (h : IsFlatOverAt (D.baseChangeMap T').toLRSHom.toShHom (D.baseChangeModule T') x') :
    IsFlatOverAt (D.baseChangeMap T).toLRSHom.toShHom (D.baseChangeModule T)
      ((Stacks.BaseChange.transition D.f g).base x') := by
  have hbase : IsFlatAt g.left.toLRSHom.toShHom ((D.baseChangeMap T') x') := by
    change (g.left.stalkMap ((D.baseChangeMap T') x')).hom.Flat
    exact Flat.stalkMap g.left _
  have _ : SheafOfModules.IsQuasicoherent
      (R := structureSheafRing (pullback D.f T.hom).toRingedSpace) (D.baseChangeModule T) :=
    D.baseChangeModule_isQuasicoherent T
  exact isFlatOverAt_of_modulePullback (Stacks.BaseChange.transition_isPullback D.f g)
    (D.baseChangeModule T) x' hbase
    ((isFlatOverAt_iff_of_moduleIso (D.baseChangeMap T').toLRSHom.toShHom
      (D.baseChangeModuleIso g) x').mpr h)

/-- Flatness in dimensions `≥ n` of the base-changed module is local for the fpqc topology on
the scheme over the base: it holds over `T` exactly when it holds over every member of an fpqc
covering of `T`. This locality is what the fpqc sheaf condition for `F_n` amounts to. -/
public theorem isFlatInDimensionsGEAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsFlatInDimensionsGEAfterBaseChange T ↔
      ∀ i, D.IsFlatInDimensionsGEAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) := by
  have hdata := (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) 𝒰.toPreZeroHypercover).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.left 𝒰.mem₀)
  let g (i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T := Over.homMk (𝒰.f i) (by simp)
  refine ⟨fun hT i ↦ D.isFlatInDimensionsGEAfterBaseChange_of_hom (g i) hT, fun h ↦ ?_⟩
  refine (isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt (D.baseChangeMap T)
    (D.baseChangeModule T) D.n).mpr fun x hnonflat ↦ ?_
  obtain ⟨i, y, hy⟩ := hdata.1 ((D.baseChangeMap T).base x)
  have hgy : (D.baseChangeMap T) x = (g i).left y := hy.symm
  obtain ⟨x', hx, hs', -, htrdeg⟩ :=
    exists_pullback_point_preserving_fibre_dimension_and_trdeg
      (Stacks.BaseChange.transition_isPullback D.f (g i)) y x hgy
  have hnonflat' : ¬ IsFlatOverAt (D.baseChangeMap (Over.mk (𝒰.f i ≫ T.hom))).toLRSHom.toShHom
      (D.baseChangeModule (Over.mk (𝒰.f i ≫ T.hom))) x' := fun hflat ↦ hnonflat <| by
    rw [← hx]
    exact D.isFlatOverAt_baseChangeModule_of_flat_hom (g i) (hdata.2 i) x' hflat
  rw [← trdeg_residueFieldMap_congr (D.baseChangeMap T) x ((g i).left y) hgy, htrdeg,
    trdeg_residueFieldMap_congr (D.baseChangeMap (Over.mk (𝒰.f i ≫ T.hom))) x' y hs']
  exact (isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt
    (D.baseChangeMap (Over.mk (𝒰.f i ≫ T.hom)))
    (D.baseChangeModule (Over.mk (𝒰.f i ≫ T.hom))) D.n).mp (h i) x' hnonflat'

/-- **Stacks Project, Tag 05MV.** Part (1): the functor `F_n` of flatness in dimensions `≥ n`
satisfies the sheaf condition for the fpqc topology on schemes over the base.

This is part (1) of the tag; the whole tag is
`AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving`,
which carries the tag. -/
public theorem flatDimensionFunctor_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) D.flatDimensionFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf ((Scheme.fpqcPrecoverage.toGrothendieck).over D.S)
    D.flatDimensionFunctor
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
  have hlocal (i : ι) :
      D.IsFlatInDimensionsGEAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) := by
    change D.IsFlatInDimensionsGEAfterBaseChange (Over.mk ((g i).left ≫ T.hom))
    convert (x i).down using 1
    exact CostructuredArrow.obj_ext _ _ rfl (CostructuredArrow.w (g i)).symm
  refine ⟨PLift.up ((D.isFlatInDimensionsGEAfterBaseChange_iff_fpqcCover T 𝒰).2 hlocal), ?_, ?_⟩
  · intro i
    cases x i
    rfl
  · intro t _
    cases t
    rfl

end AlgebraicGeometry.FlatDimensionSituation
