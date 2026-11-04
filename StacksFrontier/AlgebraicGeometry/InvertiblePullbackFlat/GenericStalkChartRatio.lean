module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreChartUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreModuleStalk
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreTrivialization
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator

/-!
# The trivializing germ on the generic fibre is a multiple of a chart generator

The first paragraph of [Stacks, Tag 0BD7] produces a generator `m` of the stalk of `ℒ` at the
generic point of `X` from a trivialization of `ℒ_ξ`; the penultimate paragraph works instead with
a generator of `ℒ` on an affine chart `U` of `X`. This file relates the two: at any point of the
generic fibre lying over `U`, the transported germ of the trivializing section is a multiple of
the germ of the chart's generator, the multiplier being the germ of the chart ratio of
`AlgebraicGeometry.genericFiberTrivGenerator_val_eq`.

Both inputs are needed and neither alone suffices. That the chart of the generic fibre is *all*
of the part of the generic fibre lying over `U`
(`AlgebraicGeometry.genericFiberChartOpens_eq`) is what puts the given point in the chart, so
that the chart ratio has a germ there at all; and the scalar law
`AlgebraicGeometry.stalkPullbackFiberιAddEquiv_stalkMap_smul` is what carries that germ down to
a scalar on `𝒪_{X, x}`, the stalk map of the fibre inclusion being bijective over the generic
point.

## Main results

* `AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator`: the transported germ of the
  trivializing section of `ℒ_ξ` is the germ of the chart ratio, read upstairs through the
  inverse of the stalk map of the fibre inclusion, times the germ of the chart's generator.
* `AlgebraicGeometry.exists_smul_eq_stalkPullbackFiberιAddEquiv_genericFiberTrivGenerator`: the
  same with the scalar existentially quantified.
* `AlgebraicGeometry.span_eq_top_grpGerm_genericFiberTrivGenerator`: that germ generates the
  stalk of `ℒ_ξ` at every point of the generic fibre.
* `AlgebraicGeometry.exists_span_eq_top_and_eq_smul_grpGerm_of_isTrivial_genericFiber`: the two
  together — a generator of the stalk of `ℒ` at the image point which is a multiple of the germ
  of the chart's generator. This is the generator the first paragraph of the source builds, in
  the form the penultimate paragraph can use.

## Implementation notes

The point of the generic fibre is a variable with the hypothesis that its image lies in `U`,
rather than the point over the generic point of `X`: the generic point enters only through
`AlgebraicGeometry.genericPoint_mem_range_fiberι_genericPoint` at the call site, and keeping it
out of the statement keeps the base point of the stalks a variable, which is what lets
`AlgebraicGeometry.stalkPullbackFiberιAddEquiv` be applied without a transport.

The multiplier is named, not existentially quantified: it is the image of the germ of the chart
ratio under `CategoryTheory.inv` of the stalk map of the fibre inclusion, which is an
isomorphism over the generic point. A consumer that must identify the multiplier with something
else — the penultimate paragraph's chart coordinate, say — cannot do so through an existential,
so the existential form is a corollary and not the statement proved.

The stalk map is spelled at the ringed-space level,
`((f.fiberι ξ).toLRSHom.toShHom).hom.stalkMap x₀`, rather than as
`(f.fiberι ξ).stalkMap x₀`. The two are definitionally equal, but only the former has its
domain *spelled* `ringStalk X.toRingedSpace (((f.fiberι ξ).toLRSHom.toShHom).hom.base x₀)`,
which is the spelling in which the module structure on the stalk is found: with the scheme-level
spelling the `•` in the statement fails to synthesize its `HSMul` instance.

No tag attribute: every statement here carries an affine chart and a point of the generic fibre,
neither of which [Stacks, Tag 0BD7] has.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.SheafOfModules RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] {x : X}
  {V : Y.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
  (e : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U)
  (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
  (hgen : AlgebraicGeometry.SheafOfModules.IsTrivial
    (f.fiber (genericPoint Y)).presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
      (f.fiber (genericPoint Y)).IsSheaf)
    ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
  (hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
  (genU : GeneratorSections X.toRingedSpace L U)

include hV hU e hx hL in
/-- **The transported germ of the trivializing section is the chart ratio times the germ of the
chart generator.** At a point `x₀` of the generic fibre lying over the affine chart `U`, the
image under `AlgebraicGeometry.stalkPullbackFiberιAddEquiv` of the germ of the trivializing
section of `ℒ_ξ` is the germ of the chart ratio, read upstairs through the inverse of the stalk
map of the fibre inclusion, times the germ of `genU` at the image of `x₀`. -/
theorem eq_smul_grpGerm_genericFiberTrivGenerator (x₀ : f.fiber (genericPoint Y))
    (hxU : ((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀ ∈ U) :
    haveI : IsIso (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
    stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
        (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
          ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
          ⊤ (Opens.mem_top x₀) (genericFiberTrivGenerator f L hgen ⊤).val) =
      inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀)
          (ringGerm (f.fiber (genericPoint Y)).toRingedSpace x₀
            (genericFiberChartOpens f hV hU e hx)
            (mem_genericFiberChartOpens f hV hU e hx x₀ hxU)
            (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
              (genericFiberChartGenerator f hV hU e hx L hL genU)
              (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)))) •
        grpGerm X.toRingedSpace L.val
          (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀) U hxU genU.val := by
  classical
  have : IsIso (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMap_fiberι_of_mem f (maximalIdeal_stalk_genericPoint_eq_bot Y) x₀)
  have hmem : x₀ ∈ genericFiberChartOpens f hV hU e hx :=
    mem_genericFiberChartOpens f hV hU e hx x₀ hxU
  -- The trivializing generator on the chart is the restriction of the one on `⊤`.
  have hr : generatorRestrict
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L)
        (le_top : genericFiberChartOpens f hV hU e hx ≤ ⊤)
        (genericFiberTrivGenerator f L hgen ⊤) =
      genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx) :=
    generatorOfIso_restrict _ hgen.some le_top
  -- The germ on `⊤` of the trivializing section is its germ on the chart.
  have h1 : grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        ⊤ (Opens.mem_top x₀) (genericFiberTrivGenerator f L hgen ⊤).val =
      grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        (genericFiberChartOpens f hV hU e hx) hmem
        (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)).val := by
    rw [← hr]
    exact (TopCat.Presheaf.germ_res_apply
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val.presheaf
      (homOfLE (le_top : genericFiberChartOpens f hV hU e hx ≤ ⊤)) x₀ hmem _).symm
  -- The germ on the chart of the chart generator is the germ of the pulled-back generator.
  have h2 : grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        (genericFiberChartOpens f hV hU e hx) hmem
        (genericFiberChartGenerator f hV hU e hx L hL genU).val =
      grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        ((opensMap (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj U) hxU
        (pullbackUnit (f.fiberι (genericPoint Y)).toLRSHom.toShHom L (op U) genU.val) :=
    TopCat.Presheaf.germ_res_apply
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val.presheaf
      (homOfLE (genericFiberChartOpens_le f hV hU e hx)) x₀ hmem _
  -- The scalar is the chart ratio read upstairs: `inv` of the stalk map, which is an
  -- isomorphism over the generic point, applied to the ratio's germ.
  have hc' : ((((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀).hom
        (inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀)
          (ringGerm (f.fiber (genericPoint Y)).toRingedSpace x₀
            (genericFiberChartOpens f hV hU e hx) hmem
            (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
              (genericFiberChartGenerator f hV hU e hx L hL genU)
              (genericFiberTrivGenerator f L hgen
                (genericFiberChartOpens f hV hU e hx)))))) =
      ringGerm (f.fiber (genericPoint Y)).toRingedSpace x₀
        (genericFiberChartOpens f hV hU e hx) hmem
        (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartGenerator f hV hU e hx L hL genU)
          (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx))) :=
    IsIso.inv_hom_id_apply
      (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀) _
  -- The germ on the chart of the trivializing section is the chart ratio times the germ of the
  -- chart generator, the ratio read as a scalar upstairs through the bijective stalk map.
  have key : grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        (genericFiberChartOpens f hV hU e hx) hmem
        (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx)).val =
      ((((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀).hom
          (inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀)
            (ringGerm (f.fiber (genericPoint Y)).toRingedSpace x₀
              (genericFiberChartOpens f hV hU e hx) hmem
              (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
                (genericFiberChartGenerator f hV hU e hx L hL genU)
                (genericFiberTrivGenerator f L hgen
                  (genericFiberChartOpens f hV hU e hx)))))) •
        grpGerm (f.fiber (genericPoint Y)).toRingedSpace
          ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
          (genericFiberChartOpens f hV hU e hx) hmem
          (genericFiberChartGenerator f hV hU e hx L hL genU).val := by
    rw [hc']
    exact (congrArg (fun s => grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        (genericFiberChartOpens f hV hU e hx) hmem s)
      (genericFiberTrivGenerator_val_eq f hV hU e hx L hgen hL genU)).trans
      (stalkModule_germ_smul (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        (genericFiberChartOpens f hV hU e hx) hmem _ _)
  refine Eq.trans (congrArg (fun v =>
    stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ v)
      (h1.trans key)) ?_
  refine Eq.trans (stalkPullbackFiberιAddEquiv_stalkMap_smul f
    (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
    (inv (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.stalkMap x₀)
      (ringGerm (f.fiber (genericPoint Y)).toRingedSpace x₀
        (genericFiberChartOpens f hV hU e hx) hmem
        (generatorRatio _ (genericFiberChartOpens f hV hU e hx)
          (genericFiberChartGenerator f hV hU e hx L hL genU)
          (genericFiberTrivGenerator f L hgen (genericFiberChartOpens f hV hU e hx))))) _) ?_
  have hlast : stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
        (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
          ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
          (genericFiberChartOpens f hV hU e hx) hmem
          (genericFiberChartGenerator f hV hU e hx L hL genU).val) =
      grpGerm X.toRingedSpace L.val
        (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀) U hxU genU.val :=
    (congrArg (fun v =>
        stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ v)
      h2).trans (stalkPullbackFiberιAddEquiv_grpGerm f
        (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ U hxU genU.val)
  rw [hlast]

include hV hU e hx hL in
/-- **The transported germ of the trivializing section is a multiple of the chart generator.**
The existential form of
`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator`, which is what a consumer that
needs only *some* scalar asks for. -/
theorem exists_smul_eq_stalkPullbackFiberιAddEquiv_genericFiberTrivGenerator
    (x₀ : f.fiber (genericPoint Y))
    (hxU : ((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀ ∈ U) :
    ∃ c : ringStalk X.toRingedSpace
        (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀),
      stalkPullbackFiberιAddEquiv f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀
          (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
            ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
            ⊤ (Opens.mem_top x₀) (genericFiberTrivGenerator f L hgen ⊤).val) =
        c • grpGerm X.toRingedSpace L.val
          (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀) U hxU genU.val :=
  ⟨_, eq_smul_grpGerm_genericFiberTrivGenerator f hV hU e hx L hgen hL genU x₀ hxU⟩

/-- **The germ of the trivializing section generates the stalk of `ℒ_ξ`.** The generator
`AlgebraicGeometry.genericFiberTrivGenerator` on `⊤` is the section
`Stacks.SheafOfModules.exists_sections_forall_span_eq_top_grpGerm_of_isTrivial` produces, so its
germ generates at every point of the generic fibre. -/
theorem span_eq_top_grpGerm_genericFiberTrivGenerator (x₀ : f.fiber (genericPoint Y)) :
    Submodule.span (ringStalk (f.fiber (genericPoint Y)).toRingedSpace x₀)
      {grpGerm (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
        ⊤ (Opens.mem_top x₀) (genericFiberTrivGenerator f L hgen ⊤).val} = ⊤ := by
  refine span_eq_top_grpGerm_of_isIso_unitHomEquiv_symm
    ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L)
    (((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).unitHomEquiv
      hgen.some.inv) ?_ x₀
  exact Eq.mpr (congrArg (fun φ => IsIso φ) (Equiv.symm_apply_apply _ hgen.some.inv))
    (CategoryTheory.Iso.isIso_inv hgen.some)

include hV hU e hx hgen hL in
/-- **The generator of the generic stalk that the first paragraph of [Stacks, Tag 0BD7] builds
is a multiple of the germ of a chart generator.** This packages
`AlgebraicGeometry.exists_smul_eq_stalkPullbackFiberιAddEquiv_genericFiberTrivGenerator` with the
generation property, so that the element produced is a generator of the stalk of `ℒ` at the image
of `x₀` and at the same time visibly a multiple of the germ of `genU` there. -/
theorem exists_span_eq_top_and_eq_smul_grpGerm_of_isTrivial_genericFiber
    (x₀ : f.fiber (genericPoint Y))
    (hxU : ((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀ ∈ U) :
    ∃ (m : grpStalk X.toRingedSpace L.val
        (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀))
      (c : ringStalk X.toRingedSpace
        (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀)),
      Submodule.span (ringStalk X.toRingedSpace
          (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀)) {m} = ⊤ ∧
        m = c • grpGerm X.toRingedSpace L.val
          (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀) U hxU genU.val :=
  let ⟨c, hc⟩ := exists_smul_eq_stalkPullbackFiberιAddEquiv_genericFiberTrivGenerator
    f hV hU e hx L hgen hL genU x₀ hxU
  ⟨_, c, span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv f
    (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ _
    (span_eq_top_grpGerm_genericFiberTrivGenerator f L hgen x₀), hc⟩

end AlgebraicGeometry

end
