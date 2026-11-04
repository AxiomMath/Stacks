module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorAction
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Restricting a regular meromorphic section to an irreducible component

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `s` a regular meromorphic section of
`L`. Part (3) of [Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) says that `s`
restricts to a *regular* meromorphic section on each irreducible component `X_i` of `X`, taken
with its reduced induced structure. The source proves this in one sentence, from two lemmas on
divisors: by [Tag 02OU](https://stacks.math.columbia.edu/tag/02OU) the pullbacks `s_i` are
defined, and by [Tag 02OY](https://stacks.math.columbia.edu/tag/02OY) they are regular.

This file supplies the first of those two steps, and the local description of `s` near a
generic point which the second one rests on.

## Main results

* `Stacks.Chow.subschemeι_genericPoint_mem_genericPoints`: the generic point of an integral
  closed subscheme whose support is an irreducible component of `X` maps to a generic point of
  an irreducible component of `X`.
* `Stacks.Chow.pullbacksMeromorphicSections_subschemeι` and
  `Stacks.Chow.pullbacksMeromorphicSections_irreducibleComponent`: consequently pullbacks of
  meromorphic functions are defined along the inclusion of such a subscheme, and in particular
  along the inclusion of an irreducible component with its reduced induced structure. This is
  the appeal to Tag 02OU in the proof of part (3): it is what makes the restriction `s_i` exist.
* `Stacks.Chow.exists_eq_toMeromorphicSectionSheafAsModule_of_isGenericPoint`: **near the
  generic point of an irreducible component a regular meromorphic section of an invertible
  module is an ordinary section.** Explicitly, there is an open neighbourhood `W` of that
  generic point and a `t ∈ L(W)` whose image in `K_X(L)(W)` is `s|_W`.

## Implementation notes

Irreducible components carrying their reduced induced structure are presented, as everywhere
else in the Chow development, as an ideal sheaf `W : X.IdealSheafData` with
`IsIntegral W.subscheme` whose support is the component; the canonical such ideal is the
vanishing ideal of the component, and `isIntegral_subscheme_vanishingIdeal_of_isIrreducible`
(in the namespace `Stacks.AlgebraicGeometry.IrreducibleDevissage`) supplies the integrality. Tag
02OU is then applied in its integral-source form,
`AlgebraicGeometry.pullbacksMeromorphicSections_of_isIntegral`, whose hypothesis is exactly that
the generic point of the source lands on a generic point of the target.

The last result is the generic-point sharpening of
[Tag 02P2](https://stacks.math.columbia.edu/tag/02P2). The exceptional subset
`AlgebraicGeometry.denominatorIdealBadLocus` of that tag is closed and nowhere dense, and the
generic point of an irreducible component of a locally Noetherian scheme avoids every such
subset; since that subset contains the support of `𝒪_X / I` for `I` the ideal of denominators
of `s`, the stalk of `I` at the generic point is the whole local ring. A denominator with germ
`1` agrees with `1` on a smaller neighbourhood, and the denominator rule
(`AlgebraicGeometry.exists_unitStalkLinearMap_denominatorIdealι_eq_iff`) turns that into the
required numerator. Only invertibility of `L` — through the closedness of the exceptional
subset — and local Noetherianness of `X` are used; the δ-dimension of the component plays no
part, so the statement is made for every irreducible component rather than for those of
δ-dimension `k + 1`.

No Stacks tag attribute is attached here: the results below are the Tag 02OU half of part (3)
and the local description the Tag 02OY half rests on, not part (3) itself. Tag 02OY part (2) is
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible` in the
generality of the source, and
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection` for an integral
source; part (3) is assembled from it and the results below in
`Stacks.Chow.isRegularMeromorphicSection_pullbackMeromorphicSection_subschemeι` of
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullbackRegular` and in
`Stacks.Chow.isRegularMeromorphicSection_componentMeromorphicSection` of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisor`, which carry the
attribute.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Topology

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Pullbacks of meromorphic functions are defined along a component -/

/-- The generic point of an integral closed subscheme whose support is an irreducible component
of `X` is carried by the inclusion to a generic point of an irreducible component of `X`. -/
theorem subschemeι_genericPoint_mem_genericPoints (W : X.IdealSheafData)
    [IsIntegral W.subscheme] (hW : (W.support : Set X) ∈ irreducibleComponents X) :
    W.subschemeι (genericPoint W.subscheme) ∈ genericPoints X := by
  simpa only [genericPoints, Set.mem_ofPred_eq,
    (Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint
      W).def] using hW

/-- **Pullbacks of meromorphic functions are defined along the inclusion of an irreducible
component.** This is the appeal to [Stacks, Tag 02OU] in the proof of part (3) of
[Stacks, Tag 02SW]: the component is integral and its generic point is a generic point of an
irreducible component of `X`, which is case (3) of that tag. -/
theorem pullbacksMeromorphicSections_subschemeι (W : X.IdealSheafData)
    [IsIntegral W.subscheme] (hW : (W.support : Set X) ∈ irreducibleComponents X) :
    PullbacksMeromorphicSections W.subschemeι.toLRSHom :=
  pullbacksMeromorphicSections_of_isIntegral W.subschemeι
    (subschemeι_genericPoint_mem_genericPoints W hW)

open Stacks.AlgebraicGeometry.IrreducibleDevissage
  (isIntegral_subscheme_vanishingIdeal_of_isIrreducible) in
/-- **Pullbacks of meromorphic functions are defined along the inclusion of an irreducible
component with its reduced induced structure.** The reduced induced structure on an irreducible
closed subset is integral, and the vanishing ideal of a closed subset is supported on it. -/
theorem pullbacksMeromorphicSections_irreducibleComponent {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    PullbacksMeromorphicSections
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι.toLRSHom :=
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩ : Closeds X)).subscheme :=
    isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hZ.1
  pullbacksMeromorphicSections_subschemeι _
    (by rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hZ)

/-! ### A regular meromorphic section is regular near a generic point -/

/-- The structure sheaf of `X` as a sheaf of rings in the form over which sheaves of modules on
`X` are indexed. -/
private noncomputable abbrev ringSh (X : Scheme.{u}) :=
  Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
    (J := Opens.grothendieckTopology X) X.sheaf

/-- Multiplication by a meromorphic section carries the unit section to the section itself. -/
private theorem meromorphicSectionMul_app_one (X : Scheme.{u}) (L : X.Modules)
    (s : MeromorphicSection X.sheaf L) (V : (Opens X)ᵒᵖ) :
    (meromorphicSectionMul X L s).val.app V (1 : (ringSh X).obj.obj V) = s.val V :=
  congrFun (congrArg Subtype.val
    ((meromorphicSectionSheafAsModule X L).unitHomEquiv.apply_symm_apply s)) V

/-- A section of the structure sheaf restricting to `1`, read in the structure sheaf regarded
as a module over itself. -/
private theorem unit_map_eq_one {X : Scheme.{u}} {U V : X.Opens} (i : U ⟶ V)
    (f : Γ(X, V)) (hf : X.presheaf.map i.op f = 1) :
    ((SheafOfModules.unit (ringSh X)).val.map i.op)
        (show ((SheafOfModules.unit (ringSh X)).val.obj (op V)) from f) =
      (1 : (ringSh X).obj.obj (op U)) := hf

/-- **Near the generic point of an irreducible component a regular meromorphic section of an
invertible module is an ordinary section.**

The generic point of an irreducible component of a locally Noetherian scheme avoids the closed
nowhere dense exceptional subset of [Stacks, Tag 02P2], which contains the support of
`𝒪_X / I` for `I` the ideal of denominators of `s`. So `I` has the whole local ring as its
stalk there, `s` has a denominator with germ `1`, and that denominator is `1` on a smaller
neighbourhood — on which `s` is therefore the image of a section of `L`. -/
theorem exists_eq_toMeromorphicSectionSheafAsModule_of_isGenericPoint (X : Scheme.{u})
    [IsLocallyNoetherian X] (L : X.Modules) (s : MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {Z : Set X} {x : X} (hZ : Z ∈ irreducibleComponents X) (hx : IsGenericPoint x Z) :
    ∃ (W : X.Opens) (_ : x ∈ W) (t : L.val.obj (op W)),
      (toMeromorphicSectionSheafAsModule X L).val.app (op W) t = s.val (op W) := by
  have hbad : x ∉ denominatorIdealBadLocus X L s :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.genericPoint_notMem_of_nowhereDense X hZ hx
      (denominatorIdealBadLocus_isClosed X L s hL)
      (denominatorIdealBadLocus_isNowhereDense X L s hL hs)
  have hι : Function.Surjective (stalkLinearMap _ _ (denominatorIdealι X L s) x) :=
    (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
      (denominatorIdealι X L s) x).2 fun h => hbad (Or.inl h)
  have hu : Function.Surjective
      (Scheme.Modules.unitStalkLinearMap x (denominatorIdealι X L s)) := by
    intro r
    obtain ⟨m, hm⟩ := hι ((Stacks.Ample.unitStalkEquiv X x).symm r)
    refine ⟨m, ?_⟩
    have hcomp : Scheme.Modules.unitStalkLinearMap x (denominatorIdealι X L s) m =
        Stacks.Ample.unitStalkEquiv X x
          (stalkLinearMap _ _ (denominatorIdealι X L s) x m) := rfl
    rw [hcomp, hm, LinearEquiv.apply_symm_apply]
  obtain ⟨m, hm⟩ := hu 1
  obtain ⟨V, hxV, f, hf, t, ht⟩ :=
    (exists_unitStalkLinearMap_denominatorIdealι_eq_iff X L s x 1).mp ⟨m, hm⟩
  have hf1 : X.presheaf.germ V x hxV f = X.presheaf.germ V x hxV 1 := by rw [hf, map_one]
  obtain ⟨W, hxW, i, j, hij⟩ := X.presheaf.germ_eq x hxV hxV f 1 hf1
  have hfW : X.presheaf.map i.op f = 1 := by rw [hij, map_one]
  refine ⟨W, hxW, L.val.map i.op t, ?_⟩
  have hnat1 := PresheafOfModules.naturality_apply (meromorphicSectionMul X L s).val i.op f
  have hnat2 := PresheafOfModules.naturality_apply
    (toMeromorphicSectionSheafAsModule X L).val i.op t
  rw [hnat2, ← ht, ← hnat1, unit_map_eq_one i f hfW, meromorphicSectionMul_app_one]

end Stacks.Chow

end
