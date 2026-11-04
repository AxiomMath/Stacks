module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict

/-!
# The nonvanishing locus of the pullback of a local section

For a morphism of schemes `i : X' ⟶ X`, an `𝒪_X`-module `M` and a section `u` of `M` over an open
`W` of `X`, the pullback `i^* u` — the image of `u` under the unit of `i^* ⊣ i_*`, a section of
`i^* M` over `i⁻¹ W` — fails to vanish at `x'` exactly when `u` fails to vanish at `i x'`.

This is [Stacks, Tag 0H78] over an open. The global case is
`Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff`, and the proof is the same: the
stalk of `i^* M` at `x'` is `𝒪_{X',x'} ⊗ M_{i x'}`, the germ of `i^* u` is `1 ⊗ u_{i x'}`, and an
element `m` of a module over a local ring lies in `𝔪 · M` exactly when `1 ⊗ m` lies in
`𝔪' · (B ⊗ M)` for a local homomorphism to `B`.

## Main results

* `Stacks.AmpleThickeningAscent.germ_pullbackUnit_notMem_maximalSmul_iff`: the pointwise
  statement.
* `Stacks.AmpleThickeningAscent.nonvanishingLocusOn_pullbackUnit`: the nonvanishing locus of
  `i^* u` is the preimage of that of `u`.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.NonvanishingPullback
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleThickeningAscent

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (M : X.Modules)

/-- **The pullback of a section over an open** `W`, a section of `i^* M` over `i⁻¹ W`. -/
noncomputable def pullbackSection {W : X.Opens} (u : Γ(M, W)) :
    Γ(pullbackModule i M, i ⁻¹ᵁ W) :=
  Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom M (op W) u

/-- The pullback of sections is semilinear over `i^♯ = i.app`. -/
theorem pullbackSection_smul {W : X.Opens} (a : Γ(X, W)) (u : Γ(M, W)) :
    pullbackSection i M (a • u) = i.app W a • pullbackSection i M u :=
  Stacks.RingedSpace.pullbackUnit_smul i.toLRSHom.toShHom M (op W) a u

/-- The pullback of sections commutes with restriction. -/
theorem pullbackSection_res {W W' : X.Opens} (h : W' ≤ W) (u : Γ(M, W)) :
    (pullbackModule i M).presheaf.map (homOfLE (i.preimage_mono h)).op (pullbackSection i M u) =
      pullbackSection i M (M.presheaf.map (homOfLE h).op u) :=
  Stacks.RingedSpace.pullbackUnit_restrict i.toLRSHom.toShHom M (homOfLE h).op u

/-- **Stacks Tag 0H78 over an open, pointwise.** -/
theorem germ_pullbackSection_mem_maximalSmul_iff {W : X.Opens} (u : Γ(M, W)) (x' : X')
    (hx' : x' ∈ i ⁻¹ᵁ W) :
    (pullbackModule i M).presheaf.germ (i ⁻¹ᵁ W) x' hx' (pullbackSection i M u) ∈
        Stacks.ModuleStalk.maximalSmul (pullbackModule i M) x' ↔
      M.presheaf.germ W (i.base x') hx' u ∈ Stacks.ModuleStalk.maximalSmul M (i.base x') := by
  refine Iff.symm ?_
  refine Iff.trans (mem_maximalSmul_iff M (i.base x') _) ?_
  refine Iff.trans ?_ (mem_maximalSmul_iff (pullbackModule i M) x' _).symm
  refine Iff.trans
    (mem_maximalIdeal_smul_iff_one_tmul
      (instAlg := Stacks.PullbackTensorIso.commStalkAlgebra i.toLRSHom.toShHom x')
      (instLoc := isLocalHom_commStalkRingMap i x')
      (instMod := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val
        (i.base x'))
      ((M.presheaf.germ W (i.base x') hx').hom u)) ?_
  refine Iff.trans
    (mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.PullbackTensorIso.pullbackStalkEquiv i.toLRSHom.toShHom x' M) _) ?_
  exact Iff.of_eq (congrArg (fun z => z ∈
    IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      X'.toRingedSpace x') • ⊤)
    (Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul i.toLRSHom.toShHom x' M W hx' u))

/-- **Stacks Tag 0H78 over an open.** The nonvanishing locus of `i^* u` over `i⁻¹ W` is the
preimage of the nonvanishing locus of `u` over `W`. -/
theorem nonvanishingLocusOn_pullbackSection {W : X.Opens} (u : Γ(M, W)) :
    nonvanishingLocusOn (pullbackModule i M) (i ⁻¹ᵁ W)
        (pullbackSection i M u) = i.base ⁻¹' nonvanishingLocusOn M W u := by
  ext x'
  exact exists_congr fun hx' =>
    not_congr (germ_pullbackSection_mem_maximalSmul_iff i M u x' hx')

end Stacks.AmpleThickeningAscent

end
