module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# The higher direct images of the associated module along `S_étale ⟶ S_Zar` vanish

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module, and let `Fᵃ` be the associated module
of [Stacks, Tag 03DU], read as an abelian sheaf on the small étale site of `S`.  This file proves
that the higher direct images of `Fᵃ` along the comparison `ε : S_étale ⟶ S_Zar` vanish, which is
the hypothesis of the Leray collapse
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` and the last input of
[Stacks, Tag 03P2] other than the identification `ε_* Fᵃ ≅ ℱ`.

Everything is in place: the affine opens of `S` form a basis, an affine open read in the small
étale site is an affine object of it — definitionally — and the higher cohomology of `Fᵃ` at an
affine object vanishes by
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`.  The criterion that turns that
into the vanishing of the higher direct images is
`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`.

## Main definitions

* `AlgebraicGeometry.affineOpensPresieve`: the affine opens contained in a given open, as a
  presieve.

## Main results

* `AlgebraicGeometry.generate_affineOpensPresieve_mem`: it generates a covering sieve.
* `AlgebraicGeometry.mem_smallEtaleAffineObjects_opensToEtale`: an affine open is an affine
  object of the small étale site.
* `AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale`: **the vanishing.**

## Implementation notes

The covering family is a *presieve* and not a sieve, which is why the criterion is applied in
its presieve form: an open subset of an affine open need not be affine, so the affine opens
below a given open are not downward closed.

`AlgebraicGeometry.opensToEtale` is the functor to use, with
`AlgebraicGeometry.opensToEtale_isContinuous` its continuity instance, stated for exactly the
two topologies the acyclicity statement is about.  The other candidates in the library are
functors into *other* sites — `AlgebraicGeometry.SmallEtale.opensToSmallEtale` lands in the
size-bounded small étale site `AlgebraicGeometry.SmallEtale`, not in
`AlgebraicGeometry.Scheme.Etale` — and do not compose with the acyclicity.

The `Ext` universe of `CategoryTheory.Sheaf.H'` is the morphism universe `u` of the small étale
site on both sides of the step: in the acyclicity statement because the instance priority is
flipped there, and here because
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections` asks for
`CategoryTheory.HasExt.{u}` outright, so no second flip is needed.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImageOnACover

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- The affine opens of `S` contained in a given open, as a presieve on that open.  Not a
sieve: an open subset of an affine open need not be affine. -/
public def affineOpensPresieve (V : S.Opens) : Presieve V :=
  fun W _ ↦ IsAffineOpen W

/-- **The affine opens below an open generate a covering sieve of it**, the affine opens of a
scheme being a basis of its topology. -/
public theorem generate_affineOpensPresieve_mem (V : S.Opens) :
    Sieve.generate (affineOpensPresieve S V) ∈ Opens.grothendieckTopology S V := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨W, homOfLE hWV, ⟨W, 𝟙 W, homOfLE hWV, hW, by simp⟩, hxW⟩

/-- **An affine open of `S`, read as an object of the small étale site, has affine total
space.**  An open immersion is étale and the total space of the resulting object is the open
subscheme itself, so this is `AlgebraicGeometry.IsAffineOpen` unfolded. -/
public theorem mem_smallEtaleAffineObjects_opensToEtale {V : S.Opens} (hV : IsAffineOpen V) :
    (opensToEtale S).obj V ∈ smallEtaleAffineObjects S := hV

/-- **The higher direct images of `Fᵃ` along the comparison `ε : S_étale ⟶ S_Zar` vanish.**
This is the hypothesis of the Leray collapse of [Stacks, Tag 03P2] in the case
`𝒞 = S_étale`. -/
public theorem isZero_rightDerived_pushforward_opensToEtale (F : S.Modules)
    [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero ((((opensToEtale S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology S) (Scheme.smallEtaleTopology S)).rightDerived p).obj
        (((Scheme.Etale.forget S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S)).obj
            (fpqcOverAssociatedSheaf S F))) := by
  refine isZero_rightDerived_pushforward_of_presieve (opensToEtale S) p _ (fun V ↦ ?_)
  refine ⟨affineOpensPresieve S V, generate_affineOpensPresieve_mem S V, fun W g hg ↦ ?_⟩
  exact (isZero_sheafCohomology_succ_smallEtaleAffine S F ((opensToEtale S).obj W)
      (mem_smallEtaleAffineObjects_opensToEtale S hg) p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (Scheme.smallEtaleTopology S) _ p ((opensToEtale S).obj W)).symm

end AlgebraicGeometry

end
