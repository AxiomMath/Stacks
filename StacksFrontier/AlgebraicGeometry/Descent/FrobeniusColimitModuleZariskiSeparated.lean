module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackTransport
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidStack
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverZariskiPrecoverage

/-!
# Frobenius-colimit modules are separated for the Zariski families of the big h site

The Zariski stack condition condition (1) of Stacks 0EX9 asks of Stacks Tag 0EXE rests, after the
reduction of
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitVectorBundleGroupoidZariski.lean`, on the
stack condition for `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at a single Zariski
family of the big h category over `S`. That condition has a separated half — the canonical
descent functor is faithful — and an effectivity half. This file proves the separated half, for
every Zariski family of the site and with the index type of the family in any universe.

Nothing in the development concluded anything about descent for
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor`: it occurred only as a hypothesis. This
is the first proved half.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage` and
  `AlgebraicGeometry.iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage`: a Zariski family
  of the big h category over `S` has underlying open immersions whose images cover.
* `AlgebraicGeometry.faithful_toDescentData_frobeniusColimitModulePseudofunctor`: **the canonical
  descent functor of the pseudofunctor of all Frobenius-colimit modules is faithful for every
  Zariski family of the big h category over `S`** — the separated half of the stack condition
  that condition (1) of Stacks 0EX9 asks for.

## Implementation notes

The content is `AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_openImmersion`, which
says that a morphism of sheaves of `colim_F 𝒪_X`-modules is determined by its images under the
transition functors of a family of open immersions whose images cover `X`; that in turn rests on
`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective` read through
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`. Both were already proved and
neither had been applied to the pseudofunctor.

What this file adds is the two passages. First, from membership of
`AlgebraicGeometry.BigHOver.zariskiPrecoverage` to the two geometric facts the content consumes:
that is `AlgebraicGeometry.BigHOver.zariskiPrecoverage_eq_comap` followed by
`Stacks.Descent.isOpenImmersion_of_mem_zariskiPrecoverage` and
`Stacks.Descent.iSup_opensRange_eq_top_of_mem_zariskiPrecoverage` on the underlying family of
morphisms of schemes. Secondly, from the transition functors to the canonical descent functor:
a morphism of descent data has a component over each member of the family, which
`CategoryTheory.Pseudofunctor.toDescentData` sends to the image of the morphism under the
transition functor of that member, so equality of the descent-data morphisms gives exactly the
hypothesis of the content. This is the same shape as
`Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top` for sheaves of
`𝒪`-modules on a scheme.

The effectivity half is not proved here, and the development does not have it: it is the gluing
of sheaves of `colim_F 𝒪_U`-modules along the family. The nearest available statements are
`Stacks.SheafOfModules.existsUnique_hom_of_over`, which glues *morphisms* over an open cover for
an arbitrary sheaf of rings on a space, and
`CategoryTheory.SiteGlueing.canonicalModuleEquivalence`, which is effective descent over *all*
slices of a site rather than along a covering family.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe t u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

section Precoverage

variable {ι : Type t} {U : BigHOver B S hS} {X : ι → BigHOver B S hS}

/-- The underlying family of morphisms of schemes of a Zariski family of the big h category over
`S` lies in the Zariski precoverage of schemes.  This is
`AlgebraicGeometry.BigHOver.zariskiPrecoverage_eq_comap` with
`CategoryTheory.Presieve.map_ofArrows`. -/
theorem ofArrows_toScheme_mem_zariskiPrecoverage {f : ∀ i, X i ⟶ U}
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) :
    Presieve.ofArrows (fun i ↦ (BigHOver.toScheme B S hS).obj (X i))
        (fun i ↦ (BigHOver.toScheme B S hS).map (f i)) ∈
      Scheme.zariskiPrecoverage.{u} ((BigHOver.toScheme B S hS).obj U) := by
  rw [BigHOver.zariskiPrecoverage_eq_comap] at hf
  simpa [Presieve.map_ofArrows] using hf

/-- Every member of a Zariski family of the big h category over `S` is an open immersion of
schemes. -/
theorem isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage {f : ∀ i, X i ⟶ U}
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) (i : ι) :
    IsOpenImmersion ((BigHOver.toScheme B S hS).map (f i)) :=
  Stacks.Descent.isOpenImmersion_of_mem_zariskiPrecoverage
    (ofArrows_toScheme_mem_zariskiPrecoverage B S hS hf) i

/-- The images of a Zariski family of the big h category over `S` cover the underlying scheme of
the base. -/
theorem iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage {f : ∀ i, X i ⟶ U}
    [∀ i, IsOpenImmersion ((BigHOver.toScheme B S hS).map (f i))]
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) :
    ⨆ i, ((BigHOver.toScheme B S hS).map (f i)).opensRange = ⊤ :=
  Stacks.Descent.iSup_opensRange_eq_top_of_mem_zariskiPrecoverage
    (ofArrows_toScheme_mem_zariskiPrecoverage B S hS hf)

end Precoverage

include hpS

/-- **The canonical descent functor of the pseudofunctor of all Frobenius-colimit modules is
faithful for every Zariski family of the big h category over `S`.**

This is the separated half of the stack condition that condition (1) of Stacks 0EX9 asks of
Stacks Tag 0EXE; the effectivity half, the gluing of sheaves of `colim_F 𝒪_U`-modules along the
family, is not proved here.

A morphism of descent data has one component over each member of the family, and
`CategoryTheory.Pseudofunctor.toDescentData` sends a morphism of sheaves of modules to its images
under the transition functors; so equality of the images is exactly the hypothesis of
`AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_openImmersion`, whose two geometric
inputs come from `AlgebraicGeometry.isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage` and
`AlgebraicGeometry.iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage`. -/
theorem faithful_toDescentData_frobeniusColimitModulePseudofunctor {ι : Type t}
    {U : BigHOver B S hS} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) :
    ((frobeniusColimitModulePseudofunctor B S hS p hpS).toDescentData f).Faithful where
  map_injective {_M _N φ ψ} h := by
    have : ∀ i, IsOpenImmersion ((BigHOver.toScheme B S hS).map (f i)) :=
      isOpenImmersion_of_mem_bigHOver_zariskiPrecoverage B S hS hf
    exact frobeniusColimitPullback_map_injective_of_openImmersion p
      ((BigHOver.toScheme B S hS).obj U) (isInCharacteristic_bigHOver B S hS p hpS U)
      (fun i ↦ (BigHOver.toScheme B S hS).map (f i))
      (fun i ↦ isInCharacteristic_bigHOver B S hS p hpS (X i))
      (iSup_opensRange_eq_top_of_mem_bigHOver_zariskiPrecoverage B S hS hf) φ ψ
      fun i ↦ congrArg (fun θ ↦ θ.hom i) h

end AlgebraicGeometry

end
