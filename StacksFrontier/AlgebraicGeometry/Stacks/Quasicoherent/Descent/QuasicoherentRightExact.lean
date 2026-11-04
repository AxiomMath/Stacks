module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize

/-!
# Right exactness of the inclusion of the quasi-coherent modules

Stacks 06WV (3) says that the inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` is right exact, and the source
derives it from clause (4) — that `QCoh(𝒪_𝒳)` has colimits and they agree with the colimits of
all modules — exactly as Homology, Lemma 010N derives right exactness of a functor from its
commuting with colimits.  Right exactness of an additive functor between categories with finite
colimits is `CategoryTheory.Limits.PreservesFiniteColimits`, so the clause is the finite-shape
case of clause (4) together with the existence of those finite colimits.

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize` proves
clause (4) at the big fppf site of a scheme and at the associated fppf site of a category
fibred in groupoids, in both cases over the closure of quasi-coherence under colimits.  This
file reads off the finite-shape consequence at both sites, and assembles the big-fppf one over
the three named statements the library still owes, so that the residue of the clause is a single
closed implication rather than a chain of conditional results in three files.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasFiniteColimits_quasicoherentOnSite` and
  `AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_quasicoherentOnSite_ι`:
  **Stacks 06WV (3) at the big fppf site of a scheme**, over the closure of quasi-coherence
  under colimits — the quasi-coherent modules have finite colimits and the inclusion into all
  module sheaves preserves them.
* `AlgebraicGeometry.FibredSite.hasFiniteColimits_quasicoherentModules` and
  `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion`: the same at
  the associated fppf site of an essentially small category fibred in groupoids, which is the
  site Stacks 06WV (3) is stated for.
* `AlgebraicGeometry.BigFppfOver.closedUnderColimitsOfSize_isQuasicoherentOnSite_of_descent`
  and `AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_quasicoherentOnSite_ι_of_descent`:
  the clause at the big fppf site over exactly three named statements, namely Stacks 03DV,
  Stacks 03DX (1) and Stacks 0GN7 in the form
  `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`.

## Implementation notes

Nothing here carries a `stacks` attribute.  Every statement is conditional, on the closure of
quasi-coherence under colimits or on the three statements listed above, and a tag would report
the clause as covered when what is proved is the implication.

Why the finiteness of the shape does not make the clause unconditional, which is the question
this file was written to settle.  Closure of quasi-coherence under colimits of a *fixed* shape
is proved in `QuasicoherentColimitsOfSize` by transfer along `𝓕 ↦ 𝓕^a`, and the alternative —
propagating `SheafOfModules.HasGlobalPresentation` along the colimit, which is how the tensor
clause Stacks 06WV (5) was proved — needs, for a cokernel, the generators of the source lifted
along the presentation of the target: the hypothesis `hl` of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`.  Those generators
lift one at a time, each on its own covering, and the family to be refined is the *generating
index set of the source's presentation*, which `SheafOfModules.IsQuasicoherentOnSite` leaves
arbitrary.  The shape of the colimit never bounds that index set, so the finiteness of
`CategoryTheory.Limits.PreservesFiniteColimits` does not reach the obstruction:
`CategoryTheory.Limits.WalkingParallelPair`, the shape of the cokernel clause Stacks 0GNC (3),
is as finite as a shape gets and the obstruction binds there undiminished.  Finiteness does
remove the analogous obstruction for *coproducts*, where the family to be refined is indexed by
the diagram, but a finite-coproduct closure is not by itself a finite-colimit closure.

The index universe is the universe of the site, as in `QuasicoherentColimitsOfSize`; the
finite-shape statements are universe-free, since `CategoryTheory.Limits.HasFiniteColimits` and
`CategoryTheory.Limits.PreservesFiniteColimits` quantify over shapes in `Type`.  Both are
obtained from the size-indexed forms by
`CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize` and
`CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits`.

The ambient colimits of all module sheaves, which the transfer consumes as an instance, are
found by instance synthesis over the structure sheaf of the big fppf site but not over the
structure sheaf of the associated fppf site of a fibred category; the latter is therefore
supplied explicitly from
`AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules_ringStructureSheafCore`.

## References

* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06WV (3), the existence half, at the big fppf site of `S`.**  The quasi-coherent
modules on `(Sch/S)_fppf` have finite colimits, which is what the inclusion into all module
sheaves is asserted to preserve.  This is
`AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite` restricted to the finite
shapes. -/
public theorem hasFiniteColimits_quasicoherentOnSite
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (structureSheaf B S hS)) :
    HasFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  have := hasColimitsOfSize_quasicoherentOnSite B S hS hclosed
  hasFiniteColimits_of_hasColimitsOfSize _

/-- **Stacks 06WV (3) at the big fppf site of `S`.**  The inclusion of the quasi-coherent
modules on `(Sch/S)_fppf` into all module sheaves on `(Sch/S)_fppf` preserves finite colimits,
that is, it is right exact.  The source derives the clause from clause (4), and so does this
proof: it is
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι` restricted to the
finite shapes. -/
public theorem preservesFiniteColimits_quasicoherentOnSite_ι
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (structureSheaf B S hS)) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι :=
  SheafOfModules.preservesFiniteColimits_quasicoherentOnSite_ι hclosed

/-- Closure of quasi-coherence on the big fppf site of `S` under colimits of every shape
`K : Type u`, over the three statements the library owes: Stacks 03DV, Stacks 03DX (1) and
Stacks 0GN7.

This is `AlgebraicGeometry.BigFppfOver.closedUnderColimitsOfSize_isQuasicoherentOnSite` with
its two `[Full]` and `[Faithful]` instance arguments supplied from
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`, so that the three inputs appear as
hypotheses of one statement rather than as instances to be arranged at the use site. -/
public theorem closedUnderColimitsOfSize_isQuasicoherentOnSite_of_descent
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)
    (hunit : UnitIsoOnQuasicoherent B S hS) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u} (structureSheaf B S hS) :=
  have := full_associatedModuleQcoh B S hS hunit
  have := faithful_associatedModuleQcoh B S hS hunit
  closedUnderColimitsOfSize_isQuasicoherentOnSite B S hS hF hsurj

/-- **Stacks 06WV (3) at the big fppf site of `S`, over the three statements the library
owes.**  The inclusion of the quasi-coherent modules into all module sheaves on
`(Sch/S)_fppf` is right exact as soon as Stacks 03DV, Stacks 03DX (1) and Stacks 0GN7 are
available, in the shapes `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent`,
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`.

This is the residue of the clause as one implication, and it is the form in which the three
remaining inputs can be read off and discharged one at a time. -/
public theorem preservesFiniteColimits_quasicoherentOnSite_ι_of_descent
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)
    (hunit : UnitIsoOnQuasicoherent B S hS) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι :=
  preservesFiniteColimits_quasicoherentOnSite_ι B S hS
    (closedUnderColimitsOfSize_isQuasicoherentOnSite_of_descent B S hS hF hsurj hunit)

/-- **Stacks 06WV (3), the existence half, at the big fppf site of `S`, over the three
statements the library owes.**  The companion of
`AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_quasicoherentOnSite_ι_of_descent`: the
finite colimits whose preservation that result asserts do exist. -/
public theorem hasFiniteColimits_quasicoherentOnSite_of_descent
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)
    (hunit : UnitIsoOnQuasicoherent B S hS) :
    HasFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  hasFiniteColimits_quasicoherentOnSite B S hS
    (closedUnderColimitsOfSize_isQuasicoherentOnSite_of_descent B S hS hF hsurj hunit)

end BigFppfOver

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Stacks 06WV (3), the existence half**, for the fppf topology and over the closure of
quasi-coherence under colimits: the quasi-coherent modules on the associated fppf site of an
essentially small category fibred in groupoids have finite colimits.  This is
`AlgebraicGeometry.FibredSite.hasColimitsOfSize_quasicoherentModules` restricted to the finite
shapes. -/
public theorem hasFiniteColimits_quasicoherentModules
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)) :
    HasFiniteColimits (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :=
  have := hasColimitsOfSize_quasicoherentModules B S hS p hp hclosed
  hasFiniteColimits_of_hasColimitsOfSize _

/-- **Stacks 06WV (3)**, for the fppf topology and over the closure of quasi-coherence under
colimits: the inclusion of the quasi-coherent modules on the associated fppf site of an
essentially small category fibred in groupoids into all module sheaves is right exact.  This is
the site Stacks 06WV (3) is stated for, and the clause is the finite-shape case of
`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion`, which is
Stacks 06WN (1). -/
public theorem preservesFiniteColimits_quasicoherentInclusion
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)) :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  have : HasColimitsOfSize.{u, u}
      (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :=
    hasColimits_sheafOfModules_ringStructureSheafCore B S hS p hp .fppf
  SheafOfModules.preservesFiniteColimits_quasicoherentOnSite_ι hclosed

end FibredSite

end AlgebraicGeometry

end
