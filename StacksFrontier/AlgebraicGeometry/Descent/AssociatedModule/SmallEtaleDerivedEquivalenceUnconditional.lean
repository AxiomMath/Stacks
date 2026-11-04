module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence

/-!
# The derived equivalence of the small étale site, with essential surjectivity discharged

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence` states its
results on the derived categories of the abelian categories of quasi-coherent modules over the
hypothesis
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`, essential surjectivity of
`𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of `S_étale`, which is Stacks 03DX (2) at `τ = étale`.

That hypothesis is **no longer a hypothesis**: it is the theorem
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`, proved with no hypothesis
in `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean`.  The two
modules do not see each other — `SmallEtaleDerivedEquivalence` imports
`SmallEtaleEssentialImage`, where the predicate is *defined*, and not `SmallEtaleCounit`, where it
is *proved* — so a consumer of either alone still has to supply it.  This file imports both, so
downstream of it every statement of `SmallEtaleDerivedEquivalence` can be applied to
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` by name; the statements of
that file are not restated here.

## Main results

* `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleDerivedQcoh'`: **Stacks 03DX (2) at
  `τ = étale`, derived** — `D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))` is an equivalence, with no
  hypothesis beyond the instances that make the two sides abelian with derived categories.

## Implementation notes

Nothing here is a new mathematical step: the statement is its counterpart in
`SmallEtaleDerivedEquivalence` applied to
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`.  It is named rather than
left to its consumers because the functor it speaks of,
`AlgebraicGeometry.SmallEtale.associatedModuleDerivedQcoh`, *takes* the essential-surjectivity
witness as an argument, so the discharged form is a different functor expression from the
conditional one and cannot be reached by supplying an argument at the use site.  The primed name
is in the style of `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'` in
`SmallEtaleCounit`.

The instance arguments that survive are not residues of Stacks 03DX (2): they are the existence
of the derived categories of the two abelian categories of quasi-coherent modules.  The
weak-Serre closure making `QCoh(S_étale, 𝒪)` abelian (Stacks 06VE (5), (10) at `τ = étale`) is
found by instance search, from
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentWeakSerre.lean`.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

open Stacks.DerivedQCoh

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derived equivalence of the abelian categories of quasi-coherent modules -/

section Abelian

variable [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (qcohOnSite B S hS).FullSubcategory]

/-- **Stacks 03DX (2) at `τ = étale`, derived, with no hypothesis.**  `ε^*` induces an equivalence
`D(QCoh(𝒪_S)) ⥤ D(QCoh(S_étale, 𝒪))` of the derived categories of the abelian categories of
quasi-coherent modules. -/
public theorem isEquivalence_associatedModuleDerivedQcoh' :
    (associatedModuleDerivedQcoh.{w} B S hS
      (quasicoherentIsEssImageAssociatedModule B S hS)).IsEquivalence :=
  isEquivalence_associatedModuleDerivedQcoh.{w} B S hS
    (quasicoherentIsEssImageAssociatedModule B S hS)

end Abelian

end AlgebraicGeometry.SmallEtale

end
