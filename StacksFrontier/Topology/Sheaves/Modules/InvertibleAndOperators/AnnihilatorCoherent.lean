module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.AnnihilatorStalk

/-!
# Coherence of the annihilator of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and let `F` be an `𝒪_X`-module. If both `𝒪_X` and `F` are
coherent, then the annihilator `Ann_{𝒪_X}(F)` of `F` is coherent.

The annihilator is the subsheaf of `𝒪_X` of
`Stacks.SheafOfModules.annihilatorSheaf`, and the proof is the one of the source: the
annihilator is the kernel of the scalar action `𝒪_X ⟶ SheafHom(F, F)`, the internal
endomorphism sheaf is coherent because `F` is coherent and hence of finite presentation, and
the kernel of a morphism of coherent modules is coherent.

## Main results

* `Stacks.SheafOfModules.isCoherent_internalSheafHom_obj`: the internal hom of two
  `𝒪_X`-modules is coherent when the source is of finite presentation and the target is
  coherent.
* `Stacks.SheafOfModules.isCoherent_annihilatorSheaf`: the annihilator of a coherent module
  over a coherent structure sheaf is coherent.

## Implementation notes

The internal endomorphism sheaf is the one packaged as a `SheafHom` by
`Stacks.SheafOfModules.internalSheafHom`, whose underlying module is the internal-hom presheaf
of Stacks 03EM; that is the same module as `Stacks.SheafOfModules.sheafHom`, so the coherence
statement of Stacks 01CQ applies to it directly.

Coherence of `F` is upgraded to finite presentation by Stacks 01BZ
(`Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation`), which is where coherence of the
structure sheaf is used a first time; it is used a second time as coherence of the source of
the scalar action.

The coherence predicate is `Stacks.SheafOfModules.IsCoherent`, the one carrying the Stacks 01BV
attribute.

## References

* [Stacks Project, Tag 0H2L](https://stacks.math.columbia.edu/tag/0H2L)
* [Stacks Project, Tag 0H2H](https://stacks.math.columbia.edu/tag/0H2H)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01BZ](https://stacks.math.columbia.edu/tag/01BZ)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

variable (X : RingedSpace.{u, u})

/-- The internal endomorphism sheaf of Stacks 01CO is coherent as soon as its source is of
finite presentation and its target is coherent: its underlying module is the internal-hom
presheaf, which is the module `Stacks.SheafOfModules.sheafHom` of Stacks 01CQ. -/
theorem isCoherent_internalSheafHom_obj (F G : SheafOfModules.{u} (structureSheafRing X))
    [hF : F.IsFinitePresentation] [hG : IsCoherent G] :
    IsCoherent (R := structureSheafRing X) (internalSheafHom X.sheaf F G).obj :=
  @sheafHom_isCoherent X.carrier X.sheaf.obj (structureSheafRing X).property F G hF hG

/-- **Stacks Project, Tag 0H2L.** If the structure sheaf of a ringed space and an `𝒪_X`-module
`F` are coherent, then the annihilator of `F` is coherent. -/
@[stacks 0H2L]
theorem isCoherent_annihilatorSheaf (F : SheafOfModules.{u} (structureSheafRing X))
    [IsCoherent (SheafOfModules.unit (structureSheafRing X))] [IsCoherent F] :
    IsCoherent (annihilatorSheaf X F).toSheafOfModules := by
  have : F.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation (structureSheafRing X) F).mp inferInstance
  have : IsCoherent (R := structureSheafRing X) (internalSheafHom X.sheaf F F).obj :=
    isCoherent_internalSheafHom_obj X F F
  exact (coherentModules (structureSheafRing X)).prop_of_iso
    (((annihilatorSheafIsKernel X F (internalSheafHom X.sheaf F F)).conePointUniqueUpToIso
      (kernelIsKernel (scalarAction X F (internalSheafHom X.sheaf F F)))).symm)
    (isCoherent_kernel (scalarAction X F (internalSheafHom X.sheaf F F)))

end Stacks.SheafOfModules
