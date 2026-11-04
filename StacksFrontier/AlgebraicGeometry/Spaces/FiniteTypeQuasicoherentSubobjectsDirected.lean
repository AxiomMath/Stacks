module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The finite type quasi-coherent submodules of a quasi-coherent module form a directed system

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `G` be
a quasi-coherent `𝒪_F`-module.  This file proves **the directedness assertion of Stacks 0829**:
the quasi-coherent submodules of `G` which are of finite type form a directed system.

It is `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobject_isFiltered`, which uses two
theorems of this tree: Descent, Proposition 03DX (2) for the small étale site of an algebraic
space, which is `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, and
closure of quasi-coherence under cokernels, which is
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`.

## Main results

* `AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`: **the directedness
  assertion of Stacks 0829**, with no hypothesis.
* `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9`: the colimit
  assertion of Stacks 0829 over Stacks 07V9 alone.

## Implementation notes

The directedness assertion is proved for an arbitrary algebraic space and an arbitrary
quasi-coherent module, where Stacks 0829 states it for a quasi-compact and quasi-separated
algebraic space.  The source's two hypotheses are used only in its proof of the colimit
assertion, through Stacks 07V9; the directedness argument — the image in `G` of the direct sum
of two finite type quasi-coherent submodules is again one — needs neither.  So the statement
below is a generalization of the source's and not a weakening of it.

The colimit assertion is *not* proved here.  Its one remaining input is Stacks 07V9, that a
quasi-coherent module on a quasi-compact and quasi-separated algebraic space is a filtered
colimit of finitely presented ones, which is
`AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite` in a module which
imports this one; it is carried as the hypothesis `h07V9`, in the spelling of
`AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone`.  Only the
directedness assertion therefore carries a `stacks` attribute, and its clause records that
scope.

The module universe is the universe `u` of the schemes; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects` for why it is not free.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The directedness assertion of Stacks 0829.**  The quasi-coherent submodules of finite type
of a quasi-coherent `𝒪_F`-module form a directed system: the image in the module of the direct
sum of two of them is a quasi-coherent submodule of finite type containing both.

Stacks 0829 states this for a quasi-compact and quasi-separated algebraic space; those two
hypotheses enter only its colimit assertion, through Stacks 07V9, so the statement here is for
an arbitrary algebraic space. -/
@[stacks 0829 "directedness, for an arbitrary algebraic space", sga "3 VIB 11.10" "partial"]
theorem isFiltered_finiteTypeQuasicoherentSubobject (G : Modules.{u, u} B S hS F hF)
    [G.IsQuasicoherentOnSite] :
    IsFiltered (FiniteTypeQuasicoherentSubobject B S hS F hF G) :=
  finiteTypeQuasicoherentSubobject_isFiltered B S hS F hF G

/-- **The colimit assertion of Stacks 0829, over Stacks 07V9 alone.**  A quasi-coherent
`𝒪_F`-module on a quasi-compact and quasi-separated algebraic space is the colimit of the
canonical diagram of its finite type quasi-coherent submodules.

This is `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone`.  **No
`stacks` attribute is carried**: `h07V9` is Stacks 07V9, which is proved only in a module that
imports this one. -/
noncomputable def isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (h07V9 : IsQuasiCompactSpace B S hS F → IsAbsolutelyQuasiSeparated B S hS hZ F →
      ∀ G : Modules.{u, u} B S hS F hF, G.IsQuasicoherentOnSite →
        ∃ (I : Type u) (inst : SmallCategory I),
          let _ := inst
          ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS F hF)
            (φ : D ⟶ (Functor.const I).obj G),
            (∀ i, (D.obj i).IsFinitePresentationOnSite) ∧
              Nonempty (IsColimit (Cocone.mk G φ)))
    (G : Modules.{u, u} B S hS F hF) [G.IsQuasicoherentOnSite] :
    IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF G) :=
  isColimit_finiteTypeQuasicoherentSubobjectCocone B S hS F hF hZ hqc hqs h07V9 G

end AlgebraicGeometry.Space

end
