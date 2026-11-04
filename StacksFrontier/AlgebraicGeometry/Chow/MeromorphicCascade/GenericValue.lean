module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent

/-!
# The generic value of a meromorphic section

Let `X` be an integral scheme with generic point `η` and let `F` be a quasi-coherent
`𝒪_X`-module. A *meromorphic section* of `F` in the sense of
[Stacks, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4) is a global section of the sheaf
`𝒦_X(F)` obtained from `F` by extension of scalars to the sheaf of total quotient rings. On an
integral scheme `𝒦_X(F)` is the constant sheaf with value the generic stalk `F_η`
([Stacks, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5) (2)), so such a section is the same
thing as an element of `F_η`. This file names that element, the *generic value* of the section,
and proves the formula characterizing it.

The two models of a meromorphic section are used side by side in this library. The order of
vanishing along a prime divisor (`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`) is defined
for an element of `F_η`, while the Stacks Project states its results for a global section of
`𝒦_X(F)`. The generic value is the passage from the second model to the first, and is what lets
those results be stated here.

## Main definitions

* `Stacks.Divisors.genericValue` — the element of `F_η` corresponding to a meromorphic section
  of `F`.

## Main results

* `Stacks.Divisors.toMeromorphicSectionStalk_genericValue` — the characterization: the image of
  the generic value under the canonical bijection `F_η → 𝒦_X(F)_η` is the germ of the section
  at `η`.
* `Stacks.Divisors.genericValue_meromorphicSectionOfSection` — the generic value of the canonical
  meromorphic image of an ordinary global section is the germ of that section at `η`.

## Implementation notes

The module structures on the two stalks `F_η` and `𝒦_X(F)_η` over the local ring `𝒪_{X, η}` are
supplied explicitly, by `Stacks.ModuleStalk.moduleStalk` and
`Stacks.Divisors.moduleStalkMeromorphicSectionSheaf`: instance search finds the first only when
the index presheaf of rings appears in the syntactic form `O ⋙ forget₂ CommRingCat RingCat`, which
it does not here. Hence the `letI` in the statement of the characterization. The generic value
itself needs no such instance, `Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk` being an
additive equivalence.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.ModuleStalk

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]

/-- **The generic value of a meromorphic section.** On an integral scheme the meromorphic sections
of a quasi-coherent module `F` are the elements of its generic stalk `F_η`; this is the element of
`F_η` attached to a global section of `𝒦_X(F)`.

It is `Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk` applied over the whole space;
`Stacks.Divisors.toMeromorphicSectionStalk_genericValue` is the characterization, and is what
should be used in place of this definition. -/
def genericValue (s : AlgebraicGeometry.MeromorphicSection X.sheaf F) :
    F.presheaf.stalk (genericPoint X) :=
  meromorphicSectionsAddEquivGenericStalk F ⊤ trivial (s.val (op ⊤))

/-- **The characterization of the generic value.** The image of the generic value of `s` under the
canonical map `F_η → 𝒦_X(F)_η` is the germ of `s` at the generic point. That map is bijective on an
integral scheme, the regular germs at `η` being units, so this determines the generic value. -/
theorem toMeromorphicSectionStalk_genericValue
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf F) :
    letI : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
        ↑((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
    toMeromorphicSectionStalk X.sheaf F (genericPoint X) (genericValue F s) =
      germ (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf F).val ⊤ (genericPoint X) trivial
        (s.val (op ⊤)) := by
  let _mFg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
  let _mKg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf F).val).stalk
        (genericPoint X)) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F (genericPoint X)
  have _hloc := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F (genericPoint X)
  have hbij : Function.Bijective (toMeromorphicSectionStalk X.sheaf F (genericPoint X)) :=
    Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
      (S := regularGerms X.sheaf (genericPoint X)) _
      fun _ hs => regularGerms_genericPoint_le_isUnit hs
  exact (AddEquiv.ofBijective
    (toMeromorphicSectionStalk X.sheaf F (genericPoint X)).toAddMonoidHom
      hbij).apply_symm_apply _

/-- The generic value of the canonical meromorphic image
(`Stacks.ChernCap42.meromorphicSectionOfSection`) of an ordinary global section `t` of `F` is the
germ of `t` at the generic point. -/
theorem genericValue_meromorphicSectionOfSection (t : Γ(F, ⊤)) :
    genericValue F (Stacks.ChernCap42.meromorphicSectionOfSection F t) =
      germ F.val ⊤ (genericPoint X) trivial t := by
  let _mFg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn F.val).stalk (genericPoint X)) := moduleStalk F.val (genericPoint X)
  let _mKg : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf F).val).stalk
        (genericPoint X)) :=
    moduleStalkMeromorphicSectionSheaf X.sheaf F (genericPoint X)
  have _hloc := isLocalizedModule_toMeromorphicSectionStalk X.sheaf F (genericPoint X)
  have hbij : Function.Bijective (toMeromorphicSectionStalk X.sheaf F (genericPoint X)) :=
    Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
      (S := regularGerms X.sheaf (genericPoint X)) _
      fun _ hs => regularGerms_genericPoint_le_isUnit hs
  refine hbij.injective ?_
  rw [toMeromorphicSectionStalk_genericValue]
  exact Stacks.ChernCap42.germ_meromorphicSectionOfSection F t (genericPoint X) ⊤ trivial

end Stacks.Divisors

end
