module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase

/-!
# The comparison of [Stacks, Tag 01XK] in a degree that is a natural number

`Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward` is defined by a sign
split on the degree `q : ℤ`: in a nonnegative degree it is the `ℕ`-indexed comparison
`Stacks.Cohomology.AffineBase.sectionsRightDerivedPushforwardIso` conjugated by
`Stacks.DerivedIndexing.rightDerivedIso`, transported along `q = (q.toNat : ℤ)`; in a negative
degree both sides vanish. No equation can be stated under that transport, so this file names
the nonnegative branch and identifies it with the comparison in degree `(n : ℤ)`.

## Main definitions

* `Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforwardOfNat`: the
  comparison of the `ℤ`-indexed derived functors in a degree that is a natural number.

## Main results

* `Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward_natCast`: in a
  degree that is a natural number, [Stacks, Tag 01XK] *is* the conjugated `ℕ`-indexed
  comparison. This is what opens the sign split in the definition, and every equation about the
  comparison in a nonnegative degree goes through it.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}}

section Comparison

variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]

/-- **The comparison in a nonnegative degree, with the degree written as a natural number.**
The `ℤ`-indexed `Functor.rightDerivedPlus` in degree `(n : ℤ)` agrees with Mathlib's `ℕ`-indexed
`Functor.rightDerived` in degree `n` by `Stacks.DerivedIndexing.rightDerivedIso`, so
`sectionsRightDerivedPushforwardIso` conjugated by that comparison on each side is the
comparison for the indexing [Stacks, Tag 01XK] is stated in.

This is the nonnegative branch of `cohomologyIsoSectionsRightDerivedPushforward`, named because
the degree there is `q.toNat` behind a transport along `q = (q.toNat : ℤ)`, which no equation can
be stated under; here the degree is a natural number and there is no transport, so
`cohomologyIsoSectionsRightDerivedPushforward_natCast` can identify the two. -/
def cohomologyIsoSectionsRightDerivedPushforwardOfNat (n : ℕ) :
    quasicoherentInclusion X ⋙
        (sectionsFunctor X ⊤).rightDerivedPlus (n : ℤ) ⋙
          ModuleCat.restrictScalars f.appTop.hom ≅
      quasicoherentInclusion X ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ) ⋙ sectionsFunctor S ⊤ :=
  Functor.isoWhiskerLeft (quasicoherentInclusion X)
      (Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X ⊤) n).symm
        (ModuleCat.restrictScalars f.appTop.hom)) ≪≫
    sectionsRightDerivedPushforwardIso f n ≪≫
    Functor.isoWhiskerLeft (quasicoherentInclusion X)
      (Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n)
        (sectionsFunctor S ⊤))

/-- `cohomologyIsoSectionsRightDerivedPushforwardOfNat`, delta-unfolded on `hom`.

Separated out because every equation about the comparison is proved on `hom`, and crossing the
three `Iso.trans` factors underneath a whiskering is what the heartbeat budget is spent on. -/
theorem cohomologyIsoSectionsRightDerivedPushforwardOfNat_hom (n : ℕ) :
    (cohomologyIsoSectionsRightDerivedPushforwardOfNat f n).hom =
      Functor.whiskerLeft (quasicoherentInclusion X)
          (Functor.whiskerRight
            (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X ⊤) n).inv
            (ModuleCat.restrictScalars f.appTop.hom)) ≫
        (sectionsRightDerivedPushforwardIso f n).hom ≫
        Functor.whiskerLeft (quasicoherentInclusion X)
          (Functor.whiskerRight
            (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).hom
            (sectionsFunctor S ⊤)) := rfl

/-- **[Stacks, Tag 01XK] in a degree that is a natural number is the conjugated `ℕ`-indexed
comparison.** This is the one equation that opens the sign split of
`cohomologyIsoSectionsRightDerivedPushforward`: in degree `(n : ℤ)` the nonnegative branch is
taken, and the transport along `(n : ℤ) = (((n : ℤ)).toNat : ℤ)` it carries is the identity
because `Int.toNat (n : ℤ)` reduces to `n`.

Every statement about the comparison in nonnegative degrees goes through this lemma; negative
degrees are discharged separately, both sides there being zero. -/
theorem cohomologyIsoSectionsRightDerivedPushforward_natCast (n : ℕ) :
    cohomologyIsoSectionsRightDerivedPushforward f (n : ℤ) =
      cohomologyIsoSectionsRightDerivedPushforwardOfNat f n := by
  unfold cohomologyIsoSectionsRightDerivedPushforward
  rw [dif_pos (Int.natCast_nonneg n)]
  rfl

end Comparison

end Stacks.Cohomology.AffineBase

end
