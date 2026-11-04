module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite

/-!
# The inverse direction of the slice comparison is a dense subsite

`AlgebraicGeometry.Space.SpacesEtale.isDenseSubsite_sliceToSmall` exhibits the comparison
`sliceToSmall : (X_{spaces,étale})/U ⥤ U_{spaces,étale}` as an equivalence of sites.  Several
transports along that equivalence — notably the reindexing of sheaves of modules of
[Stacks, Tag 03DM], `Stacks.SheafOfModules.reindexRing` and
`Stacks.SheafOfModules.reindexEquivalence` — ask for continuity of the *inverse* functor
`smallToSlice` instead.  This file supplies it, as the mirror instance.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_smallToSlice`: `smallToSlice` is an
  equivalence of categories, being the inverse of `sliceEquivSmall`.
* `AlgebraicGeometry.Space.SpacesEtale.isDenseSubsite_smallToSlice`: **`smallToSlice` exhibits
  the spaces-étale site of `U` as a dense subsite of the localization at `U` of the spaces-étale
  site of `X`**, whence continuity and cocontinuity of `smallToSlice` for the two topologies.

## Implementation notes

Only the covering-sieve correspondence has to be proved; cover-density, local fullness and local
faithfulness come from the priority-900 instances for an equivalence and for a full, faithful
functor.

The correspondence is read off the one for `sliceToSmall` and the strict round trip
`AlgebraicGeometry.Space.SpacesEtale.smallToSlice_comp_sliceToSmall`, which is an equality of
functors on the nose: pushing a sieve forward along `smallToSlice` and then along `sliceToSmall`
pushes it forward along the identity, hence returns it unchanged.  That is why no comparison
isomorphism of sieves appears.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Q : SpacesEtale B S hS X)

/-- `smallToSlice` is an equivalence of categories: it is the inverse half of
`AlgebraicGeometry.Space.SpacesEtale.sliceEquivSmall`. -/
instance isEquivalence_smallToSlice : (smallToSlice B S hS Q).IsEquivalence :=
  inferInstanceAs ((sliceEquivSmall B S hS Q).inverse.IsEquivalence)

/-- **Pushing a sieve forward along `smallToSlice` and then along `sliceToSmall` returns it.**
The round trip is the identity functor on the nose. -/
theorem functorPushforward_smallToSlice_sliceToSmall
    {V : SpacesEtale B S hS Q.obj.left} (T : Sieve V) :
    (T.functorPushforward (smallToSlice B S hS Q)).functorPushforward
        (sliceToSmall B S hS Q) = T := by
  rw [← Sieve.functorPushforward_comp]
  exact Sieve.functorPushforward_id T

/-- **The spaces-étale site of `U` is a dense subsite of the localization at `U` of the
spaces-étale site of `X`, along `smallToSlice`.**  A sieve covers in the spaces-étale site of `U`
exactly when its image covers in the localization, which is the correspondence for
`sliceToSmall` read through the strict round trip. -/
instance isDenseSubsite_smallToSlice :
    (smallToSlice B S hS Q).IsDenseSubsite (topology B S hS Q.obj.left)
      ((topology B S hS X).over Q) where
  functorPushforward_mem_iff {V T} := by
    have h := (isDenseSubsite_sliceToSmall B S hS Q).functorPushforward_mem_iff
      (S := T.functorPushforward (smallToSlice B S hS Q))
    rw [functorPushforward_smallToSlice_sliceToSmall] at h
    exact h.symm

/-- The continuity of `smallToSlice`, in the spelling `(sliceEquivSmall …).symm.functor` that
the reindexing of sheaves of modules along an equivalence of sites asks for. -/
instance isContinuous_sliceEquivSmall_symm_functor :
    (sliceEquivSmall B S hS Q).symm.functor.IsContinuous (topology B S hS Q.obj.left)
      ((topology B S hS X).over Q) :=
  inferInstanceAs ((smallToSlice B S hS Q).IsContinuous (topology B S hS Q.obj.left)
    ((topology B S hS X).over Q))

/-- The continuity of `sliceToSmall`, in the spelling `(sliceEquivSmall …).symm.inverse`. -/
instance isContinuous_sliceEquivSmall_symm_inverse :
    (sliceEquivSmall B S hS Q).symm.inverse.IsContinuous ((topology B S hS X).over Q)
      (topology B S hS Q.obj.left) :=
  inferInstanceAs ((sliceToSmall B S hS Q).IsContinuous ((topology B S hS X).over Q)
    (topology B S hS Q.obj.left))

/-- The dense-subsite correspondence for `sliceToSmall`, in the spelling
`(sliceEquivSmall …).symm.inverse`. -/
instance isDenseSubsite_sliceEquivSmall_symm_inverse :
    (sliceEquivSmall B S hS Q).symm.inverse.IsDenseSubsite ((topology B S hS X).over Q)
      (topology B S hS Q.obj.left) :=
  inferInstanceAs ((sliceToSmall B S hS Q).IsDenseSubsite ((topology B S hS X).over Q)
    (topology B S hS Q.obj.left))

end AlgebraicGeometry.Space.SpacesEtale

end
