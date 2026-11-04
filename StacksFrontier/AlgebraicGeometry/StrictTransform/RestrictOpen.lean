module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport

/-!
# The strict transform pulled back to an open of the base change

The strict transform of [Stacks, Tag 080D] is a quotient by sections supported on
`pr_{S'}^{-1}(Supp E)`, and that construction commutes with flat pullback. For an *open immersion*
`j : Y ⟶ X ×_S S'` this says that the strict transform of `F` pulled back to `Y` is the quotient
of the pullback of `F` to `Y` by the sections supported on `j^{-1}(pr_{S'}^{-1}(Supp E))` — the
same construction, performed on `Y`.

That is the step which carries the strict transform onto an affine chart of a blowup, where
[Stacks, Tag 0810] computes it; see
`StacksFrontier/AlgebraicGeometry/StrictTransform/AffinePrincipalTorsion.lean`.

## Main definitions

* `Stacks.StrictTransform.pullbackSheafIso`: the identification above, for an arbitrary second
  morphism `b` and ideal sheaf `E` whose support has affine open complement.
* `Stacks.StrictTransform.pullbackSheafBlowUpIso`: the same along a blowup, with no hypothesis —
  the exceptional ideal is an effective Cartier divisor, so its complement is affine over the
  blowup.

## Implementation notes

The content is `Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso`, the statement
that the quotient by the sections supported in the complement of an open `U` with affine inclusion
commutes with flat pullback ([Stacks, Tag 02KG]); an open immersion is flat. Its conclusion is
phrased for the complement of an open, so
`Stacks.StrictTransform.exceptionalPreimage_eq_compl` rewrites the exceptional preimage into that
form first — in both places it occurs, inside the quotient and inside the preimage. The leftover
comparison is `AlgebraicGeometry.Scheme.Modules.pullbackComp`, carried across the quotient by
`Stacks.SupportedQuotient.supportedSectionsCokernelIso`.

The affineness hypothesis is `IsAffineHom (Scheme.Opens.ι E.support.compl)`, which concerns only
the centre: `AlgebraicGeometry.isAffineHom_preimage_ι` inherits it for the complement of the
exceptional preimage in the base change. Along a blowup it is unconditional, by
`Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor` ([Stacks, Tag 07ZT]) applied to
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.StrictTransform

variable {X S S' Y : Scheme.{u}}

/-- **The strict transform pulled back to an open of the base change.** For an open immersion
`j : Y ⟶ X ×_S S'` the pullback along `j` of the strict transform of `F` is the quotient of the
pullback of `F` to `Y` by the sections supported on `j^{-1}(pr_{S'}^{-1}(Supp E))`.

The hypothesis is that the open complement of `Supp E` is affine over `S'`, which is what
`Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso` consumes; along a blowup it
holds unconditionally, see `Stacks.StrictTransform.pullbackSheafBlowUpIso`. -/
public def pullbackSheafIso (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)
    [IsAffineHom (Scheme.Opens.ι E.support.compl)] (F : X.Modules) [F.IsQuasicoherent]
    (j : Y ⟶ baseChange f b) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).obj (sheaf f b E F) ≅
      cokernel (supportedSectionsι (j.base ⁻¹' exceptionalPreimage f b E)
        ((Scheme.Modules.pullback (j ≫ pullback.fst f b)).obj F)) := by
  have : IsAffineHom (exceptionalComplement f b E).ι :=
    isAffineHom_preimage_ι (pullback.snd f b) E.support.compl
  have : ((Scheme.Modules.pullback (pullback.fst f b)).obj F).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (pullback.fst f b).toLRSHom.toShHom F ‹F.IsQuasicoherent›
  change (Scheme.Modules.pullback j).obj (cokernel (supportedSectionsι
      (exceptionalPreimage f b E)
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F))) ≅ _
  rw [exceptionalPreimage_eq_compl f b E]
  exact Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso j
      (exceptionalComplement f b E) ((Scheme.Modules.pullback (pullback.fst f b)).obj F) ≪≫
    Stacks.SupportedQuotient.supportedSectionsCokernelIso _
      ((Scheme.Modules.pullbackComp j (pullback.fst f b)).app F)

/-- **The strict transform along a blowup, pulled back to an open of the base change.** The
instance of `Stacks.StrictTransform.pullbackSheafIso` at `b` the blowup of `S` in `I` and `E` its
exceptional ideal, where the affineness hypothesis is automatic: the exceptional ideal is an
effective Cartier divisor, so the complement of its support is affine over the blowup. -/
public def pullbackSheafBlowUpIso (f : X ⟶ S) (I : S.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (j : Y ⟶ baseChange f (blowUpToBase I)) [IsOpenImmersion j] :
    (Scheme.Modules.pullback j).obj (sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
      cokernel (supportedSectionsι
        (j.base ⁻¹' exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I))
        ((Scheme.Modules.pullback (j ≫ pullback.fst f (blowUpToBase I))).obj F)) :=
  have : IsAffineHom (Scheme.Opens.ι (exceptionalIdeal I).support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  pullbackSheafIso f (blowUpToBase I) (exceptionalIdeal I) F j

end Stacks.StrictTransform

end
