module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# The blowup of a locally Noetherian scheme is an almost blowup square

Let `X` be a locally Noetherian scheme and `I` a quasi-coherent ideal sheaf on `X` which is
finitely generated on every affine open. The blowup `b : Bl_I(X) ⟶ X` of `X` in `I`, together
with the inverse image of `I` as exceptional subscheme, is an almost blowup square with centre
`I`.

The fifth condition of an almost blowup square holds because no nonzero section of the structure
sheaf is supported on an effective Cartier divisor: the ideal of sections supported on a closed
set is the kernel of restriction to the open complement, and for the complement of an effective
Cartier divisor that restriction is injective on sections over every affine open.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_eq_bot_of_forall_app_injective`: a morphism injective on
  sections over every affine open of its target has vanishing kernel.
* `AlgebraicGeometry.supportedSectionsIdeal_eq_bot_of_isEffectiveCartierDivisor`: no nonzero
  section of the structure sheaf is supported on an effective Cartier divisor.
* `AlgebraicGeometry.isAlmostBlowUpSquare_blowUpToBase_of_fg`: the blowup of a locally
  Noetherian scheme in a finitely generated quasi-coherent ideal sheaf is the modification of an
  almost blowup square with that centre.

## References

* [Stacks Project, Tag 0EV4](https://stacks.math.columbia.edu/tag/0EV4)
* [Stacks Project, Tag 0EVA](https://stacks.math.columbia.edu/tag/0EVA)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes whose map on sections over every affine open of the target is injective
has trivial kernel. -/
public theorem Scheme.Hom.ker_eq_bot_of_forall_app_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ U : Y.affineOpens, Function.Injective (f.app U.1).hom) : f.ker = ⊥ :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : Y.affineOpens ↦ U)
    (iSup_affineOpens_eq_top Y) fun U ↦
      le_bot_iff.mp ((f.ideal_ker_le U).trans_eq
        ((RingHom.injective_iff_ker_eq_bot _).mp (h U)))

/-- No nonzero section of the structure sheaf is supported on an effective Cartier divisor. -/
public theorem supportedSectionsIdeal_eq_bot_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    supportedSectionsIdeal (I.support : Set X) = ⊥ := by
  rw [supportedSectionsIdeal_eq_complementKernel (I.support : Set X) I.support.isClosed]
  exact Scheme.Hom.ker_eq_bot_of_forall_app_injective _ fun U ↦
    Stacks.Divisors.injective_app_compl_support I hI U.1

/-- For a locally Noetherian scheme `X` and a quasi-coherent ideal sheaf `I` on it which is
finitely generated on every affine open, the blowup morphism of `X` in `I` is the modification of
an almost blowup square with centre `I`. -/
@[ega "IV 19.4.10" "more general"]
public theorem isAlmostBlowUpSquare_blowUpToBase_of_fg {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsAlmostBlowUpSquare I (blowUpToBase I) := by
  have hproper : IsProper (blowUpToBase I) := isProper_blowUpToBase_of_fg I hfg
  have hEff : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (blowUpToBase I)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  have hiso : IsIso (supportedSectionsIdeal
      ((I.comap (blowUpToBase I)).support : Set (blowUp I))).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2
      (supportedSectionsIdeal_eq_bot_of_isEffectiveCartierDivisor _ hEff)
  exact ⟨(Stacks.Flatness.finitePresentation_subschemeι_iff I).mpr hfg,
    Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _ hEff, hproper,
    finitePresentation_of_finiteType (blowUpToBase I),
    ⟨Over.isoMk (asIso (supportedSectionsIdeal
      ((I.comap (blowUpToBase I)).support : Set (blowUp I))).subschemeι) rfl⟩⟩

end AlgebraicGeometry

end
