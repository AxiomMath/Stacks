module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup of a scheme is separated, and proper when the centre is of finite type

`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean` constructs the blowup
`Stacks.Blowup.blowUp ℐ` of a scheme `S` in a quasi-coherent sheaf of ideals `ℐ`, together with
its structure morphism `Stacks.Blowup.blowUpToBase ℐ`, and pins it down by
`Stacks.Blowup.isPullback_blowUpChart`: over an affine open `U` of `S` the blowup is the ordinary
`Proj` of the Rees algebra of `ℐ(U)`. `StacksFrontier/AlgebraicGeometry/Blowup/Basic.lean` proves
that this affine model is separated over its base, and proper over it when the ring is
Noetherian.

This file transports both statements to the global blowup. Separatedness and properness are
Zariski-local on the target, and the chart square exhibits the restriction of `blowUpToBase ℐ`
to an affine open `U` as the structure morphism of the affine model over `ℐ(U)`.

The properness hypothesis is weakened on the way: `AlgebraicGeometry.Proj.instIsProper` asks for
`Algebra.FiniteType (𝒜 0) A`, and for the Rees algebra `Mathlib.RingTheory.ReesAlgebra` supplies
that from `Ideal.FG` alone through `reesAlgebra.fg`. So properness of the blowup needs only that
`ℐ` is of finite type — the hypothesis under which Stacks tag 02NS asserts projectivity — and the
Noetherian case is the special case where every ideal is finitely generated.

## Main results

* `Stacks.Blowup.isProper_toSpec_of_fg`: the blowup of an affine scheme in a finitely generated
  ideal is proper over its base, and `Stacks.Blowup.compactSpace_of_fg`: hence quasi-compact.
* `Stacks.Blowup.of_forall_toSpec`: a morphism property which is Zariski-local on the target
  holds for `Stacks.Blowup.blowUpToBase ℐ` as soon as it holds for every affine model.
* `Stacks.Blowup.instIsSeparatedBlowUpToBase`: the blowup is separated over its base, with no
  hypothesis on `ℐ` or on `S`.
* `Stacks.Blowup.isProper_blowUpToBase`: the blowup is proper over its base when `ℐ` is of
  finite type, and `Stacks.Blowup.instIsProperBlowUpToBase` is the instance for a locally
  Noetherian base.

## Implementation notes

`Stacks.Blowup.blowUpSpec` is a `def`, not an `abbrev`, so its unfolding to `Proj (reesGrading I)`
is definitional but not syntactic. Rewriting across that boundary fails with the usual
"target not type-correct at `implicit` transparency" note; the two places where the boundary is
crossed therefore finish with `exact` and with `rfl`, both of which check at default
transparency.

Tag 02NS is *not* placed here. It asserts that the blowup in an ideal sheaf of finite type is a
**projective** morphism, through a closed immersion into `𝐏(ℐ)`; properness is a consequence of
that and not the statement, so claiming the tag would weaken it.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Blowup

section Affine

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The Rees algebra of a finitely generated ideal is of finite type over the base ring. This is
`reesAlgebra.fg` read through `Subalgebra.fg_top`, and it is what replaces the Noetherian
hypothesis of `Stacks.Blowup.instFiniteTypeReesGradingZero`. -/
theorem finiteType_reesAlgebra_of_fg (hI : I.FG) : Algebra.FiniteType R (reesAlgebra I) :=
  ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩

/-- The Rees algebra of a finitely generated ideal is of finite type over the degree-zero part of
its grading, which is the hypothesis of `AlgebraicGeometry.Proj.instIsProper`. -/
theorem finiteType_reesGradingZero_of_fg (hI : I.FG) :
    Algebra.FiniteType (reesGrading I 0) (reesAlgebra I) :=
  have := finiteType_reesAlgebra_of_fg I hI
  Algebra.FiniteType.of_restrictScalars_finiteType R _ _

/-- **The blowup of an affine scheme in a finitely generated ideal is proper over its base.** No
Noetherian hypothesis is needed: finite generation of `I` already makes the Rees algebra of
finite type, and `Proj 𝒜 ⟶ Spec 𝒜₀` is proper for every grading of a finite-type algebra. -/
theorem isProper_toSpec_of_fg (hI : I.FG) : IsProper (toSpec I) := by
  have := finiteType_reesGradingZero_of_fg I hI
  change IsProper (Proj.toSpecZero (reesGrading I) ≫
    Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom))
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- **The blowup of an affine scheme in a finitely generated ideal is quasi-compact.** -/
theorem compactSpace_of_fg (hI : I.FG) : CompactSpace (blowUpSpec I) :=
  have := isProper_toSpec_of_fg I hI
  QuasiCompact.compactSpace_of_compactSpace (toSpec I)

end Affine

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- The chart morphism of the blowup over an affine open `U` of the base is the structure
morphism of the affine model over `ℐ(U)`, followed by the identification of `Spec Γ(S, U)` with
`U`. -/
theorem chartToOpen_eq (U : S.affineOpens) :
    Stacks.RelativeProj.chartToOpen (fun W : S.affineOpens ↦ reesGrading (ℐ.ideal W)) U
        (reesBase ℐ U) =
      toSpec (ℐ.ideal U) ≫ (Stacks.RelativeProj.isAffineOpen U).isoSpec.inv :=
  rfl

/-- **A morphism property which is Zariski-local on the target holds for the blowup morphism as
soon as it holds for every affine model.** The chart square `Stacks.Blowup.isPullback_blowUpChart`
and the restriction square of `blowUpToBase ℐ` to `U` are pullbacks of the same cospan, so their
apexes are isomorphic over `U`; the property then transfers along that isomorphism and along the
isomorphism `Spec Γ(S, U) ≅ U`. -/
theorem of_forall_toSpec (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : S.affineOpens, P (toSpec (ℐ.ideal U))) : P (blowUpToBase ℐ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : S.affineOpens ↦ (U : S.Opens))
    (iSup_affineOpens_eq_top S) fun U ↦ ?_
  have hres := isPullback_morphismRestrict (blowUpToBase ℐ) (U : S.Opens)
  rw [← P.cancel_left_of_respectsIso
      ((isPullback_blowUpChart ℐ U).isoIsPullback _ _ hres).hom,
    (isPullback_blowUpChart ℐ U).isoIsPullback_hom_fst _ _ hres, chartToOpen_eq]
  exact (P.cancel_right_of_respectsIso (toSpec (ℐ.ideal U)) _).mpr (h U)

/-- **The blowup of a scheme in a quasi-coherent sheaf of ideals is separated over its base.** No
hypothesis on `ℐ` or on `S` is needed, since `Proj 𝒜 ⟶ Spec 𝒜₀` is separated for every
grading. -/
instance instIsSeparatedBlowUpToBase : IsSeparated (blowUpToBase ℐ) :=
  of_forall_toSpec ℐ _ fun _ ↦ inferInstance

/-- **The blowup of a scheme in a quasi-coherent sheaf of ideals of finite type is proper over
its base.** Finite type is spelled out as finite generation of `ℐ(U)` for every affine open `U`,
which is the affine-local meaning of a sheaf of ideals of finite type. -/
theorem isProper_blowUpToBase (hfg : ∀ U : S.affineOpens, (ℐ.ideal U).FG) :
    IsProper (blowUpToBase ℐ) :=
  of_forall_toSpec ℐ _ fun U ↦ isProper_toSpec_of_fg _ (hfg U)

/-- The blowup of a locally Noetherian scheme is proper over its base: on a locally Noetherian
scheme every sheaf of ideals is of finite type. -/
@[ega "IV 19.4.10" "more general"]
instance instIsProperBlowUpToBase [IsLocallyNoetherian S] : IsProper (blowUpToBase ℐ) :=
  isProper_blowUpToBase ℐ fun U ↦
    have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
    IsNoetherian.noetherian _

end Stacks.Blowup

end
