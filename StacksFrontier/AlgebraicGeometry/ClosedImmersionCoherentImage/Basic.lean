module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct

/-!
# Coherence of the direct image of an ideal sheaf along a closed immersion

The dévissage of coherent modules carries, at several places, the hypothesis that
`i_* I` is coherent for `i : W ⟶ X` a closed immersion and `I ⊆ 𝒪_W` a quasi-coherent ideal
sheaf. The implementation notes of
`StacksFrontier/AlgebraicGeometry/IrreducibleDevissage/Coproduct.lean` (at the docstring of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_pushforward_coproduct_const`)
and of `StacksFrontier/AlgebraicGeometry/ProperCoherentImage/Devissage.lean` record this
hypothesis as unavailable in this repository, and the former attributes the unavailability to
[Stacks, Tag 02O5] — "the direct image of a coherent module along a proper morphism is coherent
only conditionally here […] and [Stacks, Tag 02O5] itself depends on this dévissage".

**Both claims are false, and the attribution inverts the source's dependency order.** The
statement needed is the closed-immersion case of [Stacks, Tag 01Y6], whose proof in the source
cites only [Stacks, Tag 01XC], [Stacks, Tag 01T6], [Stacks, Tag 01WH], [Stacks, Tag 01XZ] and
[Stacks, Tag 00GJ] — no higher direct image, no proper morphism, no dévissage. It needs nothing
from [Stacks, Tag 02O5], and this file proves it from material already in the library:

* `𝒪_X ⟶ i_* 𝒪_W` is an epimorphism for a closed immersion, by
  `Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion`;
* `𝒪_X` is coherent on a locally Noetherian scheme, by
  `Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`;
* `i_*` of a quasi-coherent module is quasi-coherent for an affine morphism, by
  `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`;
* a quasi-coherent quotient, resp. submodule, of a coherent module on a locally Noetherian
  scheme is coherent, by [Stacks, Tag 01Y1], i.e.
  `Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi` and `isCoherent_of_mono`.

So `i_* 𝒪_W` is a quasi-coherent quotient of the coherent `𝒪_X`, hence coherent; and `i_* I` is
a quasi-coherent submodule of `i_* 𝒪_W`, because `i_*` is a right adjoint and so preserves
monomorphisms, hence coherent.

## Main results

* `AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_unit`: the direct image
  of the structure sheaf along a closed immersion into a locally Noetherian scheme is coherent.
* `AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit`: the
  direct image of a quasi-coherent ideal sheaf along a closed immersion into a locally Noetherian
  scheme is coherent. **This is the hypothesis the dévissage carries.**
* `AlgebraicGeometry.ClosedImmersionCoherentImage.hasKilledIdealCoproductSub_of_sub`: the
  coherence conjunct of
  `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSub` is redundant over a
  locally Noetherian scheme, so that whoever discharges [Stacks, Tag 01YE] owes only
  `HasKilledIdealCoproductSubOf`, which does not mention coherence of a direct image.

## Implementation notes

Two instances have to be supplied by hand, both because `Scheme.Modules` is a
`def`: quasi-coherence of `i_* 𝒪_W`, where instance search does not see
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit` through the pushforward;
and `PreservesMonomorphisms` for `Scheme.Modules.pushforward i`, which is supplied from
`AlgebraicGeometry.pushforward_preservesFiniteLimits` through
`CategoryTheory.preserves_mono_of_preservesLimit` rather than found. `Mono I.ι` is likewise
transported by hand from the `SheafOfModules` spelling.

No tag is attached. [Stacks, Tag 01Y6] asserts, for an arbitrary finite morphism and an arbitrary
coherent module, both coherence of `f_* F` and vanishing of `R ᵖ f_* F` for `p > 0`. What is
proved here is only the closed-immersion case, only for submodules of the structure sheaf, and
says nothing about higher direct images, so the covering set of [Stacks, Tag 01Y6] fails on three
axes.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ClosedImmersionCoherentImage

variable {W X : Scheme.{u}} (i : W ⟶ X)

/-- The canonical map `𝒪_X ⟶ i_* 𝒪_W` attached to a morphism of schemes, in the
`Scheme.Modules` spelling. -/
noncomputable def unitToPushforwardUnit :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- **For a closed immersion, `𝒪_X ⟶ i_* 𝒪_W` is an epimorphism.** This is
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion`,
whose statement is in the `RingedSpace` spelling of the pushforward; the two spellings agree
definitionally. -/
theorem epi_unitToPushforwardUnit [IsClosedImmersion i] : Epi (unitToPushforwardUnit i) :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion i

/-- **The direct image of the structure sheaf along an affine morphism is quasi-coherent.** -/
theorem isQuasicoherent_pushforward_unit [IsAffineHom i] :
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
    _ _ i (SheafOfModules.unit W.ringCatSheaf) ‹_›
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W)

/-- **The direct image of the structure sheaf along a closed immersion into a locally Noetherian
scheme is coherent.** It is a quasi-coherent quotient of `𝒪_X`, which is coherent by
[Stacks, Tag 01XZ], so [Stacks, Tag 01Y1] applies. -/
theorem isCoherent_pushforward_unit [IsLocallyNoetherian X] [IsClosedImmersion i] :
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)).IsCoherent :=
  have : Epi (unitToPushforwardUnit i) := epi_unitToPushforwardUnit i
  @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi X _ _ _
    (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X)
    (isQuasicoherent_pushforward_unit i) (unitToPushforwardUnit i) ‹_›

/-- **The closed-immersion case of [Stacks, Tag 01Y6] in degree zero, for ideal sheaves.** The
direct image of a quasi-coherent submodule `I ⊆ 𝒪_W` along a closed immersion `i : W ⟶ X` into a
locally Noetherian scheme is coherent.

`i_* I` is a submodule of `i_* 𝒪_W`, because `Scheme.Modules.pushforward i` is a right adjoint
and therefore preserves monomorphisms; `i_* 𝒪_W` is coherent by `isCoherent_pushforward_unit`;
and `i_* I` is quasi-coherent because a closed immersion is affine. [Stacks, Tag 01Y1] for
submodules finishes. -/
theorem isCoherent_pushforward_submodule_unit [IsLocallyNoetherian X] [IsClosedImmersion i]
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent) :
    ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent := by
  have hamb : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit W.ringCatSheaf)).IsCoherent := isCoherent_pushforward_unit i
  have hmono : @Mono W.Modules _ _ _ I.ι := inferInstanceAs (Mono I.ι)
  have hq : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom
      _ _ i I.toSheafOfModules inferInstance hI
  have hpl : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.pushforward i) := inferInstance
  have hmono2 : Mono ((Scheme.Modules.pushforward i).map I.ι) :=
    @preserves_mono_of_preservesLimit _ _ _ _ (Scheme.Modules.pushforward i) _ _ I.ι
      hpl.preservesLimit hmono
  exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _ _ _ hamb hq
    ((Scheme.Modules.pushforward i).map I.ι) hmono2

/-! ### The coherence conjunct of the dévissage's remaining obligation is redundant -/

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
/-- `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSub` with the
coherence conjunct `(i_* I).IsCoherent` **deleted**. This is what the construction of
[Stacks, Tag 01YE] actually has to deliver. -/
def HasKilledIdealCoproductSubOf (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (Stacks.AlgebraicGeometry.IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W) (r : ℕ)
        (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ Q,
            Mono φ ∧ SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X)

open Stacks.AlgebraicGeometry.IrreducibleDevissage in
/-- **The coherence conjunct of `HasKilledIdealCoproductSub` is free over a locally Noetherian
scheme.** It is `isCoherent_pushforward_submodule_unit` at the closed immersion the statement
already produces. So the obligation that the dévissage of [Stacks, Tag 01YF] leaves open is
`HasKilledIdealCoproductSubOf`, which mentions no direct image coherence at all — and in
particular does not mention [Stacks, Tag 02O5]. -/
theorem hasKilledIdealCoproductSub_of_sub (X : Scheme.{u}) [IsLocallyNoetherian X]
    (h : HasKilledIdealCoproductSubOf X) : HasKilledIdealCoproductSub X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, φ, hmono, hsupp⟩ := h Z hZirr Q hQq hQc hkill
  have := hi
  exact ⟨W, i, hi, hW, r, I, hIq, isCoherent_pushforward_submodule_unit i I hIq,
    φ, hmono, hsupp⟩

end AlgebraicGeometry.ClosedImmersionCoherentImage

end
