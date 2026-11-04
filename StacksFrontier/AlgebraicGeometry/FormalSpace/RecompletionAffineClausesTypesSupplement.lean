module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAdicStarCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesVariants
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Types of completions of affine formal algebraic spaces

Let `X` be an affine formal algebraic space with reduction `X_red` and let `T ⊆ |X_red|` be
closed. This module shows that the completion `X_{/T}` of `X` along `T` inherits from `X` the
properties of being countably indexed, adic\*, and Noetherian; the first two require
`|X_red| \ T` to be quasi-compact.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_completionAlong'`: if `|X_red| \ T` is
  quasi-compact and `X` is countably indexed, then so is `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.isAdicStar_completionAlong'`: if `|X_red| \ T` is quasi-compact
  and `X` is adic\*, then so is `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.isNoetherian_completionAlong'`: if `X` is Noetherian then so is
  `X_{/T}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf isomorphic to the formal spectrum of a quotient system on the adic completion of `A`
along `J` has that completion as a presenting ring. -/
private theorem isPresentingRing_adicCompletion {Y : FppfSheaf B S hS} (A : Type u) [CommRing A]
    [TopologicalSpace A] (J : Ideal A)
    (D : @QuotientSystem B S hS (AdicCompletion J A) _ (adicCompletionLimitTopology A J))
    (e : Y ≅ @formalSpectrum B S hS (AdicCompletion J A) _ (adicCompletionLimitTopology A J) D) :
    @IsPresentingRing B S hS (AdicCompletion J A) _ (adicCompletionLimitTopology A J)
      (isTopologicalRing_adicCompletion A J) (isLinearTopology_adicCompletion A J) Y :=
  letI := adicCompletionLimitTopology A J
  letI := isTopologicalRing_adicCompletion A J
  letI := isLinearTopology_adicCompletion A J
  ⟨isWeaklyAdmissible_adicCompletion A J,
    ⟨{ D.weakIdealColimitPresentation with
      colimitIso := e ≪≫ D.weakIdealColimitPresentation.colimitIso }⟩⟩

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed with `|X_red| \ T`
quasi-compact. If `X` is countably indexed then so is the completion `X_{/T}` of `X` along `T`:
it admits a presentation indexed by `ℕ` by affine schemes along thickenings. -/
@[stacks 0GVV "clause (3): if `|X_red| \\ T` is quasi-compact and `X` is countably indexed \
then so is `X_{/T}`, countably indexed being `IsCountablyIndexed` (Stacks 0AIJ, \
StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexed.lean). Carried hypotheses: `hX` is \
the tag's own countable-indexing hypothesis on `X`, `hi` supplies the reduction as data \
rather than choosing one from Stacks 0AIN (the convention of Stacks 0GVT \
and 0GB8), `hT` is the tag's own closedness of `T` in `|X_red|`, `hqc` is the tag's own \
quasi-compactness of `|X_red| \\ T`, stated as compactness of `Tᶜ` for the point topology \
`Space.pointTopologyULift` since this library has no quasi-compactness predicate for formal \
algebraic spaces. Nothing else: the source's step producing the weakly admissible ring \
`lim A/J_{m,n}` with a countable fundamental system of neighbourhoods of zero — condition (2) \
of Stacks 0AN1 — is not needed at all. The proof \
goes through condition (1) directly: `isCountablyIndexed_completionSheafULift`, which gets a \
countable directed presentation of `X_{/T}` from a countable one of `X` and turns it into a \
sequential one by Stacks 0AII \
(`isCountablyIndexed_iff_exists_countable_presentation`)."]
theorem isCountablyIndexed_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsCountablyIndexed B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) Tᶜ) :
    IsCountablyIndexed B S hS (completionAlong i T) :=
  isCountablyIndexed_completionSheafULift B S hS X hX _
    (hi.isClosed_image_pointsMapULift (T := T) hT)
    (hi.isCompact_compl_image_pointsMapULift (T := T) hqc)

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed with `|X_red| \ T`
quasi-compact. If `X` is adic\* then so is the completion `X_{/T}` of `X` along `T`: it is
presented by an adic topological ring with a finitely generated ideal of definition. -/
@[stacks 0GVV "clause (4): if `|X_red| \\ T` is quasi-compact and `X` is adic* then so is \
`X_{/T}`, adic* being `IsAdicStar` (Stacks 0AID (4), \
StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean). Carried hypotheses: `hX` is the \
tag's own adic* hypothesis on `X`, `hi` supplies the reduction as data because Stacks 0AIN is \
unavailable in this library (the convention of Stacks 0GVT and 0GB8), `hT` is the \
tag's own closedness of `T` in `|X_red|`, and `hqc` is the tag's own quasi-compactness of \
`|X_red| \\ T`, stated as compactness of `Tᶜ` for the point topology \
`Space.pointTopologyULift` since this library has no quasi-compactness predicate for formal \
algebraic spaces. NOTHING ELSE: the source's own step `X_{/T} = Spf (lim A/J^n)` for a \
finitely generated `J` is PROVED \
(`exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift`). Nothing in \
the chain asks anything of `Spec A` -- no structure morphism to `S` and no site-membership -- \
exactly as the source asks nothing: the affines of the site cutting out the powers of `J` are \
quotients of the STAGE rings `A/K`. The set-theoretic condition of Stacks 0AIS is not assumed. \
The step from `X_{/T} = Spf (lim A/J^n)` to the conclusion is the ring half of \
Stacks 0GXX (`isAdic_adicCompletion`, `isIdealOfDefinition_map_adicCompletion`, \
`isWeaklyAdmissible_adicCompletion`) together with clause (2) of this tag \
(`hasSomeSurjectivePresentation_completionAlong'`)."]
theorem isAdicStar_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsAdicStar B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) Tᶜ) :
    IsAdicStar B S hS (completionAlong i T) := by
  obtain ⟨A, instCR, instTS, instTR, instLT, hpres, hadic, I, hIdef, hIfg⟩ := hX.2
  let _ : CommRing A := instCR
  let _ : TopologicalSpace A := instTS
  let _ : IsTopologicalRing A := instTR
  let _ : IsLinearTopology A A := instLT
  obtain ⟨hwaA, ⟨P⟩⟩ := hpres
  obtain ⟨J, hJ, D, ⟨e⟩⟩ :=
    exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift B S hS A X P hwaA
      hX.1.1 hadic hIdef hIfg _ (hi.isClosed_image_pointsMapULift (T := T) hT)
      (hi.isCompact_compl_image_pointsMapULift (T := T) hqc)
  exact ⟨hasSomeSurjectivePresentation_completionAlong' B S hS hX.1 hi T hT,
    AdicCompletion J A, inferInstance, adicCompletionLimitTopology A J,
    isTopologicalRing_adicCompletion A J, isLinearTopology_adicCompletion A J,
    isPresentingRing_adicCompletion B S hS A J D e, isAdic_adicCompletion J hJ,
    Ideal.map (algebraMap A (AdicCompletion J A)) J,
    isIdealOfDefinition_map_adicCompletion J hJ, hJ.map _⟩

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed. If `X` is Noetherian
then so is the completion `X_{/T}` of `X` along `T`: it is presented by a topological ring which
is both Noetherian and adic. -/
@[stacks 0GVV "clause (5): if `X` is Noetherian then so is `X_{/T}`, Noetherian being \
`IsNoetherian` (Stacks 0AID (5), \
StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean). Carried hypotheses: `hX` is the \
tag's own Noetherian hypothesis on `X`, `hi` supplies the reduction as data because Stacks \
0AIN is unavailable in this library (the convention of Stacks 0GVT and 0GB8), and \
`hT` is the tag's own closedness of `T` in `|X_red|`. NOTHING ELSE: the source's own step \
`X_{/T} = Spf (lim A/J^n)` for a Noetherian `A` is PROVED \
(`exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift`). Nothing in \
the chain asks anything of `Spec A` -- no structure morphism to `S` and no site-membership. \
There is deliberately NO quasi-compactness hypothesis: it is automatic here, which is \
`isCompact_of_isNoetherianRing` (the point space of `X` is the prime spectrum of a quotient of \
the Noetherian presenting ring, hence a Noetherian space). The set-theoretic condition of \
Stacks 0AIS is not assumed. The step from `X_{/T} = Spf (lim A/J^n)` to the conclusion is \
Stacks 0316 for the Noetherianness of the adic completion together with the ring half of \
Stacks 0GXX (`isAdic_adicCompletion`) and clause (2) of this tag \
(`hasSomeSurjectivePresentation_completionAlong'`).",
  ega "I 10.8.6" "special case"]
theorem isNoetherian_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsNoetherian B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    IsNoetherian B S hS (completionAlong i T) := by
  obtain ⟨A, instCR, instTS, instTR, instLT, hpres, instNoeth, hadic⟩ := hX.2
  let _ : CommRing A := instCR
  let _ : TopologicalSpace A := instTS
  let _ : IsTopologicalRing A := instTR
  let _ : IsLinearTopology A A := instLT
  let _ : IsNoetherianRing A := instNoeth
  obtain ⟨hwaA, ⟨P⟩⟩ := hpres
  obtain ⟨I₀, hI₀def, hI₀adic⟩ := hadic.1
  obtain ⟨J, hJ, D, ⟨e⟩⟩ :=
    exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift B S hS A X P hwaA
      hX.1.1 hadic hI₀def I₀.fg_of_isNoetherianRing _
      (hi.isClosed_image_pointsMapULift (T := T) hT)
      (isCompact_of_isNoetherianRing B S hS A X P hwaA hI₀def _)
  exact ⟨hasSomeSurjectivePresentation_completionAlong' B S hS hX.1 hi T hT,
    AdicCompletion J A, inferInstance, adicCompletionLimitTopology A J,
    isTopologicalRing_adicCompletion A J, isLinearTopology_adicCompletion A J,
    isPresentingRing_adicCompletion B S hS A J D e, inferInstance,
    isAdic_adicCompletion J hJ⟩

end AlgebraicGeometry.FormalSpace

end
