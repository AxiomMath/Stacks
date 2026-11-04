module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSurjectiveFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.Topology.Algebra.AdicTopology.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplicationsRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRingsRefined

/-!
# Transfer of the types of affine formal algebraic spaces: the refined forms

Strengthened forms of results of `StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer`,
stated under primed names, on how the types of affine formal algebraic spaces transfer along
morphisms.

## Main results

* `isCountablyIndexed_of_isRepresentable'` and the other primed clauses: **Stacks 0AKQ**.
* `isWeaklyAdic_iff_of_surjective_flat'`: **Stacks 0GXS**; `isAdicStar_iff_of_surjective_flat'`:
  **Stacks 0AKT**; `isCountablyIndexed_iff_of_surjective_flat'`: **Stacks 0AKS**.

These take only the source's hypotheses and supersede the conditional unprimed forms of
`TypeTransfer`; the unconditional **Stacks 0GXR** and **Stacks 0AKW** are in
`AffineEtaleChartTypes`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable affine and representable flat morphisms -/

/-! ### Stacks 0AKN -/

/-! ### The inputs this library does not carry -/

/-- **Stacks 0AKN holds.** A morphism of affine formal algebraic spaces over `S` which is
representable by algebraic spaces is representable by schemes and affine. It is
`AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/AllTestObjects.lean`, and so is a hypothesis
of nothing. -/
theorem affineRepresentableIsAffine : AffineRepresentableIsAffine B S hS :=
  fun f hX hY hf =>
    relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf

/-! ### Stacks 0AKQ -/

/-- **Stacks 0AKQ, clause (1).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is countably indexed then
so is `X`. -/
@[stacks 0AKQ "clause (1); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and parts (1) and (2) of \
Stacks 0AKP are the library's `isAffineFormalAlgebraicSpace_of_relative_isAffineHom` and \
`isCountablyIndexed_of_relative_isAffineHom`"]
alias isCountablyIndexed_of_isRepresentable' := isCountablyIndexed_of_isRepresentable

/-- **Stacks 0AKQ, clause (2).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is countably indexed and
classical then so is `X`. -/
@[stacks 0AKQ "clause (2); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (3) of Stacks 0AKP is \
the library's `isCountablyIndexedAndClassical_of_relative_isAffineHom`"]
alias isCountablyIndexedAndClassical_of_isRepresentable' :=
  isCountablyIndexedAndClassical_of_isRepresentable

/-- **Stacks 0AKQ, clause (3).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is weakly adic then so is
`X`. -/
@[stacks 0AKQ "clause (3); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (4) of Stacks 0AKP is \
the library's `isWeaklyAdic_of_relative_isAffineHom`"]
alias isWeaklyAdic_of_isRepresentable' := isWeaklyAdic_of_isRepresentable

/-- **Stacks 0AKQ, clause (4).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is adic\* then so is
`X`. -/
@[stacks 0AKQ "clause (4); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (5) of Stacks 0AKP is \
the library's `isAdicStar_of_relative_isAffineHom`"]
alias isAdicStar_of_isRepresentable' := isAdicStar_of_isRepresentable

/-- **Stacks 0AKQ, clause (5).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces and locally of finite type. If `Y`
is Noetherian then so is `X`. -/
@[stacks 0AKQ "clause (5); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (6) of Stacks 0AKP is \
the library's `isNoetherian_of_relative_isAffineHom`"]
alias isNoetherian_of_isRepresentable' := isNoetherian_of_isRepresentable

/-! ### Two more ring-theoretic inputs this library does not carry -/

/-! ### Stacks 0AKS, 0GXR, 0GXS, 0AKT and 0AKW -/

/-- **Stacks 0AKS.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is countably indexed
if and only if `Y` is. -/
@[stacks 0AKS "the equivalence, at the source's own hypotheses. The forward implication is \
the source's cofinality argument, \
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_target_of_surjective_flat`, which rests on \
Stacks 0AIA, on Stacks 0AKN — the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` — and on faithful flatness of a \
represented base change; the reverse implication is clause (1) of Stacks 0AKQ"]
alias isCountablyIndexed_iff_of_surjective_flat' := isCountablyIndexed_iff_of_surjective_flat

/-- **Stacks 0GXR.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is countably indexed
and classical if and only if `Y` is. -/
theorem isCountablyIndexedAndClassical_iff_of_surjective_flat' {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (h0GXM : PreAdmissibleDescendsAlongTautFaithfullyFlat.{u})
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f) :
    IsCountablyIndexed B S hS X ∧ IsClassical B S hS X ↔
      IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y := by
  refine ⟨fun hXc ↦ ?_,
    fun hYc ↦ isCountablyIndexedAndClassical_of_isRepresentable' B S hS f hX hY hf
      hYc⟩
  obtain ⟨hrep, hflat'⟩ := id hflat
  obtain ⟨hXci, -, C, hCR, hCT, hCTR, hCLT, hCpres, hCadm⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  refine ⟨(isCountablyIndexed_iff_of_surjective_flat' B S hS f hX hY hf hsurj
      hflat).1 hXci, hYmcq, A, hAR, hAT, hATR, hALT, hApres,
    h0GXM A C hAR hAT hATR hALT hCR hCT hCTR hCLT φ hφcont hφtaut hφquot hCadm.1,
    hApres.1.2.2, hApres.1.2.1⟩

/-- **Stacks 0GXS.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is weakly adic if
and only if `Y` is. -/
@[stacks 0GXS "the equivalence, at the source's own hypotheses. The presenting ring of the \
target together with the continuous taut homomorphism to the source's, which is \
Stacks 0AN0, the implication (1) ⟹ (3) of Stacks 0AN5 and the identification of Stacks 0AMZ, \
is the library's `AlgebraicGeometry.FormalSpace`\
`.exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`, which takes countable \
indexing of the source from item (5) of Stacks 0AIK; Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`. The forward implication is the \
library's Stacks 0GXP and the reverse one is clause (3) of Stacks 0AKQ"]
alias isWeaklyAdic_iff_of_surjective_flat' := isWeaklyAdic_iff_of_surjective_flat

/-- **Stacks 0AKT.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is adic\* if and
only if `Y` is. -/
@[stacks 0AKT "the equivalence, at the source's own hypotheses. The presenting ring of the \
target together with the continuous taut homomorphism to the source's, which is \
Stacks 0AN0, the implication (1) ⟹ (3) of Stacks 0AN5 and the identification of Stacks 0AMZ, \
is the library's `AlgebraicGeometry.FormalSpace`\
`.exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`, which takes countable \
indexing of the source from items (2), (3) and (5) of Stacks 0AIK; Stacks 0AKN is the \
library's `relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`. The forward \
implication is the library's Stacks 0GXQ and the reverse one is clause (4) of Stacks 0AKQ"]
alias isAdicStar_iff_of_surjective_flat' := isAdicStar_iff_of_surjective_flat

/-- **Stacks 0AKW.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective, flat and locally of finite type. Then
`X` is Noetherian if and only if `Y` is. -/
theorem isNoetherian_iff_of_surjective_flat' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h033E : NoetherianDescendsAlongTautFaithfullyFlat.{u})
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f) :
    IsNoetherian B S hS X ↔ IsNoetherian B S hS Y := by
  refine ⟨fun hXc ↦ ?_,
    fun hYc ↦ isNoetherian_of_isRepresentable' B S hS f hX hY hf hft hYc⟩
  obtain ⟨hrep, hflat'⟩ := id hflat
  have hXci : IsCountablyIndexed B S hS X := isCountablyIndexed_of_isNoetherian B S hS hXc
  obtain ⟨-, C, hCR, hCT, hCTR, hCLT, hCpres, hCnoeth, hCadic⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  let : T2Space C := hCadic.2.1
  let : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hCadic.2.2
  let : T2Space A := hApres.1.2.2
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hApres.1.2.1
  obtain ⟨K, -, hKadic⟩ := hCadic.1
  obtain ⟨J, hJadic, hJfg⟩ :=
    TopologicalRing.exists_fg_ideal_of_definition_of_taut φ hφcont hφtaut hφquot
      ⟨K, hKadic, IsNoetherian.noetherian K⟩
  have hAadic : TopologicalRing.IsAdic A :=
    ⟨⟨J, TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJadic⟩, hApres.1.2.2, hApres.1.2.1⟩
  exact ⟨hYmcq, A, hAR, hAT, hATR, hALT, hApres,
    h033E A C hAR hAT hATR hALT hCR hCT hCTR hCLT φ hφcont hφtaut hφquot hAadic hCnoeth,
    hAadic⟩

/-! ### Stacks 0AKX -/

end AlgebraicGeometry.FormalSpace

end
