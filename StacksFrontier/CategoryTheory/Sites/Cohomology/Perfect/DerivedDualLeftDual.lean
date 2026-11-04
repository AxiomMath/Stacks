module

public import StacksFrontier.CategoryTheory.Monoidal.RigidJointlyFaithful
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionApplicationLawOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationRightUnitLawOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationUnitLawOnASite
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect
import StacksCore.Tactic.StacksAttribute

/-! # The derived dual of a perfect object is a left dual

Let `(C, O)` be a ringed site and let `K` be a **perfect** object of `D(O)` ([Stacks, Tag 08G5])
with dual `K^∨ = R𝓗om_O(K, O)`.  **Stacks 0FPU** attaches to this pair two morphisms,

`ε : K^∨ ⊗^𝐋_O K ⟶ O`  and  `η : O ⟶ K ⊗^𝐋_O K^∨`,

and asserts that `(K^∨, η, ε)` is a **left dual** of `K` in `D(O)`.  This file proves that
assertion.

* The evaluation `ε` is `AlgebraicGeometry.RingedSite.derivedDualEvaluation` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing`: the morphism which the
  tensor–internal-Hom bijection of [Stacks, Tag 08J8] matches with the identity of `K^∨`.
* The coevaluation `η` is `AlgebraicGeometry.RingedSite.coevaluation` below: the section
  corresponding to `id_K` under the comparison `K ⊗^𝐋_O K^∨ ⟶ R𝓗om_O(K, K)` of
  [Stacks, Tag 08JD], which is invertible for a perfect `K` by
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` — the third
  assertion of [Stacks, Tag 08JJ], which the source cites rather than proves.  Its defining
  property is `AlgebraicGeometry.RingedSite.coevaluation_comp`.
* The left-dual assertion is `AlgebraicGeometry.RingedSite.derivedDualExactPairing`, an
  `CategoryTheory.ExactPairing K K^∨` whose two structure maps are `η` and `ε`.  Mathlib's
  `ExactPairing` is exactly the left-dual datum of [Stacks, Tag 0FFP], so no bridge is needed
  downstream.

## What closes the gap

The "What this file does not contain" note of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing` listed three further
assertions of Stacks 0FPU as unavailable over a ringed site: invertibility of the comparison for
a perfect `K`, existence of `η` for a perfect `K`, and the two triangle identities.  **All three
are proved here**; that note is superseded.

The triangle identities reduce to one equation, which the derived-duality cluster calls **(E1)**:

`Φ_{L,M} ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ε) ≫ (ρ_ M).hom`,

the canonical map of [Stacks, Tag 08JD] followed by the application morphism of
[Stacks, Tag 08J8] being the contraction against `ε`.  (E1) is
`RingedSite.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit` below, and it
follows from the composition law **(C)** (`AlgebraicGeometry.RingedSite.compositionApplicationLaw`)
and the right unit law **(UR)**
(`RingedSite.derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit`) by the
paste `Stacks.Cohomology.DualityDescent.paste_composition_unit`, the canonical map of
Stacks 08JD *being* the composition morphism of [Stacks, Tag 0A98] at intermediate object the
structure sheaf whiskered with `M ≅ R𝓗om_O(O, M)`, by `rfl`.

Given (E1), the first triangle identity follows from the unit law **(UL)**
(`AlgebraicGeometry.RingedSite.derivedSheafHomCounit_unit_law_monoidal`) along the chain

`(η ▷ K) ≫ α ≫ (K ◁ ε) ≫ ρ = ((η ≫ Φ) ▷ K) ≫ app = (ι ▷ K) ≫ app = λ`,

whose middle step is the defining property of `η`; and the second follows from the first because
`ε` detects endomorphisms of `K^∨`
(`AlgebraicGeometry.RingedSite.eq_id_of_whiskerRight_comp_derivedDualEvaluation`), by
`CategoryTheory.ExactPairing.ofEvaluationCoevaluation`.

## The monoidal structure the assertion is read at

`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`, the symmetric monoidal structure of
[Stacks, Tag 0FPT] on `D(O)` re-seated onto the derived tensor bifunctor of
[Stacks, Tag 06YU] by
`Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`.  Re-seating changes no
constraint — it transports them along an isomorphism of bifunctors — and it is what makes the
assertion statable at all: `ε` and the application morphism of Stacks 08J8 are written at that
bifunctor, so in a monoidal structure merely isomorphic to it the whiskering `η ▷ K` would be a
different morphism from the one the bijection of Stacks 08J8 computes.

## Main definitions

* `AlgebraicGeometry.RingedSite.coevaluation`: **Stacks 0FPU**, the coevaluation `η` of a
  perfect object.
* `AlgebraicGeometry.RingedSite.monoidalCoevaluation` and
  `AlgebraicGeometry.RingedSite.monoidalEvaluation`: the same two morphisms, with their unit
  factor ascribed at the monoidal unit rather than at the structure sheaf in degree zero.
* `AlgebraicGeometry.RingedSite.derivedDualExactPairing`: **Stacks 0FPU**, the left-dual
  assertion.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_self`: **Stacks 0FPU**, the
  comparison `K ⊗^𝐋_O K^∨ ⟶ R𝓗om_O(K, K)` of Stacks 08JD is an isomorphism for a perfect `K`.
* `AlgebraicGeometry.RingedSite.coevaluation_comp`: `η` followed by the comparison of
  Stacks 08JD is the section corresponding to `id_K`.  This pins `η` down.
* `RingedSite.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit`: **(E1)**,
  for arbitrary objects.
* `AlgebraicGeometry.RingedSite.eq_id_of_whiskerRight_comp_derivedDualEvaluation`: the
  evaluation detects endomorphisms of `K^∨`.
* `AlgebraicGeometry.RingedSite.evaluation_coevaluation` and
  `AlgebraicGeometry.RingedSite.coevaluation_evaluation`: **Stacks 0FPU**, the two triangle
  identities.
* `AlgebraicGeometry.RingedSite.exists_exactPairing_derivedDual`: **Stacks 0FPU**, the left-dual
  assertion on an arbitrary ringed site with perfectness of `K` as its only hypothesis: the
  additivity of `⊗_O`, the existence of total tensor complexes and sheafification, which the
  rest of the file carries as instance arguments, are discharged for every ringed site.
* `AlgebraicGeometry.RingedSite.derivedDualExactPairing_coevaluation` and
  `AlgebraicGeometry.RingedSite.derivedDualExactPairing_evaluation`: the pairing's structure
  maps are the canonical ones.

## Implementation notes

The universes are the diagonal `RingedSite.{u, u, u}` of the whole derived-internal-Hom cluster,
with the derived category the standard one; this is what [Stacks, Tag 08JA], [Stacks, Tag 08J8]
and [Stacks, Tag 08JD] are stated at, and is not a narrowing introduced here.

The inner evaluation is carried as a variable `ev` in
`derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`, so that the
statement serves both of its spellings: `derivedSheafHomCounit X L O`, which is what (C) delivers,
and `AlgebraicGeometry.RingedSite.derivedDualEvaluation`, which is what the triangle identities
ask for.  The two are the same term, and the crossing is paid once, in
`derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`. The ringed-space mirror
`Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws`
carries `ev` in the same way.

## References

* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DualityDescent

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-! ### (E1) -/

/-- **The application morphism of Stacks 08J8 at target the structure sheaf is the evaluation of
the derived dual.**  `AlgebraicGeometry.RingedSite.derivedDualEvaluation` and
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit X L (derivedStructureSheaf X)` are the same
term: both are the image of the identity of `K^∨` under the bijection of Stacks 08J8, the derived
dual being the derived internal Hom into the structure sheaf.  The crossing between the two
spellings is paid here, once, and it is *not* paid by `rfl`: the conversion check at these
arguments reaches the maximum recursion depth.  It goes instead through the two `rfl` lemmas
that name each side's transpose,
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit_eq_transpose` and
`AlgebraicGeometry.RingedSite.derivedDualEvaluation_eq`, whose own statements are small enough
to check. -/
theorem derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomCounit X L (derivedStructureSheaf X) = derivedDualEvaluation X L := by
  rw [derivedSheafHomCounit_eq_transpose, derivedDualEvaluation_eq]

section Monoidal

attribute [local instance] derivedTensorMonoidal

/-- **The canonical map of Stacks 08JD is a whiskered composition morphism**, in the monoidal
spelling: `Φ_{L,M} : M ⊗^𝐋_O L^∨ ⟶ R𝓗om_O(L, M)` is the identification `M ≅ R𝓗om_O(O, M)` run
backwards and whiskered with `L^∨`, followed by the composition morphism of Stacks 0A98 at
intermediate object the structure sheaf.

This is the definition of `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` with the
induced map on the derived tensor product written as a right whiskering, which it is on the
nose: the `whiskerRight` field of `CategoryTheory.MonoidalCategory.reseatStruct` is literally
`(T.map f).app Y`.  The whole statement is therefore `rfl`. -/
theorem derivedTensorDualToSheafHom_eq_whiskerRight_composition
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorDualToSheafHom X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) L M =
      (derivedStructureSheafHomIso X M).inv ▷ derivedDual X L ≫
        derivedCompositionSite X L (derivedStructureSheaf X) M :=
  rfl

/-- **(E1), for arbitrary `L` and `M`, from the composition law (C).**  The canonical map of
Stacks 08JD followed by the application morphism of Stacks 08J8 is the contraction against `ev`:

`Φ_{L,M} ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom`.

The hypothesis `hcomp` is **(C)** — the compatibility of the composition morphism of Stacks 0A98
with the application morphism of Stacks 08J8 — at intermediate object the structure sheaf, with
the inner application written as `ev`; it holds for all objects, by
`AlgebraicGeometry.RingedSite.compositionApplicationLaw`.  The right unit law **(UR)** is
discharged here by
`derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal`.

The inner application stays the variable `ev` for the reason the module docstring gives: its two
spellings are the same term and a goal mentioning both is not type-correct at the `implicit`
transparency level. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ev : derivedDual X L ⊗ L ⟶
      𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hcomp : derivedCompositionSite X L (derivedStructureSheaf X) M ▷ L ≫
          derivedSheafHomCounit X L M =
        (α_ (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj M)
            (derivedDual X L) L).hom ≫
          (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj M ◁ ev) ≫
            derivedSheafHomCounit X (derivedStructureSheaf X) M) :
    derivedTensorDualToSheafHom X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) L M ▷
          L ≫ derivedSheafHomCounit X L M =
      (α_ M (derivedDual X L) L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom := by
  rw [derivedTensorDualToSheafHom_eq_whiskerRight_composition X L M]
  exact paste_composition_unit _ _ _ _ _ hcomp
    (derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal X M)

/-- **(E1), for arbitrary `L` and `M`.**  The canonical map of Stacks 08JD followed by the
application morphism of Stacks 08J8 is the contraction against the evaluation of the derived
dual:

`Φ_{L,M} ▷ L ≫ app = (α_ M L^∨ L).hom ≫ (M ◁ ε) ≫ (ρ_ M).hom`.

Both hypotheses of
`derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws` are discharged:
(C) by `AlgebraicGeometry.RingedSite.compositionApplicationLaw` at intermediate object the
structure sheaf, and (UR) already inside it.  No perfectness and no hypothesis on `L` or `M`. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorDualToSheafHom X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) L M ▷
          L ≫ derivedSheafHomCounit X L M =
      (α_ M (derivedDual X L) L).hom ≫ (M ◁ derivedDualEvaluation X L) ≫ (ρ_ M).hom := by
  have hcomp := compositionApplicationLaw X L (derivedStructureSheaf X) M
  unfold CompositionApplicationLaw at hcomp
  rw [derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation] at hcomp
  exact derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws X L M
    (derivedDualEvaluation X L) hcomp

end Monoidal

/-! ### The coevaluation of a perfect object -/

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0FPU: the canonical map `K ⊗^𝐋_O K^∨ ⟶ R𝓗om_O(K, K)` is an isomorphism.**  For a
perfect object `K` of `D(O)` the canonical map of Stacks 08JD at `M = K` is invertible.

This is the assertion Stacks 0FPU cites, from [Stacks, Tag 08JJ], in order to define the
coevaluation; the source states it only at `M = K`, which is the case registered here.  The
general statement, for an arbitrary target and an arbitrary derived tensor product datum, is
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`, which is where
the mathematics is; nothing is re-proved here. -/
@[stacks 0FPU "tensor_hom_iso", sga "5 IIIB 5.0"]
theorem isIso_derivedTensorDualToSheafHom_self
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedTensorDualToSheafHom X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K) :=
  isIso_derivedTensorDualToSheafHom_of_isPerfect X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K hK

/-- **Stacks 0FPU: the coevaluation of a perfect object.**  For a perfect object `K` of `D(O)`
with dual `K^∨ = R𝓗om_O(K, O)` the coevaluation is the morphism

`η : O ⟶ K ⊗^𝐋_O K^∨`

corresponding to `id_K` under the comparison `K ⊗^𝐋_O K^∨ ≅ R𝓗om_O(K, K)` of Stacks 08JD: the
section corresponding to `id_K` (`AlgebraicGeometry.RingedSite.derivedIdentitySection`, the class
of the identity under the two identifications of Stacks 08JA), followed by the inverse of that
comparison.

This is `AlgebraicGeometry.RingedSite.derivedDualCoevaluation`, which takes the invertibility of
the comparison as a hypothesis, with that hypothesis discharged for a perfect `K` by
`isIso_derivedTensorDualToSheafHom_self`. -/
@[stacks 0FPU "coevaluation"]
def coevaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    derivedStructureSheaf X ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj (derivedDual X K) :=
  derivedDualCoevaluation X K (isIso_derivedTensorDualToSheafHom_self X K hK)

/-- **The coevaluation corresponds to `id_K`.**  Composing `η` with the comparison of
Stacks 08JD gives back `AlgebraicGeometry.RingedSite.derivedIdentitySection`, the section
corresponding to the identity of `K`, which is the source's defining property of `η`.  This pins
`coevaluation` down: it is not an unconstrained morphism of its type. -/
theorem coevaluation_comp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    coevaluation X K hK ≫
        derivedTensorDualToSheafHom X
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K =
      derivedIdentitySection X K :=
  derivedDualCoevaluation_comp X K (isIso_derivedTensorDualToSheafHom_self X K hK)

/-! ### The two triangle identities -/

section Pairing

attribute [local instance] derivedTensorMonoidal

/-- **The evaluation of the derived dual, ascribed at the monoidal unit.**  The morphism is
`AlgebraicGeometry.RingedSite.derivedDualEvaluation`; what changes is the spelling of its target,
which is the structure sheaf in degree zero there and the monoidal unit here.  The two are the
same object, but not the same term, and every statement below mentions the monoidal unit beside
the unitors `λ_` and `ρ_`; ascribing the spelling once, here, is what keeps those statements
type-correct at the `implicit` transparency level, so that the rewriting tactics act on them.
The proof of Tag 0FPU on left duals uses the same device for the same reason. -/
def monoidalEvaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedDual X K ⊗ K ⟶
      𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  derivedDualEvaluation X K

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `AlgebraicGeometry.RingedSite.monoidalEvaluation` *is*
`AlgebraicGeometry.RingedSite.derivedDualEvaluation`, the evaluation of Stacks 0FPU. -/
theorem monoidalEvaluation_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    monoidalEvaluation X K = derivedDualEvaluation X K :=
  rfl

/-- **The coevaluation of a perfect object, ascribed at the monoidal unit**; the companion of
`AlgebraicGeometry.RingedSite.monoidalEvaluation`, pinned for the same reason. -/
def monoidalCoevaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      K ⊗ derivedDual X K :=
  coevaluation X K hK

/-- `AlgebraicGeometry.RingedSite.monoidalCoevaluation` *is*
`AlgebraicGeometry.RingedSite.coevaluation`, the coevaluation of Stacks 0FPU. -/
theorem monoidalCoevaluation_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    monoidalCoevaluation X K hK = coevaluation X K hK :=
  rfl

/-- **The comparison of Stacks 08JD at `M = K`, ascribed at the monoidal tensor product.**  The
morphism is `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, whose source is written
as an application of the derived tensor bifunctor; `K ⊗ K^∨` is that application for the
re-seated structure, but not the same term, and the triangle identity below whiskers this
morphism beside a whiskering of the coevaluation.  The spelling is therefore ascribed once,
here. -/
def monoidalDualComparison
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    K ⊗ derivedDual X K ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj K :=
  derivedTensorDualToSheafHom X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `AlgebraicGeometry.RingedSite.monoidalDualComparison` *is* the canonical map of
Stacks 08JD. -/
theorem monoidalDualComparison_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    monoidalDualComparison X K =
      derivedTensorDualToSheafHom X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K K :=
  rfl

/-- `AlgebraicGeometry.RingedSite.coevaluation_comp` in the monoidal spelling. -/
theorem monoidalCoevaluation_comp
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    monoidalCoevaluation X K hK ≫ monoidalDualComparison X K = derivedIdentitySection X K :=
  coevaluation_comp X K hK

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **(E1) at `L = M = K`**, with the comparison and the evaluation in the monoidal spelling:
the only instance of (E1) the triangle identities use. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_self
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    monoidalDualComparison X K ▷ K ≫ derivedSheafHomCounit X K K =
      (α_ K (derivedDual X K) K).hom ≫ (K ◁ monoidalEvaluation X K) ≫ (ρ_ K).hom :=
  derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit X K K

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The evaluation of the derived dual detects endomorphisms of `K^∨`.**  If `c : K^∨ ⟶ K^∨`
satisfies `c ▷ K ≫ ε = ε` then `c` is the identity.  No hypothesis on `K` is needed: the
evaluation is the image of `𝟙_{K^∨}` under the bijection of morphism groups of Stacks 08J8
(`AlgebraicGeometry.RingedSite.derivedDualEvaluation_eq`), and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_eq_tensor_evaluation` says that `c ▷ K ≫ ε` is
the image of `c` under that same bijection, so this is its injectivity.

This is what the closed structure of `D(O)` contributes to the left-dual assertion: it is why one
triangle identity suffices. -/
theorem eq_id_of_whiskerRight_comp_derivedDualEvaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (c : derivedDual X K ⟶ derivedDual X K)
    (hc : c ▷ K ≫ monoidalEvaluation X K = monoidalEvaluation X K) :
    c = 𝟙 (derivedDual X K) := by
  refine (derivedCurryHomEquiv X (derivedDual X K) K (derivedStructureSheaf X)).injective ?_
  rw [derivedCurryHomEquiv_eq_tensor_evaluation X (derivedDual X K) K
      (derivedStructureSheaf X) c,
    ← derivedDualEvaluation_eq X K]
  exact hc

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The identity section names the identity.**  Reading
`AlgebraicGeometry.RingedSite.derivedIdentitySection` back through the two identifications of
Stacks 08JA it was built from gives the identity of `K`. -/
private lemma derivedSheafHomGlobalSectionsEquiv_symm_derivedIdentitySection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomGlobalSectionsEquiv X K K
        ((derivedStructureSheafGlobalSectionsEquiv X
          (((derivedSheafHomBifunctor X).obj (op K)).obj K)).symm
            (derivedIdentitySection X K)) =
      𝟙 K := by
  rw [derivedIdentitySection_eq, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

/-- **Stacks 0FPU, the triangle identity on the perfect object.**  For a perfect `K`, with the
coevaluation `η` and the evaluation `ε`,

`(η ▷ K) ≫ α ≫ (K ◁ ε) = λ ≫ ρ⁻¹`.

The chain is `(η ▷ K) ≫ α ≫ (K ◁ ε) ≫ ρ = ((η ≫ Φ) ▷ K) ≫ app = (ι ▷ K) ≫ app = λ`, whose
first step is (E1), whose middle step is `monoidalCoevaluation_comp` and whose last step is the
unit law (UL), `AlgebraicGeometry.RingedSite.derivedSheafHomCounit_unit_law_monoidal`, at the
section corresponding to `id_K`. -/
@[stacks 0FPU "left_dual"]
theorem evaluation_coevaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    monoidalCoevaluation X K hK ▷ K ≫ (α_ K (derivedDual X K) K).hom ≫
        K ◁ monoidalEvaluation X K = (λ_ K).hom ≫ (ρ_ K).inv := by
  have hι : derivedIdentitySection X K ▷ K ≫ derivedSheafHomCounit X K K = (λ_ K).hom := by
    rw [derivedSheafHomCounit_unit_law_monoidal X K K (derivedIdentitySection X K),
      derivedSheafHomGlobalSectionsEquiv_symm_derivedIdentitySection, Category.comp_id]
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc,
    ← derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_self X K]
  -- The reassociation is an explicit application of `CategoryTheory.Category.assoc`, not a
  -- rewrite: the application morphism of Stacks 08J8 has its source written as an application
  -- of the derived tensor bifunctor and the whiskering has it written `R𝓗om_O(K, K) ⊗ K`, two
  -- spellings of one object, so no rewriting tactic abstracts a motive through the composite.
  refine Eq.trans (Category.assoc (monoidalCoevaluation X K hK ▷ K)
    (monoidalDualComparison X K ▷ K) (derivedSheafHomCounit X K K)).symm ?_
  rw [← comp_whiskerRight, monoidalCoevaluation_comp]
  exact hι

/-- **Stacks 0FPU: the derived dual of a perfect object is a left dual.**  For a perfect object
`K` of `D(O)` the pair `(η, ε)` is an exact pairing — `K^∨ = R𝓗om_O(K, O)` is a left dual of `K`
in the sense of [Stacks, Tag 0FFP] — in the monoidal structure of [Stacks, Tag 0FPT] on `D(O)`.

Only the first triangle identity is checked: the second follows from it by
`CategoryTheory.ExactPairing.ofEvaluationCoevaluation`, because the evaluation detects
endomorphisms of `K^∨` (`eq_id_of_whiskerRight_comp_derivedDualEvaluation`), which is what the
closed structure of `D(O)` supplies. -/
@[stacks 0FPU "left_dual", instance_reducible]
def derivedDualExactPairing
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) : ExactPairing K (derivedDual X K) :=
  ExactPairing.ofEvaluationCoevaluation (monoidalCoevaluation X K hK) (monoidalEvaluation X K)
    (evaluation_coevaluation X K hK) fun c hc =>
      eq_id_of_whiskerRight_comp_derivedDualEvaluation X K c hc

/-- **Stacks 0FPU, the triangle identity on the derived dual.**  For a perfect `K`,

`(K^∨ ◁ η) ≫ α⁻¹ ≫ (ε ▷ K^∨) = ρ ≫ λ⁻¹`.

This is the second clause of `derivedDualExactPairing`, which
`CategoryTheory.ExactPairing.ofEvaluationCoevaluation` derives from the first. -/
@[stacks 0FPU "left_dual"]
theorem coevaluation_evaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    derivedDual X K ◁ monoidalCoevaluation X K hK ≫
        (α_ (derivedDual X K) K (derivedDual X K)).inv ≫
        monoidalEvaluation X K ▷ derivedDual X K =
      (ρ_ (derivedDual X K)).hom ≫ (λ_ (derivedDual X K)).inv :=
  (derivedDualExactPairing X K hK).coevaluation_evaluation'

/-- The coevaluation of `derivedDualExactPairing` is the canonical coevaluation. -/
theorem derivedDualExactPairing_coevaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    letI := derivedDualExactPairing X K hK
    ExactPairing.coevaluation K (derivedDual X K) = monoidalCoevaluation X K hK :=
  rfl

/-- The evaluation of `derivedDualExactPairing` is the canonical evaluation. -/
theorem derivedDualExactPairing_evaluation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    letI := derivedDualExactPairing X K hK
    ExactPairing.evaluation K (derivedDual X K) = monoidalEvaluation X K :=
  rfl

end Pairing

/-! ### The left-dual assertion on an arbitrary ringed site -/

section ArbitraryRingedSite

variable (Y : RingedSite.{u, u, u})

/-- `⊗_O` is additive in its first variable, at the diagonal universes. -/
local instance (priority := high) sheafTensorAdditiveDiagonal :
    (sheafTensor.{u, u, u, u, u} Y.O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (J := Y.J) Y.O

/-- `F ⊗_O -` is additive, at the diagonal universes. -/
local instance (priority := high) sheafTensorObjAdditiveDiagonal
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} (J := Y.J) Y.O A

attribute [local instance high] hasMapBifunctor_sheafTensor

attribute [local instance] derivedTensorMonoidal

/-- **Stacks 0FPU: the derived dual of a perfect object is a left dual, on an arbitrary ringed
site.**  Let `(C, O)` be a ringed site and `K` a perfect object of `D(O)`, with dual
`K^∨ = R𝓗om_O(K, O)`, coevaluation `η` (the section corresponding to `id_K` under
`K ⊗^𝐋_O K^∨ ≅ R𝓗om_O(K, K)`) and evaluation `ε`.  Then `(K^∨, η, ε)` is a left dual of `K`
in the monoidal category `D(O)` of [Stacks, Tag 0FPT], in the sense of [Stacks, Tag 0FFP]: there
is an exact pairing between `K` and `K^∨` whose coevaluation is `η` and whose evaluation is `ε`,
that is, both triangle identities hold for `η` and `ε`.

The only hypothesis is the perfectness of `K`.  The additivity of `⊗_O` in each variable, the
existence of the total tensor complexes, and sheafification of abelian sheaves on the site and
on its slices hold for every ringed site, and are discharged here; the pairing is
`AlgebraicGeometry.RingedSite.derivedDualExactPairing`. -/
@[stacks 0FPU "left_dual"]
theorem exists_exactPairing_derivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : Y.IsPerfect K) :
    ∃ P : ExactPairing K (derivedDual Y K),
      P.coevaluation' = monoidalCoevaluation Y K hK ∧
        P.evaluation' = monoidalEvaluation Y K :=
  ⟨derivedDualExactPairing Y K hK, rfl, rfl⟩

end ArbitraryRingedSite

end AlgebraicGeometry.RingedSite

end
