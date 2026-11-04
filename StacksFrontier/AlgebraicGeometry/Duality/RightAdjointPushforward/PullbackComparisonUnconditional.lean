module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.RightAdjointDirectSumsUnconditional

/-!
# Equation 48.8.0.1 is an isomorphism for a perfect proper morphism

Let `f : X ⟶ Y` be a morphism of schemes and `a` a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. [Stacks, Tag 0A9U] says that the map
`Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 ([Stacks, Tag 0A9S]) is an isomorphism for
every `K` when `f` is a perfect proper morphism of Noetherian schemes. The source's proof is a
dévissage: both sides are exact functors of `K` commuting with direct sums (for the right-hand
side this is [Stacks, Tag 0A9R]), `D_QCoh(𝒪_Y)` is compactly generated ([Stacks, Tag 09IS]),
and the map is an isomorphism at perfect objects ([Stacks, Tag 0A9T]).

`CategoryTheory.MonoidalProjectionFormula.isIso_comparisonUnit_app` is that dévissage for an
arbitrary monoidal functor with two successive right adjoints, and
`Stacks.Duality.compareWithPullback_pullbackCotensorator` identifies Equation 48.8.0.1 with it.
This file supplies its inputs on `D_QCoh`: the exactness of `Lf^*`, of `Rf_*`, of `a` and of
tensoring on the right, their commutation with direct sums (for `a` this is [Stacks, Tag 0A9R],
`Stacks.Duality.preservesCoproducts_twistedInverseImage_of_perfect_proper`), the compact
generators of `Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory`,
and their dualizability, `Stacks.Duality.nonempty_hasRightDual_of_isCompactObject`. The perfect
case [Stacks, Tag 0A9T] enters, as in the source, through the dualizable case of the abstract
statement.

## Main results

* `Stacks.Duality.isIso_compareWithPullback_twistedInverseImage` — the map of Equation 48.8.0.1
  is an isomorphism for a perfect proper morphism of Noetherian schemes ([Stacks, Tag 0A9U]).
* `Stacks.Duality.isIso_compareWithPullback_of_perfect_of_isProper` — the same at any right
  adjoint of `Rf_*`.
* `Stacks.Duality.compareWithPullbackIso` — the isomorphism `Lf^*K ⊗ᴸ f^×(𝒪_Y) ≅ f^×(K)`.
* `Stacks.Duality.isIso_projectionFormulaMap_pullbackCotensorator` — the projection formula on
  `D_QCoh` at the locally small model ([Stacks, Tag 08EU]).

The intermediate forms `isIso_projectionFormulaMap_pullbackCotensorator_of_hasRightDual`,
`isIso_compareWithPullback_of_hasRightDual` and
`isIso_compareWithPullback_of_perfect_of_isProper_of_hasRightDual` state the dévissage over its
inputs (dualizability of compact objects, commutation of `a` with direct sums) for an arbitrary
quasi-compact quasi-separated `f` with quasi-compact quasi-separated target.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- `Lf^*` on `D_QCoh` is exact, for the shift structure it has as the left adjoint of `Rf_*`. -/
theorem isTriangulated_quasiCoherentDerivedPullback' :
    letI := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      hpush
    (quasiCoherentDerivedPullback' f).IsTriangulated := by
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      hpush
  let := (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    hpush).commShift_of_rightAdjoint ℤ
  exact (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    hpush).isTriangulated_leftAdjoint

/-- The projection formula ([Stacks, Tag 08EU]) on `D_QCoh` at the locally small model, for a
quasi-compact quasi-separated morphism with quasi-compact quasi-separated target all of whose
compact objects are dualizable: the projection-formula map at
`Stacks.Duality.pullbackCotensorator f` is an isomorphism. -/
theorem isIso_projectionFormulaMap_pullbackCotensorator_of_hasRightDual
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hdual : ∀ K : quasiCoherentDerivedCategory Y, IsCompactObject.{u} K →
      Nonempty (@HasRightDual _ _ (quasiCoherentDerivedMonoidal Y) K))
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f hpush (pullbackCotensorator f) E K) := by
  let := quasiCoherentDerivedMonoidal X
  let := quasiCoherentDerivedMonoidal Y
  let := quasiCoherentDerivedPullbackMonoidal f
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      hpush
  have := isTriangulated_quasiCoherentDerivedPullback' f hpush
  have := hasCoproducts_quasiCoherentDerivedCategory Y
  have hF := (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    hpush).leftAdjoint_preservesColimits
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedPushforward f hpush) := fun J =>
    LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward f hpush J
  obtain ⟨ι, G, hGc, hG⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory Y
  rw [projectionFormulaMap_pullbackCotensorator]
  exact MonoidalProjectionFormula.isIso_projectionFormulaMap _ E G hGc hG
    (fun i n => (hdual _ (isCompactObject_shift (hGc i) n)).some) K

/-- Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism with quasi-compact
quasi-separated target, such that every compact object of `D_QCoh(𝒪_Y)` is dualizable and the
projection-formula maps are isomorphisms, and let `a` be a right adjoint of `Rf_*` commuting with
direct sums. Then
the map `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 is an isomorphism for every `K`;
this is the dévissage of [Stacks, Tag 0A9U]. -/
theorem isIso_compareWithPullback_of_hasRightDual
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hdual : ∀ K : quasiCoherentDerivedCategory Y, IsCompactObject.{u} K →
      Nonempty (@HasRightDual _ _ (quasiCoherentDerivedMonoidal Y) K))
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f hpush (pullbackCotensorator f) E K)]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
    (ha : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) a)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullback f hpush (pullbackCotensorator f) adj
      quasiCoherentRightUnitor K) := by
  let := quasiCoherentDerivedMonoidal X
  let := quasiCoherentDerivedMonoidal Y
  let := quasiCoherentDerivedPullbackMonoidal f
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      hpush
  have := isTriangulated_quasiCoherentDerivedPullback' f hpush
  have := hasCoproducts_quasiCoherentDerivedCategory Y
  have hF := (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    hpush).leftAdjoint_preservesColimits
  let := adj.rightAdjointCommShift ℤ
  let := adj.commShift_of_leftAdjoint ℤ
  have : a.IsTriangulated := adj.isTriangulated_rightAdjoint
  have := ha
  have : ∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (MonoidalProjectionFormula.projectionFormulaMap
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        E K) := fun E K => by
    rw [← projectionFormulaMap_pullbackCotensorator]
    infer_instance
  obtain ⟨ι, G, hGc, hG⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory Y
  rw [compareWithPullback_pullbackCotensorator]
  exact MonoidalProjectionFormula.isIso_comparisonUnit_app _ adj G hGc hG
    (fun i n => (hdual _ (isCompactObject_shift (hGc i) n)).some) K

/-- **Equation 48.8.0.1 is an isomorphism for a perfect proper morphism of Noetherian schemes, at
every right adjoint `a` of `Rf_*`, given dualizability of compact objects.** -/
theorem isIso_compareWithPullback_of_perfect_of_isProper_of_hasRightDual [IsNoetherian X]
    [IsNoetherian Y] [IsProper f] [AlgebraicGeometry.Perfect f]
    (hdual : ∀ K : quasiCoherentDerivedCategory Y, IsCompactObject.{u} K →
      Nonempty (@HasRightDual _ _ (quasiCoherentDerivedMonoidal Y) K))
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (pullbackCotensorator f) E K)]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⊣ a)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (pullbackCotensorator f) adj quasiCoherentRightUnitor K) :=
  isIso_compareWithPullback_of_hasRightDual f _ hdual adj
    (fun J => have := preservesCoproducts_twistedInverseImage_of_perfect_proper f J
      preservesColimitsOfShape_of_natIso
        ((twistedInverseImageAdjunction f _).rightAdjointUniq adj)) K

/-! ### Unconditionally -/

/-- The projection formula ([Stacks, Tag 08EU]) on `D_QCoh` at the locally small model, for a
quasi-compact quasi-separated morphism with quasi-compact quasi-separated target, read at the
cotensorator `Stacks.Duality.pullbackCotensorator f`: the projection-formula map
`K ⊗ᴸ Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ E)` is an isomorphism. -/
instance isIso_projectionFormulaMap_pullbackCotensorator
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaMap f hpush (pullbackCotensorator f) E K) :=
  isIso_projectionFormulaMap_pullbackCotensorator_of_hasRightDual f hpush
    (nonempty_hasRightDual_of_isCompactObject Y) E K

/-- **Equation 48.8.0.1 is an isomorphism for a perfect proper morphism of Noetherian schemes, at
every right adjoint `a` of `Rf_*`.** -/
theorem isIso_compareWithPullback_of_perfect_of_isProper [IsNoetherian X] [IsNoetherian Y]
    [IsProper f] [AlgebraicGeometry.Perfect f]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⊣ a)
    (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (pullbackCotensorator f) adj quasiCoherentRightUnitor K) :=
  isIso_compareWithPullback_of_perfect_of_isProper_of_hasRightDual f
    (nonempty_hasRightDual_of_isCompactObject Y) adj K

/-- Let `f : X ⟶ Y` be a perfect proper morphism of Noetherian schemes and
let `a = f^×` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]).
The map `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of Equation 48.8.0.1 ([Stacks, Tag 0A9S]) is an
isomorphism for every object `K` of `D_QCoh(𝒪_Y)`.

The same holds at any right adjoint of `Rf_*`, by
`Stacks.Duality.isIso_compareWithPullback_of_perfect_of_isProper`. -/
@[stacks 0A9U]
theorem isIso_compareWithPullback_twistedInverseImage [IsNoetherian X] [IsNoetherian Y]
    [IsProper f] [AlgebraicGeometry.Perfect f] (K : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (pullbackCotensorator f)
      (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
      quasiCoherentRightUnitor K) :=
  isIso_compareWithPullback_of_perfect_of_isProper f _ K

/-- The isomorphism `Lf^*K ⊗ᴸ_{𝒪_X} f^×(𝒪_Y) ≅ f^×(K)` of [Stacks, Tag 0A9U] for a perfect
proper morphism of Noetherian schemes, the map being Equation 48.8.0.1. -/
def compareWithPullbackIso [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    [AlgebraicGeometry.Perfect f] (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y)) ≅
      (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K :=
  haveI := isIso_compareWithPullback_twistedInverseImage f K
  asIso (compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (pullbackCotensorator f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    quasiCoherentRightUnitor K)

/-- The isomorphism `Stacks.Duality.compareWithPullbackIso` is Equation 48.8.0.1. -/
@[simp]
theorem compareWithPullbackIso_hom [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    [AlgebraicGeometry.Perfect f] (K : quasiCoherentDerivedCategory Y) :
    (compareWithPullbackIso f K).hom =
      compareWithPullback f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (pullbackCotensorator f)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        quasiCoherentRightUnitor K :=
  rfl

end Stacks.Duality
