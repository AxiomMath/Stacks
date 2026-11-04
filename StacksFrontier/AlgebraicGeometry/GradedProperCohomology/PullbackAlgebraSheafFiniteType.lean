module

public import StacksFrontier.AlgebraicGeometry.AlgebraExtensionSection.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.Generated
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecProper

/-!
# Finite type passes to the pullback of an algebra sheaf, and to a degreewise pullback

Let `g : Z ⟶ Y` be an arbitrary morphism of schemes. This file proves two statements of finite
type, in the sense of `Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType` — the structural ring map
is of finite type over every affine open:

* the base change `g^* 𝒜` of a quasi-coherent algebra sheaf of finite type is of finite type;
* over an **affine** `Y`, so is the ungraded realization `⨁ₙ g^*(𝓐ₙ)` of the *degreewise*
  pullback of a sheaf of graded algebras whose own ungraded realization is of finite type.

The second is the hypothesis that
`Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` needs in order to produce
local Noetherianness of `Spec_Z(⨁ₙ g^*(𝓐ₙ))`, which is one of the four hypotheses that
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_int_fibreAssociatedGraded`
carries as an instance argument.

## The two steps

Neither statement is about the graded algebra; both are the bridge
`Stacks.AlgebraicGeometry.FiniteTypeDominating.isFiniteType_pushforwardAlgebra_iff` read in the
two directions, with a geometric fact in between.

1. **Base change.** `Spec_Y(𝒜) ⟶ Y` is locally of finite type
   (`Stacks.AlgebraicGeometry.FiniteTypeDominating.locallyOfFiniteType_relativeSpecOver`), the
   relative spectrum commutes with base change ([Stacks, Tag 01LX] part (2),
   `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`), and
   `AlgebraicGeometry.LocallyOfFiniteType` is stable under base change. So
   `Spec_Z(g^* 𝒜) ⟶ Z` is locally of finite type, and finite type of `g^* 𝒜` is the converse
   half of the bridge.
2. **The degreewise pullback.** The comparison of the two pullbacks
   `ψ : g^*(⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ g^*(𝓐ₙ)` is locally surjective over an affine `Y`
   (`Stacks.GradedComap.isLocallySurjective_unitPullbackHom`), and finite type passes to the
   target of a locally surjective morphism of quasi-coherent algebra sheaves
   (`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective`).

## Main results

* `FiniteTypeDominating.isFiniteType_of_locallyOfFiniteType_relativeSpecOver`:
  the converse of `locallyOfFiniteType_relativeSpecOver`.
* `Stacks.AlgebraicGeometry.FiniteTypeDominating.isFiniteType_algebraPullback_obj`: **finite type
  is stable under base change of algebra sheaves.**
* `Stacks.GradedProperCohomology.isFiniteType_pullbackGradedAlgebraSheaf`: **`⨁ₙ g^*(𝓐ₙ)` is of
  finite type over an affine base.**

## Implementation notes

The affineness of `Y` in the second statement is inherited from
`Stacks.GradedComap.isLocallySurjective_unitPullbackHom`, whose proof uses the whole of `Y` as
the affine chart carrying generating global sections of the pieces. It is no restriction at the
fibre of [Stacks, Tag 0D2N], where `Y` is `Spec κ(y)`.

No `@[stacks]` attribute is attached: [Stacks, Tag 01LX] is registered on
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso` and [Stacks, Tag 01T6] on the
Noetherianness transfer; what is here is the finite-type bookkeeping between them.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeDominating

/-- **The converse of
`Stacks.AlgebraicGeometry.FiniteTypeDominating.locallyOfFiniteType_relativeSpecOver`**: an
algebra sheaf whose relative spectrum is locally of finite type over the base is of finite type.
The structure morphism of a relative spectrum is affine, so the bridge
`isFiniteType_pushforwardAlgebra` applies, and `relativeSpecOverIso` identifies its
pushed-forward structure sheaf with the algebra sheaf. -/
theorem isFiniteType_of_locallyOfFiniteType_relativeSpecOver {X : Scheme.{u}}
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A]
    (h : LocallyOfFiniteType (relativeSpecOver A).hom) :
    AlgebraSheaf.IsFiniteType A :=
  let := h
  FiniteTypeSubalgebras.isFiniteType_of_iso (relativeSpecOverIso A)
    (isFiniteType_pushforwardAlgebra (relativeSpecOver A).hom)

/-- **Finite type of a quasi-coherent algebra sheaf is stable under base change along an
arbitrary morphism of schemes.**

`Spec_Z(g^* 𝒜) ⟶ Z` is the base change along `g` of `Spec_Y(𝒜) ⟶ Y` by [Stacks, Tag 01LX]
part (2), the latter is locally of finite type, and `AlgebraicGeometry.LocallyOfFiniteType` is
stable under base change; the conclusion is then the converse half of the bridge between finite
type of an algebra sheaf and finite type of its relative spectrum. -/
theorem isFiniteType_algebraPullback_obj {Z Y : Scheme.{u}} (g : Z ⟶ Y) (𝒜 : AlgebraSheaf Y)
    [AlgebraSheaf.IsQuasicoherent 𝒜] (hft : AlgebraSheaf.IsFiniteType 𝒜) :
    AlgebraSheaf.IsFiniteType ((algebraPullback g).obj 𝒜) := by
  have hq : LocallyOfFiniteType (relativeSpecToBase 𝒜) :=
    locallyOfFiniteType_relativeSpecOver 𝒜 hft
  have hsnd : LocallyOfFiniteType (pullback.snd (relativeSpecToBase 𝒜) g) := inferInstance
  have hiso : IsIso (relativeSpecBaseChangeIso g 𝒜).inv.left :=
    show IsIso ((Over.forget Z).map (relativeSpecBaseChangeIso g 𝒜).inv) from inferInstance
  refine isFiniteType_of_locallyOfFiniteType_relativeSpecOver _ ?_
  have hw : (relativeSpecBaseChangeIso g 𝒜).inv.left ≫
      pullback.snd (relativeSpecToBase 𝒜) g =
      relativeSpecToBase ((algebraPullback g).obj 𝒜) :=
    Over.w (relativeSpecBaseChangeIso g 𝒜).inv
  show LocallyOfFiniteType (relativeSpecToBase ((algebraPullback g).obj 𝒜))
  rw [← hw]
  infer_instance

end Stacks.AlgebraicGeometry.FiniteTypeDominating

namespace Stacks.GradedProperCohomology

open Stacks.Conormal (gradedPullback gradedPullback_mul_comm)
open Stacks.AlgebraicGeometry.FiniteTypeDominating

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (𝓐 : _root_.SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝓐.piece i).val.obj W)
    (b : (𝓐.piece j).val.obj W), HEq ((𝓐.mul i j).app W a b) ((𝓐.mul j i).app W b a))

/-- **The ungraded realization `⨁ₙ g^*(𝓐ₙ)` of a degreewise pullback is an algebra sheaf of
finite type**, for an affine `Y` over which `⨁ₙ 𝓐ₙ` is of finite type.

The base change `g^*(⨁ₙ 𝓐ₙ)` of the ungraded realization downstairs is of finite type by
`Stacks.AlgebraicGeometry.FiniteTypeDominating.isFiniteType_algebraPullback_obj`, and the
comparison of the two pullbacks `ψ : g^*(⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ g^*(𝓐ₙ)` is locally surjective
(`Stacks.GradedComap.isLocallySurjective_unitPullbackHom`), so
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` carries
finite type across it.

With `Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` this is local
Noetherianness of `Spec_Z(⨁ₙ g^*(𝓐ₙ))`, the hypothesis that
`exists_isZero_Hgroup_tensorPowTwist_of_gradedPullbackSpec` and its consumers take as an
instance argument. -/
theorem isFiniteType_pullbackGradedAlgebraSheaf [IsAffine Y]
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)]
    (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent)
    (hft : AlgebraSheaf.IsFiniteType (gradedAlgebraSheaf Y 𝓐 hA)) :
    AlgebraSheaf.IsFiniteType (pullbackGradedAlgebraSheaf g 𝓐 hA) :=
  Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective
    (Stacks.GradedComap.pullbackHom g 𝓐 (gradedPullback g 𝓐)
      (Stacks.GradedComap.unitPieceComparison g 𝓐) hA (gradedPullback_mul_comm g 𝓐 hA))
    (isQuasicoherent_algebraPullback_obj g (gradedAlgebraSheaf Y 𝓐 hA))
    ‹AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)›
    (Stacks.GradedComap.isLocallySurjective_unitPullbackHom g 𝓐 hA hqc)
    (isFiniteType_algebraPullback_obj g (gradedAlgebraSheaf Y 𝓐 hA) hft)

/-- **Local Noetherianness of `Spec_Z(⨁ₙ g^*(𝓐ₙ))`** over a locally Noetherian `Z` and an affine
`Y`: `Stacks.GradedProperCohomology.isLocallyNoetherian_relativeSpecOver` at the finite type just
proved. -/
theorem isLocallyNoetherian_relativeSpecOver_pullbackGradedAlgebraSheaf [IsAffine Y]
    [IsLocallyNoetherian Z]
    [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]
    [AlgebraSheaf.IsQuasicoherent (pullbackGradedAlgebraSheaf g 𝓐 hA)]
    (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent)
    (hft : AlgebraSheaf.IsFiniteType (gradedAlgebraSheaf Y 𝓐 hA)) :
    IsLocallyNoetherian (relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)).left :=
  isLocallyNoetherian_relativeSpecOver (pullbackGradedAlgebraSheaf g 𝓐 hA)
    (isFiniteType_pullbackGradedAlgebraSheaf g 𝓐 hA hqc hft)

end Stacks.GradedProperCohomology

end
