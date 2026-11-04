module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
import StacksFrontier.AlgebraicGeometry.Stacks.InvertibleCoherent

/-!
# Descending finite locally free and invertible modules along a limit of algebraic spaces

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms, small enough for the big fppf site, and let `X = lim D` be its limit.  Stacks 0D2X
asserts, in the setting of Stacks 07SK, that every finite locally free `𝒪_X`-module is the
inverse image of a finite locally free `𝒪_{X_i}`-module from some stage, and that every
invertible `𝒪_X`-module is the inverse image of an invertible `𝒪_{X_i}`-module from some stage.

Both clauses are proved, in the setting of Stacks 07SK, as
`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_stage_model` and
`AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FiniteLocallyFreeStageModel.lean`.  This file
records named hypotheses, clauses of *other* tags that this tree does not have, through which the
argument of Stacks 0D2X can be read without the quasi-compactness and quasi-separatedness
assumptions of Stacks 07SK; they are listed under "What is carried" below and none of them is a
clause of Stacks 0D2X.

## Main definitions

* `AlgebraicGeometry.Space.ModuleModelOverSystem`: the essential-surjectivity clause of the
  colimit assertion of Stacks 07V7, as a named hypothesis.
* `AlgebraicGeometry.Space.EventualModuleIsoOverSystem`: the consequence of the fullness and
  faithfulness clauses of Stacks 07V7 that an isomorphism between the inverse images to the
  limit of two finitely presented modules on a stage already exists over a later stage.
* `AlgebraicGeometry.Space.TensorFinitePresentationOnSite`: Stacks 03L6 for the on-site
  rendering of finite presentation, as a named hypothesis.
* `AlgebraicGeometry.Space.EventualFiniteLocallyFreeOverSystem`: the second step of the proof of
  Stacks 0B8W, read on the small étale sites, as a named hypothesis.

## What is carried

**Stacks 07V7, essential surjectivity** (`ModuleModelOverSystem`).  Both clauses of Stacks 0D2X
begin by descending the given module, which is finitely presented, to a stage.  That is the
essential-surjectivity clause of Stacks 07V7, and the notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FinitePresentationModuleColimit.lean` record why it
is out of reach here: it needs the equivalence `QCoh(𝒪_X) = QCoh(U, R, s, t, c)` of Stacks 03M3,
of which this tree has only the functor in one direction, and that functor's essential
surjectivity rests on
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`, which
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean` does not
have.  Only the faithfulness clause of Stacks 07V7 is proved in this tree, and that is not what
either clause of Stacks 0D2X uses.

**Stacks 07V7, fullness and faithfulness** (`EventualModuleIsoOverSystem`).  The proof of clause
(2) descends the trivialization `𝓛 ⊗ 𝓝 ≅ 𝒪_X` to a stage, which is the standard consequence of
fullness and faithfulness that an isomorphism between inverse images comes from a later stage.
Carried in that consequence form rather than as fullness itself, so that the hypothesis is the
weaker of the two.

**Stacks 03L6, on-site** (`TensorFinitePresentationOnSite`).  Clause (2) applies the previous
hypothesis to `𝓛_k ⊗ 𝓝_k` on a stage, so it needs that module to be finitely presented.  Tag
03L6 is proved in this tree as
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentation`, for Mathlib's
`SheafOfModules.IsFinitePresentation`, whereas the Stacks 07V7 hypotheses above are stated —
as the faithfulness clause of the library states them — with the covering-family predicate
`SheafOfModules.IsFinitePresentationOnSite` of Stacks 03DL(7).  The implication from the
covering-family predicate to Mathlib's is
`AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`; there is
no implication back, as the notes of
`StacksFrontier/AlgebraicGeometry/Stacks/InvertibleCoherent.lean` also record, so the two cannot be
composed and the on-site form of Stacks 03L6 is assumed.

**The second step of Stacks 0B8W** (`EventualFiniteLocallyFreeOverSystem`): a finitely presented
module on a stage whose inverse image to the limit is finite locally free becomes finite locally
free along some transition morphism.  This is the hypothesis which
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFiniteLocallyFree_pullback_iso_of_eventually`
carries for schemes under the same name, where it is discharged by the eventual flatness of
Tag 05LY together with Tags 02JO and 00NX.  Neither route is available on the small étale site
of an algebraic space: there is no implication `IsFiniteLocallyFreeOnSite → IsFlat` for sheaves
of modules on a site, and the source's alternative hint — that on a locally ringed site a module
is finite locally free exactly when it admits a dual — needs the dual
`Stacks.SheafOfModules.dualSheaf`, which exists only at module universe `max u v`, whereas the
modules of an algebraic space live at the universe `u` of the schemes.

## Implementation notes

The limit, the stages, the projections and the transition morphisms are the ones Stacks 07SK's
setting is read with in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FinitePresentationModuleColimit.lean`:
`AlgebraicGeometry.Space.limitAlgebraicSpace`, `AlgebraicGeometry.Space.stageAlgebraicSpace`,
`AlgebraicGeometry.Space.limitProjection` and `AlgebraicGeometry.Space.stageTransition`, so the
statements below compose with that file and with Stacks 07SK itself.

## References

* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03L6 for the covering-family rendering of finite presentation**, as a named
hypothesis: the tensor product of two finitely presented `𝒪_Z`-modules on an algebraic space `Z`
is finitely presented in the sense of Stacks 03DL(7). -/
def TensorFinitePresentationOnSite : Prop :=
  ∀ (Z : AlgebraicSpaces B S hS) (M N : Modules.{u, u} B S hS Z.1 Z.2),
    M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(structureSheaf B S hS Z.1 Z.2).obj, Presheaf.isSheaf_of_isSheaf_comp _ ((structureSheaf B S hS Z.1 Z.2).obj) (forget₂ CommRingCat RingCat) ((structureRingPresheaf_isSheaf B S hS Z.1 Z.2))⟩).obj (M))).obj N).IsFinitePresentationOnSite

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **Stacks 07V7, the essential-surjectivity clause of the colimit assertion**, as a named
hypothesis: every finitely presented `𝒪_X`-module on the limit of the system is the inverse
image of a finitely presented `𝒪_{X_i}`-module from some stage. -/
def ModuleModelOverSystem : Prop :=
  ∀ M : Modules.{u, u} B S hS
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).1
      (limitAlgebraicSpace B S hS D hSize hHomSize hD hAffine).2,
    M.IsFinitePresentationOnSite →
      ∃ (i : I) (Mᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
          (stageAlgebraicSpace B S hS D hD i).2),
        Mᵢ.IsFinitePresentationOnSite ∧
          Nonempty (M ≅ (modulePullback B S hS
            (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj Mᵢ)

/-- **Stacks 07V7, the fullness and faithfulness clauses of the colimit assertion in the form of
an eventual isomorphism**, as a named hypothesis: two finitely presented `𝒪_{X_i}`-modules on a
stage whose inverse images to the limit are isomorphic have isomorphic inverse images along some
transition morphism from a later stage. -/
def EventualModuleIsoOverSystem : Prop :=
  ∀ (i : I) (M N : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2),
    M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      Nonempty ((modulePullback B S hS
            (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj M ≅
          (modulePullback B S hS
            (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj N) →
        ∃ (j : I) (e : j ⟶ i),
          Nonempty ((modulePullback B S hS (stageTransition B S hS D hD e)).obj M ≅
            (modulePullback B S hS (stageTransition B S hS D hD e)).obj N)

/-- **The second step of the proof of Stacks 0B8W, read on the small étale sites**, as a named
hypothesis: a finitely presented `𝒪_{X_i}`-module on a stage whose inverse image to the limit is
finite locally free is finite locally free along some transition morphism from a later stage. -/
def EventualFiniteLocallyFreeOverSystem : Prop :=
  ∀ (i : I) (Mᵢ : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2),
    Mᵢ.IsFinitePresentationOnSite →
      SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj Mᵢ) →
        ∃ (j : I) (e : j ⟶ i), SheafOfModules.IsFiniteLocallyFreeOnSite
          ((modulePullback B S hS (stageTransition B S hS D hD e)).obj Mᵢ)

/-- The inverse image along the projection of the limit to a stage, read through a transition
morphism: the inverse image along the projection to a later stage of the inverse image along the
transition morphism. -/
private def limitProjectionPullbackIso {i j : I} (t : j ⟶ i)
    (M : Modules.{u, u} B S hS (stageAlgebraicSpace B S hS D hD i).1
      (stageAlgebraicSpace B S hS D hD i).2) :
    (modulePullback B S hS
        (limitProjection B S hS D hSize hHomSize hD hAffine i)).obj M ≅
      (modulePullback B S hS
          (limitProjection B S hS D hSize hHomSize hD hAffine j)).obj
        ((modulePullback B S hS (stageTransition B S hS D hD t)).obj M) :=
  eqToIso (congrArg (fun g => (modulePullback B S hS g).obj M)
      (limitProjection_comp B S hS D hSize hHomSize hD hAffine t).symm) ≪≫
    ((modulePullbackCompIso B S hS
      (limitProjection B S hS D hSize hHomSize hD hAffine j)
      (stageTransition B S hS D hD t)).app M).symm

end AlgebraicGeometry.Space

end
