module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackIsCommutative
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackComp

/-!
# The restriction of a graded algebra on an algebraic space to a scheme point

In Situation 0849 let `X` be an algebraic space over a scheme `S` and let `𝒜` be a
quasi-coherent graded `𝒪_X`-algebra.  The functor of quadruples of Stacks 084A is built from the
restrictions `f^*𝒜` of `𝒜` to the scheme points `f : T ⟶ X`, read as quasi-coherent graded
algebras on the scheme `T` in the sense of Situation 01NN.  This file constructs that restriction.

It is the composite of two operations.  First `𝒜` is pulled back along `f`, viewed as a morphism
from the represented algebraic space `T` to `X`, by the pullback of sheaves of graded algebras of
Stacks 0FQX along the morphism of small étale ringed topoi of Stacks 03G8.  Then the result is
read on the Zariski opens of `T`: a Zariski open is an étale chart of the represented space, and
the reading is the direct image of sheaves of graded algebras along that inclusion of sites, so
its sections over an open are literally the sections over the corresponding étale chart.

## Main definitions

* `AlgebraicGeometry.Space.pointHom`: a scheme point as a morphism from the algebraic space
  `AlgebraicGeometry.Space.yonedaSpace` of the test object.
* `AlgebraicGeometry.Space.etalePointAlgebra`: the pullback of a graded algebra on `X` to the
  small étale site of a scheme point.
* `AlgebraicGeometry.Space.zariskiReading`: a graded algebra on the small étale site of a
  represented algebraic space, read on the Zariski opens of the representing scheme.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`: **the restriction `f^*𝒜`** of the
  graded algebra of Situation 0849 to a scheme point, as graded algebra data of Situation 01NN.

## Main results

* `AlgebraicGeometry.Space.etalePointAlgebra_mul_comm` and
  `AlgebraicGeometry.Space.etalePointAlgebra_eq_zero`: commutativity and the vanishing of a
  homogeneous piece survive the pullback.
* `AlgebraicGeometry.Space.isQuasicoherent_zariskiReading_piece`: the Zariski reading of a
  quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra_def` and
  `AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra_piece`: the restriction `f^*𝒜` is
  the Zariski reading of the pullback of `𝒜`, and so are its homogeneous pieces.

## Implementation notes

The Zariski reading is taken as the direct image along
`AlgebraicGeometry.Space.selfOpensFunctor` rather than as the sheafified chart restriction
`AlgebraicGeometry.Space.restrictToChartScheme`: the two are isomorphic, by
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` and
`AlgebraicGeometry.Space.selfOpensPushforwardIso`, and the isomorphism is how quasi-coherence is
transported, but the direct image has the sections of the original sheaf as its sections, with
the multiplication evaluated there, so no sheafification intervenes in the graded structure.

The construction is stated for a situation whose homogeneous pieces live in the universe of the
schemes, which is the universe in which the pullback of sheaves of graded algebras of
Stacks 0FQX is available.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Zariski reading of a sheaf of graded algebras on the small étale site of a represented
algebraic space. -/
abbrev zariskiReading (T : BigFppfOver B S hS)
    (E : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T))) :
    SheafOfModules.GradedAlgebra.{u, u} (chartScheme (idEtaleChart B S hS T)).ringCatSheaf :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  SheafOfModules.GradedAlgebra.pushforward (selfOpensStructureMap B S hS T) E

variable {X : AlgebraicSpaces B S hS}

/-- A scheme point of an algebraic space, as a morphism of algebraic spaces. -/
abbrev pointHom {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X.1) : yonedaSpace B S hS T ⟶ X :=
  ObjectProperty.homMk f

/-- The pullback of a graded algebra on `X` to the small étale site of a scheme point. -/
abbrev etalePointAlgebra (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)) :=
  (gradedPull (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS (pointHom f))).obj A

/-- Commutativity passes to the pullback to a scheme point. -/
theorem etalePointAlgebra_mul_comm
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (A.piece i).val.obj U)
      (b : (A.piece j).val.obj U), HEq ((A.mul i j).app U a b) ((A.mul j i).app U b a))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (i j : ℤ)
    (U : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ)
    (a : ((etalePointAlgebra A T f).piece i).val.obj U)
    (b : ((etalePointAlgebra A T f).piece j).val.obj U) :
    HEq (((etalePointAlgebra A T f).mul i j).app U a b)
      (((etalePointAlgebra A T f).mul j i).app U b a) :=
  (Stacks.Sheaves.GradedAlgebraPullback.isCommutative_toposPullbackGradedAlgebra
    (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T)) (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposModulesHom B S hS (pointHom f)) A (hB := ⟨hA⟩)).mul_comm i j U a b

/-- A piece of `A` all of whose sections vanish has a pullback all of whose sections vanish. -/
theorem etalePointAlgebra_eq_zero
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ)
    (hn : Limits.IsZero (A.piece n))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1)
    (U : (SmallEtale B S hS (yoneda.obj T))ᵒᵖ)
    (x : ((etalePointAlgebra A T f).piece n).val.obj U) : x = 0 :=
  have := (modulePullbackAdjunction B S hS (pointHom f)).isLeftAdjoint
  SheafOfModules.eq_zero_of_isZero ((modulePullback B S hS (pointHom f)).map_isZero hn) U x

/-- The Zariski reading of a quasi-coherent module on a represented algebraic space is
quasi-coherent. -/
theorem isQuasicoherent_zariskiReading_piece (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N :
        (chartScheme (idEtaleChart B S hS T)).Modules) :=
  ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (chartScheme (idEtaleChart B S hS T)).ringCatSheaf)
    (restrictToChartSchemeIdEtaleChartIso B S hS T N ≪≫ selfOpensPushforwardIso B S hS T N)
    (isQuasicoherent_restrictToChartScheme_idEtaleChart B S hS T N hN)

end

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- **The restriction `f^*𝒜` of the graded algebra of Situation 0849 to a scheme point** `f` of
the algebraic space, as graded algebra data of Situation 01NN on the scheme of the test object:
the pullback of `𝒜` to the small étale site of the represented algebraic space, read on the
Zariski opens of the scheme. -/
def pointAlgebra (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) :
    Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T) :=
  Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra
    (zariskiReading T (etalePointAlgebra s.algebra T f))
    (fun i j _ a b => etalePointAlgebra_mul_comm s.algebra s.mul_comm T f i j _ a b)
    (fun n hn _ x => etalePointAlgebra_eq_zero s.algebra n (s.negative_isZero n hn) T f _ x)
    (fun n => isQuasicoherent_zariskiReading_piece T _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase
        (pointHom f) _ (s.isQuasicoherent n)))

/-- The restriction `f^*𝒜` is the Zariski reading of the pullback of `𝒜` to the small étale site
of the point, with commutativity, the vanishing in negative degrees and quasi-coherence of
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra` supplied by
`AlgebraicGeometry.Space.etalePointAlgebra_mul_comm`,
`AlgebraicGeometry.Space.etalePointAlgebra_eq_zero` and
`AlgebraicGeometry.Space.isQuasicoherent_zariskiReading_piece`. -/
theorem pointAlgebra_def (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    s.pointAlgebra T f =
      Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra
        (zariskiReading T (etalePointAlgebra s.algebra T f))
        (fun i j _ a b => etalePointAlgebra_mul_comm s.algebra s.mul_comm T f i j _ a b)
        (fun n hn _ x => etalePointAlgebra_eq_zero s.algebra n (s.negative_isZero n hn) T f _ x)
        (fun n => isQuasicoherent_zariskiReading_piece T _
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base
            s.containsBase (pointHom f) _ (s.isQuasicoherent n))) :=
  rfl

/-- The homogeneous pieces of the restriction `f^*𝒜` are the Zariski readings of the pullbacks of
the homogeneous pieces of `𝒜`. -/
theorem pointAlgebra_piece (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (n : ℤ) :
    (s.pointAlgebra T f).piece n =
      (zariskiReading T (etalePointAlgebra s.algebra T f)).piece n := by
  rw [pointAlgebra_def]
  rfl

end RelativeProjSituation

end AlgebraicGeometry.Space
