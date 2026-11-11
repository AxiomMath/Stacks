module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleToposBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitFreeModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedToposShift
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0FSC: two out of three for good differential graded modules

Let `Y` be a ringed topos, let `A` be a sheaf of differential graded `O_Y`-algebras on it and let
`0 → K → L → M → 0` be an admissible short exact sequence of right differential graded
`A`-modules, that is, one which splits after the differentials are forgotten. **If two of the
three are good, so is the third**, goodness being `SheafOfModules.IsGoodToposBaseChange`, the
definition of Tag 0FSA: flat as a graded module, K-flat, and — condition (3) — for every
morphism of ringed topoi `f : X ⟶ Y`, every sheaf of differential graded algebras `B` on `X` and
every unital `ψ : A ⟶ f_*B`, a pullback exists and every pullback is flat and K-flat.

## Main results

* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGoodToposBaseChange_right`,
  `isGoodToposBaseChange_left` and `isGoodToposBaseChange_middle`: **Tag 0FSC**, the three cases
  of two out of three.

## Implementation notes

Conditions (1) and (2) are the source's first two sentences: two out of three for flatness and
for K-flatness along an admissible short exact sequence,
`SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGradedFlat_right` and
`isKFlat_right` and their siblings.

For condition (3) the source says that the pullback of the sequence along `(f, B, ψ)` is again an
admissible short exact sequence and that the same argument applies. That is
`SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.toposBaseChange`, which needs
a pullback of each of the three terms. Condition (3) of Tag 0FSA asserts the **existence** of a
pullback, so for the term which is not assumed good one has to be produced, and this is where the
three cases differ.

* **Third term.** `M` is the cokernel of `f : K ⟶ L`, and a pullback is a value of a partial left
  adjoint of the direct image, which preserves colimits
  (`CategoryTheory.Functor.corepresentableByCompCoyonedaObjOfIsColimit`).
* **Middle term.** `L[1]` is the cone of the connecting morphism `δ : M ⟶ K[1]`
  (`SheafOfModules.DifferentialGradedModule.GradedSplitting.coneConnectingIso`), and a pullback
  of a cone is the cone of the pullback
  (`SheafOfModules.DifferentialGradedModule.coneToposCorepresentableBy`); goodness passes to and
  from a shift by `SheafOfModules.IsGoodToposBaseChange.shiftBy`.
* **First term.** `K[1]` is the third term of the admissible short exact sequence
  `0 → C(1_M) → C(g) → K[1] → 0`
  (`SheafOfModules.DifferentialGradedModule.GradedSplitting.isAdmissibleShortExact_cone`), whose
  other two terms are cones of morphisms between good modules; so this case is the third-term case
  applied to that sequence.

The hypotheses are those under which `SheafOfModules.IsGoodToposBaseChange` is stated, with no
addition; in particular no sheafification of types on `Y` is assumed.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section Predicate

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- The cone of a homomorphism of good right differential graded modules is good. This is the
argument of `SheafOfModules.DifferentialGradedModule.cone_isGoodToposBaseChange`, without the
sheafification of types on `Y` which that statement carries and does not use. -/
private theorem isGoodToposBaseChange_cone {P P' : DifferentialGradedModule.{w, w, w} A}
    (φ : P ⟶ P') (hP : IsGoodToposBaseChange.{w, v₁, u₁} P)
    (hP' : IsGoodToposBaseChange.{w, v₁, u₁} P') :
    IsGoodToposBaseChange.{w, v₁, u₁} (cone φ) := by
  have h := isGradedFlat_and_isKFlat_cone φ ⟨hP.isGradedFlat, hP.isKFlat⟩
    ⟨hP'.isGradedFlat, hP'.isKFlat⟩
  refine ⟨h.1, h.2, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨T, ⟨e⟩⟩ := (hP.baseChange f B ψ hψ).1
  obtain ⟨T', ⟨e'⟩⟩ := (hP'.baseChange f B ψ hψ).1
  have hT := (hP.baseChange f B ψ hψ).2 T e
  have hT' := (hP'.baseChange f B ψ hψ).2 T' e'
  have hcone := isGradedFlat_and_isKFlat_cone
    (baseChangeHom (toposDirectImageModules f) ψ hψ e e' φ) hT hT'
  refine ⟨⟨cone (baseChangeHom (toposDirectImageModules f) ψ hψ e e' φ),
    ⟨coneToposCorepresentableBy (toposDirectImageModules f) ψ hψ e e' φ⟩⟩, ?_⟩
  intro Tc ec
  have hiso := ec.uniqueUpToIso
    (coneToposCorepresentableBy (toposDirectImageModules f) ψ hψ e e' φ)
  exact ⟨RelativeTensor.IsGradedFlat.of_iso
      (GradedModule.ofDifferentialGradedIso hiso).symm hcone.1,
    RelativeTensor.IsKFlat.of_iso hiso.symm hcone.2⟩

namespace IsAdmissibleShortExact

variable {K L M : DifferentialGradedModule.{w, w, w} A} {f : K ⟶ L} {g : L ⟶ M}

/-- **Tag 0FSC, the third term.** If the first and the middle term of an admissible short exact
sequence of right differential graded modules are good in the sense of Tag 0FSA, so is the third.

Conditions (1) and (2) are two out of three for flatness and K-flatness. For condition (3) at a
base change `(f, B, ψ)`: the third term is the cokernel of the first map, so a pullback of it is
the cokernel of the pullbacks of the first two, a pullback being a value of a partial left adjoint
of the direct image; and every pullback of it sits in the pullback of the sequence, which is an
admissible short exact sequence whose first two terms are flat and K-flat. -/
@[stacks 0FSC "the third term: if the first and the middle term of an admissible short exact \
sequence are good in the sense of 0FSA (`SheafOfModules.IsGoodToposBaseChange`, condition (3) \
over every morphism of ringed topoi), so is the third"]
theorem isGoodToposBaseChange_right (h : IsAdmissibleShortExact f g)
    (hK : IsGoodToposBaseChange.{w, v₁, u₁} K) (hL : IsGoodToposBaseChange.{w, v₁, u₁} L) :
    IsGoodToposBaseChange.{w, v₁, u₁} M := by
  refine ⟨h.isGradedFlat_right hK.isGradedFlat hL.isGradedFlat,
    h.isKFlat_right hK.isKFlat hL.isKFlat, ?_⟩
  intro X _ _ _ _ _ _ fT B ψ hψ
  obtain ⟨TK, ⟨eK⟩⟩ := (hK.baseChange fT B ψ hψ).1
  obtain ⟨TL, ⟨eL⟩⟩ := (hL.baseChange fT B ψ hψ).1
  have hTK := (hK.baseChange fT B ψ hψ).2 TK eK
  have hTL := (hL.baseChange fT B ψ hψ).2 TL eL
  set F := toposPushforward (toposDirectImageModules fT) ψ hψ with hF
  have hdef : ∀ j : WalkingParallelPair,
      F.leftAdjointObjIsDefined ((parallelPair f 0).obj j) := by
    rintro (_ | _)
    exacts [eK.isCorepresentable, eL.isCorepresentable]
  have eM := Functor.corepresentableByCompCoyonedaObjOfIsColimit (F := F)
    (R := ObjectProperty.lift _ (parallelPair f 0) hdef) h.shortExact.gIsCokernel
    (colimit.isColimit _)
  refine ⟨⟨_, ⟨eM⟩⟩, fun TM eM' => ?_⟩
  have hadm := h.toposBaseChange (toposDirectImageModules fT) ψ hψ eK eL eM'
  exact ⟨hadm.isGradedFlat_right hTK.1 hTL.1, hadm.isKFlat_right hTK.2 hTL.2⟩

/-- **Tag 0FSC, the first term.** If the middle and the third term of an admissible short exact
sequence of right differential graded modules are good in the sense of Tag 0FSA, so is the first.

The shift `K[1]` is the third term of the admissible short exact sequence
`0 → C(1_M) → C(g) → K[1] → 0`, whose first two terms are cones of morphisms between good
modules and hence good; so `K[1]` is good by the third-term case, and `K` is good with it. -/
@[stacks 0FSC "the first term: if the middle and the third term of an admissible short exact \
sequence are good in the sense of 0FSA (`SheafOfModules.IsGoodToposBaseChange`, condition (3) \
over every morphism of ringed topoi), so is the first"]
theorem isGoodToposBaseChange_left (h : IsAdmissibleShortExact f g)
    (hL : IsGoodToposBaseChange.{w, v₁, u₁} L) (hM : IsGoodToposBaseChange.{w, v₁, u₁} M) :
    IsGoodToposBaseChange.{w, v₁, u₁} K := by
  obtain ⟨S⟩ := h
  have h1 := isGoodToposBaseChange_cone (𝟙 M) hM hM
  have h2 := isGoodToposBaseChange_cone g hL hM
  exact isGoodToposBaseChange_of_shiftBy 1
    (S.isAdmissibleShortExact_cone.isGoodToposBaseChange_right h1 h2)

/-- **Tag 0FSC, the middle term.** If the two outer terms of an admissible short exact sequence of
right differential graded modules are good in the sense of Tag 0FSA, so is the middle one.

The shift `L[1]` is the cone of the connecting morphism `δ : M ⟶ K[1]`, a morphism between good
modules, so it is good, and `L` is good with it. -/
@[stacks 0FSC "the middle term: if the two outer terms of an admissible short exact sequence are \
good in the sense of 0FSA (`SheafOfModules.IsGoodToposBaseChange`, condition (3) over every \
morphism of ringed topoi), so is the middle one"]
theorem isGoodToposBaseChange_middle (h : IsAdmissibleShortExact f g)
    (hK : IsGoodToposBaseChange.{w, v₁, u₁} K) (hM : IsGoodToposBaseChange.{w, v₁, u₁} M) :
    IsGoodToposBaseChange.{w, v₁, u₁} L := by
  obtain ⟨S⟩ := h
  have h1 := isGoodToposBaseChange_cone S.connecting hM (hK.shiftBy 1)
  exact isGoodToposBaseChange_of_shiftBy 1 (isGoodToposBaseChange_of_iso S.coneConnectingIso h1)

end IsAdmissibleShortExact

end Predicate

end SheafOfModules.DifferentialGradedModule

end
