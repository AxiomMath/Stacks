module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissibleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Two out of three for goodness along an admissible short exact sequence

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded algebras on it and let
`0 → K → L → M → 0` be an admissible short exact sequence of right differential graded
`A`-modules, that is, one which splits after the differentials are forgotten. If two out of the
three modules are good, so is the third.

Goodness has three conditions: flatness of the underlying right graded module, K-flatness, and
both of those after an arbitrary base change. Two out of three for the first two conditions is
`SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGradedFlat_left` and
`isKFlat_left` and their siblings. This file supplies the third condition, which needs the
pullback of an admissible short exact sequence to be admissible again, and then the full
statement.

## Main results

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.pullback` and
  `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.pullback`: **the pullback of
  an admissible short exact sequence along a morphism of ringed sites is an admissible short
  exact sequence.**
* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.isGood_left`, `isGood_middle`
  and `isGood_right`: **two out of three for goodness**, with goodness in the sense of
  `SheafOfModules.DifferentialGradedModule.IsGood`.
* `isGoodCocontinuousBaseChange_left`, `_middle` and `_right`: the same with goodness in the
  sense of `SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange`.

## Implementation notes

The splitting of an admissible short exact sequence is a retraction and a section of the
*underlying graded* modules, so it does not commute with the differentials and the pullback
functor of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean` cannot be applied
to it; additivity of that functor does not reach it either. What transports it is
`SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackGraded.lean`, the
transport of a homomorphism of underlying graded modules extracted from the degree-zero
universal property through the cofree differential graded module. It is an additive functor
agreeing with the pullback on morphisms of differential graded modules, which is exactly what
the three splitting identities need.

Nothing is assumed of the base change beyond what `IsGood` itself quantifies over: no continuity
of the underlying functor of sites, and no hypothesis on the pullback. In particular the three
results below are about `IsGood` with its own condition (3), not about the variant
`IsGoodCocontinuousBaseChange`, which the direct-sum and filtered-colimit lemmas have to use;
the versions for that predicate are derived from the same splitting.

**Why these are not stated at the definition of Tag 0FSA.** That definition is
`SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
whose condition (3) runs over morphisms of ringed topoi. Transporting the splitting is what
blocks the restatement, in the following precise way. At the topos reading a base change of an
object is an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`, and Mathlib's
`CategoryTheory.Functor.partialLeftAdjoint` makes that assignment functorial on *morphisms of
differential graded modules*, so the two maps of the short exact sequence do transport. The
retraction `r` and the section `s` of a `GradedSplitting` are not such morphisms — they are
homomorphisms of the underlying *graded* modules — and the three identities they satisfy are
the whole content of `GradedSplitting.pullback` above. Along a morphism of ringed sites they
transport by `PullbackData.gradedMap`, which reads a graded homomorphism as a morphism of
differential graded modules into a cofree object, `SheafOfModules.Cofree.cofree`, and then
applies the degree-zero universal property of the `PullbackData`. The same route at a morphism
of ringed topoi needs the direct image of *graded* modules along it and an identification of
`f_{*,ψ}(Cofree.cofree N)` with the cofree object on that direct image. **Both now exist**:
`SheafOfModules.DifferentialGradedModule.toposGradedPushMap` and
`SheafOfModules.DifferentialGradedModule.toposCofreeIsoGraded` of
`DifferentialGradedToposDirectImageCofree.lean`, and the transport itself is
`SheafOfModules.DifferentialGradedModule.toposGradedEquiv` of
`ConeDifferentialGradedModuleToposPullback.lean`, with the unit formula
`toposGradedEquiv_eq`. So the splitting does transport.

What still blocks two out of three at the definition of Tag 0FSA is the other half, and it is
the **existential** in condition (3) of `SheafOfModules.IsGoodToposBaseChange`. A
`PullbackData` hands over the pullback of *every* module at once, so at the site reading the
pullback of the third term is free and the three statements below are symmetric. At the topos
reading a base change has to be *constructed*, and for the term that is not assumed good there
is nothing to construct it from: the middle term of an admissible short exact sequence is the
twisted direct sum of the two outer ones, that is `cone δ` for a connecting
`δ : M[-1] ⟶ K`, and `SheafOfModules.DifferentialGradedModule.cone_isGoodToposBaseChange`
applies to it only once `M[-1]` is known to be good. That needs a shift *down* of a right
differential graded module at this general base — `SheafOfModules.DifferentialGradedModule.shift`
is degree-one only and `translate` exists only over a `RingedSite` in one universe — together
with the base change of a shift being the shift of the base change. Until those exist the
statements below stay at the two site-indexed variants.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace SheafOfModules

namespace DifferentialGradedModule

section Pullback

universe t a m v u a₁ m₁ v₁ u₁

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{t}}
  {w : C ⥤ C₁} {σ : R.obj ⟶ w.op ⋙ R₁.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A₁ : DifferentialGradedAlgebra.{t, a₁} R₁}
  {φ : DifferentialGradedAlgebra.SemilinearHom w σ A A₁}
  {K L M : DifferentialGradedModule.{t, a, m} A} {f : K ⟶ L} {g : L ⟶ M}

/-- **The pullback of an admissible short exact sequence is admissible**: the transport of the
retraction and of the section along the pullback splits the pullback sequence, the transport
being an additive functor which agrees with the pullback on morphisms of differential graded
modules. -/
noncomputable def GradedSplitting.pullback (S : GradedSplitting f g)
    (PD : PullbackData.{t, a₁, m₁, v₁, u₁, a, m, v, u} φ) :
    GradedSplitting (PD.map f) (PD.map g) where
  r := PD.gradedMap (W := L) (Z := K) S.r
  s := PD.gradedMap (W := M) (Z := L) S.s
  f_r := by
    change (forgetToGradedModule A₁).map (PD.map f) ≫ PD.gradedMap (W := L) (Z := K) S.r = 𝟙 _
    rw [← PD.gradedMap_forget f, ← PD.gradedMap_comp ((forgetToGradedModule A).map f) S.r]
    exact (congrArg (PD.gradedMap (W := K) (Z := K)) S.f_r).trans (PD.gradedMap_id (W := K))
  s_g := by
    change PD.gradedMap (W := M) (Z := L) S.s ≫ (forgetToGradedModule A₁).map (PD.map g) = 𝟙 _
    rw [← PD.gradedMap_forget g, ← PD.gradedMap_comp S.s ((forgetToGradedModule A).map g)]
    exact (congrArg (PD.gradedMap (W := M) (Z := M)) S.s_g).trans (PD.gradedMap_id (W := M))
  id := by
    change PD.gradedMap (W := L) (Z := K) S.r ≫ (forgetToGradedModule A₁).map (PD.map f) +
      (forgetToGradedModule A₁).map (PD.map g) ≫ PD.gradedMap (W := M) (Z := L) S.s = 𝟙 _
    rw [← PD.gradedMap_forget f, ← PD.gradedMap_forget g,
      ← PD.gradedMap_comp S.r ((forgetToGradedModule A).map f),
      ← PD.gradedMap_comp ((forgetToGradedModule A).map g) S.s]
    exact (PD.gradedMap_add (S.r ≫ (forgetToGradedModule A).map f)
          ((forgetToGradedModule A).map g ≫ S.s)).symm.trans
      ((congrArg (PD.gradedMap (W := L) (Z := L)) S.id).trans (PD.gradedMap_id (W := L)))

/-- **The pullback of an admissible short exact sequence of right differential graded modules is
an admissible short exact sequence.** -/
theorem IsAdmissibleShortExact.pullback (h : IsAdmissibleShortExact f g)
    (PD : PullbackData.{t, a₁, m₁, v₁, u₁, a, m, v, u} φ) :
    IsAdmissibleShortExact (PD.map f) (PD.map g) :=
  Nonempty.elim h fun S ↦ ⟨S.pullback PD⟩

end Pullback

section Good

universe t m v u m₁ v₁ u₁

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {K L M : DifferentialGradedModule.{t, m, m} A} {f : K ⟶ L} {g : L ⟶ M}

namespace IsAdmissibleShortExact

/-- Two out of three for graded flatness together with K-flatness: the first term. -/
private theorem isGradedFlat_and_isKFlat_left (h : IsAdmissibleShortExact f g)
    (hL : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded L) ∧
      RelativeTensor.IsKFlat L)
    (hM : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded M) ∧
      RelativeTensor.IsKFlat M) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded K) ∧
      RelativeTensor.IsKFlat K :=
  ⟨h.isGradedFlat_left hL.1 hM.1, h.isKFlat_left hL.2 hM.2⟩

/-- Two out of three for graded flatness together with K-flatness: the third term. -/
private theorem isGradedFlat_and_isKFlat_right (h : IsAdmissibleShortExact f g)
    (hK : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded K) ∧
      RelativeTensor.IsKFlat K)
    (hL : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded L) ∧
      RelativeTensor.IsKFlat L) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded M) ∧
      RelativeTensor.IsKFlat M :=
  ⟨h.isGradedFlat_right hK.1 hL.1, h.isKFlat_right hK.2 hL.2⟩

/-- Two out of three for graded flatness together with K-flatness: the middle term. -/
private theorem isGradedFlat_and_isKFlat_middle (h : IsAdmissibleShortExact f g)
    (hK : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded K) ∧
      RelativeTensor.IsKFlat K)
    (hM : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded M) ∧
      RelativeTensor.IsKFlat M) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded L) ∧
      RelativeTensor.IsKFlat L :=
  ⟨h.isGradedFlat_middle hK.1 hM.1, h.isKFlat_middle hK.2 hM.2⟩

/-- **Two out of three for goodness**: if the middle and the third term of an admissible short
exact sequence of right differential graded modules are good, so is the first one. -/
@[stacks 0FSC "two out of three for goodness: the first term, from the middle and the third"]
theorem isGood_left (h : IsAdmissibleShortExact f g)
    (hL : IsGood.{t, m, v, u, m₁, v₁, u₁} L) (hM : IsGood.{t, m, v, u, m₁, v₁, u₁} M) :
    IsGood.{t, m, v, u, m₁, v₁, u₁} K := by
  refine ⟨h.isGradedFlat_left hL.isGradedFlat hM.isGradedFlat,
    h.isKFlat_left hL.isKFlat hM.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD
  exact isGradedFlat_and_isKFlat_left (h.pullback PD) (hL.baseChange u σ A₁ φ PD)
    (hM.baseChange u σ A₁ φ PD)

/-- **Two out of three for goodness**: if the first and the middle term of an admissible short
exact sequence of right differential graded modules are good, so is the third one. -/
@[stacks 0FSC "two out of three for goodness: the third term, from the first and the middle"]
theorem isGood_right (h : IsAdmissibleShortExact f g)
    (hK : IsGood.{t, m, v, u, m₁, v₁, u₁} K) (hL : IsGood.{t, m, v, u, m₁, v₁, u₁} L) :
    IsGood.{t, m, v, u, m₁, v₁, u₁} M := by
  refine ⟨h.isGradedFlat_right hK.isGradedFlat hL.isGradedFlat,
    h.isKFlat_right hK.isKFlat hL.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD
  exact isGradedFlat_and_isKFlat_right (h.pullback PD) (hK.baseChange u σ A₁ φ PD)
    (hL.baseChange u σ A₁ φ PD)

/-- **Two out of three for goodness**: if the two outer terms of an admissible short exact
sequence of right differential graded modules are good, so is the middle one. -/
@[stacks 0FSC "two out of three for goodness: the middle term, from the two outer ones"]
theorem isGood_middle (h : IsAdmissibleShortExact f g)
    (hK : IsGood.{t, m, v, u, m₁, v₁, u₁} K) (hM : IsGood.{t, m, v, u, m₁, v₁, u₁} M) :
    IsGood.{t, m, v, u, m₁, v₁, u₁} L := by
  refine ⟨h.isGradedFlat_middle hK.isGradedFlat hM.isGradedFlat,
    h.isKFlat_middle hK.isKFlat hM.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD
  exact isGradedFlat_and_isKFlat_middle (h.pullback PD) (hK.baseChange u σ A₁ φ PD)
    (hM.baseChange u σ A₁ φ PD)

/-- **Two out of three for goodness**, goodness taken in the sense of
`IsGoodCocontinuousBaseChange`: if the middle and the third term of an admissible short exact
sequence are good, so is the first one. -/
@[stacks 0FSC "two out of three for goodness in the sense of IsGoodCocontinuousBaseChange — \
condition (3) quantified over the base changes whose pullback preserves colimits — the first \
term, from the middle and the third"]
theorem isGoodCocontinuousBaseChange_left (h : IsAdmissibleShortExact f g)
    (hL : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} L)
    (hM : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} M) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} K := by
  refine ⟨h.isGradedFlat_left hL.isGradedFlat hM.isGradedFlat,
    h.isKFlat_left hL.isKFlat hM.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD hPD
  exact isGradedFlat_and_isKFlat_left (h.pullback PD) (hL.baseChange u σ A₁ φ PD hPD)
    (hM.baseChange u σ A₁ φ PD hPD)

/-- **Two out of three for goodness**, goodness taken in the sense of
`IsGoodCocontinuousBaseChange`: if the first and the middle term of an admissible short exact
sequence are good, so is the third one. -/
@[stacks 0FSC "two out of three for goodness in the sense of IsGoodCocontinuousBaseChange — \
condition (3) quantified over the base changes whose pullback preserves colimits — the third \
term, from the first and the middle"]
theorem isGoodCocontinuousBaseChange_right (h : IsAdmissibleShortExact f g)
    (hK : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} K)
    (hL : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} L) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} M := by
  refine ⟨h.isGradedFlat_right hK.isGradedFlat hL.isGradedFlat,
    h.isKFlat_right hK.isKFlat hL.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD hPD
  exact isGradedFlat_and_isKFlat_right (h.pullback PD) (hK.baseChange u σ A₁ φ PD hPD)
    (hL.baseChange u σ A₁ φ PD hPD)

/-- **Two out of three for goodness**, goodness taken in the sense of
`IsGoodCocontinuousBaseChange`: if the two outer terms of an admissible short exact sequence are
good, so is the middle one. -/
@[stacks 0FSC "two out of three for goodness in the sense of IsGoodCocontinuousBaseChange — \
condition (3) quantified over the base changes whose pullback preserves colimits — the middle \
term, from the two outer ones"]
theorem isGoodCocontinuousBaseChange_middle (h : IsAdmissibleShortExact f g)
    (hK : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} K)
    (hM : IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} M) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m₁, v₁, u₁} L := by
  refine ⟨h.isGradedFlat_middle hK.isGradedFlat hM.isGradedFlat,
    h.isKFlat_middle hK.isKFlat hM.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD hPD
  exact isGradedFlat_and_isKFlat_middle (h.pullback PD) (hK.baseChange u σ A₁ φ PD hPD)
    (hM.baseChange u σ A₁ φ PD hPD)

end IsAdmissibleShortExact

end Good

end DifferentialGradedModule

end SheafOfModules

end
