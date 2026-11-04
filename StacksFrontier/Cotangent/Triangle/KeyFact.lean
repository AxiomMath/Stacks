module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Triangle.BaseChangeComparison

/-!
# The key fact of Tag 08SD, reduced to the Δ-instance of Tag 08RX

Let `A → B → C` be ring maps with `B → C` injective, let `P_•` and `Q_•` be the standard
resolutions of `B` and of `C` over `A`, and let `Q̄_• = Q_• ⊗_{P_•} B` be the base-changed
simplicial `B`-algebra of [Stacks, Tag 08SD]
(`CommAlgCat.baseChangedStandardResolution`). The "key fact" of that remark is that `Q̄_•` is a
*resolution* of `C` over `B` — that is, `CommAlgCat.IsResolution`: every `Q̄_n` is a polynomial
algebra over `B`, and the augmentation `Q̄_• ⟶ C` is a trivial Kan fibration of underlying
simplicial sets.

Those two conditions are exactly the hypotheses `hP` and `hae` carried by
`CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution` in
`StacksFrontier/Cotangent/Triangle/Fundamental.lean`. This file disposes of the first outright and
reduces the second to a single statement, which is the Δ-instance of [Stacks, Tag 08RX] and
nothing else.

## What is proved

* **`hP` is not a hypothesis.** `CommAlgCat.isPolynomialAlgebra_baseChangedStandardResolution`
  is `hP`, proved from the injectivity of `B → C` alone. It is
  `CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra` of
  `StacksFrontier/Cotangent/Triangle/BaseChangeComparison.lean` read at a scalar tower.

* **`hae` is the conclusion of Tag 08RX, and nothing more.**
  `CommAlgCat.trivialKanFibrations_baseChangedStandardResolution_of_quasiIso_leg` is `hae`,
  proved from

  > `QuasiIso ((alternatingFaceMapComplex AddCommGrpCat).map (CommAlgCat.baseChangedLeg f))`,

  the statement that the canonical leg `Q_• ⟶ Q̄_•` of the degreewise pushout is a
  quasi-isomorphism on Moore complexes of underlying simplicial abelian groups.

* **The fundamental triangle under one hypothesis.**
  `CommAlgCat.exists_distTriang_fundamentalVertex_of_quasiIso_leg` is the triangle of
  [Stacks, Tag 08QX] on the three vertices of the display of [Stacks, Tag 08QS], carrying only
  `B → C` injective — as Tag 08SD does — and that one quasi-isomorphism.

## How `hae` is reduced

Three ingredients, in the order they are used.

1. **Degreewise surjectivity.** `CommAlgCat.surjective_baseChangedStandardResolution_hom`: the
   augmentation `Q̄_n ⟶ C` is surjective, because `Q_n ⟶ Q̄_n ⟶ C` is the augmentation of the
   standard resolution of `C` over `A`
   (`CommAlgCat.canonicalBaseChangeMap_augmentation_apply`), which is surjective
   (`CommAlgCat.surjective_standardResolution_augmentation`).

2. **Two out of three.**
   `CommAlgCat.quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg`: the composite of the
   leg `Q_• ⟶ Q̄_•` with the augmentation `Q̄_• ⟶ C` is the augmentation `Q_• ⟶ C`
   (`CommAlgCat.baseChangedLeg_comp_hom`), which is a quasi-isomorphism because the standard
   resolution is a resolution ([Stacks, Tag 08QI],
   `CommAlgCat.standardResolution_isResolution`). So quasi-isomorphy of the leg gives
   quasi-isomorphy of the augmentation.

3. **Tag 08P1.** With the terms polynomial and the augmentation degreewise surjective, a
   quasi-isomorphism of Moore complexes *is* a trivial Kan fibration: this is the equivalence
   `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae` of
   `StacksFrontier/Cotangent/Resolution.lean`, resting on
   `SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso`.

## What remains, exactly

The one open input is

```
QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (CommAlgCat.baseChangedLeg f))
```

Degreewise `CommAlgCat.baseChangedLeg` is the pushout leg `Q_n ⟶ Q_n ⊗_{P_n} B`, so this says
that base change along the augmentation `P_• ⟶ B̲` does not change the homology of the Moore
complex of `Q_•`. That is precisely the Δ-instance of [Stacks, Tag 08RX] — the source's own
justification of the key fact, applied with `𝒞 = Δ`, `𝒪 = P_•`, `𝒪' = B` and `ℱ = Q_•` — whose
two hypotheses hold here: `Q_n` is a polynomial, hence free, hence flat `P_n`-algebra
(`CommAlgCat.standardResolution_isPolynomialAlgebra`, where the injectivity of `B → C` is
consumed), and `s(P_•) ⟶ s(B̲)` is a quasi-isomorphism because `P_•` is a resolution of `B` over
`A` (`CommAlgCat.quasiIso_standardResolution_hom` at `B`).

That statement is set up, and proved in its column direction only, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeOfSimplicialModules.lean`:
`Stacks.SimplicialModules.mooreCochainBaseChange` is the base-change unit on Moore complexes and
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover` (line 915 of that file)
is the column step. Two things stand between that and the statement above.

* **The double-complex assembly**, described in the implementation notes of that file: a
  resolution of the simplicial module by objects `PresheafOfModules.stdCover`, the two
  filtrations of the resulting double complex compared by
  `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound` and
  `…_flip`, with the columns given by the column step and the rows by K-flatness
  (`CochainComplex.KFlat.kFlat_of_flat`,
  `CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`). Nothing of
  this is started.

* **The identification of `CommAlgCat.baseChangedLeg` with that base-change unit**: `Q̄_n` is
  built in this library as a pushout of commutative rings
  (`CommAlgCat.baseChanged_isPushout`), and recognising its underlying abelian group as the
  extension of scalars `ModuleCat.extendScalars (P_n → B)` of `Q_n`, naturally in `n`, is not
  done anywhere.

The generator step of Tag 08RX at a general chaotic site is
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/CoefficientQuasiIsomorphism.lean`; it
mentions no tensor product and is not an input to the route above.

## Main definitions

* `CommAlgCat.forgetAlgToAddCommGrp`: the forgetful functor from commutative `R`-algebras to
  abelian groups, factored as the bridges of Tags 08P1 and 08P2 are stated at.
* `CommAlgCat.baseChangedLeg`: the canonical leg `Q_• ⟶ Q̄_•` on underlying simplicial abelian
  groups.

## Main results

* `CommAlgCat.surjective_baseChangedStandardResolution_hom`: the augmentation `Q̄_• ⟶ C` is
  degreewise surjective.
* `CommAlgCat.flat_standardResolution`: `Q_n` is flat over `P_n` — the flatness hypothesis of
  Tag 08RX, discharged in this instance.
* `CommAlgCat.quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg`: two out of three.
* `CommAlgCat.isResolution_baseChangedStandardResolution_of_quasiIso_leg`: **the key fact of
  Tag 08SD**, granted the Δ-instance of Tag 08RX.
* `CommAlgCat.trivialKanFibrations_relativeBaseChange_of_quasiIso_leg`: the same reduction for
  the hypothesis `hεR` of Remark 08SE, carried by
  `CommAlgCat.baseChangedCotangentComplexIso`.
* `CommAlgCat.isPolynomialAlgebra_baseChangedStandardResolution` and
  `CommAlgCat.trivialKanFibrations_baseChangedStandardResolution_of_quasiIso_leg`: the two
  carried hypotheses of `CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution`, the
  first discharged and the second reduced.
* `CommAlgCat.exists_distTriang_fundamentalVertex_of_quasiIso_leg`: the fundamental triangle
  under `B → C` injective and the Δ-instance of Tag 08RX alone.

## Implementation notes

The statements about `Q̄_•` are given for a map `f : B ⟶ C` of commutative `A`-algebras, as in
`StacksFrontier/Cotangent/Triangle/BaseChangeComparison.lean`, and repeated in the `Tower` section
for a scalar tower `A → B → C` of plain types, which is the form
`StacksFrontier/Cotangent/Triangle/Fundamental.lean` states its hypotheses in.

`CommAlgCat.isResolution_baseChangedStandardResolution` spells its `Algebra` instance out with
`@IsResolution`. The algebra structure on `C` over `B` carried by `Q̄_•` is
`CommAlgCat.algebraOver`, i.e. `f.hom.toRingHom.toAlgebra` bundled into the object
`(CommAlgCat.baseChangedStandardResolution A f).right`, and instance search does not find it
from the carrier alone; the trivial-Kan-fibration form
`CommAlgCat.trivialKanFibrations_baseChangedStandardResolution` needs no instance and is the one
the triangle consumes.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD), the key fact.
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX), what it rests on.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08P1](https://stacks.math.columbia.edu/tag/08P1)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite Simplicial
open AlgebraicTopology

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-- The augmentation of the standard resolution is surjective in every simplicial degree, read
as a ring homomorphism. This is `CommAlgCat.surjective_standardResolution_augmentation` at an
arbitrary object of `Δᵒᵖ` rather than at `⦋n⦌`. -/
theorem surjective_standardResolutionAugmentationHom (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (standardResolutionAugmentationHom A B n) := by
  have hm : n = op ⦋n.unop.len⦌ := by rw [SimplexCategory.mk_len]
  rw [hm]
  exact surjective_standardResolution_augmentation A B n.unop.len

/-- **The augmentation `Q̄_• ⟶ C` is surjective in every simplicial degree.** The composite of
the pushout leg `Q_n ⟶ Q̄_n` with it is the augmentation `Q_n ⟶ C` of the standard resolution of
`C` over `A`, which is surjective. -/
theorem surjective_baseChangedStandardResolution_hom (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((baseChangedStandardResolution A f).hom.app n).hom := by
  intro c
  obtain ⟨q, hq⟩ := surjective_standardResolutionAugmentationHom A C n c
  exact ⟨canonicalBaseChangeMap A f n q,
    (canonicalBaseChangeMap_augmentation_apply f n q).trans hq⟩

/-- The forgetful functor from commutative `R`-algebras to abelian groups, factored as the
composite the two-out-of-three bridges of Tags 08P1 and 08P2 are stated at. -/
abbrev forgetAlgToAddCommGrp (R : Type u) [CommRing R] :
    CommAlgCat.{u} R ⥤ AddCommGrpCat.{u} :=
  forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- **The augmentation `Q̄_• ⟶ C` is a trivial Kan fibration of underlying simplicial sets as
soon as it is a quasi-isomorphism on Moore complexes.** This is [Stacks, Tag 08P1]
(`SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso`)
together with the degreewise surjectivity
`CommAlgCat.surjective_baseChangedStandardResolution_hom`. -/
theorem trivialKanFibrations_baseChangedStandardResolution (f : B ⟶ C)
    (hqi : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (baseChangedStandardResolution A f).hom
        (forgetAlgToAddCommGrp ↥B)))) :
    SSet.trivialKanFibrations (Functor.whiskerRight (baseChangedStandardResolution A f).hom
      (forget (CommAlgCat.{u} ↥B))) := by
  have hforget : Functor.whiskerRight
        (Functor.whiskerRight (baseChangedStandardResolution A f).hom
          (forgetAlgToAddCommGrp ↥B)) (forget AddCommGrpCat.{u}) =
      Functor.whiskerRight (baseChangedStandardResolution A f).hom
        (forget (CommAlgCat.{u} ↥B)) := by
    ext n x
    rfl
  exact hforget ▸
    SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso _
      (fun n => surjective_baseChangedStandardResolution_hom f n)

/-- **`Q̄_• = Q_• ⊗_{P_•} B` is a resolution of `C` over `B`, granted that its augmentation is a
quasi-isomorphism on Moore complexes.** Polynomiality of the terms comes from the injectivity of
`B → C` (`CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra`), the trivial Kan
fibration from the quasi-isomorphism. -/
theorem isResolution_baseChangedStandardResolution (f : B ⟶ C)
    (hf : Function.Injective f.hom)
    (hqi : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (baseChangedStandardResolution A f).hom
        (forgetAlgToAddCommGrp ↥B)))) :
    @IsResolution ↥B B.commRing ↥(algebraOver f) (algebraOver f).commRing (algebraOver f).algebra
      (baseChangedStandardResolution A f).left (baseChangedStandardResolution A f).hom :=
  ⟨baseChangedStandardResolution_isPolynomialAlgebra f hf,
    trivialKanFibrations_baseChangedStandardResolution f hqi⟩

/-- **A polynomial algebra is free, hence flat.** -/
theorem flat_of_isPolynomialAlgebra (R : Type u) [CommRing R] (S : CommAlgCat.{u} R)
    (h : IsPolynomialAlgebra R S) : Module.Flat R ↥S := by
  obtain ⟨ι, ⟨e⟩⟩ := h
  exact Module.Flat.of_linearEquiv (M := MvPolynomial ι R) e.symm.toLinearEquiv

/-- **The flatness hypothesis of Tag 08RX holds in the instance the key fact of Tag 08SD needs
it in.** Every term of the standard resolution of `C` over `A` is flat over the corresponding
term of the standard resolution of `B` over `A`, when `B → C` is injective: it is a polynomial
algebra over it (`CommAlgCat.standardResolution_isPolynomialAlgebra`), hence free, hence flat.

Together with `CommAlgCat.quasiIso_standardResolution_hom` at `B` — which is the second
hypothesis of Tag 08RX, that `s(P_•) ⟶ s(B̲)` be a quasi-isomorphism — this leaves the
Δ-instance of Tag 08RX with no hypothesis left to verify in this situation. -/
theorem flat_standardResolution (f : B ⟶ C) (hf : Function.Injective f.hom)
    (n : SimplexCategoryᵒᵖ) :
    letI : Algebra ((standardResolution A B).left.obj n) ((standardResolution A C).left.obj n) :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    Module.Flat ((standardResolution A B).left.obj n)
      ((standardResolution A C).left.obj n) :=
  flat_of_isPolynomialAlgebra _ _ (standardResolution_isPolynomialAlgebra A f hf n)

/-- **The canonical leg `Q_• ⟶ Q̄_•` on underlying simplicial abelian groups.** Degreewise it is
the pushout leg `CommAlgCat.canonicalBaseChangeMap`, read additively. -/
noncomputable def baseChangedLeg (f : B ⟶ C) :
    (standardResolution A C).left ⋙ forgetAlgToAddCommGrp A ⟶
      (baseChangedStandardResolution A f).left ⋙ forgetAlgToAddCommGrp ↥B where
  app n := AddCommGrpCat.ofHom (canonicalBaseChangeMap A f n).toAddMonoidHom
  naturality i j m := by
    ext q
    exact (canonicalBaseChangeMap_naturality_apply f m q).symm

/-- The canonical leg `Q_• ⟶ Q̄_•` lies over the two augmentations to `C`. -/
theorem baseChangedLeg_comp_hom (f : B ⟶ C) :
    baseChangedLeg f ≫ Functor.whiskerRight (baseChangedStandardResolution A f).hom
        (forgetAlgToAddCommGrp ↥B) =
      Functor.whiskerRight (standardResolution A C).hom (forgetAlgToAddCommGrp A) := by
  ext n q
  exact canonicalBaseChangeMap_augmentation_apply f n q

/-- The augmentation of the standard resolution of `C` over `A` is a quasi-isomorphism of Moore
complexes: the standard resolution is a resolution (Tag 08QI). -/
theorem quasiIso_standardResolution_hom (A : Type u) [CommRing A] (C : CommAlgCat.{u} A) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (standardResolution A C).hom (forgetAlgToAddCommGrp A))) :=
  ((isResolution_quasiIso_homotopyEquivalence_tfae A C (standardResolution A C).left
      (standardResolution A C).hom (standardResolution_obj_isPolynomialAlgebra A C)
      (surjective_standardResolutionAugmentationHom A C)).out 1 2).mp
    (standardResolution_isResolution A C)

/-- **Two out of three: the key fact follows from the conclusion of Tag 08RX.** If the canonical
leg `Q_• ⟶ Q̄_•` is a quasi-isomorphism of Moore complexes, then so is the augmentation
`Q̄_• ⟶ C`, because the composite of the two is the augmentation `Q_• ⟶ C` of the standard
resolution of `C` over `A`, which is a quasi-isomorphism. -/
theorem quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg (f : B ⟶ C)
    (hleg : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (baseChangedLeg f))) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (baseChangedStandardResolution A f).hom
        (forgetAlgToAddCommGrp ↥B))) := by
  have hcomp : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (baseChangedLeg f) ≫
      (alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight (baseChangedStandardResolution A f).hom
          (forgetAlgToAddCommGrp ↥B))) := by
    rw [← Functor.map_comp, baseChangedLeg_comp_hom]
    exact quasiIso_standardResolution_hom A C
  exact quasiIso_of_comp_left ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
    (baseChangedLeg f)) _

/-- **The key fact of Tag 08SD, granted the conclusion of Tag 08RX.** If the canonical leg
`Q_• ⟶ Q̄_•` is a quasi-isomorphism on Moore complexes — which is what the Δ-instance of
Tag 08RX asserts — and `B → C` is injective, then `Q̄_• = Q_• ⊗_{P_•} B` is a resolution of `C`
over `B`. -/
theorem isResolution_baseChangedStandardResolution_of_quasiIso_leg (f : B ⟶ C)
    (hf : Function.Injective f.hom)
    (hleg : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map (baseChangedLeg f))) :
    @IsResolution ↥B B.commRing ↥(algebraOver f) (algebraOver f).commRing (algebraOver f).algebra
      (baseChangedStandardResolution A f).left (baseChangedStandardResolution A f).hom :=
  isResolution_baseChangedStandardResolution f hf
    (quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg f hleg)

/-- **The hypothesis `hεR` of Remark 08SE, reduced in the same way.** `R̄_• = R_• ⊗_{S_•} B` is
`CommAlgCat.baseChangedStandardResolution` at the base ring `B` and the map
`CommAlgCat.overBase f`, so the reduction above applies to it verbatim: the augmentation
`R̄_• ⟶ C` is a trivial Kan fibration as soon as the canonical leg `R_• ⟶ R̄_•` is a
quasi-isomorphism on Moore complexes.

This is the hypothesis carried by `CommAlgCat.isIso_q_relativeBaseChangeCotangentLeg`,
`CommAlgCat.isIso_q_baseChangedCotangentComparison` and
`CommAlgCat.baseChangedCotangentComplexIso`. -/
theorem trivialKanFibrations_relativeBaseChange_of_quasiIso_leg (f : B ⟶ C)
    (hleg : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (baseChangedLeg (overBase f)))) :
    SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B))) :=
  trivialKanFibrations_baseChangedStandardResolution (overBase f)
    (quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg (overBase f) hleg)

/-! ### The tower form, as the fundamental triangle consumes it -/

section Tower

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **The hypothesis `hP` of `CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution` is
not a hypothesis.** Every term of `Q̄_• = Q_• ⊗_{P_•} B` is a polynomial algebra over `B` as soon
as `B → C` is injective, which Tag 08SD assumes anyway. -/
theorem isPolynomialAlgebra_baseChangedStandardResolution
    (hf : Function.Injective (algebraMap B C)) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebra B ((baseChangedStandardResolution A (towerHom A B C)).left.obj n) :=
  baseChangedStandardResolution_isPolynomialAlgebra (towerHom A B C) hf n

/-- **The hypothesis `hae` reduced to the conclusion of Tag 08RX.** The augmentation
`Q̄_• ⟶ C` is a trivial Kan fibration of underlying simplicial sets as soon as the canonical leg
`Q_• ⟶ Q̄_•` is a quasi-isomorphism on Moore complexes. -/
theorem trivialKanFibrations_baseChangedStandardResolution_of_quasiIso_leg
    (hleg : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (baseChangedLeg (towerHom A B C)))) :
    SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A (towerHom A B C)).hom (forget (CommAlgCat.{u} B))) :=
  trivialKanFibrations_baseChangedStandardResolution (towerHom A B C)
    (quasiIso_baseChangedStandardResolution_hom_of_quasiIso_leg (towerHom A B C) hleg)

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Pretriangulated in
/-- **Stacks Project, Tag 08QX, under one carried hypothesis.** The fundamental triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

of the display of Tag 08QS, for `B → C` injective as in Tag 08SD, and granted the Δ-instance of
Tag 08RX in the form of the quasi-isomorphy of the canonical leg `Q_• ⟶ Q̄_•`.

This is `CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution` with its hypothesis `hP`
discharged outright and its hypothesis `hae` reduced to the single open input. -/
theorem exists_distTriang_fundamentalVertex_of_quasiIso_leg
    (hf : Function.Injective (algebraMap B C))
    (hleg : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (baseChangedLeg (towerHom A B C)))) :
    ∃ (α : fundamentalVertex₁.{u, u, u + 1, u + 1} A B C ⟶ fundamentalVertex₂.{u, u, u + 1} A C)
      (β : fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C)
      (δ : fundamentalVertex₃.{u, u, u + 1} B C ⟶
        (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  exists_distTriang_fundamentalVertex_of_isResolution A B C hf
    (isPolynomialAlgebra_baseChangedStandardResolution A B C hf)
    (trivialKanFibrations_baseChangedStandardResolution_of_quasiIso_leg A B C hleg)

end Tower

end CommAlgCat

end
