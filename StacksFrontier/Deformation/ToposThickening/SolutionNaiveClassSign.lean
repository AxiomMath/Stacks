module

public import StacksFrontier.Deformation.AlgebraExtension.ConormalExtClass
public import StacksFrontier.Deformation.AlgebraExtension.ExtClass
public import StacksFrontier.Deformation.ToposThickening.CanonicalCotangentObstruction
public import StacksFrontier.Deformation.ToposThickening.ExtensionPresentationRemark

/-!
# The class of a solution and the class of an extension of algebras: the sign

Let `S` be a square-zero extension problem of ringed topoi (Stacks 08UF). A solution `𝒪'` of `S`
is in particular an extension `0 → 𝒢 → 𝒪' → 𝒪 → 0` of `f⁻¹𝒪_{B'}`-algebras, through its map from
the thickened base. Two classes in `Ext¹_𝒪(NL_{𝒪/f⁻¹𝒪_{B'}}, 𝒢)` are attached to it:

* `...RingedToposExtensionProblem.solutionNaiveClass`, the obstruction class of Stacks 08UG
  separating the trivial extension `𝒪 ⊕ 𝒢` from `𝒪'`, as in the proof of Stacks 08UK;
* `Deformation.AlgebraExtension.extClass` of the extension of algebras, the class of Stacks 0GQ5
  computed from the conormal map of a lift of generators.

This file proves that they are opposite. On the generators given by the local sections of `𝒪'`
itself, lifted to `𝒪 ⊕ 𝒢` with zero `𝒢`-component, the difference map of Stacks 08UG is the
conormal map of the identity lift, and the two constructions read a conormal map in
`Ext¹(NL, 𝒢)` with opposite signs
(`Deformation.AlgebraExtension.presentationConormalExtClass_eq_neg`).

## Main definitions

* `...RingedToposExtensionProblem.thickenedAlgebraExtension`: a solution of the problem over the
  thickened base, as an extension of `f⁻¹𝒪_{B'}`-algebras.

## Main results

* `...RingedToposExtensionProblem.solutionNaiveClass_eq_neg_extClass`: the class of a solution is
  minus the class of its extension of `f⁻¹𝒪_{B'}`-algebras.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra Stacks.Sheaves.Differentials

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  (S : RingedToposExtensionProblem X B)

/-- **A solution of the problem over the thickened base, as an extension of
`f⁻¹𝒪_{B'}`-algebras**: its map from `f⁻¹𝒪_{B'}` is the algebra structure. -/
def thickenedAlgebraExtension (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) :
    Deformation.AlgebraExtension (J := X.J) S.squareZeroProblem.f.fSharpInverseImage
      S.squareZeroProblem.G where
  extension := Q.extension
  reduction := Q.reduction
  locallySurjective := Q.locallySurjective
  squareZero := Q.squareZero
  algebraMap := Q.baseMap
  algebraMap_reduction := Q.baseMap_reduction.trans
    ((congrArg (· ≫ S.squareZeroProblem.f.fSharpInverseImage)
      ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).map_id
        S.baseExtension)).trans (Category.id_comp _))
  kernelInclusion := Q.kernelInclusion
  kernelZero := Q.kernelZero
  kernelUniversal := Q.kernelUniversal

namespace CompatibleFirstOrderThickening

variable {S} (Q : S.squareZeroProblem.CompatibleFirstOrderThickening)

/-- The presentation `f⁻¹𝒪_{B'}[𝒪'] ⟶ 𝒪` by the local sections of a solution is surjective. -/
instance isLocallySurjective_sectionsPresentation :
    Presheaf.IsLocallySurjective X.J
      (Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).obj
          S.thickenedBase.O) X.O S.squareZeroProblem.f.fSharpInverseImage
        (underlyingPresheaf X.J Q.extension) Q.reductionSet).hom := by
  have := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q.reduction.hom).mp
    Q.locallySurjective
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc X.J _ X.O
        (underlyingPresheaf X.J Q.extension) S.squareZeroProblem.f.fSharpInverseImage
        Q.reductionSet))

/-- **The pair datum of the trivial extension and a solution on the sections of the solution**:
a local section of `𝒪'` goes to itself in `𝒪'` and to its reduction, with zero `𝒢`-component, in
`𝒪 ⊕ 𝒢`. -/
def sectionsPairDatum :
    PairDatum (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction) Q where
  E := underlyingPresheaf X.J Q.extension
  α := Q.reductionSet
  β₁ := Functor.whiskerRight (Q.reduction ≫ sqZeroExtSheafInl X.O S.squareZeroProblem.G).hom
    (forget CommRingCat.{u})
  β₂ := 𝟙 _
  comm₁ := rfl
  comm₂ := Category.id_comp _
  isLocallySurjective := isLocallySurjective_sectionsPresentation Q

/-- The identity lift of the sections of a solution to its extension of algebras. -/
def sectionsLift :
    Deformation.AlgebraExtension.GeneratorLift Q.reductionSet
      (S.thickenedAlgebraExtension Q) where
  lift := 𝟙 _
  lift_comp := Category.id_comp _

/-- The presentation of the sections pair datum is locally surjective. -/
private instance isLocallySurjective_sectionsPairDatum_presentation :
    Presheaf.IsLocallySurjective X.J (sectionsPairDatum Q).presentation.hom :=
  (sectionsPairDatum Q).isLocallySurjective

omit [X.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- The base change of the free algebra along the (identity) base reduction of the problem over
the thickened base is the identity. -/
theorem baseChange_squareZeroProblem_baseReduction (E : X.Cᵒᵖ ⥤ Type u) :
    baseChange X.J ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).map
      S.squareZeroProblem.baseReduction) E = 𝟙 _ := by
  have h : (inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).map
      S.squareZeroProblem.baseReduction = 𝟙 _ :=
    (inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).map_id S.baseExtension
  exact (congrArg (fun u => baseChange X.J u E) h).trans (baseChange_id X.J _ E)

omit [X.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- Sectionwise form of `baseChange_squareZeroProblem_baseReduction`: the base change along the
base reduction fixes every local section of the free algebra. -/
theorem baseChange_squareZeroProblem_baseReduction_apply (E : X.Cᵒᵖ ⥤ Type u) (U : X.Cᵒᵖ)
    (y : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).obj
      S.squareZeroProblem.baseExtension) E).obj.obj U) :
    (baseChange X.J ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).map
      S.squareZeroProblem.baseReduction) E).hom.app U y = y := by
  rw [baseChange_squareZeroProblem_baseReduction]
  rfl

omit [X.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- The lift to the trivial extension of the sections pair datum is the presentation followed by
the inclusion `𝒪 ⟶ 𝒪 ⊕ 𝒢`: its `𝒢`-component vanishes. -/
theorem sectionsPairDatum_lift₁ :
    (sectionsPairDatum Q).lift₁ =
      (sectionsPairDatum Q).restrictedPresentation ≫
        sqZeroExtSheafInl X.O S.squareZeroProblem.G := by
  rw [Category.assoc, freeAlgebraSheafDesc_comp, baseChange_comp_desc]
  rfl

omit [X.J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms] in
/-- **The difference map of the sections pair datum is the conormal map of the identity lift.** -/
theorem sectionsPairDatum_conormalMap :
    (sectionsPairDatum Q).conormalMap = (sectionsLift Q).conormalHom := by
  refine Deformation.AlgebraExtension.GeneratorLift.conormal_ext fun U g => ?_
  have hp : ((sectionsPairDatum Q).restrictedPresentation).hom.app U g.1 = 0 :=
    (congrArg ((Stacks.SheafOfModules.presentation X.J _ X.O
      S.squareZeroProblem.f.fSharpInverseImage _ Q.reductionSet).hom.app U)
      (baseChange_squareZeroProblem_baseReduction_apply (S := S) _ U g.1)).trans g.2
  let p : Stacks.Sites.Conormal.kernelIdeal (sectionsPairDatum Q).restrictedPresentation.hom U :=
    ⟨g.1, hp⟩
  have h₁ : (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction).incl 0 =
      (sectionsPairDatum Q).lift₁.hom.app U p := by
    rw [CompatibleFirstOrderThickening.incl_zero, sectionsPairDatum_lift₁]
    change (0 : (sqZeroExtSheaf X.O S.squareZeroProblem.G).obj.obj U) =
      (sqZeroExtSheafInl X.O S.squareZeroProblem.G).hom.app U
        (((sectionsPairDatum Q).restrictedPresentation).hom.app U g.1)
    rw [hp, map_zero]
  have h₂ : Q.incl ((sectionsLift Q).restriction U g) = (sectionsPairDatum Q).lift₂.hom.app U p :=
    Deformation.AlgebraExtension.GeneratorLift.incl_restriction (sectionsLift Q) U g
  have key := (sectionsPairDatum Q).conormalMap_conormalClass p 0 _ h₁ h₂
  rw [sub_zero] at key
  refine Eq.trans ?_ (key.trans
    (Deformation.AlgebraExtension.GeneratorLift.conormalHom_relClass (sectionsLift Q) U g).symm)
  congr 2
  exact Subtype.ext (baseChange_squareZeroProblem_baseReduction_apply (S := S) _ U g.1).symm

end CompatibleFirstOrderThickening

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

omit [X.J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- **The class of a solution is minus the class of its extension of algebras.** For a solution
`𝒪'` of the problem `S`, the class `o(𝒪 ⊕ 𝒢, 𝒪') ∈ Ext¹(NL_{𝒪/f⁻¹𝒪_{B'}}, 𝒢)` of Stacks 08UG
(`solutionNaiveClass`) is minus the class of Stacks 0GQ5 of `𝒪'` as an extension of
`f⁻¹𝒪_{B'}`-algebras (`Deformation.AlgebraExtension.extClass`). -/
theorem solutionNaiveClass_eq_neg_extClass (P : S.CompatibleFirstOrderThickening) :
    S.solutionNaiveClass P =
      -Deformation.AlgebraExtension.extClass
        (S.thickenedAlgebraExtension (S.solutionEquivSquareZero P).1) := by
  let Q := (S.solutionEquivSquareZero P).1
  let d := CompatibleFirstOrderThickening.sectionsPairDatum Q
  refine (d.obstruction_eq_pairObstruction).symm.trans ?_
  rw [Deformation.AlgebraExtension.extClass_eq_of_lift
    (CompatibleFirstOrderThickening.sectionsLift Q)]
  change inv _ ≫ Stacks.SheafOfModules.presentationConormalExtClass _ _ _ _ _ _ _ d.conormalMap = _
  rw [CompatibleFirstOrderThickening.sectionsPairDatum_conormalMap]
  exact (congrArg (_ ≫ ·) (Deformation.AlgebraExtension.presentationConormalExtClass_eq_neg
    (δ := (CompatibleFirstOrderThickening.sectionsLift Q).conormalHom))).trans
    (Preadditive.comp_neg _ _)

end Deformation.ToposThickening.RingedToposExtensionProblem

end
