module

public import StacksFrontier.Deformation.ToposThickening.SolutionClassesFibre
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphismClassesExt

/-!
# Existence of solutions, read on `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`

Let `S` be the square-zero extension problem of [Stacks Project, Tag 08UF]: a first order
thickening `O_{B'} ⟶ O_B` of the base with ideal `J`, a morphism of ringed topoi
`f : (Sh(C), O) ⟶ (Sh(B), O_B)`, an `O`-module `G` and `c : f⁻¹J ⟶ G`. A solution is a
square-zero extension of `f⁻¹O_{B'}`-algebras of `O` by `G` inducing `c` on `f⁻¹J`
(`RingedToposExtensionProblem.solutionEquivSquareZero`). Those extensions are the twists
`(O ⋉ G)_ξ` of the trivial one by the classes `ξ ∈ Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` (Tags 08UK and
0GQ5), and twisting by `ξ` changes the map induced on `f⁻¹J` by the restriction of `ξ` to `f⁻¹J`.
So a solution exists exactly when `c` is such a restriction, and the isomorphism classes of
solutions are the classes restricting to `c`. This is the proof of Tag 0GQ9 with the target
`Ext¹_O(Lf^*NL_{O_B/O_{B'}}, G)` read as maps `f⁻¹J ⟶ G`, and the input of part (1) of Tag 08V5.

## Main definitions

* `...CompatibleFirstOrderThickening.idealRestrictionOfExt`: the restriction of a class of
  `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` to the base ideal, `a ↦ δ [a]` for the conormal functional `δ` of
  the class (Tag 08UJ).
* `...CompatibleFirstOrderThickening.classesEquivNaiveExt`: square-zero extensions of
  `f⁻¹O_{B'}`-algebras of `O` by `G`, up to isomorphism, are `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`.

## Main results

* `...CompatibleFirstOrderThickening.idealObstruction_twist`: twisting by `ξ` adds the
  restriction of `ξ` to the obstruction on the base ideal.
* `RingedToposExtensionProblem.idealObstruction_trivialSolution`: the trivial extension induces
  `0` on the base ideal.
* `...CompatibleFirstOrderThickening.nonempty_iff_exists_idealRestrictionOfExt`: solutions exist
  exactly when `c` is the restriction of a class.
* `...CompatibleFirstOrderThickening.classesEquivIdealRestriction`: isomorphism classes of
  solutions are the classes whose restriction to the base ideal is `c`, the fibre of Tag 0GQ9
  read on the base ideal.

## References

* [Stacks Project, Tag 0GQ9](https://stacks.math.columbia.edu/tag/0GQ9)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

omit [X.J.WEqualsLocallyBijective CommRingCat] [HasSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- A section of the base ideal, read as a coefficient of the presentation `f⁻¹O_{B'}[E] ⟶ O`,
lies in its kernel. -/
theorem coeff_idealInclusion_mem {E : X.Cᵒᵖ ⥤ Type u}
    (α : E ⟶ underlyingPresheaf X.J X.O) (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    (freeAlgebraSheafCoefficientMap X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj
        S.baseExtension) E).hom.app U (S.idealInclusion.val.app U a) ∈
      kernelIdeal (Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) X.O
          S.squareZeroProblem.f.fSharpInverseImage E α).hom U := by
  show ((freeAlgebraSheafCoefficientMap X.J _ E) ≫ Stacks.SheafOfModules.presentation X.J
    _ X.O S.squareZeroProblem.f.fSharpInverseImage E α).hom.app U _ = 0
  rw [freeAlgebraSheafCoefficientMap_comp_desc]
  show S.toThickenedBase.fSharpInverseImage.hom.app U _ = 0
  rw [S.toThickenedBase_fSharpInverseImage]
  show S.f.fSharpInverseImage.hom.app U (((inverseImageCommRingFunctor S.f.toToposHom).map
    S.baseReduction).hom.app U (S.idealInclusion.val.app U a)) = 0
  rw [S.idealZero U a, map_zero]

omit [HasWeakSheafify X.J CommRingCat] [X.J.WEqualsLocallyBijective CommRingCat]
  [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasDerivedCategory (Sheaf.targetModules X.J X.O)] in
/-- **The trivial extension `O ⋉ G` over the thickened base induces `0` on the base ideal**, so its
obstruction is `-c`. -/
theorem idealObstruction_trivialSolution (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    S.idealObstruction (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction)
      U a = -(show S.G.val.obj U from S.c.val.app U a) := by
  refine S.kincl_injective (S.squareZeroProblem.trivialSolution
    S.isIso_squareZeroProblem_baseReduction) U ?_
  rw [S.kincl_idealObstruction, S.idealDifference_eq]
  have h0 : (S.squareZeroProblem.trivialSolution
      S.isIso_squareZeroProblem_baseReduction).baseMap.hom.app U
        (S.idealInclusion.val.app U a) = 0 := by
    show (Stacks.Sheaves.Differentials.sqZeroExtSheafInl X.O S.G).hom.app U
      (S.squareZeroProblem.f.fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor S.f.toToposHom).map (𝟙 S.baseExtension)).hom.app U
          (S.idealInclusion.val.app U a))) = 0
    rw [CategoryTheory.Functor.map_id]
    show (Stacks.Sheaves.Differentials.sqZeroExtSheafInl X.O S.G).hom.app U
      (S.toThickenedBase.fSharpInverseImage.hom.app U (S.idealInclusion.val.app U a)) = 0
    rw [S.toThickenedBase_fSharpInverseImage]
    show (Stacks.Sheaves.Differentials.sqZeroExtSheafInl X.O S.G).hom.app U
      (S.f.fSharpInverseImage.hom.app U (((inverseImageCommRingFunctor S.f.toToposHom).map
        S.baseReduction).hom.app U (S.idealInclusion.val.app U a))) = 0
    rw [S.idealZero U a, map_zero, map_zero]
  rw [h0, zero_sub]
  exact (map_neg ((S.squareZeroProblem.trivialSolution
    S.isIso_squareZeroProblem_baseReduction).kernelInclusion.val.app U).hom _).symm

namespace CompatibleFirstOrderThickening

variable {S}

/-- **The restriction of a class of `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` to the base ideal.** A class
`ξ` is the class of a conormal functional `δ_ξ : I/I² ⟶ G` on the presentation of Tag 08UJ, and a
section `a` of `f⁻¹J` is a coefficient of that presentation lying in its kernel `I`; the
restriction sends `a` to `δ_ξ [a]`. -/
def idealRestrictionOfExt (ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1)
    (U : X.Cᵒᵖ) (a : S.I.val.obj U) : S.G.val.obj U :=
  haveI := isLocallySurjective_twistPresentation (S := S.squareZeroProblem) ξ
  (twistFunctional (S := S.squareZeroProblem) ξ).val.app U
    (conormalClass X.J ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).obj
        S.thickenedBase.O) _ X.O
      (freeAlgebraSheafCoefficientMap X.J _ (twistGenerators (S := S.squareZeroProblem) ξ))
      (Stacks.SheafOfModules.presentation X.J _ X.O S.squareZeroProblem.f.fSharpInverseImage
        (twistGenerators (S := S.squareZeroProblem) ξ)
        (twistGeneratorsMap (S := S.squareZeroProblem) ξ)) U
      ⟨_, S.coeff_idealInclusion_mem (twistGeneratorsMap (S := S.squareZeroProblem) ξ) U a⟩)

section Twist

variable (Q : S.squareZeroProblem.CompatibleFirstOrderThickening)
  (ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1)

local notation "E''" => Q.liftedGenerators (twistGeneratorsMap (S := S.squareZeroProblem) ξ)
local notation "β''" => Q.liftedGeneratorsLift (twistGeneratorsMap (S := S.squareZeroProblem) ξ)

/-- A section of the base ideal, as a coefficient of `f⁻¹O_{B'}[E''] ⟶ O`, lies in its kernel. -/
theorem coeff_idealInclusion_mem_thickened (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    (freeAlgebraSheafCoefficientMap X.J S.squareZeroProblem.thickenedBaseInverseImage E'').hom.app
        U (S.idealInclusion.val.app U a) ∈
      kernelIdeal (Q.thickenedPresentation E'' β'').hom U := by
  show ((freeAlgebraSheafCoefficientMap X.J _ E'' ≫
    baseChange X.J S.squareZeroProblem.baseReductionInverseImage E'') ≫
      Q.reducedPresentation E'' β'').hom.app U _ = 0
  rw [freeAlgebraSheafCoefficientMap_comp_baseChange, Category.assoc,
    freeAlgebraSheafCoefficientMap_comp_desc]
  show S.toThickenedBase.fSharpInverseImage.hom.app U
    (((inverseImageCommRingFunctor S.f.toToposHom).map (𝟙 S.baseExtension)).hom.app U
      (S.idealInclusion.val.app U a)) = 0
  rw [CategoryTheory.Functor.map_id, S.toThickenedBase_fSharpInverseImage]
  show S.f.fSharpInverseImage.hom.app U (((inverseImageCommRingFunctor S.f.toToposHom).map
    S.baseReduction).hom.app U (S.idealInclusion.val.app U a)) = 0
  rw [S.idealZero U a, map_zero]

/-- **Twisting by `ξ` adds the restriction of `ξ` to the obstruction on the base ideal.** -/
theorem idealObstruction_twist (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    S.idealObstruction (Q.twist ξ) U a =
      S.idealObstruction Q U a + idealRestrictionOfExt ξ U a := by
  have := isLocallySurjective_twistPresentation (S := S.squareZeroProblem) ξ
  have := Q.isLocallySurjective_reducedPresentation_twist ξ
  let p : kernelIdeal (Q.thickenedPresentation E'' β'').hom U :=
    ⟨_, coeff_idealInclusion_mem_thickened Q ξ U a⟩
  have hlr : Q.incl ((Q.liftRestriction E'' β'').app U p) =
      Q.baseMap.hom.app U (S.idealInclusion.val.app U a) :=
    (Q.incl_liftRestriction E'' β'' U p).trans (congrArg (fun t => t.hom.app U
      (S.idealInclusion.val.app U a)) (freeAlgebraSheafCoefficientMap_comp_desc X.J _
        Q.extension E'' Q.baseMap β''))
  have hQ : S.idealObstruction Q U a =
      (show S.G.val.obj U from (Q.liftRestriction E'' β'').app U p) -
        (show S.G.val.obj U from S.c.val.app U a) := by
    refine S.kincl_injective Q U ?_
    rw [S.kincl_idealObstruction, S.idealDifference_eq]
    exact (congrArg (· - _) hlr.symm).trans (map_sub (Q.kernelInclusion.val.app U).hom _ _).symm
  have hc : (baseChange X.J S.squareZeroProblem.baseReductionInverseImage E'').hom.app U
      (p : (freeAlgebraSheaf X.J S.squareZeroProblem.thickenedBaseInverseImage E'').obj.obj U) =
      (freeAlgebraSheafCoefficientMap X.J _ E'').hom.app U (S.idealInclusion.val.app U a) := by
    have h := congrArg (fun t => t.hom.app U (S.idealInclusion.val.app U a))
      (freeAlgebraSheafCoefficientMap_comp_baseChange X.J
        S.squareZeroProblem.baseReductionInverseImage E'')
    refine h.trans ?_
    show (freeAlgebraSheafCoefficientMap X.J _ E'').hom.app U
      (((inverseImageCommRingFunctor S.f.toToposHom).map (𝟙 S.baseExtension)).hom.app U
        (S.idealInclusion.val.app U a)) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hf : (Stacks.SheafOfModules.freeAlgebraMap X.J _ E'' _
      (Q.liftedGeneratorsFst (twistGeneratorsMap (S := S.squareZeroProblem) ξ))).hom.app U
        ((freeAlgebraSheafCoefficientMap X.J _ E'').hom.app U (S.idealInclusion.val.app U a)) =
      (freeAlgebraSheafCoefficientMap X.J _ (twistGenerators (S := S.squareZeroProblem) ξ)).hom.app
        U (S.idealInclusion.val.app U a) :=
    congrArg (fun t => t.hom.app U (S.idealInclusion.val.app U a))
      (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap X.J _ E''
        (twistGenerators (S := S.squareZeroProblem) ξ)
        (Q.liftedGeneratorsFst (twistGeneratorsMap (S := S.squareZeroProblem) ξ)))
  have hδ : (Q.twistLiftedFunctional ξ).val.app U
      (conormalClass X.J ((inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).obj
        S.thickenedBase.O) _ X.O (freeAlgebraSheafCoefficientMap X.J _ E'')
        (Q.reducedPresentation E'' β'') U
        ⟨(baseChange X.J S.squareZeroProblem.baseReductionInverseImage E'').hom.app U p, p.2⟩) =
      idealRestrictionOfExt ξ U a := by
    show (twistFunctional (S := S.squareZeroProblem) ξ).val.app U
      ((Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u} X.J _ _ _
        (Q.liftedGeneratorsFst (twistGeneratorsMap (S := S.squareZeroProblem) ξ)) X.O
        S.squareZeroProblem.f.fSharpInverseImage _ _
        (Q.reducedGenerators_liftedGenerators _).symm).val.app U _) = _
    refine (congrArg ((twistFunctional (S := S.squareZeroProblem) ξ).val.app U).hom
      (conormalSheafMapOfFac_conormalClass X.J _ X.O _ _ _ _ _ _ _ _ U _)).trans ?_
    unfold idealRestrictionOfExt
    congr 2
    exact Subtype.ext ((congrArg _ hc).trans hf)
  have hδ' : (IdealRestriction.ofConormal (Q.reducedPresentation E'' β'')
      (freeAlgebraSheafCoefficientMap X.J _ E'')
      (baseChange X.J S.squareZeroProblem.baseReductionInverseImage E'')
      (Q.twistLiftedFunctional ξ)).app U p = idealRestrictionOfExt ξ U a := hδ
  have hψ : (show S.G.val.obj U from
        (Q.pushoutRestriction E'' β'' (Q.twistLiftedFunctional ξ)).app U p) -
      (show S.G.val.obj U from S.c.val.app U a) =
      S.idealObstruction Q U a + idealRestrictionOfExt ξ U a := by
    show ((Q.liftRestriction E'' β'').app U p + _) - _ = _
    rw [hQ, hδ']
    exact add_sub_right_comm _ _ _
  refine S.kincl_injective (Q.twist ξ) U ?_
  rw [S.kincl_idealObstruction, S.idealDifference_eq, ← hψ]
  have hb := Stacks.Sites.SqZeroPushout.pushoutMk_inl _ _
    (Q.pushoutDatum E'' β'' (Q.twistLiftedFunctional ξ)) U p
  exact (congrArg (fun y => y - Stacks.Sites.SqZeroPushout.pushoutInr _ _
      (Q.pushoutDatum E'' β'' (Q.twistLiftedFunctional ξ)) U (S.c.val.app U a)) hb).trans
    (map_sub (Stacks.Sites.SqZeroPushout.pushoutInrHom _ _
      (Q.pushoutDatum E'' β'' (Q.twistLiftedFunctional ξ)) U) _ _).symm

end Twist

section Existence

variable [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- Every square-zero extension of `f⁻¹O_{B'}`-algebras is the twist of the trivial one by its
obstruction class against it. -/
theorem isomorphic_twist_trivialSolution (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Isomorphic
      ((S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction).twist
        (pairObstruction (S.squareZeroProblem.trivialSolution
          S.isIso_squareZeroProblem_baseReduction) Q)) Q := by
  let T := pairObstructionData S.squareZeroProblem
  let O := S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction
  refine (pairObstruction_eq_zero_iff_isomorphic _ _).1 ?_
  have h := T.o_add (O.twist (pairObstruction O Q)) O Q
  have h₁ : T.o (O.twist (pairObstruction O Q)) O = -pairObstruction O Q :=
    (T.o_swap _ _).trans (congrArg Neg.neg (pairObstruction_twist O (pairObstruction O Q)))
  show T.o _ _ = 0
  rw [← h, h₁]
  exact neg_add_cancel _

/-- **Solutions exist exactly when `c` is the restriction to the base ideal of a class of
`Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`.** -/
theorem nonempty_iff_exists_idealRestrictionOfExt :
    Nonempty S.CompatibleFirstOrderThickening ↔
      ∃ ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1,
        ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
          idealRestrictionOfExt ξ U a = (show S.G.val.obj U from S.c.val.app U a) := by
  let O := S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction
  constructor
  · rintro ⟨P⟩
    let Q := (S.solutionEquivSquareZero P).1
    have hQ : S.idealObstruction Q = 0 := (S.isCompatibleWithIdeal_iff_idealObstruction_eq_zero
      Q).1 (S.solutionEquivSquareZero P).2
    refine ⟨pairObstruction O Q, fun U a => ?_⟩
    obtain ⟨e⟩ := isomorphic_twist_trivialSolution (S := S) Q
    have h := (congrFun (congrFun (S.idealObstruction_of_iso e) U) a).trans
      (congrFun (congrFun hQ U) a)
    rw [idealObstruction_twist, S.idealObstruction_trivialSolution] at h
    exact (neg_add_eq_zero.1 h).symm
  · rintro ⟨ξ, hξ⟩
    have h : S.IsCompatibleWithIdeal (O.twist ξ) := by
      rw [S.isCompatibleWithIdeal_iff_idealObstruction_eq_zero]
      refine funext fun U => funext fun a => ?_
      rw [idealObstruction_twist, S.idealObstruction_trivialSolution, hξ]
      exact neg_add_cancel _
    exact ⟨S.solutionEquivSquareZero.symm ⟨O.twist ξ, h⟩⟩

/-- The class of `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` of an isomorphism class of square-zero extensions
of `f⁻¹O_{B'}`-algebras: the obstruction class of a representative against the trivial
extension. -/
def extClassOfClass :
    IsomorphismClasses S.squareZeroProblem →
      S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1 :=
  Quotient.lift (pairObstruction
      (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction))
    fun Q Q' h => by
      have h₀ : pairObstruction Q Q' = 0 := (pairObstruction_eq_zero_iff_isomorphic Q Q').2 h
      have h₁ := (pairObstructionData S.squareZeroProblem).o_add
        (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction) Q Q'
      change pairObstruction _ Q + pairObstruction Q Q' = pairObstruction _ Q' at h₁
      rw [h₀, add_zero] at h₁
      exact h₁

/-- **Square-zero extensions of `f⁻¹O_{B'}`-algebras of `O` by `G` are classified by
`Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`**: an isomorphism class goes to its obstruction class against the
trivial extension, and a class `ξ` to the twist of the trivial extension by `ξ`. -/
def classesEquivNaiveExt :
    IsomorphismClasses S.squareZeroProblem ≃
      S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1 where
  toFun := extClassOfClass (S := S)
  invFun ξ := Quotient.mk (isomorphicSetoid S.squareZeroProblem)
    ((S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction).twist ξ)
  left_inv q := by
    induction q using Quotient.ind with
    | _ Q => exact Quotient.sound (isomorphic_twist_trivialSolution (S := S) Q)
  right_inv ξ := pairObstruction_twist _ ξ

omit [X.J.HasSheafCompose (forget CommRingCat)] [(forget CommRingCat).ReflectsIsomorphisms] in
/-- The twist of the trivial extension by `ξ` induces `c` on the base ideal exactly when `c` is
the restriction of `ξ` to the base ideal. -/
theorem isCompatibleWithIdeal_twist_iff
    (ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1) :
    S.IsCompatibleWithIdeal
        ((S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction).twist ξ) ↔
      ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
        idealRestrictionOfExt ξ U a = (show S.G.val.obj U from S.c.val.app U a) := by
  rw [S.isCompatibleWithIdeal_iff_idealObstruction_eq_zero]
  constructor
  · intro h U a
    have h' := congrFun (congrFun h U) a
    rw [idealObstruction_twist, S.idealObstruction_trivialSolution] at h'
    exact (neg_add_eq_zero.1 h').symm
  · intro h
    refine funext fun U => funext fun a => ?_
    rw [idealObstruction_twist, S.idealObstruction_trivialSolution, h]
    exact neg_add_cancel _

/-- **Isomorphism classes of solutions are the classes of `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` whose
restriction to the base ideal is `c`.** A solution is a square-zero extension of
`f⁻¹O_{B'}`-algebras inducing `c` on `f⁻¹J` (`classesEquivCompatible`), such extensions are
classified by `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)` (`classesEquivNaiveExt`), and the twist of the
trivial extension by `ξ` induces `c` exactly when the restriction of `ξ` is `c`. -/
def classesEquivIdealRestriction :
    IsomorphismClasses S ≃
      { ξ : S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1 //
        ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
          idealRestrictionOfExt ξ U a = (show S.G.val.obj U from S.c.val.app U a) } :=
  S.classesEquivCompatible.trans ((classesEquivNaiveExt (S := S)).subtypeEquiv fun q => by
    rw [← isCompatibleWithIdeal_twist_iff]
    induction q using Quotient.ind with
    | _ Q =>
      obtain ⟨e⟩ := isomorphic_twist_trivialSolution (S := S) Q
      exact ⟨fun h => S.isCompatibleWithIdeal_of_iso (CompatibleFirstOrderThickening.Iso.symm e) h,
        fun h => S.isCompatibleWithIdeal_of_iso e h⟩)

end Existence

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
