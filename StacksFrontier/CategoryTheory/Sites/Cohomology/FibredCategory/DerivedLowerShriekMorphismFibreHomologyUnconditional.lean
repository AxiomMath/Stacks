module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekMorphismFibreHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.UliftFreeCoverGenerators
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08PK with no hypothesis

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `Lg_!` be the left derived lower-shriek functor of the
induced morphism of topoi `g : Sh(C') ⟶ Sh(C)`. Stacks 08PK computes `L_n g_!(F')` as the sheaf
associated to the presheaf `U ↦ H_n(I_U, F'_U)`, where `I_U` is the fibre over `U` of the
amelioration `C''` of `u` and `F'_U` is `(U', φ) ↦ F'(U')`.

`DerivedLowerShriekMorphismFibreHomology.lean` proves this identification,
`MorphismSituation.derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf`, with the side
conditions of its section — sheafification on the amelioration, right adjointness of the three
restrictions, the pointwise right Kan extensions presenting them and the existence of `Lg_!` and
`Lg''_!` — as instance arguments, and the three acyclicity statements as arguments. This file
discharges all of them.

## Main results

* `MorphismSituation.hasSheafifyAmelioratedTopology` and the instances after it: the size
  conditions of `DerivedLowerShriekMorphismFibreHomology.lean`, seated as instances. The
  amelioration is small by construction, so sheafification exists and the three restrictions are
  right adjoints; the pointwise right Kan extensions exist for the same reason.
* `MorphismSituation.hasPointwiseLeftDerivedFunctor_amelioratedAbelianLowerShriekOnHomotopy`:
  the existence of `Lg''_!` (Stacks 07AC for the projection of the amelioration), seated here at
  the coefficient universe of the ameliorated situation. The existence of `Lg_!` is the instance
  `MorphismSituation.hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy` of
  `MorphismLowerShriekAcyclic.lean`.
* `MorphismSituation.derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf_unconditional`:
  **Stacks 08PK**, with no hypothesis. The two acyclicity statements of Stacks 07AC are
  `MorphismSituation.abelianLowerShriekAcyclic` and
  `FibredCategorySituation.abelianLowerShriekAcyclic`, and the cover acyclicity that Stacks 08PJ
  consumes follows from `FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic` by
  `uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

namespace MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

attribute [local instance] HasDerivedCategory.standard

/-- Sheafification of abelian presheaves exists on the amelioration, which is small. -/
instance hasSheafifyAmelioratedTopology :
    HasSheafify (amelioratedSituation S).topology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  hasSheafify_addCommGrpCat.{max u₁ u₂ v₁ v₂, max u₁ u₂ v₁ v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}
    (amelioratedSituation S).topology

/-- The weak form of sheafification on the amelioration, recorded so that the existence of the
left adjoints of the three restrictions is found without re-deriving it. -/
instance hasWeakSheafifyAmelioratedTopology :
    HasWeakSheafify (amelioratedSituation S).topology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  (hasSheafifyAmelioratedTopology S).isRightAdjoint

/-- Restriction along the retraction of the amelioration is a right adjoint. -/
instance amelioratedLowerShriek_isRightAdjoint : (amelioratedLowerShriek S).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (amelioratedRetraction S)
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (amelioratedSituation S).topology
    S.sourceTopology).isRightAdjoint

/-- Restriction along the inclusion of the source into the amelioration is a right adjoint. -/
instance amelioratedInverseImage_isRightAdjoint : (amelioratedInverseImage S).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (amelioratedInclusion S)
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology
    (amelioratedSituation S).topology).isRightAdjoint

/-- Restriction along the projection of the amelioration is a right adjoint. -/
instance amelioratedBaseInverseImage_isRightAdjoint :
    (amelioratedSituation S).abelianInverseImage.IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (amelioratedProjection S)
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} (amelioratedSituation S).topology
    S.totalTopology).isRightAdjoint

/-- Every abelian presheaf on the amelioration has a pointwise right Kan extension along the
opposite of the retraction of the amelioration. -/
instance amelioratedRetraction_hasPointwiseRightKanExtension
    (F : (amelioratedTotal S)ᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (amelioratedRetraction S).op.HasPointwiseRightKanExtension F := inferInstance

/-- Every abelian presheaf on the source has a pointwise right Kan extension along the opposite
of the inclusion of the source into the amelioration. -/
instance amelioratedInclusion_hasPointwiseRightKanExtension
    (F : S.sourceᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (amelioratedInclusion S).op.HasPointwiseRightKanExtension F := inferInstance

/-- Every abelian presheaf on the amelioration has a pointwise right Kan extension along the
opposite of the projection of the amelioration. -/
instance amelioratedProjection_hasPointwiseRightKanExtension
    (F : (amelioratedTotal S)ᵒᵖ ⥤ AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (amelioratedProjection S).op.HasPointwiseRightKanExtension F := inferInstance

/-- The left derived functor of the lower-shriek functor of the projection of the amelioration,
composed with `DerivedCategory.Qh`, exists pointwise with respect to quasi-isomorphisms. -/
instance hasPointwiseLeftDerivedFunctor_amelioratedAbelianLowerShriekOnHomotopy :
    ((amelioratedSituation S).abelianLowerShriekOnHomotopy ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (amelioratedSituation S).topology
        AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ)) :=
  (amelioratedSituation S).hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy

/-- For an abelian sheaf `F'` on the source, `L_n g_!(F')` is the sheaf on the total category
associated to the presheaf `U ↦ H_n(I_U, F'_U)`, where `I_U` is the fibre over `U` of the
amelioration of `u`. -/
@[stacks 08PK "L_n g_!(F') is the sheaf of H_n(I_U, F'_U)"]
def derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf_unconditional (n : ℕ)
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    (S.derivedAbelianLowerShriekHomology n).obj F' ≅
      fiberHomologySheaf (amelioratedSituation S)
        ((amelioratedLowerShriek S).obj F').obj n :=
  derivedAbelianLowerShriekHomologyObjIsoFiberHomologySheaf S S.abelianLowerShriekAcyclic
    (amelioratedSituation S).abelianLowerShriekAcyclic
    ((amelioratedSituation S).uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic
      (FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic _)) n F'

end MorphismSituation

end Stacks.Sites.FibredCategory

end
