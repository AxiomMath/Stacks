module

public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionRestrict
public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionSquare
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The residual square of Stacks 0D9E (2) from its sheaf-level form

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. `CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare` is what
`CategoryTheory.SimplicialSiteSituation.moduleProjection_restrict_of_adjunctSquare` leaves of the
summandwise comparison `proj_restrict` of Stacks 0D9E (2): the derived adjunct of the canonical
map, carried along `Lf_φ^*` and followed by the derived transition of Stacks 0D9P and by the
identification of the target with `⨁_φ K_m`, is the derived transition at `K` followed by the
`φ`th summand inclusion. Nothing in the development produced it.

This file produces it from the sheaf-level square
`CategoryTheory.SimplicialSiteSituation`
`.transitionPullbackModules_map_componentModuleProjectionAdjunct_comp`:
the derived-image passage that the module docstring of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleProjectionRestrict.lean`
asserts "needs nothing new" is carried out here, in
`CategoryTheory.derivedNatTrans_square` and `CategoryTheory.liftedTransition_square` for the
abstract algebra and here for the instantiation. The sheaf-level square is taken as a hypothesis,
in the exact shape that theorem states it; a second form takes its two coherence hypotheses
instead.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleProjectionAdjunctSquare_of_sheafSquare`:
  **the residual square of Stacks 0D9E (2) holds as soon as its sheaf-level form does**, granted
  flatness of the structure-sheaf transitions and the leg equation of Stacks 0D72 (6) on sheaves
  of modules.
* `CategoryTheory.SimplicialSiteSituation.moduleProjectionAdjunctSquare_of_coherence`: the same
  with the sheaf-level square supplied from the tensorator and unitor coherences of the
  transition.
* `CategoryTheory.SimplicialSiteSituation`
  `.isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence`:
  **Stacks 0D9E (2) with `proj_restrict` discharged**, granted the summand description of the
  source direct-sum formula and the two coherences.

## Implementation notes

*What the passage consists of.* Both sides of the residual square are built from three kinds of
map: `CategoryTheory.derivedNatTrans` of a map of sheaves of modules, the compositor
`CategoryTheory.derivedCompIso` of derived functors, and the derived transition of Stacks 0D9P,
which is a `CategoryTheory.liftedTransition` and so opaque except through
`CategoryTheory.liftedTransition_eq_derivedNatTrans`. Once that presentation is used, the square
is the derived image of the sheaf-level one, which is `CategoryTheory.liftedTransition_square`.

*Where the identification of the target goes.* The derived adjunct ends with the restriction to
degree `n` of the inverse of
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitTensorDerivedIso`, and the
`φ`th summand inclusion of the target ends with the restriction to degree `m` of the same
inverse, by `…biproduct_ι_moduleProjectionTargetIso_inv_leg`. The naturality of the derived
transition at that one map is what exchanges the two, so the identification cancels from the
square and the abstract statement does not have to mention it.

*Why the assembly is done over abstract morphisms.* The composites below live in the derived
categories of sheaves of modules on the components, where the two spellings of a component's
module category make reassociation not type-correct at the transparency a rewrite builds its
motive at; `square_assemble` therefore takes the five facts and the ten morphisms as variables of
an abstract category and is applied by `exact`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- A functor applied to a threefold composite, split after the second factor. Named because the
composite the derived adjunct of Stacks 0D9E (2) is defined as is right-nested, while the square
consumes it split before its last factor, and no rewrite reassociates it in place. -/
private theorem map_assoc_comp {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z W : C} (x : X ⟶ Y) (y : Y ⟶ Z) (z : Z ⟶ W) :
    F.map (x ≫ y ≫ z) = F.map (x ≫ y) ≫ F.map z :=
  (congrArg F.map (Category.assoc x y z).symm).trans (F.map_comp _ _)

/-- The reassociation that assembles the residual square of Stacks 0D9E (2) out of the derived
image of its sheaf-level form: the derived adjunct split before its last factor, the naturality
of the derived transition at that factor, the square itself, the description of the `φ`th summand
inclusion of the target, and the invertibility of the target identification. Stated over abstract
morphisms because the composites it reassociates are not type-correct at the transparency a
rewrite builds its motive at. -/
private theorem square_assemble {Z : Type*} [Category Z]
    {s₀ s₁ s₂ tX tY tK bip : Z}
    {tC : Z}
    (a₀ : s₀ ⟶ s₂) (a₁ : s₀ ⟶ s₁) (a₂ : s₁ ⟶ s₂)
    (dY : s₂ ⟶ tY) (tgt : tY ⟶ bip) (dX : s₁ ⟶ tX) (mu : tX ⟶ tY)
    (dK : s₀ ⟶ tK) (cd₁ : tK ⟶ tC) (cd₂ : tC ⟶ tX) (iota : tK ⟶ bip) (tinv : bip ⟶ tY)
    (ha₀ : a₀ = a₁ ≫ a₂) (hnat : a₂ ≫ dY = dX ≫ mu) (hstar : a₁ ≫ dX = dK ≫ cd₁ ≫ cd₂)
    (hiota : iota ≫ tinv = cd₁ ≫ cd₂ ≫ mu) (hinv : tinv ≫ tgt = 𝟙 bip) :
    a₀ ≫ dY ≫ tgt = dK ≫ iota := by
  subst ha₀
  simp only [Category.assoc, reassoc_of% hnat, reassoc_of% hstar]
  rw [← Category.assoc cd₂, ← Category.assoc cd₁, ← hiota, Category.assoc, hinv, Category.comp_id]

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The residual square of Stacks 0D9E (2) holds as soon as its sheaf-level form does.**
Granted flatness of the structure-sheaf transitions, the leg equation of Stacks 0D72 (6) on
sheaves of modules, and the sheaf-level square
`…transitionPullbackModules_map_componentModuleProjectionAdjunct_comp` — the pullback along `f_φ`
of the adjunct of Stacks 0D9E (2) followed by the transition of Stacks 09WF is the transition
followed by the `φ`th summand inclusion of the sheaf-level target identification — the derived
square `CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare` holds at every
object of `D(O)`.

The passage is `CategoryTheory.liftedTransition_square`: the derived transition of Stacks 0D9P is
a lift along the localization of the homotopy category, and
`CategoryTheory.liftedTransition_eq_derivedNatTrans` presents it as the derived functor of the
transition of Stacks 09WF conjugated by the compositor, after which the derived square is the
derived image of the sheaf-level one. The identification of the target with
`g_{n!}O_n ⊗^L_O -` cancels: it occurs as the last factor of the derived adjunct and, by
`…biproduct_ι_moduleProjectionTargetIso_inv_leg`, also as the last factor of the `φ`th summand
inclusion, and the naturality of the derived transition at it exchanges the two. -/
theorem moduleProjectionAdjunctSquare_of_sheafSquare
    (hleg : S.ModuleSumFormulaLegEq O)
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsq : ∀ (n m : SimplexCategory) (φ : n ⟶ m) (M : (S.totalRingedTopos O).Modules),
      (S.transitionPullbackModules' O φ).map
            ((S.componentModuleProjectionAdjunct O n).app M) ≫
          (S.componentModuleTransition O φ).app
            ((S.componentModuleLowerShriekUnitTensor O n).obj M) =
        (S.componentModuleTransition O φ).app M ≫
          (S.restrictionTensorWhiskeredUnitIso O m).inv.app M ≫
            ((S.restrictionTensorWhiskered O m).map
                ((pullbackModulesObjUnitIso
                      (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
                  (S.moduleSumFormulaLeg O φ).app
                    (SheafOfModules.unit
                      (S.componentRingSheaf (S.totalRingSheaf O) n)))).app M ≫
              (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom.app M)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.ModuleProjectionAdjunctSquare O K := by
  intro n m φ
  let : PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat n m φ))).1
  let : PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O φ)
  have hstar := liftedTransition_square (S.componentModuleLowerShriekUnitTensor O n)
    (S.componentModulesRestriction O n) (S.componentModulesRestriction O m) _
    (S.componentModuleProjectionAdjunct O n)
    (S.componentModuleTransition O φ)
    ((S.restrictionTensorWhiskeredUnitIso O m).inv ≫
      (S.restrictionTensorWhiskered O m).map
          ((pullbackModulesObjUnitIso
                (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
            (S.moduleSumFormulaLeg O φ).app
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))) ≫
        (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom)
    (hsq n m φ) (S.derivedTransitionPullbackIsoMapDerivedCategory O φ (hflat n m φ))
    (S.derivedComponentModuleTransition O φ)
    (liftedTransition_eq_derivedNatTrans (S.componentModulesRestriction O n) _
      (S.componentModulesRestriction O m)
      (S.componentModuleTransition O φ) (S.derivedTransitionComparison O φ)
      (S.derivedTransitionPullbackIsoMapDerivedCategory O φ (hflat n m φ))
      (S.whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom O φ (hflat n m φ))) K
  exact square_assemble _ _ _ _ _ _ _ _ _ _ _ _ (map_assoc_comp _ _ _ _)
    ((S.derivedComponentModuleTransition O φ).naturality _) hstar
    (S.biproduct_ι_moduleProjectionTargetIso_inv_leg O n m hleg K φ) (Iso.inv_hom_id _)

/-- **The residual square of Stacks 0D9E (2) from the two coherences of the transition.** The
sheaf-level square is `…transitionPullbackModules_map_componentModuleProjectionAdjunct_comp`,
which holds granted that the transition of Stacks 09WF is compatible with the comparison of
Stacks 03EL (`…TransitionTensorCoherence`) and with the left unitors of the components
(`…TransitionUnitorCoherence`). -/
theorem moduleProjectionAdjunctSquare_of_coherence
    (hleg : S.ModuleSumFormulaLegEq O)
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (htensor : S.TransitionTensorCoherence O) (hunit : S.TransitionUnitorCoherence O)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.ModuleProjectionAdjunctSquare O K :=
  S.moduleProjectionAdjunctSquare_of_sheafSquare O hleg hflat
    (fun _ _ φ M =>
      S.transitionPullbackModules_map_componentModuleProjectionAdjunct_comp O htensor hunit φ M) K

/-- **Stacks 0D9E (2) with the summandwise comparison `proj_restrict` discharged.** Under the
source's flatness hypothesis, granted the summand description of the componentwise direct-sum
formula on derived categories, the leg equation of Stacks 0D72 (6) on sheaves of modules, and the
two coherences of the transition of Stacks 09WF, an object `K` of `D(O)` is cartesian exactly when
the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism in every simplicial degree.

This is `…isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare` with its residual
square supplied. -/
theorem isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence
    (hleg : S.ModuleSumFormulaLegEq O)
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (htensor : S.TransitionTensorCoherence O) (hunit : S.TransitionUnitorCoherence O)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.IsCartesianDerivedModule O K ↔
      ∀ n : SimplexCategory, IsIso (S.moduleProjection O n (hflat n) K) :=
  S.isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare O hflat hsummand K
    (S.moduleProjectionAdjunctSquare_of_coherence O hleg hflat htensor hunit K)

end CategoryTheory.SimplicialSiteSituation

end
