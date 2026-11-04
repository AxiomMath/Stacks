module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismModuleLowerShriekAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shriek of modules commutes with forgetting the module structure in
Situation 08PA

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, with `Lg_! : D(O_{C'}) ⥤ D(O_C)` and `Lg_!^{Ab} : D(C') ⥤ D(C)` the
two left derived lower shrieks of Stacks 08PC part (3). **Stacks 08PC part (4)** is that the
square

```
D(O_{C'}) --Lg_!--> D(O_C)
    |                  |
 forget             forget
    v                  v
  D(C')  --Lg_!^{Ab}--> D(C)
```

commutes, that is, the canonical comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of Stacks
07AE is an isomorphism. This file proves it.

The comparison is the unique transformation compatible with the comparisons of the two left
derived functors and the canonical comparison of Stacks 0798 applied degreewise; it exists
because `forget ∘ Lg_!` is a left derived functor of `forget ∘ g_!`, by the absoluteness of `Lg_!`
(`MorphismSituation.isLeftDerivedFunctor_derivedModuleLowerShriek_comp`). It is an isomorphism as
soon as `Lg_!^{Ab} ∘ forget` is a left derived functor of the same functor; and it is one of
`g_!^{Ab} ∘ forget`, which is isomorphic to `forget ∘ g_!` through the canonical comparison by
part (2) (`MorphismSituation.isIso_moduleLowerShriekForgetComparison`). That is checked on the
complexes cellular for the class of direct sums of the `j_{U'!} O_{U'}`, which resolve every
complex and between which `g_!` inverts quasi-isomorphisms (Stacks 0794): `forget` carries such a
complex to one cellular for the class of `Ext`-acyclic abelian sheaves for `g_!^{Ab} ⊣ g^{-1}`
(`StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular.map`, with
`MorphismSituation.extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits`), and `Lg_!^{Ab}` is
computed by `g_!^{Ab}` on those, that class satisfying the hypotheses of Stacks 0794 as well.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.extAcyclic_biprod` and
  `Stacks.Sites.FibredCategory.MorphismSituation.containsZero_extAcyclic`: the `Ext`-acyclic
  abelian sheaves for `g_!^{Ab} ⊣ g^{-1}` form a class to which Stacks 0794 applies.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_derivedAbelianLowerShriekComparison_app`:
  `Lg_!^{Ab}` is computed by `g_!^{Ab}` on complexes cellular for that class.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_derivedModuleLowerShriekForgetComparison`:
  **Stacks 08PC part (4)**, the canonical comparison
  `derivedModuleLowerShriekForgetComparison : Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is an
  isomorphism; `derivedModuleLowerShriekForgetIso` is its inverse.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

attribute [local instance] hasWeakSheafify_sourceTopology hasWeakSheafify_totalTopology
  wEqualsLocallyBijective_sourceTopology wEqualsLocallyBijective_totalTopology

variable {S} in
/-- The `Ext`-acyclic abelian sheaves for `g_!^{Ab} ⊣ g^{-1}` are closed under binary direct
sums. -/
theorem extAcyclic_biprod
    {X Y : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}}
    (hX : S.abelianLowerShriekAdjunction.extAcyclic X)
    (hY : S.abelianLowerShriekAdjunction.extAcyclic Y) :
    S.abelianLowerShriekAdjunction.extAcyclic (X ⊞ Y) := by
  have : HasCoproduct (pairFunction X Y) := (inferInstance : HasBinaryCoproduct X Y)
  exact S.abelianLowerShriekAdjunction.extAcyclic_of_iso (biprod.isoCoprod X Y).symm
    (S.abelianLowerShriekAdjunction.extAcyclic_coproduct (pairFunction X Y)
      (by rintro (_ | _) <;> assumption))

/-- The `Ext`-acyclic abelian sheaves for `g_!^{Ab} ⊣ g^{-1}` contain a zero object. -/
instance containsZero_extAcyclic :
    S.abelianLowerShriekAdjunction.extAcyclic.ContainsZero :=
  ⟨(HasZeroObject.zero
    (C := Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})).elim
    fun Z hZ => ⟨Z, hZ, S.abelianLowerShriekAdjunction.extAcyclic_of_isZero hZ⟩⟩

variable {S} in
/-- A direct sum of the free abelian sheaves `j_{U'!} ℤ_{U'}` is `Ext`-acyclic for
`g_!^{Ab} ⊣ g^{-1}`: this is Stacks 0D6X along `u`,
`subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`. -/
theorem extAcyclic_of_isSumOfExtensionByZeroUnitsAb
    {X : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}}
    (hX : Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w u₀ u₁ u₂
      v₀ v₁ v₂} S.sourceTopology X) :
    S.abelianLowerShriekAdjunction.extAcyclic X := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hX
  have hcol : HasColimitsOfShape (Discrete ι)
      (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
    Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb S.sourceTopology ι
  let Y : ι → Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} := fun i =>
    Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology (U i)
  have : HasCoproduct Y := @HasColimitsOfShape.has_colimit _ _ _ _ hcol _
  refine S.abelianLowerShriekAdjunction.extAcyclic_of_iso e ?_
  exact S.abelianLowerShriekAdjunction.extAcyclic_coproduct Y fun i I _ n hn =>
    S.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage (U i) I n hn

section Derived

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedLowerShriek StacksDraft.UnboundedLeftDerivedFunctor

include S in
/-- The two classes that compute the derived lower shrieks: the direct sums of the
`j_{U'!} O_{U'}` for `g_!` on modules and the `Ext`-acyclic abelian sheaves for `g_!^{Ab}`, with
the hypotheses of Stacks 0794 for each — they resolve every complex, and the lower shriek inverts
the quasi-isomorphisms between the complexes cellular for them. -/
theorem derives_cellular :
    (cellularLocalizerMorphism
        (IsSumOfExtensionByZeroUnits S.sourceModuleRing)).HasLeftResolutions ∧
      (cellularLocalizerMorphism (IsSumOfExtensionByZeroUnits S.sourceModuleRing)).Derives
        (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) ∧
      (cellularLocalizerMorphism S.abelianLowerShriekAdjunction.extAcyclic).HasLeftResolutions ∧
      (cellularLocalizerMorphism S.abelianLowerShriekAdjunction.extAcyclic).Derives
        (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) := by
  let P := IsSumOfExtensionByZeroUnits S.sourceModuleRing
  let P' := S.abelianLowerShriekAdjunction.extAcyclic
  have : Small.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.source := small_max.{max w u₀ u₁ v₀ v₁ v₂, u₂} _
  have : HasExactColimitsOfShape ℕ
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceModuleRing) :=
    hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ
      (SheafOfModules.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalModuleRing) :=
    hasExactColimitsOfShape_nat _
  have := hasExactColimitsOfShape_nat_sheafAb.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology
  have := hasExactColimitsOfShape_nat_sheafAb.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology
  have : PreservesColimitsOfShape ℕ S.abelianLowerShriek :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      S.abelianLowerShriekAdjunction).preservesColimitsOfShape
  have : PreservesColimitsOfShape ℕ S.moduleLowerShriek :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      S.moduleLowerShriekAdjunction).preservesColimitsOfShape
  have hsum : ∀ X Y, P X → P Y → P (X ⊞ Y) := fun _ _ => isSumOfExtensionByZeroUnits_biprod _
  have hP : ∀ X, ∃ (Y : _) (_ : P Y) (p : Y ⟶ X), Epi p := fun M =>
    exists_epi_isSumOfExtensionByZeroUnits _ M
  have hsum' : ∀ X Y, P' X → P' Y → P' (X ⊞ Y) := fun _ _ => extAcyclic_biprod
  have hP' : ∀ X, ∃ (Y : _) (_ : P' Y) (p : Y ⟶ X), Epi p := fun F => by
    obtain ⟨Y, hY, p, hp⟩ :=
      exists_epi_isSumOfExtensionByZeroUnitsAb.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology F
    exact ⟨Y, extAcyclic_of_isSumOfExtensionByZeroUnitsAb hY, p, hp⟩
  have hFP' : ∀ (a : ℤ) (L : CochainComplex (Sheaf S.sourceTopology
      AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ), L.IsStrictlyLE a → (∀ n, P' (L.X n)) →
      L.Acyclic → ((S.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L).Acyclic := fun a L hLE hLP hL => by
    have := hLE
    exact S.abelianLowerShriekAdjunction.map_acyclic_of_extAcyclic L a hL hLP
  exact ⟨hasLeftResolutions_cellularLocalizerMorphism P hsum hP,
    derives_cellularLocalizerMorphism S.moduleLowerShriek P hsum hP S.moduleLowerShriekAcyclic,
    hasLeftResolutions_cellularLocalizerMorphism P' hsum' hP',
    derives_cellularLocalizerMorphism S.abelianLowerShriek P' hsum' hP' hFP'⟩

/-- **`Lg_!^{Ab}` is computed by `g_!^{Ab}` on complexes cellular for the `Ext`-acyclic class.**
The comparison `Lg_!^{Ab} ⟶ g_!^{Ab}` of the left derived functor is invertible at every object
of the homotopy category cellular for the class of `Ext`-acyclic abelian sheaves for
`g_!^{Ab} ⊣ g^{-1}`: that class satisfies the hypotheses of Stacks 0794 (`derives_cellular`), so
its cellular complexes form a left derivability structure on which `g_!^{Ab}` inverts
quasi-isomorphisms. -/
theorem isIso_derivedAbelianLowerShriekComparison_app
    (X : (cellular S.abelianLowerShriekAdjunction.extAcyclic).FullSubcategory) :
    IsIso (S.derivedAbelianLowerShriekComparison.app X.obj) := by
  obtain ⟨-, -, hres', hder'⟩ := S.derives_cellular
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism _ hres'
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ hder'
    DerivedCategory.Qh _ _ X

/-- The comparison exhibiting `Lg_!^{Ab} ∘ forget` as a left derived functor of
`g_!^{Ab} ∘ forget` on the homotopy category of `Mod(O_{C'})`: `forget` on derived categories is
`forget` degreewise followed by the localization, and then the comparison `Lg_!^{Ab} ⟶ g_!^{Ab}`
of the left derived functor. -/
def derivedForgetAbelianLowerShriekComparison :
    DerivedCategory.Qh ⋙
        (S.sourceModuleForget.mapDerivedCategory ⋙ S.derivedAbelianLowerShriek) ⟶
      S.sourceModuleForget.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight S.sourceModuleForget.mapDerivedCategoryFactorsh.hom
      S.derivedAbelianLowerShriek ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ S.derivedAbelianLowerShriekComparison

/-- **Part (2) on the homotopy category, followed by the localization.** Degreewise `g_!` followed
by `forget` is degreewise `forget` followed by `g_!^{Ab}`, by
`moduleLowerShriekForgetIsoInherited`; the localization `Qh` commutes with the exact functor
`forget`. -/
def moduleLowerShriekOnHomotopyForgetIso :
    (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) ⋙
        S.totalModuleForget.mapDerivedCategory ≅
      S.sourceModuleForget.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ S.totalModuleForget.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso S.moduleLowerShriekForgetIsoInherited
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **`Lg_!^{Ab} ∘ forget` is a left derived functor of `g_!^{Ab} ∘ forget`.** Its comparison is
invertible on the complexes cellular for the direct sums of the `j_{U'!} O_{U'}`, which resolve
every complex: `forget` carries such a complex to one cellular for the `Ext`-acyclic abelian
sheaves (`StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular.map`), where `Lg_!^{Ab}` is computed
by `g_!^{Ab}` (`isIso_derivedAbelianLowerShriekComparison_app`). -/
theorem isLeftDerivedFunctor_derivedForgetAbelianLowerShriek :
    (S.sourceModuleForget.mapDerivedCategory ⋙ S.derivedAbelianLowerShriek).IsLeftDerivedFunctor
      S.derivedForgetAbelianLowerShriekComparison S.moduleSourceQuasiIso := by
  obtain ⟨hres, hder, -, -⟩ := S.derives_cellular
  have : PreservesColimitsOfShape ℕ S.sourceModuleForget :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  refine CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    S.moduleSourceQuasiIso (cellular (IsSumOfExtensionByZeroUnits S.sourceModuleRing))
    (fun X => ?_) _ (fun f hf hX hY => ?_) DerivedCategory.Qh _ _ (fun X hX => ?_)
  · obtain ⟨R⟩ := hres X
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  · have : IsIso ((S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).map f) :=
      hder (ObjectProperty.homMk (X := ⟨_, hX⟩) (Y := ⟨_, hY⟩) f) hf
    have : IsIso (((S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) ⋙
        S.totalModuleForget.mapDerivedCategory).map f) :=
      inferInstanceAs (IsIso (S.totalModuleForget.mapDerivedCategory.map _))
    exact (NatIso.isIso_map_iff S.moduleLowerShriekOnHomotopyForgetIso f).1 this
  · obtain ⟨K, hK, ⟨e⟩⟩ := hX
    rw [NatTrans.isIso_app_iff_of_iso _ e]
    have hK' := IsPCellular.map S.sourceModuleForget
      (P' := S.abelianLowerShriekAdjunction.extAcyclic)
      (fun M hM => S.extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits M hM) hK
    have h1 := S.isIso_derivedAbelianLowerShriekComparison_app
      ⟨_, ⟨_, hK', ⟨Iso.refl _⟩⟩⟩
    have h1' : IsIso (S.derivedAbelianLowerShriekComparison.app
        ((S.sourceModuleForget.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :=
      (NatTrans.isIso_app_iff_of_iso _
        ((S.sourceModuleForget.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)).2 h1
    simp only [derivedForgetAbelianLowerShriekComparison, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.id_comp]
    infer_instance

/-- The canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798
(`moduleLowerShriekForgetTransformation`), with the two forgetful functors spelled at the
inherited topologies. -/
def moduleLowerShriekForgetTransformationInherited :
    S.sourceModuleForget ⋙ S.abelianLowerShriek ⟶ S.moduleLowerShriek ⋙ S.totalModuleForget :=
  S.moduleLowerShriekForgetTransformation

/-- The canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!`, spelled at the inherited
topologies, is an isomorphism. -/
instance isIso_moduleLowerShriekForgetTransformationInherited :
    IsIso S.moduleLowerShriekForgetTransformationInherited :=
  S.isIso_moduleLowerShriekForgetTransformation

/-- The canonical comparison of Stacks 0798 applied degreewise, read on the homotopy categories
and followed by the localization: a transformation from `g_!^{Ab} ∘ forget` to `forget ∘ g_!` on
the homotopy category of `Mod(O_{C'})`, `forget` on derived categories being degreewise
`forget` followed by the localization. -/
def degreewiseForgetComparison :
    S.sourceModuleForget.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) ⟶
      (S.moduleLowerShriekOnHomotopy ⋙ DerivedCategory.Qh) ⋙
        S.totalModuleForget.mapDerivedCategory :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory S.moduleLowerShriekForgetTransformationInherited
          (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv)
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ S.totalModuleForget.mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv

/-- The degreewise comparison `degreewiseForgetComparison` from `g_!^{Ab} ∘ forget` to
`forget ∘ g_!` on the homotopy category of `Mod(O_{C'})` is an isomorphism. -/
instance isIso_degreewiseForgetComparison : IsIso S.degreewiseForgetComparison := by
  have : IsIso (NatTrans.mapHomotopyCategory S.moduleLowerShriekForgetTransformationInherited
      (ComplexShape.up ℤ)) :=
    ⟨⟨NatTrans.mapHomotopyCategory (inv S.moduleLowerShriekForgetTransformationInherited)
        (ComplexShape.up ℤ),
      by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩⟩
  unfold degreewiseForgetComparison
  infer_instance

/-- **The canonical comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of Stacks 07AE** in Situation
08PA: the unique natural transformation which, restricted along the localization of the homotopy
category of `Mod(O_{C'})`, is compatible with the comparison `Lg_!^{Ab} ⟶ g_!^{Ab}` of the left
derived functor, the comparison `Lg_! ⟶ g_!` of the left derived functor and the canonical
comparison of Stacks 0798 applied degreewise. It exists and is unique because `forget ∘ Lg_!` is
a left derived functor of `forget ∘ g_!` (`isLeftDerivedFunctor_derivedModuleLowerShriek_comp`). -/
def derivedModuleLowerShriekForgetComparison :
    S.sourceModuleForget.mapDerivedCategory ⋙ S.derivedAbelianLowerShriek ⟶
      S.derivedModuleLowerShriek ⋙ S.totalModuleForget.mapDerivedCategory :=
  have := S.isLeftDerivedFunctor_derivedModuleLowerShriek_comp S.moduleLowerShriekAcyclic
    S.totalModuleForget.mapDerivedCategory
  Functor.leftDerivedLift _
    ((Functor.associator DerivedCategory.Qh S.derivedModuleLowerShriek
        S.totalModuleForget.mapDerivedCategory).inv ≫
      Functor.whiskerRight S.derivedModuleLowerShriekComparison
        S.totalModuleForget.mapDerivedCategory)
    S.moduleSourceQuasiIso _
    (S.derivedForgetAbelianLowerShriekComparison ≫ S.degreewiseForgetComparison)

/-- **Stacks 08PC, part (4).** In Situation 08PA the canonical comparison of Stacks 07AE

`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`

of functors `D(O_{C'}) ⥤ D(C)` (`derivedModuleLowerShriekForgetComparison`) is an isomorphism:
the derived lower shriek on sheaves of modules commutes with forgetting the module structure.

`Lg_!^{Ab} ∘ forget` is a left derived functor of `g_!^{Ab} ∘ forget` on the homotopy category
of `Mod(O_{C'})` (`isLeftDerivedFunctor_derivedForgetAbelianLowerShriek`), hence of
`forget ∘ g_!`, the degreewise comparison being invertible by part (2)
(`isIso_moduleLowerShriekForgetComparison`); and the lift of a comparison between two left derived
functors of the same functor is an isomorphism. -/
@[stacks 08PC "part (4): the canonical comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is an \
isomorphism"]
theorem isIso_derivedModuleLowerShriekForgetComparison :
    IsIso S.derivedModuleLowerShriekForgetComparison := by
  have := S.isLeftDerivedFunctor_derivedModuleLowerShriek_comp S.moduleLowerShriekAcyclic
    S.totalModuleForget.mapDerivedCategory
  have h₁ := S.isLeftDerivedFunctor_derivedForgetAbelianLowerShriek
  have h₂ : (S.sourceModuleForget.mapDerivedCategory ⋙
      S.derivedAbelianLowerShriek).IsLeftDerivedFunctor
      (S.derivedForgetAbelianLowerShriekComparison ≫ S.degreewiseForgetComparison)
      S.moduleSourceQuasiIso := by
    rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension] at h₁ ⊢
    exact (Functor.isRightKanExtension_iff_of_iso₂ _ _ (asIso S.degreewiseForgetComparison)
      (Iso.refl _) (by simp)).1 h₁
  exact (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift _ _ _ _ _).1 h₂

/-- `forget ∘ Lg_! ≅ Lg_!^{Ab} ∘ forget`, the inverse of the canonical comparison
`derivedModuleLowerShriekForgetComparison`; Stacks 08PC part (4) as an isomorphism of
functors. -/
def derivedModuleLowerShriekForgetIso :
    S.derivedModuleLowerShriek ⋙ S.totalModuleForget.mapDerivedCategory ≅
      S.sourceModuleForget.mapDerivedCategory ⋙ S.derivedAbelianLowerShriek :=
  have := S.isIso_derivedModuleLowerShriekForgetComparison
  (asIso S.derivedModuleLowerShriekForgetComparison).symm

end Derived

end Stacks.Sites.FibredCategory.MorphismSituation

end
