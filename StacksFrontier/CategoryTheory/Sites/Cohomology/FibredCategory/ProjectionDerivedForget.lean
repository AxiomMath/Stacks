module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionForgetAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AdjointExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfCellularInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of modules commutes with forgetting the module structure

Let `p : C ⥤ D` be a fibred category over a site `D`, give `C` the inherited topology, let `O` be
a sheaf of rings on `D` and `O_C = π^{-1}O`, as in Situation 08P8. Stacks 08PC part (4), for the
reduction of Situation 08P8 to Situation 08PA made in Remark 09CY, states that the square

```
D(O_C) --Lπ_!--> D(O)
  |                |
forget           forget
  v                v
D(C) --Lπ_!^{Ab}--> D(D)
```

commutes. This file proves it: the canonical comparison `Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of
Stacks 07AE (`existsUnique_derivedForgetComparison`) is an isomorphism, provided `Lπ_!` on modules
exists, i.e. given the acyclicity statement of Stacks 07AC for `π_!` on modules.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.IsSumOfForgetGenerators`: the class of
  direct sums of underlying abelian sheaves of the `j_{U!}O_U` and of free abelian sheaves
  `j_{U!}ℤ_U`, which satisfies the hypotheses of Stacks 0794 for `π_!^{Ab}`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.isIso_derivedForgetComparison`: the
  comparison of Stacks 07AE is an isomorphism.

## Implementation notes

The source deduces part (4) from the vanishing of `Hom_{D(C/U)}(L(π_U)^{Ab}_! O_U, -)` against the
identity. The argument here is the one that sentence abbreviates. A complex of `O_C`-modules is
resolved by a cellular complex `S` built from direct sums of the `j_{U!}O_U` (Stacks 0794); on it
`Lπ_!` is `π_!` degreewise. Its underlying complex of abelian sheaves is cellular for the class
`IsSumOfForgetGenerators`, which is `Ext`-acyclic for `π_!^{Ab} ⊣ π^{-1}`
(`extAcyclic_toSheaf_extensionByZeroUnit` and Stacks 0D6X), so on it `Lπ_!^{Ab}` is `π_!^{Ab}`
degreewise as well. Finally `π_!^{Ab} ∘ forget = forget ∘ π_!` underived, which is part (2)
(`isIso_lowerShriekForgetComparison`). The comparison of Stacks 07AE is assembled from exactly
these three maps, so it is invertible.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.DerivedLowerShriek StacksDraft.UnboundedLeftDerivedFunctor

universe u

/- The abelian structure on sheaves of modules is the library's canonical
`AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules`, the one the derived functors used
here are built with; the alternative instance of `SiteModules` would produce a different derived
category. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.Sites.FibredCategory

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{u, u, u, u, u}) (O : Sheaf s.base.J RingCat.{u})

section Generators

/-- Direct sums of abelian sheaves on the total category, indexed in the universe of the sections.
Supplied by name: instance search does not reach it within its budget. -/
local instance hasCoproduct_total {ι : Type u} (f : ι → Sheaf s.topology AddCommGrpCat.{u}) :
    HasCoproduct f :=
  (hasColimitsOfShape_discrete_sheafAb.{u} s.topology ι).has_colimit _

/-- The generators of the abelian class: on the left, the underlying abelian sheaf of `j_{U!}O_U`;
on the right, the free abelian sheaf `j_{U!}ℤ_U`. -/
abbrev forgetGenerator : s.C ⊕ s.C → Sheaf s.topology AddCommGrpCat.{u} :=
  Sum.elim
    (fun U => (SheafOfModules.toSheaf (s.totalRing O)).obj (extensionByZeroUnit (s.totalRing O) U))
    (fun U => extensionByZeroUnitAb.{u} s.topology U)

/-- The direct sums of the generators `forgetGenerator`. -/
def IsSumOfForgetGenerators : ObjectProperty (Sheaf s.topology AddCommGrpCat.{u}) := fun X =>
  ∃ (ι : Type u) (E : ι → s.C ⊕ s.C), Nonempty ((∐ fun i => s.forgetGenerator O (E i)) ≅ X)

/-- The class `IsSumOfForgetGenerators` contains a zero object. -/
instance containsZero_isSumOfForgetGenerators :
    (s.IsSumOfForgetGenerators O).ContainsZero := by
  let E₀ : PEmpty.{u + 1} → s.C ⊕ s.C := fun i => nomatch i
  have hE : IsInitial (∐ fun i => s.forgetGenerator O (E₀ i)) :=
    IsInitial.ofUniqueHom (fun _ => Sigma.desc (fun i => isEmptyElim i))
      (fun _ _ => Sigma.hom_ext _ _ (fun i => isEmptyElim i))
  exact ⟨_, hE.isZero, ⟨PEmpty.{u + 1}, E₀, ⟨Iso.refl _⟩⟩⟩

/-- The class `IsSumOfForgetGenerators` is closed under binary biproducts. -/
lemma isSumOfForgetGenerators_biprod {X Y : Sheaf s.topology AddCommGrpCat.{u}}
    (hX : s.IsSumOfForgetGenerators O X) (hY : s.IsSumOfForgetGenerators O Y) :
    s.IsSumOfForgetGenerators O (X ⊞ Y) := by
  obtain ⟨ι, E, ⟨eX⟩⟩ := hX
  obtain ⟨κ, E', ⟨eY⟩⟩ := hY
  refine ⟨ι ⊕ κ, Sum.elim E E', ?_⟩
  let A : ι → Sheaf s.topology AddCommGrpCat.{u} := fun i => s.forgetGenerator O (E i)
  let B : κ → Sheaf s.topology AddCommGrpCat.{u} := fun j => s.forgetGenerator O (E' j)
  have hAB : (fun i : ι ⊕ κ => s.forgetGenerator O (Sum.elim E E' i)) = Sum.elim A B := by
    funext i
    cases i <;> rfl
  let e : Discrete.functor (fun i : ι ⊕ κ => s.forgetGenerator O (Sum.elim E E' i)) ≅
      Discrete.functor (Sum.elim A B) :=
    Discrete.natIso fun i => eqToIso (congrFun hAB i.as)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim A B)).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct A) (coproductIsCoproduct B)
        (coprodIsCoprod (∐ A) (∐ B))) ≪≫
    (biprod.isoCoprod (∐ A) (∐ B)).symm ≪≫ biprod.mapIso eX eY⟩

/-- Every abelian sheaf on the total category is the target of an epimorphism from an object of
`IsSumOfForgetGenerators`. -/
lemma exists_epi_isSumOfForgetGenerators (X : Sheaf s.topology AddCommGrpCat.{u}) :
    ∃ (Y : Sheaf s.topology AddCommGrpCat.{u}) (_ : s.IsSumOfForgetGenerators O Y)
      (p : Y ⟶ X), Epi p := by
  obtain ⟨Y, ⟨ι, U, ⟨e⟩⟩, p, hp⟩ :=
    exists_epi_isSumOfExtensionByZeroUnitsAb.{u} s.topology X
  exact ⟨Y, ⟨ι, fun i => Sum.inr (U i), ⟨e⟩⟩, p, hp⟩

/-- Every generator is `Ext`-acyclic for `π_!^{Ab} ⊣ π^{-1}`. -/
lemma extAcyclic_forgetGenerator (E : s.C ⊕ s.C) :
    s.abelianLowerShriekAdjunction.extAcyclic (s.forgetGenerator O E) := by
  rcases E with U | U
  · exact s.extAcyclic_toSheaf_extensionByZeroUnit O U
  · intro I _ n hn
    exact s.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage U I n hn

/-- **The acyclicity statement of Stacks 0794 for `π_!^{Ab}` and the class
`IsSumOfForgetGenerators`.** -/
theorem abelianLowerShriek_acyclic_forgetGenerators (a : ℤ)
    (L : CochainComplex (Sheaf s.topology AddCommGrpCat.{u}) ℤ) (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, s.IsSumOfForgetGenerators O (L.X n)) (hLac : L.Acyclic) :
    ((s.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine s.abelianLowerShriekAdjunction.map_acyclic_of_extAcyclic L a hLac fun n => ?_
  obtain ⟨ι, E, ⟨e⟩⟩ := hLP n
  exact s.abelianLowerShriekAdjunction.extAcyclic_of_iso e
    (s.abelianLowerShriekAdjunction.extAcyclic_coproduct _
      fun i => s.extAcyclic_forgetGenerator O (E i))

/-- Forgetting the module structure carries a direct sum of the `j_{U!}O_U` into the class
`IsSumOfForgetGenerators`, forgetting being a left adjoint and so commuting with direct sums. -/
lemma isSumOfForgetGenerators_toSheaf {M : SheafOfModules.{u} (s.totalRing O)}
    (hM : IsSumOfExtensionByZeroUnits (s.totalRing O) M) :
    s.IsSumOfForgetGenerators O ((SheafOfModules.toSheaf (s.totalRing O)).obj M) := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  exact ⟨ι, fun i => Sum.inl (U i), ⟨(PreservesCoproduct.iso (SheafOfModules.toSheaf
    (s.totalRing O)) (fun i => extensionByZeroUnit (s.totalRing O) (U i))).symm ≪≫
    (SheafOfModules.toSheaf (s.totalRing O)).mapIso e⟩⟩

end Generators

section ModuleAcyclic

/-- `ℤ_U`, the sheafified free abelian presheaf on the presheaf represented by `U`, in the spelling
of `ModuleSheafCohomology`: it corepresents sections over `U`. -/
@[sga "4 XVIII 1.4.24"]
abbrev freeAbelianSheafOn {E : Type u} [SmallCategory E] (L : GrothendieckTopology E) (U : E) :
    Sheaf L AddCommGrpCat.{u} :=
  (presheafToSheaf L AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Stacks 0D6X along the projection, in the spelling `freeAbelianSheafOn`. -/
theorem ext_freeAbelianSheafOn_abelianInverseImage_eq_zero (U : s.C)
    (I : Sheaf s.base.J AddCommGrpCat.{u}) [Injective I] (n : ℕ)
    (e : Ext (freeAbelianSheafOn s.topology U) (s.abelianInverseImage.obj I) (n + 1)) :
    e = 0 := by
  have h' : Subsingleton (Ext (freeAbelianSheafOn s.topology U)
      (s.abelianInverseImage.obj I) (n + 1)) :=
    Stacks.Cohomology.subsingleton_ext_of_iso
      ((presheafToSheaf s.topology AddCommGrpCat.{u}).mapIso
        (Functor.isoWhiskerRight
          (NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (fun _ => rfl))
          AddCommGrpCat.free)) (n + 1)
      (s.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage U I (n + 1) n.succ_pos)
  exact Subsingleton.elim _ _

/-- `Ext^n(ℤ_{p(U)}, G) ≅ Ext^n(ℤ_U, π^{-1}G)`, naturally in the abelian sheaf `G` on the base:
`π^{-1}` is exact, both sides corepresent the sections of `G` over `p(U)` in degree zero, and the
generators `ℤ_U` are acyclic against inverse images of injectives by Stacks 0D6X. -/
def extFreeAbelianSheafOnInverseImageIso (U : s.C) (n : ℕ) :
    extFunctorObj.{u} (freeAbelianSheafOn s.base.J (s.p.obj U)) n ≅
      s.abelianInverseImage ⋙ extFunctorObj.{u} (freeAbelianSheafOn s.topology U) n :=
  have : s.abelianInverseImage.Additive :=
    Functor.additive_sheafPushforwardContinuous _ s.topology s.base.J _
  have : PreservesFiniteColimits s.abelianInverseImage :=
    Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous _
      s.topology s.base.J (isAlmostCocontinuous_of_isCocontinuous _ s.topology s.base.J)
  have : PreservesFiniteLimits s.abelianInverseImage :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous s.topology s.base.J _ _
  ModuleSheafCohomology.extComparisonIso s.abelianInverseImage
    (freeAbelianSheafOn s.topology U) (freeAbelianSheafOn s.base.J (s.p.obj U))
    (fun I _ n e => s.ext_freeAbelianSheafOn_abelianInverseImage_eq_zero U I n e)
    ((ModuleSheafCohomology.evaluationRepresentation s.base.J (s.p.obj U)).symm ≪≫
      Functor.isoWhiskerLeft s.abelianInverseImage
        (ModuleSheafCohomology.evaluationRepresentation s.topology U)) n

/-- **The generators `j_{U!} O_U` of `Mod(O_C)` are `Ext`-acyclic for `π_! ⊣ π^{-1}` on modules.**
For an injective `O`-module `I`, `Ext^n_{O_C}(j_{U!} O_U, π^{-1} I) = 0` for `n ≥ 1`: `Ext` out
of `j_{U!} O_U` in modules is `Ext` out of `ℤ_U` in abelian sheaves (Stacks 03FD), which against
an inverse image is `Ext` out of `ℤ_{p(U)}` on the base, and the underlying abelian sheaf of an
injective module is acyclic. -/
theorem extAcyclic_extensionByZeroUnit (U : s.C) :
    (adjunctionModules s.topology s.base.J s.p O).extAcyclic
      (extensionByZeroUnit (s.totalRing O) U) := by
  intro I _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let R := s.totalRing O
  let M := (restrictionModules s.topology s.base.J s.p O).obj I
  have e₁ := (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    (freeAbelianSheafOn s.topology U)
    (Stacks.Cohomology.ObjectSections.sectionObject s.topology R U)
    (fun I _ n e => ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf s.topology R I U n e)
    (ModuleSheafCohomology.tensorSheafHomIso s.topology R _) (m + 1)).app M
  have e₂ := (s.extFreeAbelianSheafOnInverseImageIso U (m + 1)).app
    ((SheafOfModules.toSheaf O).obj I)
  have h₀ : Subsingleton (Ext (freeAbelianSheafOn s.base.J (s.p.obj U))
      ((SheafOfModules.toSheaf O).obj I) (m + 1)) :=
    subsingleton_of_forall_eq 0 fun e =>
      ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf s.base.J O I (s.p.obj U) m e
  have h₂ : Subsingleton (Ext (freeAbelianSheafOn s.topology U)
      ((SheafOfModules.toSheaf R).obj M) (m + 1)) :=
    e₂.addCommGroupIsoToAddEquiv.subsingleton_congr.mp h₀
  have h₁ : Subsingleton (Ext
      (Stacks.Cohomology.ObjectSections.sectionObject s.topology R U) M (m + 1)) :=
    e₁.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr h₂
  exact Stacks.Cohomology.subsingleton_ext_of_iso
    (sectionObjectIsoExtensionByZeroUnit s.topology R U).symm (m + 1) h₁

/-- **The acyclicity statement of Stacks 07AC for `π_!` on modules**, for the projection of a
fibred category. -/
theorem lowerShriekModules_acyclic (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (s.totalRing O)) ℤ) (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits (s.totalRing O) (L.X n)) (hLac : L.Acyclic) :
    (((SheafOfModules.pullback.{u} (idRingMap s.topology s.base.J s.p O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine (adjunctionModules s.topology s.base.J s.p O).map_acyclic_of_extAcyclic L a hLac
    fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (adjunctionModules s.topology s.base.J s.p O).extAcyclic_of_iso e
    ((adjunctionModules s.topology s.base.J s.p O).extAcyclic_coproduct _
      fun i => s.extAcyclic_extensionByZeroUnit O (U i))

end ModuleAcyclic

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08PC part (3) for the projection of a fibred category, existence**: the left derived
functor `Lπ_!` of lower shriek on modules exists at every object. -/
instance hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy :
    (lowerShriekOnHomotopy s.topology s.base.J s.p O ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso s.topology s.base.J s.p O) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE s.topology s.base.J s.p O
    (s.lowerShriekModules_acyclic O)

/-- `Lπ_!` followed by forgetting the module structure is again a left derived functor, `Lπ_!`
being constructed by resolutions. -/
instance isLeftDerivedFunctor_derivedLowerShriek_comp_forget :
    (derivedLowerShriek s.topology s.base.J s.p O ⋙
      (forgetTargetModules s.base.J O).mapDerivedCategory).IsLeftDerivedFunctor
        (derivedLowerShriekForgetCounit s.topology s.base.J s.p O)
        (sourceQuasiIso s.topology s.base.J s.p O) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic s.topology s.base.J s.p O
    (s.lowerShriekModules_acyclic O) _

/-- **The comparison `Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of Stacks 07AE** for the projection of a
fibred category: the unique natural transformation compatible with the two counits and the
comparison of Stacks 0798 (`existsUnique_derivedForgetComparison`). -/
def derivedForgetComparison :
    (forgetSourceModules s.topology s.base.J s.p O).mapDerivedCategory ⋙
        derivedLowerShriekAbelian s.topology s.base.J s.p ⟶
      derivedLowerShriek s.topology s.base.J s.p O ⋙
        (forgetTargetModules s.base.J O).mapDerivedCategory :=
  Functor.leftDerivedLift _ (derivedLowerShriekForgetCounit s.topology s.base.J s.p O)
    (sourceQuasiIso s.topology s.base.J s.p O) _
    (derivedForgetComparisonCounit s.topology s.base.J s.p O)

/-- The comparison `derivedForgetComparison` composed with `derivedLowerShriekForgetCounit` is
`derivedForgetComparisonCounit`. -/
lemma derivedForgetComparison_fac :
    Functor.whiskerLeft DerivedCategory.Qh (s.derivedForgetComparison O) ≫
        derivedLowerShriekForgetCounit s.topology s.base.J s.p O =
      derivedForgetComparisonCounit s.topology s.base.J s.p O :=
  Functor.leftDerived_fac _ _ _ _ _

/-- On a complex cellular for the direct sums of the `j_{U!}O_U`, `Lπ_!` on modules is `π_!`
degreewise (Stacks 0794). -/
lemma isIso_derivedLowerShriekComparison_app_of_cellular
    (X : HomotopyCategory (SheafOfModules.{u} (s.totalRing O)) (ComplexShape.up ℤ))
    (hX : cellular (IsSumOfExtensionByZeroUnits (s.totalRing O)) X) :
    IsIso ((derivedLowerShriekComparison s.topology s.base.J s.p O).app X) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (s.totalRing O)) :=
    hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} O) := hasExactColimitsOfShape_nat _
  have : PreservesColimitsOfShape ℕ (lowerShriekModules s.topology s.base.J s.p O) :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules s.topology s.base.J s.p O)).preservesColimitsOfShape
  exact Stacks.ChaoticSite.isIso_app_of_cellular (F := lowerShriekModules s.topology s.base.J s.p O)
    (IsSumOfExtensionByZeroUnits (s.totalRing O)) (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M) (s.lowerShriekModules_acyclic O)
    (derivedLowerShriek s.topology s.base.J s.p O)
    (derivedLowerShriekComparison s.topology s.base.J s.p O) X hX

/-- On the underlying complex of abelian sheaves of a complex cellular for the direct sums of the
`j_{U!}O_U`, `Lπ_!^{Ab}` is `π_!^{Ab}` degreewise: that complex is cellular for the class
`IsSumOfForgetGenerators`, which satisfies the hypotheses of Stacks 0794 for `π_!^{Ab}`. -/
lemma isIso_derivedLowerShriekAbelianComparison_app_of_cellular
    (X : HomotopyCategory (SheafOfModules.{u} (s.totalRing O)) (ComplexShape.up ℤ))
    (hX : cellular (IsSumOfExtensionByZeroUnits (s.totalRing O)) X) :
    IsIso ((derivedLowerShriekAbelianComparison s.topology s.base.J s.p).app
      (((forgetSourceModules s.topology s.base.J s.p O).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj X)) := by
  have : HasExactColimitsOfShape ℕ (Sheaf s.topology AddCommGrpCat.{u}) :=
    hasExactColimitsOfShape_nat_sheafAb.{u} s.topology
  have : HasExactColimitsOfShape ℕ (Sheaf s.base.J AddCommGrpCat.{u}) :=
    hasExactColimitsOfShape_nat_sheafAb.{u} s.base.J
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (s.totalRing O)) :=
    hasExactColimitsOfShape_nat _
  have : PreservesColimitsOfShape ℕ s.abelianLowerShriek :=
    s.abelianLowerShriekAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape ℕ (forgetSourceModules s.topology s.base.J s.p O) :=
    have : PreservesColimitsOfSize.{u, u} (forgetSourceModules s.topology s.base.J s.p O) :=
      AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits (R := s.totalRing O)
    have : PreservesColimitsOfSize.{0, 0} (forgetSourceModules s.topology s.base.J s.p O) :=
      preservesColimitsOfSize_shrink _
    inferInstance
  obtain ⟨S, hS, ⟨e⟩⟩ := hX
  have hcell : cellular (s.IsSumOfForgetGenerators O)
      (((forgetSourceModules s.topology s.base.J s.p O).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj X) :=
    ⟨_, isPCellular_map (forgetSourceModules s.topology s.base.J s.p O)
      (fun N hN => s.isSumOfForgetGenerators_toSheaf O hN) hS,
      ⟨((forgetSourceModules s.topology s.base.J s.p O).mapHomotopyCategory
        (ComplexShape.up ℤ)).mapIso e ≪≫
        ((forgetSourceModules s.topology s.base.J s.p O).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app S⟩⟩
  exact Stacks.ChaoticSite.isIso_app_of_cellular (F := s.abelianLowerShriek)
    (s.IsSumOfForgetGenerators O) (fun _ _ => s.isSumOfForgetGenerators_biprod O)
    (s.exists_epi_isSumOfForgetGenerators O) (s.abelianLowerShriek_acyclic_forgetGenerators O)
    (derivedLowerShriekAbelian s.topology s.base.J s.p)
    (derivedLowerShriekAbelianComparison s.topology s.base.J s.p) _ hcell

/-- The comparison of Stacks 0798, read on homotopy categories, is invertible: it is so
degreewise, by Stacks 08PC part (2) (`isIso_lowerShriekForgetComparison`). -/
instance isIso_forgetComparisonOnHomotopy :
    IsIso (forgetComparisonOnHomotopy s.topology s.base.J s.p O) := by
  have := s.isIso_lowerShriekForgetComparison O
  have : IsIso (NatTrans.mapHomotopyCategory (forgetComparison s.topology s.base.J s.p O)
      (ComplexShape.up ℤ)) :=
    ⟨⟨NatTrans.mapHomotopyCategory (inv (forgetComparison s.topology s.base.J s.p O))
        (ComplexShape.up ℤ), by
      rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id, NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩⟩
  dsimp only [forgetComparisonOnHomotopy]
  infer_instance

/-- On a complex cellular for the direct sums of the `j_{U!}O_U`, the comparison
`derivedForgetComparison` is an isomorphism. -/
lemma isIso_derivedForgetComparison_app_of_cellular
    (X : HomotopyCategory (SheafOfModules.{u} (s.totalRing O)) (ComplexShape.up ℤ))
    (hX : cellular (IsSumOfExtensionByZeroUnits (s.totalRing O)) X) :
    IsIso ((s.derivedForgetComparison O).app (DerivedCategory.Qh.obj X)) := by
  have h₁ := s.isIso_derivedLowerShriekComparison_app_of_cellular O X hX
  have h₂ := s.isIso_derivedLowerShriekAbelianComparison_app_of_cellular O X hX
  have h₃ : IsIso ((derivedForgetComparisonCounit s.topology s.base.J s.p O).app X) := by
    dsimp only [derivedForgetComparisonCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  have h₄ : IsIso ((derivedLowerShriekForgetCounit s.topology s.base.J s.p O).app X) := by
    dsimp only [derivedLowerShriekForgetCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_inv_app]
    infer_instance
  have hfac := NatTrans.congr_app (s.derivedForgetComparison_fac O) X
  rw [NatTrans.comp_app, Functor.whiskerLeft_app] at hfac
  rw [← hfac] at h₃
  exact IsIso.of_isIso_comp_right _
    ((derivedLowerShriekForgetCounit s.topology s.base.J s.p O).app X)

/-- **Stacks 08PC part (4) for the projection of a fibred category.** The comparison
`Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of Stacks 07AE is an isomorphism: derived lower shriek of
`O_C`-modules commutes with forgetting the module structure. Every object of `D(O_C)` is
resolved by a complex cellular for the direct sums of the `j_{U!}O_U` (Stacks 0794), at which the
comparison is invertible by `isIso_derivedForgetComparison_app_of_cellular`. -/
instance isIso_derivedForgetComparison : IsIso (s.derivedForgetComparison O) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (s.totalRing O)) :=
    hasExactColimitsOfShape_nat _
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨R⟩ := hasLeftResolutions_cellularLocalizerMorphism
    (IsSumOfExtensionByZeroUnits (s.totalRing O)) (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M) (DerivedCategory.Qh.objPreimage K)
  have : IsIso ((s.derivedForgetComparison O).app (DerivedCategory.Qh.obj
      ((cellularLocalizerMorphism (IsSumOfExtensionByZeroUnits (s.totalRing O))).functor.obj
        R.X₁))) :=
    s.isIso_derivedForgetComparison_app_of_cellular O R.X₁.obj R.X₁.property
  have : IsIso (DerivedCategory.Qh.map R.w) :=
    Localization.inverts DerivedCategory.Qh _ R.w R.hw
  exact (NatTrans.isIso_app_iff_of_iso (s.derivedForgetComparison O)
    ((DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Qh.map R.w)).symm)).mpr inferInstance

/-- **Stacks 08PC part (4) for the projection of a fibred category**, as an isomorphism:
`Lπ_!^{Ab} ∘ forget ≅ forget ∘ Lπ_!`. -/
def derivedForgetIso :
    (forgetSourceModules s.topology s.base.J s.p O).mapDerivedCategory ⋙
        derivedLowerShriekAbelian s.topology s.base.J s.p ≅
      derivedLowerShriek s.topology s.base.J s.p O ⋙
        (forgetTargetModules s.base.J O).mapDerivedCategory :=
  asIso (s.derivedForgetComparison O)

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
