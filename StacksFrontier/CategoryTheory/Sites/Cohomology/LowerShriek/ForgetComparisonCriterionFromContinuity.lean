module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfCellularInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparisonCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparisonFromContinuity
import StacksCore.Tactic.StacksAttribute

/-!
# The criterion of Stacks 07AE, for a continuous functor of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `g : Sh(C) ⟶ Sh(D)` the
corresponding morphism of topoi, `O_D` a sheaf of rings on `D` and `O_C = g^{-1}O_D`, as in
Stacks 07AC. The warning of Stacks 07AE asserts that `Lg_!` agrees with `Lg_!^{Ab}` *if and only
if* the canonical maps `Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` are isomorphisms in `D(D)` for
all objects `U` of `C`. "Agrees" is read as invertibility of the canonical comparison
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedForgetComparison.lean`; the
canonical maps are `derivedForgetComparisonGenerator` of `ForgetComparisonCriterion.lean`.
This file proves both directions with no hypothesis beyond those of Stacks 07AC.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparison_iff`: **Stacks 07AE**, the
  criterion.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparison_of_isIso_generator`: its
  converse half.
* `Stacks.Cohomology.DerivedLowerShriek.extAcyclic_forget_extensionByZeroUnit`: if the
  comparison is invertible at `j_{U!}O_U`, the underlying abelian sheaf of `j_{U!}O_U` is
  `Ext`-acyclic for `g_!^{Ab} ⊣ g^{-1}`.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_forgetComparison_app_extensionByZeroUnit`: and
  the comparison of Stacks 0798 is then invertible at `j_{U!}O_U`.

## Implementation notes

The forward half is `isIso_derivedForgetComparisonGenerator` of `ForgetComparisonCriterion.lean`
with its hypothesis `hU` discharged: on a small site with a commutative structure sheaf the first
map of the displayed chain of Stacks 07AC is the isomorphism
`derivedLowerShriekSingleExtensionByZeroUnitIso`.

The converse is the source's "the construction of `Lg_!` in the proof of Lemma 07AC shows",
carried out in three steps.

1. *`Ext`-acyclicity.* For an injective abelian sheaf `I` on `D`,
   `Ext^n(forget j_{U!}O_U, g^{-1}I) = Hom(Lg_!^{Ab}(forget j_{U!}O_U), I[n])` by the derived
   adjunction of `Lg_!^{Ab}`; invertibility at `U` identifies the source with
   `forget j_{u(U)!}O_{u(U)}` in degree zero, and `Ext^n` into an injective vanishes for `n ≥ 1`.
2. *`Lg_!^{Ab}` on underlying complexes.* The class of abelian sheaves which are `Ext`-acyclic
   for `g_!^{Ab} ⊣ g^{-1}` contains zero, is closed under binary sums, contains the generators
   `j_{U!}ℤ_U` (Stacks 0D6X) and so generates, and is carried by `g_!^{Ab}` to acyclic complexes
   in the bounded above case (`Adjunction.map_acyclic_of_extAcyclic`); by the criterion of
   Stacks 0794 the counit of `Lg_!^{Ab}` is invertible at complexes cellular for it. The
   underlying complex of a complex cellular for the direct sums of the `j_{U!}O_U` is such a
   complex once step 1 holds (`StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_map`).
3. *The degreewise comparison.* At `j_{U!}O_U[0]` both counits are invertible, so the
   compatibility `derivedForgetComparison_fac` makes the degreewise comparison of Stacks 0798 a
   quasi-isomorphism between complexes concentrated in degree zero, hence invertible at
   `j_{U!}O_U`; it is then invertible at direct sums of them and at `ℕ`-indexed colimits of
   those (`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_of_isColimit`), hence
   degreewise on every cellular complex. Every object of `D(O_C)` is represented by a cellular
   complex, on which `Lg_!` is computed degreewise, so the comparison is invertible everywhere.

The class used for `Lg_!^{Ab}` in step 2 is the `Ext`-acyclic class itself rather than the direct
sums of the `j_{U!}ℤ_U` with which `Lg_!^{Ab}` is constructed: the counit of a left derived
functor is invertible at objects cellular for *any* class satisfying the criterion of Stacks
0794 (`CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives`), and the underlying
abelian sheaves of the `j_{U!}O_U` are not direct sums of the `j_{V!}ℤ_V`.

## References

* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian ZeroObject

universe u

namespace HomologicalComplex

variable {A : Type*} [Category A] [Abelian A]

/-- A morphism of cochain complexes which is a quasi-isomorphism in degree `i`, between two
complexes whose differentials into and out of degree `i` vanish, is an isomorphism in degree
`i`: there both the cycles and the homology are the term itself. -/
lemma isIso_f_of_quasiIsoAt {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) [QuasiIsoAt φ i]
    (hK₁ : K.d (i - 1) i = 0) (hK₂ : K.d i (i + 1) = 0)
    (hL₁ : L.d (i - 1) i = 0) (hL₂ : L.d i (i + 1) = 0) :
    IsIso (φ.f i) := by
  have hi : (ComplexShape.up ℤ).prev i = i - 1 := by simp
  have hn : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have := K.isIso_iCycles i (i + 1) hn hK₂
  have := L.isIso_iCycles i (i + 1) hn hL₂
  have := K.isIso_homologyπ (i - 1) i hi hK₁
  have := L.isIso_homologyπ (i - 1) i hi hL₁
  have h1 : IsIso (homologyMap φ i) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have h2 : cyclesMap φ i = K.homologyπ i ≫ homologyMap φ i ≫ inv (L.homologyπ i) := by
    rw [← Category.assoc, homologyπ_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have h3 : IsIso (cyclesMap φ i) := by
    rw [h2]
    infer_instance
  rw [show φ.f i = inv (K.iCycles i) ≫ cyclesMap φ i ≫ L.iCycles i by
    rw [cyclesMap_i, IsIso.inv_hom_id_assoc]]
  infer_instance

end HomologicalComplex


namespace Stacks.Cohomology.DerivedLowerShriek

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J f] (O : Sheaf K CommRingCat.{u})

attribute [local instance] HasDerivedCategory.standard

open StacksDraft.UnboundedLeftDerivedFunctor

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- Extension by zero of `O_C`-modules along `C/V ⥤ C` exists. -/
theorem isRightAdjoint_sourceSliceRestriction (V : C) :
    (_root_.SheafOfModules.pushforward.{u} (F := Over.forget V)
      (𝟙 ((inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).over V))).IsRightAdjoint :=
  Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint_of_univLE.{u}
    J (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) V

omit [f.IsContinuous J K] [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- Extension by zero of `O_D`-modules along `D/W ⥤ D` exists. -/
theorem isRightAdjoint_targetSliceRestriction (W : D) :
    (_root_.SheafOfModules.pushforward.{u} (F := Over.forget W)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O).over
        W))).IsRightAdjoint :=
  Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint_of_univLE.{u} K
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) W

attribute [local instance] isRightAdjoint_sourceSliceRestriction
  isRightAdjoint_targetSliceRestriction

/-- `Lg_! ⋙ forget` is a left derived functor, `Lg_!` being constructed by resolutions; this is
the absoluteness on which `derivedForgetComparison` rests. -/
theorem isLeftDerivedFunctor_derivedLowerShriek_comp_forget_of_continuous :
    (derivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
      (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).mapDerivedCategory).IsLeftDerivedFunctor
      (derivedLowerShriekForgetCounit J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) (sourceQuasiIso J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic J K f _
    (lowerShriekModules_acyclic J K f O) _

attribute [local instance] isLeftDerivedFunctor_derivedLowerShriek_comp_forget_of_continuous

/-- The first map of the displayed chain `Lg_!(j_{U!}O_U) = g_!j_{U!}O_U` of Stacks 07AC is
invertible: this discharges the hypothesis `hU` of `ForgetComparisonCriterion.lean`. -/
theorem isIso_derivedLowerShriekSingleComparison_of_continuous (U : C) :
    IsIso (derivedLowerShriekSingleComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O) U) := by
  change IsIso (derivedLowerShriekSingleExtensionByZeroUnitIso J K f O U).hom
  infer_instance

/-- **If the comparison of Stacks 07AE is invertible at `j_{U!}O_U`, its underlying abelian sheaf
is `Ext`-acyclic for `g_!^{Ab} ⊣ g^{-1}`.** By the derived adjunction of `Lg_!^{Ab}`,
`Ext^n(forget j_{U!}O_U, g^{-1}I) = Hom(Lg_!^{Ab} forget j_{U!}O_U, I[n])`, and the invertible
comparison together with Stacks 07AC identifies `Lg_!^{Ab} forget j_{U!}O_U` with
`forget(g_! j_{U!}O_U)` in degree zero, out of which `Ext^n` into an injective vanishes. -/
theorem extAcyclic_forget_extensionByZeroUnit (U : C)
    (hU : IsIso ((derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      ((DerivedCategory.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)) U))))
    (I : Sheaf K AddCommGrpCat.{u}) [Injective I] (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Ext.{u} ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U))
        ((abelianRestriction.{u} J K f).obj I) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let jU := extensionByZeroUnit (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U
  let X := (forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)).obj jU
  let W := (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)).obj ((lowerShriekModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj jU)
  let dR := derivedAbelianRestriction.{u} J K f
  let adj := derivedAbelianLowerShriekAdjunction.{u} J K f
  let E : (derivedLowerShriekAbelian J K f).obj ((DerivedCategory.singleFunctor _ 0).obj X) ≅
      (DerivedCategory.singleFunctor _ 0).obj W :=
    (derivedLowerShriekAbelian J K f).mapIso
        (((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)).mapDerivedCategorySingleFunctor 0).app jU).symm ≪≫
      asIso ((derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).app _) ≪≫
      (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).mapDerivedCategory.mapIso
        (derivedLowerShriekSingleExtensionByZeroUnitIso J K f O U) ≪≫
      ((forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).mapDerivedCategorySingleFunctor 0).app _
  let T := ((DerivedCategory.singleFunctor _ 0).obj I)⟦((m + 1 : ℕ) : ℤ)⟧
  let e1 : ((DerivedCategory.singleFunctor _ 0).obj
      ((abelianRestriction.{u} J K f).obj I))⟦((m + 1 : ℕ) : ℤ)⟧ ≅ dR.obj T :=
    (shiftFunctor _ ((m + 1 : ℕ) : ℤ)).mapIso
        (((abelianRestriction.{u} J K f).mapDerivedCategorySingleFunctor 0).app I).symm ≪≫
      ((dR.commShiftIso ((m + 1 : ℕ) : ℤ)).app _).symm
  let eq : Ext.{u} X ((abelianRestriction.{u} J K f).obj I) (m + 1) ≃ Ext.{u} W I (m + 1) :=
    Ext.homEquiv.trans (((Iso.refl _).homCongr e1).trans ((adj.homEquiv _ _).symm.trans
      ((E.homCongr (Iso.refl T)).trans Ext.homEquiv.symm)))
  have := Ext.subsingleton_of_injective W I m
  exact eq.subsingleton

omit [f.IsContinuous J K] [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- Coproducts of abelian sheaves on `C` indexed by a type in the coefficient universe, recorded
as a term: instance search explores the special-shape instances first and runs out of budget. -/
theorem hasCoproduct_sheafAb {ι : Type u} (X : ι → Sheaf J AddCommGrpCat.{u}) : HasCoproduct X :=
  HasColimitsOfShape.has_colimit _

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The `Ext`-acyclic abelian sheaves for `g_!^{Ab} ⊣ g^{-1}` contain a zero object. -/
instance containsZero_extAcyclic :
    (abelianAdjunction.{u} J K f).extAcyclic.ContainsZero :=
  ⟨⟨0, isZero_zero _, (abelianAdjunction.{u} J K f).extAcyclic_of_isZero (isZero_zero _)⟩⟩

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The `Ext`-acyclic abelian sheaves for `g_!^{Ab} ⊣ g^{-1}` are closed under binary sums. -/
lemma extAcyclic_biprod {M N : Sheaf J AddCommGrpCat.{u}}
    (hM : (abelianAdjunction.{u} J K f).extAcyclic M)
    (hN : (abelianAdjunction.{u} J K f).extAcyclic N) :
    (abelianAdjunction.{u} J K f).extAcyclic (M ⊞ N) := by
  let X : WalkingPair → Sheaf J AddCommGrpCat.{u} := fun j => WalkingPair.casesOn j M N
  have : HasCoproduct X := (inferInstance : HasBinaryCoproduct M N)
  exact (abelianAdjunction.{u} J K f).extAcyclic_of_iso (biprod.isoCoprod M N).symm
    ((abelianAdjunction.{u} J K f).extAcyclic_coproduct X fun j => by cases j <;> assumption)

omit [f.IsCocontinuous J K] in
/-- Direct sums of the `j_{U!}ℤ_U` are `Ext`-acyclic for `g_!^{Ab} ⊣ g^{-1}`: this is Stacks
0D6X for injective abelian sheaves. -/
lemma extAcyclic_of_isSumOfExtensionByZeroUnitsAb {M : Sheaf J AddCommGrpCat.{u}}
    (hM : IsSumOfExtensionByZeroUnitsAb.{u} J M) :
    (abelianAdjunction.{u} J K f).extAcyclic M := by
  obtain ⟨ι, V, ⟨e⟩⟩ := hM
  have := hasCoproduct_sheafAb J (fun i => extensionByZeroUnitAb.{u} J (V i))
  exact (abelianAdjunction.{u} J K f).extAcyclic_of_iso e
    ((abelianAdjunction.{u} J K f).extAcyclic_coproduct _ fun i I _ n hn =>
      Stacks.CechSite.injective_sheaf_subsingleton_ext_of_continuous J K f (V i) I n hn)

omit [f.IsCocontinuous J K] in
/-- Every abelian sheaf on `C` is a quotient of an `Ext`-acyclic one. -/
lemma exists_epi_extAcyclic (M : Sheaf J AddCommGrpCat.{u}) :
    ∃ (N : Sheaf J AddCommGrpCat.{u}) (_ : (abelianAdjunction.{u} J K f).extAcyclic N)
      (p : N ⟶ M), Epi p := by
  obtain ⟨N, hN, p, hp⟩ := exists_epi_isSumOfExtensionByZeroUnitsAb.{u} J M
  exact ⟨N, extAcyclic_of_isSumOfExtensionByZeroUnitsAb J K f hN, p, hp⟩

omit [f.IsCocontinuous J K] [Sites.PreservesCoveringPullbacks J f] in
/-- If the underlying abelian sheaves of the `j_{U!}O_U` are `Ext`-acyclic, so are those of their
direct sums, forgetting the module structure commuting with direct sums. -/
lemma extAcyclic_forget_of_isSumOfExtensionByZeroUnits
    (hU : ∀ U : C, (abelianAdjunction.{u} J K f).extAcyclic
      ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    {M : SheafOfModules.{u} (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O))}
    (hM : IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) M) :
    (abelianAdjunction.{u} J K f).extAcyclic ((forgetSourceModules J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj M) := by
  obtain ⟨ι, V, ⟨e⟩⟩ := hM
  have := hasCoproduct_sheafAb J (fun i => (forgetSourceModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
    (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)) (V i)))
  exact (abelianAdjunction.{u} J K f).extAcyclic_of_iso
    ((PreservesCoproduct.iso (forgetSourceModules J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
      (fun i => extensionByZeroUnit (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (V i))).symm ≪≫
        (forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)).mapIso e)
    ((abelianAdjunction.{u} J K f).extAcyclic_coproduct _ fun i => hU (V i))

/-- A natural transformation invertible at an object is invertible at every isomorphic one. -/
lemma isIso_app_of_iso' {X Y : Type*} [Category X] [Category Y] {F G : X ⥤ Y}
    (τ : F ⟶ G) {a b : X} (e : a ≅ b) (h : IsIso (τ.app a)) : IsIso (τ.app b) := by
  rw [show τ.app b = F.map e.inv ≫ τ.app a ≫ G.map e.hom by
    rw [← Category.assoc, τ.naturality, Category.assoc, ← G.map_comp, e.inv_hom_id,
      G.map_id, Category.comp_id]]
  infer_instance

omit [f.IsContinuous J K] [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The third factor of an invertible fourfold composite whose other factors are invertible is
invertible. -/
lemma isIso_of_isIso_comp₄ {X : Type*} [Category X] {a b c d e : X} (f₁ : a ⟶ b) (f₂ : b ⟶ c)
    (f₃ : c ⟶ d) (f₄ : d ⟶ e) [IsIso f₁] [IsIso f₂] [IsIso f₄] (h : IsIso (f₁ ≫ f₂ ≫ f₃ ≫ f₄)) :
    IsIso f₃ := by
  rw [show f₃ = inv f₂ ≫ inv f₁ ≫ (f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ inv f₄ by simp]
  infer_instance

omit [f.IsContinuous J K] [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The middle factor of an invertible threefold composite whose outer factors are invertible
is invertible. -/
lemma isIso_of_isIso_comp₃ {X : Type*} [Category X] {a b c d : X} (f₁ : a ⟶ b) (f₂ : b ⟶ c)
    (f₃ : c ⟶ d) [IsIso f₁] [IsIso f₃] (h : IsIso (f₁ ≫ f₂ ≫ f₃)) : IsIso f₂ := by
  rw [show f₂ = inv f₁ ≫ (f₁ ≫ f₂ ≫ f₃) ≫ inv f₃ by simp]
  infer_instance

omit [f.IsCocontinuous J K] in
/-- **`Lg_!^{Ab}` is computed degreewise on complexes cellular for the `Ext`-acyclic class**:
that class contains zero, is closed under binary sums, generates, and is carried by `g_!^{Ab}`
to acyclic complexes in the bounded above case, which is all the criterion of Stacks 0794 asks. -/
lemma isIso_derivedLowerShriekAbelianComparison_app_of_isPCellular
    {S : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ}
    (hS : IsPCellular (abelianAdjunction.{u} J K f).extAcyclic S) :
    IsIso ((derivedLowerShriekAbelianComparison J K f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)) := by
  have := hasExactColimitsOfShape_nat_sheafAb.{u} J
  have := hasExactColimitsOfShape_nat_sheafAb.{u} K
  exact Stacks.ChaoticSite.isIso_app_of_cellular (F := abelianLowerShriek.{u} J K f)
    (abelianAdjunction.{u} J K f).extAcyclic (fun _ _ => extAcyclic_biprod J K f)
    (exists_epi_extAcyclic J K f) (fun a L hLE hLP hLac => by
      have := hLE
      exact (abelianAdjunction.{u} J K f).map_acyclic_of_extAcyclic L a hLac hLP)
    _ (derivedLowerShriekAbelianComparison J K f) _ ⟨S, hS, ⟨Iso.refl _⟩⟩

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The forgetful functor from `O_C`-modules commutes with `ℕ`-indexed colimits. -/
lemma preservesColimitsOfShape_nat_forgetSource :
    PreservesColimitsOfShape ℕ (forgetSourceModules J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) := by
  have : PreservesColimitsOfSize.{0, 0} (forgetSourceModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
    preservesSmallestColimits_of_preservesColimits _
  infer_instance

omit [f.IsCocontinuous J K] [Sites.PreservesCoveringPullbacks J f] in
/-- The underlying complex of abelian sheaves of a complex cellular for the direct sums of the
`j_{U!}O_U` is cellular for the `Ext`-acyclic class, once the underlying abelian sheaves of the
`j_{U!}O_U` are `Ext`-acyclic. -/
lemma isPCellular_forget
    (hU : ∀ U : C, (abelianAdjunction.{u} J K f).extAcyclic
      ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    {S : CochainComplex (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ}
    (hS : IsPCellular (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) S) :
    IsPCellular (abelianAdjunction.{u} J K f).extAcyclic
      (((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj S) := by
  have := preservesColimitsOfShape_nat_forgetSource J K f O
  exact StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_map
    (forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
    (fun _ hM => extAcyclic_forget_of_isSumOfExtensionByZeroUnits J K f O hU hM) hS

omit [f.IsCocontinuous J K] in
/-- The components of `derivedForgetComparisonCounit`: the counit of `Lg_!^{Ab}` at the
underlying complex followed by the degreewise comparison of Stacks 0798, between the two
identifications of the derived and homotopy-category incarnations of `forget`. -/
lemma derivedForgetComparisonCounit_app_eq
    (X : HomotopyCategory (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) (ComplexShape.up ℤ)) :
    (derivedForgetComparisonCounit J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app X =
      (derivedLowerShriekAbelian J K f).map
          ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
            (targetRingedSite K O).O)).mapDerivedCategoryFactorsh.hom.app X) ≫
        (derivedLowerShriekAbelianComparison J K f).app
          (((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
            (targetRingedSite K O).O)).mapHomotopyCategory _).obj X) ≫
        DerivedCategory.Qh.map ((forgetComparisonOnHomotopy J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app X) ≫
        (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)).mapDerivedCategoryFactorsh.inv.app
          ((lowerShriekOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf
            (targetRingedSite K O).O)).obj X) := by
  simp only [derivedForgetComparisonCounit, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]

/-- `derivedForgetComparison_fac` at a single object of the homotopy category. -/
lemma derivedForgetComparison_app_comp
    (X : HomotopyCategory (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) (ComplexShape.up ℤ)) :
    (derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app (DerivedCategory.Qh.obj X) ≫
        (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)).mapDerivedCategory.map
          ((derivedLowerShriekComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
            (targetRingedSite K O).O)).app X) =
      (derivedForgetComparisonCounit J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).app X := by
  simpa only [derivedLowerShriekForgetCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp] using
    congrArg (fun t => t.app X) (derivedForgetComparison_fac J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The components of `forgetComparisonOnHomotopy`: the degreewise comparison of Stacks 0798 on
homotopy categories, between the identifications of the composites on homotopy categories. -/
private lemma forgetComparisonOnHomotopy_app_eq
    (X : HomotopyCategory (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) (ComplexShape.up ℤ)) :
    (forgetComparisonOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app X =
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O) ⋙ lowerShriekAbelian J K f))
        (ComplexShape.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory (forgetComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
        (ComplexShape.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (lowerShriekModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O) ⋙ forgetTargetModules K
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
        (ComplexShape.up ℤ)).inv.app X := by
  simp only [forgetComparisonOnHomotopy, NatTrans.comp_app]

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The comparison of Stacks 0798 on homotopy categories is invertible at a complex at whose terms
it is invertible. -/
lemma isIso_forgetComparisonOnHomotopy_app
    (S : CochainComplex (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ)
    (h : ∀ n, IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app (S.X n))) :
    IsIso ((forgetComparisonOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)) := by
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex (forgetComparison J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
      (ComplexShape.up ℤ)).app S).f n) := h
  have : IsIso ((NatTrans.mapHomologicalComplex (forgetComparison J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
      (ComplexShape.up ℤ)).app S) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((NatTrans.mapHomotopyCategory (forgetComparison J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
      (ComplexShape.up ℤ)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)) :=
    Functor.map_isIso (HomotopyCategory.quotient _ _)
      ((NatTrans.mapHomologicalComplex (forgetComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
        (ComplexShape.up ℤ)).app S)
  simp only [forgetComparisonOnHomotopy, NatTrans.comp_app]
  infer_instance

/-- `Lg_!` is computed degreewise on every complex cellular for the direct sums of the
`j_{U!}O_U`, these being the complexes by which it is constructed (Stacks 0794). -/
lemma isIso_derivedLowerShriekComparison_app_of_isPCellular
    {S : CochainComplex (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ}
    (hS : IsPCellular (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) S) :
    IsIso ((derivedLowerShriekComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) :=
    hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)) := hasExactColimitsOfShape_nat _
  have : PreservesColimitsOfShape ℕ (lowerShriekModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O))).preservesColimitsOfShape
  exact Stacks.ChaoticSite.isIso_app_of_cellular (F := lowerShriekModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
    (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M) (lowerShriekModules_acyclic J K f O)
    _ (derivedLowerShriekComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)) _ ⟨S, hS, ⟨Iso.refl _⟩⟩

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The comparison of Stacks 0798 is invertible at a colimit of a `ℕ`-indexed system at whose
objects it is invertible, and at a direct sum of objects at which it is invertible. -/
lemma isIso_forgetComparison_app_of_isColimit {I : Type*} [Category* I]
    [HasColimitsOfShape I AddCommGrpCat.{u}]
    (Z : I ⥤ SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) (c : Cocone Z)
      (hc : IsColimit c)
    (h : ∀ i, IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app (Z.obj i))) :
    IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app c.pt) :=
  Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_app_of_isColimit f
    (idRingMap J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) Z c hc
      (_root_.SheafOfModules.preservesColimitsOfShape_toSheaf _)
    (_root_.SheafOfModules.preservesColimitsOfShape_toSheaf _) h

/-- **The comparison of Stacks 0798 is invertible at `j_{U!}O_U` once the canonical map of the
criterion of Stacks 07AE is.** At the complex `j_{U!}O_U[0]` the counit of `Lg_!` is invertible
(Stacks 07AC), and so is that of `Lg_!^{Ab}` at its underlying complex, which is cellular for the
`Ext`-acyclic class; the compatibility of the comparison with the two counits then makes the
degreewise comparison a quasi-isomorphism between complexes concentrated in degree zero. -/
lemma isIso_forgetComparison_app_extensionByZeroUnit
    (hU : ∀ U : C, (abelianAdjunction.{u} J K f).extAcyclic
      ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    (U : C)
    (hα : IsIso ((derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      ((DerivedCategory.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)) U)))) :
    IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)) := by
  let jU := extensionByZeroUnit (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U
  let L := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj jU
  let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L
  have hLP : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (L.X n) :=
    isSumOfExtensionByZeroUnits_single J _ U
  have h1 : IsIso ((derivedLowerShriekComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)).app X) :=
    isIso_derivedLowerShriekComparison_app J K f O L hLP
  have h2 : IsIso ((derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)).app (DerivedCategory.Qh.obj X)) :=
    isIso_app_of_iso' _ ((DerivedCategory.quotientCompQhIso _).app L).symm hα
  have h3 : IsIso ((derivedForgetComparisonCounit J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app X) := by
    rw [← derivedForgetComparison_app_comp]
    infer_instance
  have h4 : IsIso ((derivedLowerShriekAbelianComparison J K f).app
      (((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).mapHomotopyCategory _).obj X)) :=
    isIso_derivedLowerShriekAbelianComparison_app_of_isPCellular J K f
      (isPCellular_forget J K f O hU (CochainComplex.isPCellular_of_isStrictlyLE _ L hLP))
  have h5 : IsIso (DerivedCategory.Qh.map ((forgetComparisonOnHomotopy J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app X)) := by
    rw [derivedForgetComparisonCounit_app_eq] at h3
    exact isIso_of_isIso_comp₄ _ _ _ _ h3
  let φ := (NatTrans.mapHomologicalComplex (forgetComparison J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (ComplexShape.up ℤ)).app L
  have h6 : IsIso (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (forgetComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (ComplexShape.up ℤ)).app
        X)) := by
    rw [forgetComparisonOnHomotopy_app_eq, Functor.map_comp, Functor.map_comp] at h5
    exact isIso_of_isIso_comp₃ _ _ _ h5
  have h7 : QuasiIso φ := CochainComplex.quasiIso_of_isIso_Qh_map φ h6
  have hz : ∀ {a b : Sheaf J AddCommGrpCat.{u}}, (lowerShriekAbelian J K f).map (0 : a ⟶ b) = 0 :=
    fun {_ _} => (abelianLowerShriek.{u} J K f).map_zero _ _
  have h8 : IsIso (φ.f 0) :=
    HomologicalComplex.isIso_f_of_quasiIsoAt φ 0 (by simp [L, hz]) (by simp [L, hz])
      (by simp [L]) (by simp [L])
  exact isIso_app_of_iso' _ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 jU) h8

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The comparison of Stacks 0798 is invertible at a direct sum of the `j_{U!}O_U` once it is
invertible at each `j_{U!}O_U`. -/
private lemma isIso_forgetComparison_app_of_isSumOfExtensionByZeroUnits
    (hτU : ∀ U : C, IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    {M : SheafOfModules.{u} (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O))}
    (hM : IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) M) :
    IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app M) := by
  obtain ⟨ι, V, ⟨e⟩⟩ := hM
  exact isIso_app_of_iso' _ e (isIso_forgetComparison_app_of_isColimit J K f O
    (Discrete.functor fun i => extensionByZeroUnit (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (V i))
    (colimit.cocone _) (colimit.isColimit _) (fun i => hτU (V i.as)))

omit [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The comparison of Stacks 0798 is invertible at every term of a complex cellular for the direct
sums of the `j_{U!}O_U` once it is invertible at each `j_{U!}O_U`. -/
private lemma isIso_forgetComparison_app_X_of_isPCellular
    (hτU : ∀ U : C, IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    {S : CochainComplex (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ}
    (hS : IsPCellular (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) S) (n : ℤ) :
    IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app (S.X n)) := by
  obtain ⟨Q, g, c, hc, e, -, hQ, -⟩ := hS
  exact isIso_app_of_iso' _ ((HomologicalComplex.eval _ _ n).mapIso e)
    (isIso_forgetComparison_app_of_isColimit J K f O
      (Functor.ofSequence g ⋙ HomologicalComplex.eval _ _ n)
      ((HomologicalComplex.eval _ _ n).mapCocone c)
      (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hc)
      (fun i => isIso_forgetComparison_app_of_isSumOfExtensionByZeroUnits J K f O hτU (hQ i n)))

/-- The comparison `derivedForgetComparison` is invertible at every complex cellular for the
direct sums of the `j_{U!}O_U`, once the underlying abelian sheaves of the `j_{U!}O_U` are
`Ext`-acyclic and the comparison of Stacks 0798 is invertible at each `j_{U!}O_U`. -/
private lemma isIso_derivedForgetComparison_app_of_isPCellular
    (hU : ∀ U : C, (abelianAdjunction.{u} J K f).extAcyclic
      ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    (hτU : ∀ U : C, IsIso ((forgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)))
    {S : CochainComplex (SheafOfModules.{u} (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ}
    (hS : IsPCellular (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) S) :
    IsIso ((derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S))) := by
  have h1 := isIso_derivedLowerShriekComparison_app_of_isPCellular J K f O hS
  have h4 : IsIso ((derivedLowerShriekAbelianComparison J K f).app
      (((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S))) :=
    isIso_derivedLowerShriekAbelianComparison_app_of_isPCellular J K f
      (isPCellular_forget J K f O hU hS)
  have h5 := isIso_forgetComparisonOnHomotopy_app J K f O S
    (isIso_forgetComparison_app_X_of_isPCellular J K f O hτU hS)
  have h3 : IsIso ((derivedForgetComparisonCounit J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)) := by
    rw [derivedForgetComparisonCounit_app_eq]
    infer_instance
  rw [← derivedForgetComparison_app_comp] at h3
  exact IsIso.of_isIso_comp_right _ ((forgetTargetModules K
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).mapDerivedCategory.map
    ((derivedLowerShriekComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S)))

/-- **The criterion of Stacks 07AE, the converse.** If every canonical map
`Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` is invertible, then so is the comparison
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`.

This is the source's "the construction of `Lg_!` in the proof of Lemma 07AC shows", carried out.
Invertibility at the generators makes the underlying abelian sheaves of the `j_{U!}O_U`
`Ext`-acyclic for `g_!^{Ab} ⊣ g^{-1}` (by the derived adjunction of `Lg_!^{Ab}`), and makes the
comparison of Stacks 0798 invertible at them, hence at their direct sums and at the `ℕ`-indexed
colimits of those. Every object of `D(O_C)` is represented by a complex cellular for the direct
sums of the `j_{U!}O_U`; on such a complex `Lg_!` is computed degreewise, `Lg_!^{Ab}` is computed
degreewise on its underlying complex, which is cellular for the `Ext`-acyclic class, and the
comparison is the degreewise comparison of Stacks 0798, which is invertible. -/
theorem isIso_derivedForgetComparison_of_isIso_generator
    (h : ∀ U : C, IsIso (derivedForgetComparisonGenerator J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) U)) :
    IsIso (derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)) := by
  have hα : ∀ U : C, IsIso ((derivedForgetComparison J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app
      ((DerivedCategory.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (targetRingedSite K O).O)) U))) := fun U =>
    (isIso_derivedForgetComparisonGenerator_iff J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O) U
      (isIso_derivedLowerShriekSingleComparison_of_continuous J K f O U)).1 (h U)
  have hU : ∀ U : C, (abelianAdjunction.{u} J K f).extAcyclic
    ((forgetSourceModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf
    (targetRingedSite K O).O)).obj
      (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (targetRingedSite K O).O)) U)) := fun U I _ n hn =>
    extAcyclic_forget_extensionByZeroUnit J K f O U (hα U) I n hn
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (inverseImageRing J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) :=
    hasExactColimitsOfShape_nat _
  obtain ⟨R⟩ := hasLeftResolutions_cellularLocalizerMorphism
    (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M)
    (DerivedCategory.Qh.objPreimage Y)
  obtain ⟨S, hS, ⟨eS⟩⟩ := R.X₁.property
  have hw : IsIso (DerivedCategory.Qh.map R.w) :=
    Localization.inverts DerivedCategory.Qh _ _ R.hw
  exact isIso_app_of_iso' _ (DerivedCategory.Qh.mapIso eS.symm ≪≫
    asIso (DerivedCategory.Qh.map R.w) ≪≫ DerivedCategory.Qh.objObjPreimageIso Y)
    (isIso_derivedForgetComparison_app_of_isPCellular J K f O hU
      (fun U => isIso_forgetComparison_app_extensionByZeroUnit J K f O hU U (hα U)) hS)

/-- **Stacks Project, Tag 07AE, the criterion.** Let `u : C ⥤ D` be a continuous and
cocontinuous functor of sites, `g` the corresponding morphism of topoi, `O_D` a sheaf of rings on
`D` and `O_C = g^{-1}O_D`. Then `Lg_!` agrees with `Lg_!^{Ab}`, in the sense that the canonical
comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is an isomorphism, if and only if the canonical
maps `Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` are isomorphisms in `D(D)` for all objects `U`
of `C`.

The comparison is `derivedForgetComparison`, the unique transformation compatible with the two
counits and the comparison of Stacks 0798
(`existsUnique_derivedForgetComparison_of_continuous`). The canonical map at `U` is
`derivedForgetComparisonGenerator`: the component of the comparison at `j_{U!}O_U` in degree
zero, followed by the identification `Lg_!(j_{U!}O_U) = g_!j_{U!}O_U = j_{u(U)!}O_{u(U)}` of
Stacks 07AC. The hypotheses are those of Stacks 07AC; continuity in the sense of Stacks 00WV is
`Functor.IsContinuous` with `Stacks.Sites.PreservesCoveringPullbacks`. The forward implication
is `isIso_derivedForgetComparisonGenerator`, the converse
`isIso_derivedForgetComparison_of_isIso_generator`. -/
@[stacks 07AE "the criterion: `Lg_!` agrees with `Lg_!^{Ab}` (the comparison \
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is invertible) iff every canonical map \
`Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` is invertible in D(D); both directions, under the \
hypotheses of Stacks 07AC only, in the library's convention for it: small sites with objects, \
morphisms and module sections in one universe, and a sheaf of (commutative) rings"]
theorem isIso_derivedForgetComparison_iff :
    IsIso (derivedForgetComparison J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (targetRingedSite K O).O)) ↔
      ∀ U : C, IsIso (derivedForgetComparisonGenerator J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) U) :=
  ⟨fun h U => isIso_derivedForgetComparisonGenerator J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) h U
      (isIso_derivedLowerShriekSingleComparison_of_continuous J K f O U),
    isIso_derivedForgetComparison_of_isIso_generator J K f O⟩

end Stacks.Cohomology.DerivedLowerShriek
