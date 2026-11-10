module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftSectionCorepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ULiftModuleDerivedLowerShriek

/-!
# The lower shriek of modules commutes with raising the universe of the sections

Let `f : C ⥤ D` be a continuous and cocontinuous functor of sites whose morphisms lie in the
universe `r` of a sheaf of commutative rings `O_D`, and let `O_C = g^{-1} O_D`. The lower shriek
`g_!` of sheaves of modules is formed at the universe `r` of the rings
(`Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules`, an abstract left adjoint) and at the
universe `max u₁ r` containing the sites (`Stacks.SheafOfModules.lowerShriek`). The universe lifts
`Λ` of the sections commute with restriction `g^*` on the nose, so their mate is a comparison

`g_! (Λ M) ⟶ Λ (g_! M)`.

This file proves that the comparison is invertible at every direct sum of the `j_{U!} O_U`, the
modules out of which the derived lower shrieks are computed: at `j_{U!} O_U` both sides
corepresent the sections over `f(U)` at the raised universe
(`Stacks.SheafOfModules.isCorepresentingSection_uliftForPresentation`) and the comparison carries
one corepresenting section to the other; both sides commute with direct sums.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.ULiftComparison.restrictionULiftIso`: `g^* ∘ Λ = Λ ∘ g^*`.
* `Stacks.Cohomology.DerivedLowerShriek.ULiftComparison.lowerShriekULiftComparison`: the mate
  `g_! ∘ Λ ⟶ Λ ∘ g_!`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.ULiftComparison.isIso_lowerShriekULiftComparison_app`:
  the comparison is invertible at every direct sum of the `j_{U!} O_U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v r u₁

namespace Stacks.Cohomology.DerivedLowerShriek.ULiftComparison

/- Instance search for coproducts of sheaves of modules times out since the Lean v4.35.0 bump;
this local instance gives the direct route. -/
local instance (priority := high) hasColimitsOfShape_discrete_presheafOfModules
    {C : Type*} [Category* C] (R : Cᵒᵖ ⥤ RingCat.{v}) (I : Type v) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{v} R) :=
  PresheafOfModules.hasColimitsOfShape R (Discrete I)

variable {C : Type u₁} [Category.{r} C] {D : Type u₁} [Category.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ r}] [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}]
  [(SheafOfModules.pushforward.{r} (F := f) (idRingMap J K f O)).IsRightAdjoint]

/-- The universe lift of the sections of sheaves of `O_C`-modules. -/
abbrev sourceULift :
    SheafOfModules.{r} (inverseImageRing J K f O) ⥤
      SheafOfModules.{max u₁ r} (inverseImageRing J K f O) :=
  SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, max u₁ r}

/-- The universe lift of the sections of sheaves of `O_D`-modules. -/
abbrev targetULift : SheafOfModules.{r} O ⥤ SheafOfModules.{max u₁ r} O :=
  SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, max u₁ r}

/-- **Restriction of modules commutes with raising the universe of the sections**, on the
nose: both composites send a sheaf of modules to the universe lift of its restriction along
`f`. -/
def restrictionULiftIso :
    restrictionModules J K f O ⋙ sourceULift J K f O ≅
      targetULift K O ⋙ Stacks.SheafOfModules.inverseImage.{max u₁ r} J K f O :=
  Iso.refl _


/-- **The comparison `g_! ∘ Λ ⟶ Λ ∘ g_!`**: the mate, across the adjunctions `g_! ⊣ g^*` at the
two universes, of the identification `g^* ∘ Λ = Λ ∘ g^*`. -/
def lowerShriekULiftComparison :
    TwoSquare (sourceULift J K f O) (lowerShriekModules J K f O)
      (Stacks.SheafOfModules.lowerShriek.{max u₁ r} J K f O) (targetULift K O) :=
  (mateEquiv (adjunctionModules J K f O)
    (Stacks.SheafOfModules.lowerShriekAdjunction.{max u₁ r} J K f O)).symm
      (TwoSquare.mk _ _ _ _ (restrictionULiftIso J K f O).hom)

omit [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}] in
/-- The defining property of the comparison: after the unit of `g_! ⊣ g^*` at the raised
universe, its restriction is the universe lift of the unit at the universe of the rings. -/
theorem lowerShriekULiftComparison_unit (M : SheafOfModules.{r} (inverseImageRing J K f O)) :
    (sourceULift J K f O).map ((adjunctionModules J K f O).unit.app M) =
      (Stacks.SheafOfModules.lowerShriekAdjunction.{max u₁ r} J K f O).unit.app _ ≫
        (Stacks.SheafOfModules.inverseImage.{max u₁ r} J K f O).map
          ((lowerShriekULiftComparison J K f O).app M) :=
  (Category.comp_id _).symm.trans (unit_mateEquiv_symm (adjunctionModules J K f O)
    (Stacks.SheafOfModules.lowerShriekAdjunction.{max u₁ r} J K f O)
    (TwoSquare.mk _ _ _ _ (restrictionULiftIso J K f O).hom) M)

/-- A section `a` of `L M` corepresents the sections over `V` if it is the transpose of a
corepresenting section `e` of `M` over `U`, for an adjunction `L ⊣ G`, where `ι` identifies the
sections of `G N` over `U` with those of `N` over `V`. -/
private theorem isCorepresentingSection_of_homEquiv.{w} {A B : Type*} [Category A] [Category B]
    {JA : GrothendieckTopology A} {JB : GrothendieckTopology B} {RA : Sheaf JA RingCat.{r}}
    {RB : Sheaf JB RingCat.{r}} {L : SheafOfModules.{w} RA ⥤ SheafOfModules.{w} RB}
    {G : SheafOfModules.{w} RB ⥤ SheafOfModules.{w} RA} (adj : L ⊣ G)
    {M : SheafOfModules.{w} RA} {U : A} {V : B} {e : M.val.obj (op U)}
    {a : (L.obj M).val.obj (op V)} (he : Stacks.SheafOfModules.IsCorepresentingSection U e)
    (ι : ∀ N, (G.obj N).val.obj (op U) → N.val.obj (op V)) (hι : ∀ N, Function.Bijective (ι N))
    (h : ∀ {N} (ψ : L.obj M ⟶ N),
      (ψ.val.app (op V)).hom a = ι N (((adj.homEquiv _ _ ψ).val.app (op U)).hom e)) :
    Stacks.SheafOfModules.IsCorepresentingSection V a := fun N => by
  convert (hι N).comp ((he _).comp (adj.homEquiv M N).bijective) using 1
  exact funext h

section ExtensionByZero

variable [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f O).over U) :
      (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]

/-- **The comparison is invertible at `j_{U!} O_U`.** Both `g_!(Λ j_{U!} O_U)` and
`Λ(g_! j_{U!} O_U)` corepresent the sections over `f(U)` at the raised universe, through the
image of the tautological section of `j_{U!} O_U` under the respective units, and the comparison
carries the first to the second. -/
theorem isIso_lowerShriekULiftComparison_app_extensionByZeroUnit (U : C) :
    IsIso ((lowerShriekULiftComparison J K f O).app
      (extensionByZeroUnit (inverseImageRing J K f O) U)) := by
  let adj₁ := adjunctionModules J K f O
  let adj₂ := Stacks.SheafOfModules.lowerShriekAdjunction.{max u₁ r} J K f O
  let j := extensionByZeroUnit (inverseImageRing J K f O) U
  let e := Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J
    (inverseImageRing J K f O) U j (𝟙 j)
  have hj : Stacks.SheafOfModules.IsCorepresentingSection U e :=
    Stacks.SheafOfModules.isCorepresentingSection_extensionByZeroUnit J
      (inverseImageRing J K f O) U
  have hΛj : Stacks.SheafOfModules.IsCorepresentingSection
      (T := (sourceULift J K f O).obj j) U (ULift.up e) :=
    Stacks.SheafOfModules.isCorepresentingSection_uliftForPresentation.{r, max u₁ r} J _ hj
  let a : ((Stacks.SheafOfModules.lowerShriek.{max u₁ r} J K f O).obj
      ((sourceULift J K f O).obj j)).val.obj (op (f.obj U)) :=
    ((adj₂.unit.app ((sourceULift J K f O).obj j)).val.app (op U)).hom (ULift.up e)
  have hA : Stacks.SheafOfModules.IsCorepresentingSection (f.obj U) a := by
    refine isCorepresentingSection_of_homEquiv adj₂ hΛj (fun _ => id)
      (fun _ => Function.bijective_id) fun _ => ?_
    rw [Adjunction.homEquiv_unit]
    rfl
  let t : ((lowerShriekModules J K f O).obj j).val.obj (op (f.obj U)) :=
    ((adj₁.unit.app j).val.app (op U)).hom e
  have hT : Stacks.SheafOfModules.IsCorepresentingSection (f.obj U) t := by
    refine isCorepresentingSection_of_homEquiv adj₁ hj (fun _ => id)
      (fun _ => Function.bijective_id) fun _ => ?_
    rw [Adjunction.homEquiv_unit]
    rfl
  have hB : Stacks.SheafOfModules.IsCorepresentingSection
      (T := (targetULift K O).obj ((lowerShriekModules J K f O).obj j)) (f.obj U)
        (ULift.up t) :=
    Stacks.SheafOfModules.isCorepresentingSection_uliftForPresentation.{r, max u₁ r} K O hT
  exact Stacks.SheafOfModules.isIso_of_isCorepresentingSection hA hB _
    (congrArg (fun φ => (φ.val.app (op U)).hom (ULift.up e))
      (lowerShriekULiftComparison_unit J K f O j)).symm

end ExtensionByZero


/-- A natural transformation between two functors preserving a coproduct is invertible at the
coproduct as soon as it is invertible at each summand. -/
theorem _root_.CategoryTheory.NatTrans.isIso_app_sigma {A B : Type*} [Category A] [Category B]
    {F₁ F₂ : A ⥤ B} (α : F₁ ⟶ F₂) {ι : Type*} (X : ι → A) [HasCoproduct X]
    [PreservesColimit (Discrete.functor X) F₁] [PreservesColimit (Discrete.functor X) F₂]
    (h : ∀ i, IsIso (α.app (X i))) : IsIso (α.app (∐ X)) := by
  let h₁ := isColimitOfPreserves F₁ (colimit.isColimit (Discrete.functor X))
  let h₂ := isColimitOfPreserves F₂ (colimit.isColimit (Discrete.functor X))
  let w : Discrete.functor X ⋙ F₁ ≅ Discrete.functor X ⋙ F₂ :=
    NatIso.ofComponents (fun i => asIso (α.app (X i.as)))
      (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl⟩⟩; simp)
  have he : (IsColimit.coconePointsIsoOfNatIso h₁ h₂ w).hom = α.app (∐ X) := by
    refine h₁.hom_ext (fun i => ?_)
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp [w]
  rw [← he]
  infer_instance

section Sums

variable [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f O).over U) :
      (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]

/-- **The comparison `g_!(Λ M) ⟶ Λ(g_! M)` is invertible at every direct sum `M` of the
`j_{U!} O_U`**: it is invertible at each `j_{U!} O_U`, and both sides commute with direct sums,
the universe lift of the sections preserving the colimits indexed in the universe of the rings
and the lower shrieks being left adjoints. -/
theorem isIso_lowerShriekULiftComparison_app {M : SheafOfModules.{r} (inverseImageRing J K f O)}
    (hM : IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) M) :
    IsIso ((lowerShriekULiftComparison J K f O).app M) := by
  obtain ⟨ι, U, ⟨φ⟩⟩ := hM
  let X := fun i : ι => extensionByZeroUnit (inverseImageRing J K f O) (U i)
  have : PreservesColimitsOfSize.{r, r} (sourceULift J K f O) :=
    SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' _
  have : PreservesColimitsOfSize.{r, r} (targetULift K O) :=
    SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' _
  have : PreservesColimitsOfSize.{r, r} (lowerShriekModules J K f O) :=
    (adjunctionModules J K f O).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{r, r}
      (Stacks.SheafOfModules.lowerShriek.{max u₁ r} J K f O) :=
    (Stacks.SheafOfModules.lowerShriekAdjunction.{max u₁ r} J K f O).leftAdjoint_preservesColimits
  exact (NatTrans.isIso_app_iff_of_iso (lowerShriekULiftComparison J K f O) φ).1
    (NatTrans.isIso_app_sigma (F₁ := sourceULift J K f O ⋙
        Stacks.SheafOfModules.lowerShriek.{max u₁ r} J K f O)
      (F₂ := lowerShriekModules J K f O ⋙ targetULift K O)
      (lowerShriekULiftComparison J K f O) X
      (fun i => isIso_lowerShriekULiftComparison_app_extensionByZeroUnit J K f O (U i)))

end Sums


section Lifted

variable (O' : Sheaf K CommRingCat.{r}) [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r u₁} RingCat.{max r u₁})]

omit [f.IsCocontinuous J K]
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{max u₁ r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r u₁} RingCat.{max r u₁})] in
/-- The transport of sheaves of modules to the raised structure sheaf preserves corepresenting
sections: it is an equivalence acting as the identity on sections. -/
theorem isCorepresentingSection_sourceModulesEquivalence
    {X : SheafOfModules.{max u₁ r}
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O'))}
    {V : C} {x : X.val.obj (op V)}
    (hx : Stacks.SheafOfModules.IsCorepresentingSection (T := X) V x) :
    Stacks.SheafOfModules.IsCorepresentingSection
      (T := (ULift.sourceModulesEquivalence.{u₁} J K f O').functor.obj X) V
      (show ((ULift.sourceModulesEquivalence.{u₁} J K f O').functor.obj X).val.obj (op V)
        from x) := by
  intro N
  let E := ULift.sourceModulesEquivalence.{u₁} J K f O'
  have h : (fun ψ : E.functor.obj X ⟶ N => (ψ.val.app (op V)).hom x) =
      (fun y => ((E.counitIso.hom.app N).val.app (op V)).hom y) ∘
        (fun φ : X ⟶ E.inverse.obj N => (φ.val.app (op V)).hom x) ∘
          (fun ψ => E.fullyFaithfulFunctor.preimage (ψ ≫ E.counitIso.inv.app N)) := by
    funext ψ
    have hψ : ψ = E.functor.map (E.fullyFaithfulFunctor.preimage (ψ ≫ E.counitIso.inv.app N)) ≫
        E.counitIso.hom.app N := by simp
    conv_lhs => rw [hψ]
    rfl
  rw [h]
  have : IsIso ((E.counitIso.hom.app N).val.app (op V)) :=
    Functor.map_isIso (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V))
      (E.counitIso.hom.app N)
  refine (ConcreteCategory.bijective_of_isIso ((E.counitIso.hom.app N).val.app (op V))).comp
    ((hx _).comp ?_)
  exact E.fullyFaithfulFunctor.homEquiv.symm.bijective.comp
    ⟨fun ψ₁ ψ₂ h => (cancel_mono _).1 h, fun ψ => ⟨ψ ≫ E.counitIso.hom.app N, by
      dsimp only
      rw [Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id ψ⟩⟩

variable [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')).over U) :
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')).over U ⟶
        (inverseImageRing J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf O')).over U)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{max r u₁} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (ULift.liftedStructureSheaf.{u₁} K O'))).over U) :
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (ULift.liftedStructureSheaf.{u₁} K O'))).over U ⟶
        (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (ULift.liftedStructureSheaf.{u₁} K O'))).over U)).IsRightAdjoint]

/-- **The universe lift of `j_{U!} O_U`, read over the raised structure sheaf, is `j_{U!} O_U`
at the raised universe**: both corepresent the sections over `U`. -/
def extensionByZeroUnitULiftIso (U : C) :
    extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (ULift.liftedStructureSheaf.{u₁} K O'))) U ≅
      (ULift.sourceModulesEquivalence.{u₁} J K f O').functor.obj
        ((sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
          (extensionByZeroUnit (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O'))
            U)) := by
  let R := inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')
  let R' := inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
    (ULift.liftedStructureSheaf.{u₁} K O'))
  let j := extensionByZeroUnit R U
  let e := Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U j (𝟙 j)
  have hΛ := isCorepresentingSection_sourceModulesEquivalence J K f O'
    (Stacks.SheafOfModules.isCorepresentingSection_uliftForPresentation.{r, max u₁ r} J R
      (Stacks.SheafOfModules.isCorepresentingSection_extensionByZeroUnit J R U))
  have hJ := Stacks.SheafOfModules.isCorepresentingSection_extensionByZeroUnit J R' U
  let N := (ULift.sourceModulesEquivalence.{u₁} J K f O').functor.obj
    ((sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj j)
  let y : N.val.obj (op U) := ULift.up e
  let φ := Classical.choose ((hJ N).2 y)
  have hφ := Classical.choose_spec ((hJ N).2 y)
  have : IsIso φ := Stacks.SheafOfModules.isIso_of_isCorepresentingSection hJ hΛ φ hφ
  exact asIso φ

omit [f.IsCocontinuous J K]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{max u₁ r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r u₁} RingCat.{max r u₁})] in
/-- **S1: the universe lift of a direct sum of the `j_{U!} O_U`, read over the raised structure
sheaf, is a direct sum of the `j_{U!} O_U` at the raised universe**, the hypothesis of
`Stacks.Cohomology.DerivedLowerShriek.ULift.derivedLowerShriekObjQIso`. -/
theorem isSumOfExtensionByZeroUnits_sourceModulesEquivalence_sourceULift
    {M : SheafOfModules.{r} (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O'))}
    (hM : IsSumOfExtensionByZeroUnits
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')) M) :
    IsSumOfExtensionByZeroUnits (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (ULift.liftedStructureSheaf.{u₁} K O')))
      ((ULift.sourceModulesEquivalence.{u₁} J K f O').functor.obj
        ((sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj M)) := by
  obtain ⟨ι, U, ⟨φ⟩⟩ := hM
  let F := sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O') ⋙
    (ULift.sourceModulesEquivalence.{u₁} J K f O').functor
  have : PreservesColimitsOfSize.{r, r}
      (sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')) :=
    SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' _
  have : PreservesColimitsOfSize.{r, r} F := inferInstance
  let X := fun i : ι => extensionByZeroUnit
    (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O')) (U i)
  exact ⟨ULift.{u₁} ι, fun i => U i.down, ⟨Sigma.whiskerEquiv (g := fun i => F.obj (X i))
    Equiv.ulift (fun i => (extensionByZeroUnitULiftIso J K f O' (U i.down)).symm) ≪≫
      (PreservesCoproduct.iso F X).symm ≪≫ F.mapIso φ⟩⟩

end Lifted

end Stacks.Cohomology.DerivedLowerShriek.ULiftComparison

end
