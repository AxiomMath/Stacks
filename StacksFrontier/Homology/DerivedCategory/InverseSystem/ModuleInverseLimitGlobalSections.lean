module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic

/-!
# Derived inverse limits of modules as cohomology on the chaotic site

An inverse system of rings is a sheaf of rings for the bottom (chaotic) topology on the ordered
category of natural numbers, and sheaves of modules over it are exactly the compatible inverse
systems of modules. Under this equivalence the right-derived functor of
`ModuleInverseLimit.inverseLimit` is the right-derived global-sections functor of the site, and
after forgetting scalars it is the right-derived global-sections functor of the underlying sheaf
of abelian groups.

## Main definitions

* `ModuleInverseLimitGlobalSections.inverseSystemRingSheaf`: an inverse system of rings, regarded
  as a sheaf of rings for the bottom topology.
* `ModuleInverseLimitGlobalSections.moduleSheafBotEquivalence`: the canonical equivalence between
  module sheaves over that sheaf of rings and compatible inverse systems of modules.

## Main results

* `ModuleInverseLimitGlobalSections.derivedInverseLimitIsoDerivedGlobalSections`: the derived
  inverse limit is the derived global sections of the module sheaf, and its image under the
  forgetful functor is the derived global sections of the underlying abelian sheaf, compatibly
  with the three derived-functor units.

## Implementation notes

For the bottom topology every presheaf is a sheaf, so the equivalence of module categories is
obtained by forgetting, or adding, the automatically satisfied sheaf condition. Global sections
of a module sheaf are the inverse limit of the underlying compatible module system. The two
comparison isomorphisms are pinned down by commutation with the units of the three right-derived
functors; the second one is produced by resolving simultaneously by complexes whose terms have
vanishing first derived limit, which exist by Tag 091D.

## References

* [Stacks Project, Tag 091E](https://stacks.math.columbia.edu/tag/091E)
-/
section


@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace ModuleInverseLimitGlobalSections

universe u v

/-- An inverse system of rings, regarded as a sheaf of rings for the bottom topology. -/
public def inverseSystemRingSheaf (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology ℕ) RingCat.{u} :=
  ⟨A, Presheaf.isSheaf_bot A⟩

/-- The underlying presheaf of rings of `inverseSystemRingSheaf A` is `A`. -/
@[simp]
public lemma inverseSystemRingSheaf_obj (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (inverseSystemRingSheaf A).obj = A := rfl

/-- For the bottom topology, sheaves of modules over an inverse system of rings are canonically
equivalent to compatible inverse systems of modules. -/
public def moduleSheafBotEquivalence (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    SheafOfModules.{v} (inverseSystemRingSheaf A) ≌ PresheafOfModules.{v} A where
  functor := SheafOfModules.forget (inverseSystemRingSheaf A)
  inverse :=
    { obj := fun M ↦ ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
      map := fun f ↦ ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := rfl

/-- The functor of `moduleSheafBotEquivalence A` sends a module sheaf to its underlying presheaf
of modules. -/
@[simp]
public lemma moduleSheafBotEquivalence_functor_obj (A : ℕᵒᵖ ⥤ RingCat.{u})
    (M : SheafOfModules.{v} (inverseSystemRingSheaf A)) :
    (moduleSheafBotEquivalence A).functor.obj M = M.val := rfl

/-- The inverse of `moduleSheafBotEquivalence A` sends a presheaf of modules to a module sheaf
whose underlying presheaf of modules is the given one. -/
@[simp]
public lemma moduleSheafBotEquivalence_inverse_obj_val (A : ℕᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{v} A) :
    ((moduleSheafBotEquivalence A).inverse.obj M).val = M := rfl

/-- Module sheaves over `inverseSystemRingSheaf A` form an abelian category, transported along
`moduleSheafBotEquivalence A`. -/
noncomputable local instance (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    Abelian (SheafOfModules.{v} (inverseSystemRingSheaf A)) :=
  abelianOfEquivalence (moduleSheafBotEquivalence A).functor

/-- Sheaves of abelian groups for the bottom topology on `ℕ` form an abelian category,
transported along `sheafBotEquivalence`. -/
noncomputable local instance :
    Abelian (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) :=
  abelianOfEquivalence (sheafBotEquivalence Ab.{v}).functor

end ModuleInverseLimitGlobalSections
end

end

section


@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace ModuleInverseLimitGlobalSections

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- Module sheaves over `inverseSystemRingSheaf A` form an abelian category, transported along
`moduleSheafBotEquivalence A`. -/
noncomputable local instance (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    Abelian (SheafOfModules.{v} (inverseSystemRingSheaf A)) :=
  abelianOfEquivalence (moduleSheafBotEquivalence A).functor

/-- Sheaves of abelian groups for the bottom topology on `ℕ` form an abelian category,
transported along `sheafBotEquivalence`. -/
noncomputable local instance :
    Abelian (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) :=
  abelianOfEquivalence (sheafBotEquivalence Ab.{v}).functor

private lemma moduleSheafBotEquivalence_additive (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (moduleSheafBotEquivalence.{u, v} A).functor.Additive := by
  apply Functor.additive_of_preserves_binary_products

/-- The functor of `moduleSheafBotEquivalence A` is additive. -/
local instance (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (moduleSheafBotEquivalence.{u, v} A).functor.Additive :=
  moduleSheafBotEquivalence_additive A

private lemma globalSectionsAb_additive :
    (sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⋙ lim).Additive := by
  apply Functor.additive_of_preserves_binary_products

/-- The global-sections functor on sheaves of abelian groups for the bottom topology on `ℕ` is
additive. -/
local instance :
    (sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⋙ lim).Additive :=
  globalSectionsAb_additive

private lemma moduleForget_preservesFiniteColimits (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    PreservesFiniteColimits
      (forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

private lemma moduleForget_preservesHomology (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}).PreservesHomology := by
  let := moduleForget_preservesFiniteColimits.{u, v} A
  exact Functor.preservesHomologyOfExact _

private def globalSectionsForgetIso (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    ((moduleSheafBotEquivalence.{u, v} A).functor ⋙ ModuleInverseLimit.inverseLimit A) ⋙
      forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v} ≅
    SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A) ⋙
      (sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⋙ lim) :=
  Functor.isoWhiskerLeft
    ((moduleSheafBotEquivalence.{u, v} A).functor ⋙ ModuleInverseLimit.moduleDiagramFunctor A)
    (preservesLimitNatIso (J := ℕᵒᵖ) (forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}))

private lemma toSheaf_preservesFiniteColimits_bot
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    PreservesFiniteColimits
      (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A)) := by
  have hcomp : PreservesFiniteColimits
      (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A) ⋙
        sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) := by
    rw [show (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A) ⋙
      sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) =
      (moduleSheafBotEquivalence.{u, v} A).functor ⋙
        PresheafOfModules.toPresheaf.{v} A from rfl]
    exact comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_reflects_of_preserves
    (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A))
    (sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v})

private lemma toSheaf_additive_bot (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A)).Additive := by
  apply Functor.additive_of_preserves_binary_products

private lemma toSheaf_preservesHomology_bot (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A)).PreservesHomology := by
  let := toSheaf_preservesFiniteColimits_bot.{u, v} A
  exact Functor.preservesHomologyOfExact _

private lemma moduleGlobalSections_additive (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    ((moduleSheafBotEquivalence.{u, v} A).functor ⋙
      ModuleInverseLimit.inverseLimit A).Additive := by
  let := moduleSheafBotEquivalence_additive.{u, v} A
  let := ModuleInverseLimit.inverseLimit_additive.{u, v} A
  infer_instance

private lemma mapHomotopyCategory_isEquivalence {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {ι : Type*} (e : C ≌ D) [e.functor.Additive] (c : ComplexShape ι) :
    (e.functor.mapHomotopyCategory c).IsEquivalence := by
  let : (e.functor.mapHomologicalComplex c).IsEquivalence :=
    (e.mapHomologicalComplex c).isEquivalence_functor
  have : (e.functor.mapHomotopyCategory c).EssSurj := by
    have := Functor.essSurj_of_iso
      (e.functor.mapHomotopyCategoryFactors c).symm
    refine ⟨fun Y => ?_⟩
    obtain ⟨X, hX⟩ := Functor.EssSurj.mem_essImage
      (HomotopyCategory.quotient C c ⋙
        e.functor.mapHomotopyCategory c) Y
    exact ⟨_, hX⟩
  exact {}

section

universe w₁ w₂ w₃
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasDerivedCategory.{w₃} E]

private def equivalenceDerivedUnit (e : C ≌ D) [e.functor.Additive]
    (F : D ⥤ E) [F.Additive]
    (RF : DerivedCategory D ⥤ DerivedCategory E)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF) :
    (e.functor ⋙ F).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶
      Qh ⋙ e.functor.mapDerivedCategory ⋙ RF :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (e.functor ⋙ F))
        (ComplexShape.up ℤ)).inv Qh ≫
    Functor.whiskerLeft (e.functor.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
    Functor.whiskerRight e.functor.mapDerivedCategoryFactorsh.inv RF

private lemma equivalenceDerivedUnit_isRightDerivedFunctor (e : C ≌ D) [e.functor.Additive]
    (F : D ⥤ E) [F.Additive]
    (RF : DerivedCategory D ⥤ DerivedCategory E)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))] :
    (e.functor.mapDerivedCategory ⋙ RF).IsRightDerivedFunctor
      (equivalenceDerivedUnit e F RF α) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  have := mapHomotopyCategory_isEquivalence e (ComplexShape.up ℤ)
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
  apply (Functor.isLeftKanExtension_iff_precomp_equivalence
    (equivalenceDerivedUnit e F RF α) α e.functor.mapDerivedCategoryFactorsh.symm
    ((Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (e.functor ⋙ F))
        (ComplexShape.up ℤ)).symm Qh)) (Iso.refl _) ?_).mp
  · exact Functor.IsRightDerivedFunctor.isLeftKanExtension RF α
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
  · ext K
    simp [equivalenceDerivedUnit]

/-- The unit `equivalenceDerivedUnit e F RF α` is invertible at `K` when `α` is invertible at the
image of `K`. -/
private lemma isIso_equivalenceDerivedUnit_app (e : C ≌ D) [e.functor.Additive]
    (F : D ⥤ E) [F.Additive] (RF : DerivedCategory D ⥤ DerivedCategory E)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF)
    (K : HomotopyCategory C (ComplexShape.up ℤ))
    [IsIso (α.app ((e.functor.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))] :
    IsIso ((equivalenceDerivedUnit e F RF α).app K) := by
  dsimp [equivalenceDerivedUnit]
  infer_instance

end

private lemma globalSectionsAb_hasRightDerivedFunctor :
    ∃ (RF : DerivedCategory (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) ⥤
        DerivedCategory Ab.{v})
      (α : (sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⋙ lim).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF),
      RF.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v})
          (ComplexShape.up ℤ)) := by
  obtain ⟨RF, α, hRF, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{v}
  have := hRF
  let e := sheafBotEquivalence (C := ℕ) Ab.{v}
  let : (lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  exact ⟨e.functor.mapDerivedCategory ⋙ RF, equivalenceDerivedUnit e lim RF α,
    equivalenceDerivedUnit_isRightDerivedFunctor e lim RF α⟩


private lemma moduleGlobalSections_hasRightDerivedFunctor (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    let e := moduleSheafBotEquivalence.{u, v} A
    let F := ModuleInverseLimit.inverseLimit.{u, v} A
    ∃ (hF : F.Additive),
      let := hF
      ∃ (RF : DerivedCategory (PresheafOfModules.{v} A) ⥤
          DerivedCategory (ModuleCat.{v} (limit A : RingCat.{u})))
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF)
        (RΓ : DerivedCategory (SheafOfModules.{v} (inverseSystemRingSheaf A)) ⥤
          DerivedCategory (ModuleCat.{v} (limit A : RingCat.{u})))
        (β : (e.functor ⋙ F).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RΓ),
        RF.IsRightDerivedFunctor α
            (HomotopyCategory.quasiIso (PresheafOfModules.{v} A) (ComplexShape.up ℤ)) ∧
        RΓ.IsRightDerivedFunctor β
            (HomotopyCategory.quasiIso (SheafOfModules.{v} (inverseSystemRingSheaf A))
              (ComplexShape.up ℤ)) ∧
        ∃ η : e.functor.mapDerivedCategory ⋙ RF ≅ RΓ,
          ∀ K, β.app K ≫ η.inv.app (Qh.obj K) =
            Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (e.functor ⋙ F))
              (ComplexShape.up ℤ)).inv.app K) ≫
            α.app ((e.functor.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            RF.map (e.functor.mapDerivedCategoryFactorsh.inv.app K) := by
  dsimp only
  obtain ⟨hF, RF, α, hRF, _⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations.{u, v} A
  let := hF
  let := hRF
  let e := moduleSheafBotEquivalence.{u, v} A
  refine ⟨hF, RF, α, e.functor.mapDerivedCategory ⋙ RF,
    equivalenceDerivedUnit e _ RF α, hRF,
    equivalenceDerivedUnit_isRightDerivedFunctor e _ RF α, Iso.refl _, ?_⟩
  intro K
  simp [equivalenceDerivedUnit, e]

section Comparison

open CategoryTheory.Category

variable {C H : Type*} [Category* C] [Category* H]
  {F P Q : C ⥤ H}

private lemma comparison_naturality (α : F ⟶ P) (β : F ⟶ Q)
    {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)] [IsIso (α.app Y)] :
    P.map f ≫ inv (α.app Y) ≫ β.app Y =
      inv (α.app X) ≫ β.app X ≫ Q.map f := by
  rw [← cancel_epi (α.app X)]
  simp only [← α.naturality_assoc, IsIso.hom_inv_id_assoc, β.naturality]

private lemma exists_iso_of_common_resolutions
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (hP : W.IsInvertedBy P) (hQ : W.IsInvertedBy Q)
    (α : F ⟶ P) (β : F ⟶ Q)
    (hres : ∀ X, ∃ (Y : C) (s : X ⟶ Y), W s ∧ IsIso (α.app Y) ∧ IsIso (β.app Y)) :
    ∃ e : P ≅ Q, α ≫ e.hom = β := by
  choose Y s hs hα hβ using hres
  let e (X : C) : P.obj X ≅ Q.obj X :=
    let := hP _ (hs X)
    let := hQ _ (hs X)
    let := hα X
    let := hβ X
    asIso (P.map (s X)) ≪≫ (asIso (α.app (Y X))).symm ≪≫
      asIso (β.app (Y X)) ≪≫ (asIso (Q.map (s X))).symm
  have he (X : C) : (e X).hom ≫ Q.map (s X) =
      P.map (s X) ≫ inv (α.app (Y X)) ≫ β.app (Y X) := by
    let := hP _ (hs X)
    let := hQ _ (hs X)
    let := hα X
    let := hβ X
    simp [e]
  have hgood {X Z : C} (t : X ⟶ Z) [IsIso (α.app Z)] :
      (e X).hom ≫ Q.map t = P.map t ≫ inv (α.app Z) ≫ β.app Z := by
    obtain ⟨φ, hφ⟩ := (MorphismProperty.RightFraction.mk (s X) (hs X) t).exists_leftFraction
    let w := φ.s ≫ s φ.Y'
    have hw : W w := W.comp_mem _ _ φ.hs (hs _)
    let := hQ _ hw
    let := hα X
    let := hα φ.Y'
    have hwfac : t ≫ w = s X ≫ (φ.f ≫ s φ.Y') := by
      simpa only [w, assoc] using congrArg (fun f ↦ f ≫ s φ.Y') hφ
    rw [← cancel_mono (Q.map w), assoc]
    calc
      (e X).hom ≫ Q.map t ≫ Q.map w =
          (e X).hom ≫ Q.map (s X) ≫ Q.map (φ.f ≫ s φ.Y') := by
        rw [← Q.map_comp, hwfac, Q.map_comp]
      _ = P.map (s X) ≫ inv (α.app (Y X)) ≫
          β.app (Y X) ≫ Q.map (φ.f ≫ s φ.Y') := by
        rw [← assoc, he]
        simp [assoc]
      _ = P.map (s X) ≫ P.map (φ.f ≫ s φ.Y') ≫
          inv (α.app (Y φ.Y')) ≫ β.app (Y φ.Y') := by
        rw [comparison_naturality α β]
      _ = P.map t ≫ P.map w ≫ inv (α.app (Y φ.Y')) ≫ β.app (Y φ.Y') := by
        rw [← P.map_comp_assoc, ← hwfac, P.map_comp, assoc]
      _ = (P.map t ≫ inv (α.app Z) ≫ β.app Z) ≫ Q.map w := by
        rw [comparison_naturality α β]
        simp only [assoc]
  let ε : P ≅ Q := NatIso.ofComponents e (fun {X Z} f ↦ by
    let := hQ _ (hs Z)
    let := hα Z
    rw [← cancel_mono (Q.map (s Z)), assoc, he]
    simpa only [P.map_comp, Q.map_comp, assoc] using (hgood (f ≫ s Z)).symm)
  refine ⟨ε, ?_⟩
  ext X
  let := hQ _ (hs X)
  let := hα X
  show α.app X ≫ (e X).hom = β.app X
  rw [← cancel_mono (Q.map (s X)), assoc, he, ← assoc, ← α.naturality]
  simp only [assoc, IsIso.hom_inv_id_assoc, β.naturality]

private lemma exists_iso_of_common_localized_resolutions
    {D : Type*} [Category* D] (W : MorphismProperty C)
    [W.HasLeftCalculusOfFractions] (L : C ⥤ D) [L.IsLocalization W]
    (RF RG : D ⥤ H) (α : F ⟶ L ⋙ RF) (β : F ⟶ L ⋙ RG)
    (hres : ∀ X, ∃ (Y : C) (s : X ⟶ Y), W s ∧ IsIso (α.app Y) ∧ IsIso (β.app Y)) :
    ∃ e : RF ≅ RG, α ≫ Functor.whiskerLeft L e.hom = β := by
  obtain ⟨ε, hε⟩ := exists_iso_of_common_resolutions W
    (MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) RF)
    (MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) RG) α β hres
  let hL := Localization.fullyFaithfulWhiskeringLeft L W H
  refine ⟨hL.preimageIso ε, ?_⟩
  show α ≫ ((Functor.whiskeringLeft C D H).obj L).map (hL.preimage ε.hom) = β
  rw [hL.map_preimage, hε]

end Comparison

set_option backward.isDefEq.respectTransparency false in
private lemma epi_underlying_delta
    (B : Type u) [Ring B] (M : ℕᵒᵖ ⥤ ModuleCat.{v} B)
    (hδ : Epi (𝟙 (∏ᶜ fun n : ℕ ↦ M.obj (Opposite.op n)) -
      Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ M.obj (Opposite.op n)) (n + 1) ≫
        M.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (Rlim.delta (M ⋙ forget₂ (ModuleCat.{v} B) Ab.{v})) := by
  let G := forget₂ (ModuleCat.{v} B) Ab.{v}
  let P := fun n : ℕ ↦ M.obj (Opposite.op n)
  let δ : ∏ᶜ P ⟶ ∏ᶜ P := 𝟙 _ - Pi.lift fun n : ℕ ↦
    Pi.π P (n + 1) ≫ M.map (homOfLE (Nat.le_succ n)).op
  let d : (∏ᶜ fun n ↦ G.obj (P n)) ⟶ ∏ᶜ fun n ↦ G.obj (P n) :=
    𝟙 _ - Pi.lift fun n : ℕ ↦ Pi.π (fun n ↦ G.obj (P n)) (n + 1) ≫
      G.map (M.map (homOfLE (Nat.le_succ n)).op)
  show Epi d
  let c := piComparison G P
  have hmap : Epi (G.map δ) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (ModuleCat.epi_iff_surjective δ).mp hδ
  have hcomp : G.map δ ≫ c = c ≫ d := by
    dsimp only [δ, d, c]
    rw [G.map_sub, G.map_id, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id]
    congr 1
    rw [map_lift_piComparison]
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [Category.assoc, Pi.lift_comp_π, G.map_comp, piComparison_comp_π_assoc]
  have he : Epi (c ≫ d) := by
    rw [← hcomp]
    infer_instance
  exact epi_of_epi c _

private lemma underlying_firstDerivedLimit_isZero
    (A : ℕᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{v} A)
    (hδ : Epi (𝟙 (∏ᶜ fun n : ℕ ↦ (ModuleInverseLimit.moduleDiagram A M).obj (Opposite.op n)) -
      Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (ModuleInverseLimit.moduleDiagram A M).obj (Opposite.op n)) (n + 1) ≫
          (ModuleInverseLimit.moduleDiagram A M).map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (Rlim.firstDerivedLimit M.presheaf) := by
  have : Epi (Rlim.delta M.presheaf) :=
    epi_underlying_delta (limit A : RingCat.{u}) (ModuleInverseLimit.moduleDiagram A M) hδ
  exact isZero_cokernel_of_epi _

section AcyclicComputation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Preadditive E]
  [HasDerivedCategory C] [HasDerivedCategory D]

omit [HasDerivedCategory C] in
private lemma isZero_map_mappingCone_X (H : C ⥤ E) [H.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : ∀ i, IsZero (H.obj (K.X i))) (hL : ∀ i, IsZero (H.obj (L.X i))) (i : ℤ) :
    IsZero (H.obj ((CochainComplex.mappingCone f).X i)) := by
  rw [IsZero.iff_id_eq_zero, ← H.map_id,
    ← CochainComplex.mappingCone.id_X f i (i + 1) rfl, H.map_add, H.map_comp, H.map_comp,
    (hK (i + 1)).eq_of_tgt (H.map _) 0, (hL i).eq_of_tgt (H.map _) 0]
  simp

private lemma map_quasiIso_of_computations (F : C ⥤ D) [F.Additive]
    (H : C ⥤ E) [H.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory D) [RF.PreservesZeroMorphisms]
    (hcomp : ∀ K : CochainComplex C ℤ, (∀ i, IsZero (H.obj (K.X i))) →
      Nonempty (RF.obj (Q.obj K) ≅ Q.obj ((F.mapHomologicalComplex _).obj K)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ i, IsZero (H.obj (K.X i))) (hL : ∀ i, IsZero (H.obj (L.X i))) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hz : IsZero (Q.obj (CochainComplex.mappingCone f)) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      (DerivedCategory.mappingCone_triangle_distinguished f) (by
        show IsIso (Q.map f)
        infer_instance)
  obtain ⟨e⟩ := hcomp (CochainComplex.mappingCone f) (isZero_map_mappingCone_X H f hK hL)
  have hz' := ((RF.map_isZero hz).of_iso e.symm).of_iso
    (Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)).symm
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mp
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished _)).mp hz'

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_unit_of_resolutions (F : C ⥤ D) [F.Additive]
    (P : ObjectProperty C)
    (hres : ∀ K : CochainComplex C ℤ, ∃ (L : CochainComplex C ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ i, P (L.X i))
    (hmap : ∀ {K L : CochainComplex C ℤ} (f : K ⟶ L), QuasiIso f →
      (∀ i, P (K.X i)) → (∀ i, P (L.X i)) →
        QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶ Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (K : CochainComplex C ℤ) (hK : ∀ i, P (K.X i)) :
    IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := by
  let P' : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) := fun K ↦ ∀ i, P (K.as.X i)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let Φ := LocalizerMorphism.ofEq (F := P'.ι) (W₁ := W.inverseImage P'.ι) rfl
  have : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  have : Φ.IsRightDerivabilityStructure :=
    CategoryTheory.Functor.rightDerivability_of_resolutions W P' (by
    intro X
    obtain ⟨L, f, hf, hL⟩ := hres X.as
    exact ⟨(HomotopyCategory.quotient C _).obj L, hL,
      (HomotopyCategory.quotient C _).map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hf⟩)
  have hd : Φ.Derives (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh) := by
    intro X Y f hf
    have hq : QuasiIso f.hom.out := by
      apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
      rwa [HomotopyCategory.quotient_map_out]
    have := hmap f.hom.out hq X.property Y.property
    show IsIso (Qh.map ((F.mapHomotopyCategory _).map f.hom))
    rw [← HomotopyCategory.quotient_map_out f.hom, Functor.mapHomotopyCategory_map]
    exact Localization.inverts Qh (HomotopyCategory.quasiIso D _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr this)
  exact hd.isIso_of_isRightDerivedFunctor α ⟨(HomotopyCategory.quotient C _).obj K, hK⟩

end AcyclicComputation


/-- The inverse-limit functor on inverse systems of abelian groups is additive. -/
local instance : (lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).Additive :=
  Functor.additive_of_preserves_binary_products _

private lemma inverseLimitAb_acyclic_data :
    ∃ (RF : DerivedCategory (ℕᵒᵖ ⥤ Ab.{v}) ⥤ DerivedCategory Ab.{v})
      (α : (lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶
        Qh ⋙ RF),
      RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ Ab.{v}) _) ∧
      (∀ K : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ,
        ∃ (L : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ) (f : K ⟶ L),
          QuasiIso f ∧ ∀ i, IsZero (Rlim.firstDerivedLimit (L.X i))) ∧
      (∀ {K L : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ} (f : K ⟶ L), QuasiIso f →
        (∀ i, IsZero (Rlim.firstDerivedLimit (K.X i))) →
        (∀ i, IsZero (Rlim.firstDerivedLimit (L.X i))) →
          QuasiIso (((lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).mapHomologicalComplex _).map f)) ∧
      ∀ K : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ,
        (∀ i, IsZero (Rlim.firstDerivedLimit (K.X i))) →
          IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
  obtain ⟨RF, α, hRF, _, _, _, hres, hcomp, _, hcok, _, _, hshift⟩ :=
    Rlim.lim_hasRightDerivedFunctor_and_computations.{v}
  obtain ⟨hshift, hcomm, htri, _⟩ := hshift
  let := hshift
  let := htri
  let := hRF
  let H := DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ Ab.{v}) 0 ⋙ RF ⋙
    DerivedCategory.homologyFunctor Ab.{v} 1
  have hzero (M : ℕᵒᵖ ⥤ Ab.{v}) :
      IsZero (H.obj M) ↔ IsZero (Rlim.firstDerivedLimit M) := by
    obtain ⟨e⟩ := hcok M
    exact e.isZero_iff
  have hr : ∀ K : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ,
      ∃ (L : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ) (f : K ⟶ L),
        QuasiIso f ∧ ∀ i, IsZero (Rlim.firstDerivedLimit (L.X i)) := by
    intro K
    obtain ⟨L, f, hf, hL⟩ := hres K
    exact ⟨L, f, hf, fun i ↦ (hzero _).mp (hL i)⟩
  have hm : ∀ {K L : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ} (f : K ⟶ L), QuasiIso f →
      (∀ i, IsZero (Rlim.firstDerivedLimit (K.X i))) →
      (∀ i, IsZero (Rlim.firstDerivedLimit (L.X i))) →
        QuasiIso (((lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).mapHomologicalComplex _).map f) := by
    intro K L f hf hK hL
    let := hf
    exact map_quasiIso_of_computations lim H RF hcomp f
      (fun i ↦ (hzero _).mpr (hK i)) (fun i ↦ (hzero _).mpr (hL i))
  exact ⟨RF, α, hRF, hr, hm, isIso_unit_of_resolutions lim
    (fun M ↦ IsZero (Rlim.firstDerivedLimit M)) hr hm RF α⟩


private def inverseLimitForgetIso (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    ModuleInverseLimit.inverseLimit.{u, v} A ⋙ forget₂ (ModuleCat.{v} (limit A : RingCat.{u}))
      Ab.{v} ≅
      PresheafOfModules.toPresheaf.{v} A ⋙ lim :=
  Functor.isoWhiskerLeft (ModuleInverseLimit.moduleDiagramFunctor A)
    (preservesLimitNatIso (J := ℕᵒᵖ) (forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}))

set_option backward.isDefEq.respectTransparency false in
private lemma inverseLimit_map_quasiIso (A : ℕᵒᵖ ⥤ RingCat.{u})
    (hmap : ∀ {K L : CochainComplex (ℕᵒᵖ ⥤ Ab.{v}) ℤ} (f : K ⟶ L), QuasiIso f →
      (∀ i, IsZero (Rlim.firstDerivedLimit (K.X i))) →
      (∀ i, IsZero (Rlim.firstDerivedLimit (L.X i))) →
        QuasiIso (((lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v}).mapHomologicalComplex _).map f))
    [hF : (ModuleInverseLimit.inverseLimit.{u, v} A).Additive]
    {K L : CochainComplex (PresheafOfModules.{v} A) ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ i, IsZero (Rlim.firstDerivedLimit (K.X i).presheaf))
    (hL : ∀ i, IsZero (Rlim.firstDerivedLimit (L.X i).presheaf)) :
    QuasiIso (((ModuleInverseLimit.inverseLimit A).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      := by
  let G := forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}
  let U := PresheafOfModules.toPresheaf.{v} A
  have : G.PreservesHomology := moduleForget_preservesHomology A
  have : U.PreservesHomology := Functor.preservesHomologyOfExact U
  have hm := hmap ((U.mapHomologicalComplex _).map f) inferInstance hK hL
  let e := NatIso.mapHomologicalComplex (inverseLimitForgetIso.{u, v} A) (ComplexShape.up ℤ)
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ G).mp
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)).mpr hm

private lemma inverseLimit_acyclic_resolutions (A : ℕᵒᵖ ⥤ RingCat.{u})
    (K : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    ∃ (L : CochainComplex (PresheafOfModules.{v} A) ℤ) (f : K ⟶ L),
      QuasiIso f ∧ ∀ i, IsZero (Rlim.firstDerivedLimit (L.X i).presheaf) := by
  obtain ⟨hF, RF, α, _, _, _, _, hseq, _, hres, _⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations.{u, v} A
  obtain ⟨L, f, hf, hL⟩ := hres K
  refine ⟨L, f, hf, fun i ↦ ?_⟩
  obtain ⟨w, hw⟩ := hseq (L.X i) (hL i)
  exact underlying_firstDerivedLimit_isZero A (L.X i) hw.epi_g

section HomotopyComparison

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  {ι : Type*} (c : ComplexShape ι)

private lemma mapHomotopyCategory_iso_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (K : HomotopyCategory C c) :
    IsIso ((NatTrans.mapHomotopyCategory e.hom c).app K) := by
  show IsIso ((HomotopyCategory.quotient D c).map
    ((NatIso.mapHomologicalComplex e c).hom.app K.as))
  infer_instance

private lemma mapHomotopyCategoryCompIso_refl_hom_app
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C c) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app K = 𝟙 _ := by
  show (HomotopyCategory.quotient E c).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma mapHomotopyCategoryCompIso_refl_inv_app
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C c) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app K = 𝟙 _ := by
  show (HomotopyCategory.quotient E c).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

end HomotopyComparison

-- Elaborating the dependent comparison data and both unit identities needs a larger budget.
set_option backward.isDefEq.respectTransparency false in
/-- On the site `ℕ` with its bottom topology, module sheaves over an inverse system of rings are
compatible inverse systems of modules. Under this equivalence, the right derived inverse-limit
functor is canonically the right-derived global-sections functor. After forgetting the module
structure, it is canonically the right-derived global-sections functor of the underlying sheaf of
abelian groups. The two comparison isomorphisms commute with the respective derived-functor
structure transformations. -/
@[stacks 091E]
public theorem derivedInverseLimitIsoDerivedGlobalSections (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    let R := inverseSystemRingSheaf A
    let e : SheafOfModules.{v} R ≌ PresheafOfModules.{v} A := moduleSheafBotEquivalence A
    let B : RingCat.{u} := limit A
    let limMod : PresheafOfModules.{v} A ⥤ ModuleCat.{v} B := ModuleInverseLimit.inverseLimit A
    let Γ : SheafOfModules.{v} R ⥤ ModuleCat.{v} B := e.functor ⋙ limMod
    let ΓAb : Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⥤ Ab.{v} :=
      sheafToPresheaf (⊥ : GrothendieckTopology ℕ) Ab.{v} ⋙ lim
    ∃ (hE : e.functor.Additive),
      letI := hE
      ∃ (hLim : limMod.Additive),
      letI := hLim
      ∃ (Rlim : DerivedCategory (PresheafOfModules.{v} A) ⥤
            DerivedCategory (ModuleCat.{v} B))
          (α : limMod.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ Rlim)
          (hΓ : Γ.Additive),
        letI := hΓ
        ∃ (hΓAb : ΓAb.Additive),
        letI := hΓAb
        ∃ (hToSheafAdd : (SheafOfModules.toSheaf.{v} R).Additive),
        letI := hToSheafAdd
        ∃ (hForgetFiniteColimits :
            PreservesFiniteColimits (forget₂ (ModuleCat.{v} B) Ab.{v})),
        letI := hForgetFiniteColimits
        ∃ (RΓ : DerivedCategory (SheafOfModules.{v} R) ⥤
              DerivedCategory (ModuleCat.{v} B))
            (β : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
              DerivedCategory.Qh ⋙ RΓ)
          (RΓAb : DerivedCategory (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) ⥤
              DerivedCategory Ab.{v})
            (γ : ΓAb.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
              DerivedCategory.Qh ⋙ RΓAb)
            (hToSheaf : PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R)),
          letI := hToSheaf
          Rlim.IsRightDerivedFunctor α
              (HomotopyCategory.quasiIso (PresheafOfModules.{v} A) (ComplexShape.up ℤ)) ∧
          RΓ.IsRightDerivedFunctor β
              (HomotopyCategory.quasiIso (SheafOfModules.{v} R) (ComplexShape.up ℤ)) ∧
          RΓAb.IsRightDerivedFunctor γ
              (HomotopyCategory.quasiIso
                (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) (ComplexShape.up ℤ)) ∧
          ∃ (η : e.functor.mapDerivedCategory ⋙ Rlim ≅ RΓ)
              (θ : Γ ⋙ forget₂ (ModuleCat.{v} B) Ab.{v} ≅
                SheafOfModules.toSheaf.{v} R ⋙ ΓAb)
              (ζ : RΓ ⋙ (forget₂ (ModuleCat.{v} B) Ab.{v}).mapDerivedCategory ≅
                (SheafOfModules.toSheaf.{v} R).mapDerivedCategory ⋙ RΓAb),
            (∀ K,
              β.app K ≫ η.inv.app (DerivedCategory.Qh.obj K) =
                DerivedCategory.Qh.map
                    ((Functor.mapHomotopyCategoryCompIso (Iso.refl Γ)
                      (ComplexShape.up ℤ)).inv.app K) ≫
                  α.app ((e.functor.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
                  Rlim.map (e.functor.mapDerivedCategoryFactorsh.inv.app K)) ∧
            ∀ K,
              (forget₂ (ModuleCat.{v} B) Ab.{v}).mapDerivedCategoryFactorsh.inv.app
                    ((Γ.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
                  (forget₂ (ModuleCat.{v} B) Ab.{v}).mapDerivedCategory.map (β.app K) ≫
                  ζ.hom.app (DerivedCategory.Qh.obj K) =
                DerivedCategory.Qh.map
                    ((NatTrans.mapHomotopyCategory θ.hom (ComplexShape.up ℤ)).app K) ≫
                  γ.app (((SheafOfModules.toSheaf.{v} R).mapHomotopyCategory
                    (ComplexShape.up ℤ)).obj K) ≫
                  RΓAb.map
                    ((SheafOfModules.toSheaf.{v} R).mapDerivedCategoryFactorsh.inv.app K) := by
  classical
  dsimp only
  let e := moduleSheafBotEquivalence.{u, v} A
  let s := sheafBotEquivalence (C := ℕ) Ab.{v}
  let := moduleSheafBotEquivalence_additive.{u, v} A
  obtain ⟨hF, RF, α, hRF, _⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations.{u, v} A
  let := hF
  let := hRF
  let F := ModuleInverseLimit.inverseLimit.{u, v} A
  let Γ := e.functor ⋙ F
  let ΓAb := s.functor ⋙ (lim : (ℕᵒᵖ ⥤ Ab.{v}) ⥤ Ab.{v})
  let := moduleGlobalSections_additive.{u, v} A
  let := globalSectionsAb_additive.{v}
  let S := SheafOfModules.toSheaf.{v} (inverseSystemRingSheaf A)
  let G := forget₂ (ModuleCat.{v} (limit A : RingCat.{u})) Ab.{v}
  let := toSheaf_additive_bot.{u, v} A
  let := toSheaf_preservesFiniteColimits_bot.{u, v} A
  let := moduleForget_preservesFiniteColimits.{u, v} A
  let := moduleForget_preservesHomology.{u, v} A
  let := toSheaf_preservesHomology_bot.{u, v} A
  obtain ⟨RFAb, αAb, hRFAb, _, hmapAb, hunitAb⟩ := inverseLimitAb_acyclic_data.{v}
  let := hRFAb
  let : s.functor.Additive := Functor.additive_of_preserves_binary_products _
  let RΓ := e.functor.mapDerivedCategory ⋙ RF
  let β := equivalenceDerivedUnit e F RF α
  let RΓAb := s.functor.mapDerivedCategory ⋙ RFAb
  let γ := equivalenceDerivedUnit s lim RFAb αAb
  have hRΓ : RΓ.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{v} (inverseSystemRingSheaf A)) _) :=
    equivalenceDerivedUnit_isRightDerivedFunctor e F RF α
  have hRΓAb : RΓAb.IsRightDerivedFunctor γ
      (HomotopyCategory.quasiIso (Sheaf (⊥ : GrothendieckTopology ℕ) Ab.{v}) _) :=
    equivalenceDerivedUnit_isRightDerivedFunctor s lim RFAb αAb
  let θ := globalSectionsForgetIso.{u, v} A
  let a : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶
        Qh ⋙ RΓ ⋙ G.mapDerivedCategory :=
    Functor.whiskerLeft (Γ.mapHomotopyCategory _) G.mapDerivedCategoryFactorsh.inv ≫
      Functor.whiskerRight β G.mapDerivedCategory
  let b : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh ⟶
        Qh ⋙ S.mapDerivedCategory ⋙ RΓAb :=
    Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (Γ ⋙ G)) (ComplexShape.up ℤ)).hom Qh ≫
      Functor.whiskerRight (NatTrans.mapHomotopyCategory θ.hom (ComplexShape.up ℤ)) Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ ΓAb)) (ComplexShape.up ℤ)).inv Qh ≫
      Functor.whiskerLeft (S.mapHomotopyCategory _) γ ≫
      Functor.whiskerRight S.mapDerivedCategoryFactorsh.inv RΓAb
  have hab : ∀ K : HomotopyCategory (SheafOfModules.{v} (inverseSystemRingSheaf A))
      (ComplexShape.up ℤ), ∃ (L : HomotopyCategory
        (SheafOfModules.{v} (inverseSystemRingSheaf A)) (ComplexShape.up ℤ)) (r : K ⟶ L),
      HomotopyCategory.quasiIso _ _ r ∧ IsIso (a.app L) ∧ IsIso (b.app L) := by
    intro K
    obtain ⟨L, f, hf, hL⟩ := inverseLimit_acyclic_resolutions A
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.as)
    let := hf
    let N := (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let r : K.as ⟶ N := (e.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.hom.app K.as ≫
      (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f
    have hr : QuasiIso r := by
      dsimp [r]
      infer_instance
    have ha : IsIso (α.app ((e.functor.mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj N))) := by
      apply isIso_unit_of_resolutions F
        (fun M ↦ IsZero (Rlim.firstDerivedLimit M.presheaf))
        (inverseLimit_acyclic_resolutions A)
        (fun f hf hK hL ↦ by
          let := hf
          exact inverseLimit_map_quasiIso A hmapAb f hK hL) RF α
      exact hL
    have hβ := isIso_equivalenceDerivedUnit_app e F RF α ((HomotopyCategory.quotient _ _).obj N)
    have haAb : IsIso (αAb.app ((s.functor.mapHomotopyCategory _).obj
        ((S.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj N)))) := by
      apply hunitAb
      exact hL
    have hγ := isIso_equivalenceDerivedUnit_app s lim RFAb αAb
      ((S.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj N))
    refine ⟨(HomotopyCategory.quotient _ _).obj N,
      (HomotopyCategory.quotient _ _).map r,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff r).mpr hr, ?_, ?_⟩
    · dsimp [a]
      infer_instance
    · have := mapHomotopyCategory_iso_app (ComplexShape.up ℤ) θ
        ((HomotopyCategory.quotient _ _).obj N)
      have hγ' : IsIso (γ.app ((S.mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient _ _).obj N))) := hγ
      dsimp [b] at hγ' this ⊢
      infer_instance
  have : (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (inverseSystemRingSheaf A))
      (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  obtain ⟨ζ, hζ⟩ := exists_iso_of_common_localized_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{v} (inverseSystemRingSheaf A)) _) Qh
    (RΓ ⋙ G.mapDerivedCategory) (S.mapDerivedCategory ⋙ RΓAb) a b hab
  refine ⟨moduleSheafBotEquivalence_additive A, hF, RF, α,
    moduleGlobalSections_additive A, globalSectionsAb_additive,
    toSheaf_additive_bot A, moduleForget_preservesFiniteColimits A,
    RΓ, β, RΓAb, γ, toSheaf_preservesFiniteColimits_bot A,
    hRF, hRΓ, hRΓAb, Iso.refl _, θ, ζ, ?_, ?_⟩
  · intro K
    show β.app K ≫ 𝟙 _ = β.app K
    exact CategoryTheory.Category.comp_id _
  · intro K
    have h := congr_app hζ K
    simp only [a, b, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      mapHomotopyCategoryCompIso_refl_hom_app, mapHomotopyCategoryCompIso_refl_inv_app,
      CategoryTheory.Functor.map_id, CategoryTheory.Category.assoc] at h
    simp only [Functor.comp_obj, CategoryTheory.Category.id_comp] at h
    exact h.trans (congrArg (_ ≫ ·) (CategoryTheory.Category.id_comp _))

end ModuleInverseLimitGlobalSections

end

end
