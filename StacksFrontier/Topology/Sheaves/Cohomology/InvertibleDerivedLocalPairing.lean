module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalHomotopy

/-!
# A derived tensor pairing of strictly perfect complexes splits locally

Let `P`, `P'` be strictly perfect complexes on a ringed space `X` with `Tot(P ⊗ P')` isomorphic
to `𝒪_X[0]` in `D(𝒪_X)`. Near every point the isomorphism and its inverse are induced by maps of
complexes (Stacks 08C9), and the cohomology of `P` and `P'` splits there.

## References

* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open StrictlyPerfect Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {Y : RingedSpace.{u, u}}

/-- Two maps of complexes which are mutually inverse in the derived category after conjugating by
isomorphisms of complexes are mutually inverse there. -/
public theorem Q_map_conj_eq_id {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{d} C]
    {A B A' B' : CochainComplex C ℤ} (a : A ⟶ B) (b : B ⟶ A) (eA : A ≅ A') (eB : B ≅ B')
    (h : DerivedCategory.Q.map (a ≫ b) = 𝟙 _) :
    DerivedCategory.Q.map ((eA.inv ≫ a ≫ eB.hom) ≫ (eB.inv ≫ b ≫ eA.hom)) = 𝟙 _ := by
  have : (eA.inv ≫ a ≫ eB.hom) ≫ (eB.inv ≫ b ≫ eA.hom) = eA.inv ≫ (a ≫ b) ≫ eA.hom := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [this, Functor.map_comp, Functor.map_comp, h, Category.id_comp, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Maps of complexes inverse in the derived category after a functor, from Stacks 08C9 applied to
an isomorphism and to the inverse of its local representative. -/
public theorem Q_map_comp_eq_id_of_factors {A B : Type*} [Category* A] [Abelian A] [Category* B]
    [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {K L : CochainComplex A ℤ} (a : K ⟶ L)
    [IsIso (DerivedCategory.Q.map a)]
    (b : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hb : F.mapDerivedCategory.map (inv (DerivedCategory.Q.map a)) ≫
        F.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map b) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ b) = 𝟙 _ ∧
      DerivedCategory.Q.map (b ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a) = 𝟙 _ := by
  have nat := F.mapDerivedCategoryFactors.hom.naturality a
  simp only [Functor.comp_map] at nat
  constructor
  · rw [← cancel_epi (F.mapDerivedCategoryFactors.hom.app K), Functor.map_comp,
      ← Category.assoc, ← nat, Category.assoc, ← hb, ← Category.assoc, ← Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
    simp
  · rw [← cancel_epi (F.mapDerivedCategoryFactors.hom.app L), Functor.map_comp,
      ← Category.assoc, ← hb, Category.assoc, ← nat, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    simp

/-- The restriction of a strictly perfect complex to an open subspace is strictly perfect. -/
public theorem isStrictlyPerfect_restrict (U : Opens Y.carrier)
    {P : CochainComplex (OXMod.{u, u} Y) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((restrictModules Y U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ⟨Set.Finite.subset hP.bounded fun _ hi h => hi ((restrictModules Y U).map_isZero h),
    fun i => RingedSpace.isDirectSummandOfFiniteFree_restrictModules U (hP.directSummand i)⟩

variable (Y) in
/-- **A derived tensor pairing of strictly perfect complexes splits locally.** -/
public theorem exists_localSplitting_of_derivedPairing
    [inst : HasDerivedCategory.{d} (Mod Y.sheaf)]
    (P P' : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P)
    (hP' : IsStrictlyPerfect P')
    (γ : DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.sheaf).obj P).obj P') ≅
      DerivedCategory.Q.obj (LeftDualPerfect.unitComplex Y))
    (x : Y.carrier) : ∃ V : Opens Y.carrier, x ∈ V ∧ Nonempty (LocalSplitting P P' V) := by
  let : HasDerivedCategory.{d} (OXMod.{u, u} Y) := inst
  let : ∀ U : Opens Y.carrier,
      HasDerivedCategory (OXMod.{u, u} (Y.restrict U.isOpenEmbedding)) :=
    fun _ => HasDerivedCategory.standard _
  have hT := StrictlyPerfect.isStrictlyPerfect_tensorComplex Y P P' hP hP'
  obtain ⟨U₁, hx₁, a, ha⟩ := RingedSpace.exists_local_complex_map_of_instances
    (LeftDualPerfect.isStrictlyPerfect_unitComplex Y) γ.inv x
  have hQa : IsIso (DerivedCategory.Q.map a) := by
    have : IsIso ((restrictModules Y U₁).mapDerivedCategoryFactors.hom.app
        (LeftDualPerfect.unitComplex Y) ≫
        DerivedCategory.Q.map a) := ha ▸ (((restrictModules Y U₁).mapDerivedCategory.mapIso
          γ.symm ≪≫ (restrictModules Y U₁).mapDerivedCategoryFactors.app _).isIso_hom)
    have : IsIso ((restrictModules Y U₁).mapDerivedCategoryFactors.hom.app
        (LeftDualPerfect.unitComplex Y)) := (Iso.app _ _).isIso_hom
    exact IsIso.of_isIso_comp_left ((restrictModules Y U₁).mapDerivedCategoryFactors.hom.app
      (LeftDualPerfect.unitComplex Y)) (DerivedCategory.Q.map a)
  let : ∀ U : Opens (Y.restrict U₁.isOpenEmbedding).carrier, HasDerivedCategory
      (OXMod.{u, u} ((Y.restrict U₁.isOpenEmbedding).restrict U.isOpenEmbedding)) :=
    fun _ => HasDerivedCategory.standard _
  obtain ⟨U₂, hx₂, b, hb⟩ := RingedSpace.exists_local_complex_map_of_instances
    (isStrictlyPerfect_restrict U₁ hT) (@inv _ _ _ _ (DerivedCategory.Q.map a) hQa)
    (⟨x, hx₁⟩ : (Y.restrict U₁.isOpenEmbedding).carrier)
  obtain ⟨e₁, e₂⟩ := Q_map_comp_eq_id_of_factors
    (restrictModules (Y.restrict U₁.isOpenEmbedding) U₂) a b hb
  let F₂ := (restrictModules (Y.restrict U₁.isOpenEmbedding) U₂).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let eT := F₂.mapIso (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso Y U₁ P P') ≪≫
    Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso (Y.restrict U₁.isOpenEmbedding) U₂
      (RingedSpace.restrictComplex P U₁) (RingedSpace.restrictComplex P' U₁)
  let eU : F₂.obj (((restrictModules Y U₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (LeftDualPerfect.unitComplex Y)) ≅
      LeftDualPerfect.unitComplex ((Y.restrict U₁.isOpenEmbedding).restrict U₂.isOpenEmbedding) :=
    F₂.mapIso (restrictUnitComplexIso U₁) ≪≫ restrictUnitComplexIso U₂
  let : HasDerivedCategory (Mod ((Y.restrict U₁.isOpenEmbedding).restrict
      U₂.isOpenEmbedding).sheaf) := HasDerivedCategory.standard _
  obtain ⟨V, hV, ⟨A⟩⟩ := exists_localSplitting_of_chainPairing
    ((Y.restrict U₁.isOpenEmbedding).restrict U₂.isOpenEmbedding)
    (RingedSpace.restrictComplex (RingedSpace.restrictComplex P U₁) U₂)
    (RingedSpace.restrictComplex (RingedSpace.restrictComplex P' U₁) U₂)
    (isStrictlyPerfect_restrict U₂ (isStrictlyPerfect_restrict U₁ hP))
    (isStrictlyPerfect_restrict U₂ (isStrictlyPerfect_restrict U₁ hP'))
    (eU.inv ≫ F₂.map a ≫ eT.hom) (eT.inv ≫ b ≫ eU.hom)
    (Q_map_conj_eq_id _ _ eU eT e₁) (Q_map_conj_eq_id _ _ eT eU e₂) ⟨⟨x, hx₁⟩, hx₂⟩
  let A₁ := LocalSplitting.transport U₂ (fun k => (restrictModulesHomologyIso _ U₂ k).symm)
    (fun k => (restrictModulesHomologyIso _ U₂ k).symm) A
  let A₀ := LocalSplitting.transport U₁ (fun k => (restrictModulesHomologyIso P U₁ k).symm)
    (fun k => (restrictModulesHomologyIso P' U₁ k).symm) A₁
  exact ⟨U₁.isOpenEmbedding.functor.obj (U₂.isOpenEmbedding.functor.obj V),
    ⟨⟨x, hx₁⟩, ⟨⟨⟨x, hx₁⟩, hx₂⟩, hV, rfl⟩, rfl⟩, ⟨A₀⟩⟩

end Stacks.Cohomology.InvertibleDerived

end
