module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTensor
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceProperSupport
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSectionsOverOpen
public import StacksFrontier.AlgebraicGeometry.Cohomology.FlatPushforwardSectionsHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTopDegree
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting

/-!
# The comparison of Stacks 0CTG on homotopy colimits

In Situation [Stacks, Tag 0CTC], the proof of [Stacks, Tag 0CTG] writes `RΓ(U, K)` as a homotopy
colimit `hocolim RΓ(X, K ⊗^𝐋 Eₘ)` over perfect complexes `Eₘ` ([Stacks, Tag 0CRR]) and applies
[Stacks, Tag 0CTE] levelwise. The step which makes this legitimate is recorded here: a natural
transformation between two functors into a derived category, both of which carry a homotopy
colimit presentation `L = hocolim Eₘ` to a homotopy colimit presentation, is invertible at `L`
as soon as it is invertible at every `Eₘ`. The cohomology of a homotopy colimit is the colimit of
the cohomologies ([Stacks, Tag 0CRK]), and a colimit of isomorphisms is an isomorphism.

## Main results

* `CategoryTheory.Pretriangulated.isIso_app_of_isHomotopyColimitWith`: the statement above.

## References

* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
* [Stacks Project, Tag 0CRK](https://stacks.math.columbia.edu/tag/0CRK)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isFinitePresentation)
open Stacks.Cohomology.CountableSections
  (preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent)
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

/-- **A natural transformation which is invertible on the terms of a homotopy colimit is
invertible at the homotopy colimit**, when both functors carry the homotopy colimit, with its
coprojections, to a homotopy colimit. The target is a derived category whose cohomology functors
commute with countable direct sums and in which sequential colimits are exact. -/
theorem isIso_app_of_isHomotopyColimitWith {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ i : ℤ, PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor C i)]
    {𝒟 : Type*} [Category 𝒟] {G₁ G₂ : 𝒟 ⥤ DerivedCategory C} (ψ : G₁ ⟶ G₂)
    (E : ℕ ⥤ 𝒟) (L : 𝒟) (c : ∀ m, E.obj m ⟶ L)
    [HasCoproduct (E ⋙ G₁).obj] [HasCoproduct (E ⋙ G₂).obj]
    (h₁ : IsHomotopyColimitWith (E ⋙ G₁) (G₁.obj L) fun m => G₁.map (c m))
    (h₂ : IsHomotopyColimitWith (E ⋙ G₂) (G₂.obj L) fun m => G₂.map (c m))
    (hψ : ∀ m, IsIso (ψ.app (E.obj m))) :
    IsIso (ψ.app L) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  let H := DerivedCategory.homologyFunctor C i
  obtain ⟨p₁, q₁, hT₁, hc₁⟩ := h₁
  obtain ⟨p₂, q₂, hT₂, hc₂⟩ := h₂
  obtain ⟨e₁, he₁⟩ := exists_iso_colimit_of_isHomotopyColimit (E ⋙ G₁) H p₁ q₁ hT₁
  obtain ⟨e₂, he₂⟩ := exists_iso_colimit_of_isHomotopyColimit (E ⋙ G₂) H p₂ q₂ hT₂
  let α : (E ⋙ G₁) ⋙ H ⟶ (E ⋙ G₂) ⋙ H := Functor.whiskerRight (Functor.whiskerLeft E ψ) H
  have : ∀ m, IsIso (α.app m) := fun m => by
    dsimp [α]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have key : H.map (ψ.app L) = e₁.inv ≫ colim.map α ≫ e₂.hom := by
    rw [Iso.eq_inv_comp]
    refine colimit.hom_ext fun m => ?_
    rw [← Category.assoc, he₁ m, ← H.map_comp, hc₁ m, colim_map, ι_colimMap_assoc, he₂ m,
      hc₂ m]
    dsimp only [α, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj]
    rw [← H.map_comp, ψ.naturality]
  rw [key]
  infer_instance

end CategoryTheory.Pretriangulated

open Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- Sequential colimits of modules are exact. -/
instance hasExactColimitsOfShape_nat_moduleCat (R : Type u) [CommRing R] :
    HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
  (AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)).ofShape ℕ

/-- The derived category of modules has countable direct sums, at every model. -/
instance hasCountableCoproducts_derivedCategory_moduleCat (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] :
    HasCountableCoproducts (DerivedCategory (ModuleCat.{u} R)) :=
  derivedCategory_hasCountableCoproducts _ ⟨inferInstance, fun _ _ => ⟨inferInstance,
      inferInstance⟩⟩

/-- The cohomology functors of the derived category of modules commute with countable direct
sums, at every model. -/
instance preservesColimitsOfShape_discrete_nat_homologyFunctor_moduleCat (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (i : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i) :=
  have := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
    (ModuleCat.{u} R) (J := ULift.{u} ℕ) i
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- A quasi-compact open of `X` is quasi-compact over `X`. -/
theorem quasiCompact_ι_of_isCompact (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left)) :
    QuasiCompact U.ι :=
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  quasiCompact_of_compactSpace _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The cohomology sheaves of `ℱₙ`, read in `D(𝒪_{Xₙ})`, are quasi-coherent**: in degree zero
because `ℱₙ` is of finite presentation, and in every other degree because they vanish. Stated at
the standard model. -/
theorem isQuasicoherent_homology_levelSheafStandard (n : ℕ) (j : ℤ) :
    ((DerivedCategory.homologyFunctor (schemeAt S.system S.X n).Modules j).obj
      (S.levelSheafStandard n)).IsQuasicoherent := by
  have := S.finitelyPresented n
  rcases eq_or_ne j 0 with rfl | hj
  · exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (isQuasicoherent_isFiniteType_of_isFinitePresentation _ (S.finitelyPresented n)).1
  · exact (isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (isFinitePresentation_of_isZero _
        (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj))).1

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`E ↦ RΓ(X, K ⊗^𝐋 E) ⊗_A^𝐋 Aₙ` carries a homotopy colimit presentation by perfect objects to
a homotopy colimit presentation**: the tensor product with `K` and the derived extension of
scalars are triangulated and preserve the direct sum of the system, being left adjoints, and the
derived global sections preserve it because the terms `K ⊗^𝐋 Eₘ` have quasi-coherent cohomology
([Stacks, Tag 08DZ]). Stated at the standard model. -/
theorem isHomotopyColimitWith_globalSectionsTensor_extendScalars (d : S.DerivedLimitQCoh) (n : ℕ)
    {E : ℕ ⥤ DerivedCategory S.X.left.Modules} {L : DerivedCategory S.X.left.Modules}
    {c : ∀ m, E.obj m ⟶ L}
    (hEp : ∀ m, Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := S.X.left.toRingedSpace) (E.obj m))
    (hc : Pretriangulated.IsHomotopyColimitWith E L c) :
    Pretriangulated.IsHomotopyColimitWith
      (E ⋙ (derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K ⋙
        derivedGlobalSectionsOver S.X.hom ⋙
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          (S.limitProjection n)).functor)
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K ⋙
        derivedGlobalSectionsOver S.X.hom ⋙
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          (S.limitProjection n)).functor).obj L)
      (fun m => ((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K ⋙
        derivedGlobalSectionsOver S.X.hom ⋙
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
          (S.limitProjection n)).functor).map (c m)) := by
  have : QuasiCompact S.X.hom := S.finitePresentation.2.1
  have : QuasiSeparated S.X.hom := S.finitePresentation.2.2
  let TK : DerivedCategory S.X.left.Modules ⥤ DerivedCategory S.X.left.Modules :=
    (derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj d.K
  let : TK.CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).commShift_right d.K
  have : TK.IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).exact_right d.K
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) TK :=
    Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor
      _ (ULift.{u} ℕ) d.K
  have : PreservesColimitsOfShape (Discrete ℕ) TK :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have hq : ∀ m i, ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj
      (TK.obj (E.obj m))).IsQuasicoherent := fun m i =>
    Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj S.X.left d.K
      (E.obj m) d.quasicoherent
      (fun j => PerfectApproximation.isQuasicoherent_homology_of_isPerfect S.X.left _ (hEp m) j) i
  have : PreservesColimit (Discrete.functor (E ⋙ TK).obj) (derivedGlobalSectionsOver S.X.hom) :=
    preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent S.X.hom _ hq
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (S.limitProjection n)
  let := D.commShift
  have : D.functor.IsTriangulated := D.isTriangulated
  have : PreservesColimitsOfSize.{0, 0} D.functor :=
    (StacksDraft.TopDegreeExtendScalars.extAdj (S.limitProjection n)).leftAdjoint_preservesColimits
  exact ((hc.map TK).map (derivedGlobalSectionsOver S.X.hom)).map D.functor

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`E ↦ RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* E)` carries a homotopy colimit presentation by perfect objects to a
homotopy colimit presentation**: the derived restriction to `Xₙ` and the tensor product with `ℱₙ`
are triangulated and preserve the direct sum of the system, and the derived global sections
preserve it because the terms `ℱₙ ⊗^𝐋 Liₙ^* Eₘ` have quasi-coherent cohomology
([Stacks, Tag 08DZ]). Stated at the standard model. -/
theorem isHomotopyColimitWith_levelTensor (n : ℕ)
    {E : ℕ ⥤ DerivedCategory S.X.left.Modules} {L : DerivedCategory S.X.left.Modules}
    {c : ∀ m, E.obj m ⟶ L}
    (hEp : ∀ m, Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := S.X.left.toRingedSpace) (E.obj m))
    (hc : Pretriangulated.IsHomotopyColimitWith E L c) :
    Pretriangulated.IsHomotopyColimitWith
      (E ⋙ S.levelPullback n ⋙
        (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
          (S.levelSheafStandard n) ⋙ derivedGlobalSectionsOver (S.levelStructure n))
      ((S.levelPullback n ⋙
        (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
          (S.levelSheafStandard n) ⋙ derivedGlobalSectionsOver (S.levelStructure n)).obj L)
      (fun m => (S.levelPullback n ⋙
        (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
          (S.levelSheafStandard n) ⋙
          derivedGlobalSectionsOver (S.levelStructure n)).map (c m)) := by
  let Li := S.levelPullback n
  let : Li.CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
      (S.closedImmersion n).toLRSHom.toShHom
  have : Li.IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
      (S.closedImmersion n).toLRSHom.toShHom
  have : PreservesColimitsOfSize.{0, 0} Li :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
      (S.closedImmersion n).toLRSHom.toShHom).leftAdjoint_preservesColimits
  let TF : DerivedCategory (schemeAt S.system S.X n).Modules ⥤
      DerivedCategory (schemeAt S.system S.X n).Modules :=
    (derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
      (S.levelSheafStandard n)
  let : TF.CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).commShift_right _
  have : TF.IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _).exact_right _
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) TF :=
    Stacks.DerivedTensor.RingedSite.preservesColimitsOfShape_discrete_derivedTensorProductFunctor
      _ (ULift.{u} ℕ) _
  have : PreservesColimitsOfShape (Discrete ℕ) TF :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have hq : ∀ m i, ((DerivedCategory.homologyFunctor _ i).obj
      (TF.obj (Li.obj (E.obj m)))).IsQuasicoherent := fun m i =>
    Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj _ _ _
      (S.isQuasicoherent_homology_levelSheafStandard n)
      (fun j => PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
          (S.closedImmersion n).toLRSHom.toShHom _ (hEp m)) j) i
  have : QuasiCompact (S.levelStructure n) := (S.finitePresentation_levelStructure n).2.1
  have : QuasiSeparated (S.levelStructure n) := (S.finitePresentation_levelStructure n).2.2
  have : PreservesColimit (Discrete.functor ((E ⋙ Li) ⋙ TF).obj)
      (derivedGlobalSectionsOver (S.levelStructure n)) :=
    preservesColimit_derivedGlobalSectionsOver_of_isQuasicoherent (S.levelStructure n) _ hq
  exact ((hc.map Li).map TF).map (derivedGlobalSectionsOver (S.levelStructure n))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The comparison of [Stacks, Tag 0CTE] (1) is invertible at `Rι_* 𝒪_U`**, for `U` a
quasi-compact open, granted that it is invertible at perfect objects. By [Stacks, Tag 0CRR] (in its
`𝒪_X`-level form) `Rι_* 𝒪_U = hocolim Eₘ` with `Eₘ` perfect; both
`E ↦ RΓ(X, K ⊗^𝐋 E) ⊗_A^𝐋 Aₙ` and `E ↦ RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* E)` carry this presentation to a
homotopy colimit, as they are composites of triangulated functors preserving the relevant direct
sums. Stated at the standard model, at which the derived pushforward and the projection formula
are available. -/
theorem isIso_tensorBaseChange_app_derivedPushforward_unit (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ)
    (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left))
    (h0CTE : ∀ E : DerivedCategory S.X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app E)) :
    IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app
      ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U))) := by
  have := S.quasiCompact_ι_of_isCompact U hU
  have : QuasiCompact S.X.hom := S.finitePresentation.2.1
  have : QuasiSeparated S.X.hom := S.finitePresentation.2.2
  obtain ⟨E, c₀, hEp, hc⟩ :=
    Stacks.Cohomology.CountableSections.exists_isHomotopyColimitWith_derivedPushforward_unit
      S.X.hom U.ι
  exact Pretriangulated.isIso_app_of_isHomotopyColimitWith _ E _ c₀
    (S.isHomotopyColimitWith_globalSectionsTensor_extendScalars d n hEp hc)
    (S.isHomotopyColimitWith_levelTensor n hEp hc) fun m => h0CTE _ (hEp m)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The comparison of [Stacks, Tag 0CTG] from that of [Stacks, Tag 0CTE] (1) at `Rι_* 𝒪_U`.**
Let `ν : RΓ(X, - ⊗^𝐋 Rι_* 𝒪_U) ⟶ RΓ(U, -)` be natural and invertible at `K` (the projection
formula, [Stacks, Tag 08EU]), and let `μ : RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* Rι_* 𝒪_U) ≅ RΓ(Uₙ, ℱₙ)` be an
isomorphism of `D(Aₙ)` compatible with `ν` at `iₙ,* ℱₙ`. Then the comparison
`RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` is the comparison of [Stacks, Tag 0CTE] (1) at `Rι_* 𝒪_U` up to
these isomorphisms, hence invertible when the latter is. Stated at the standard model. -/
theorem isIso_sectionsOverComparison_of_isIso_tensorBaseChange (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ)
    (U : S.X.left.Opens)
    (ν : (derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).flip.obj
        ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ⋙
          derivedGlobalSectionsOver S.X.hom ⟶ S.sectionsOver U)
    (hν : IsIso (ν.app d.K))
    (μ : S.levelTensor n ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ≅
      S.levelSectionsOver U n)
    (hsq : S.levelRestrictionMap n
        ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ≫
        (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map μ.hom =
      ν.app (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≫ (S.sectionsOverPushforwardIso U n).hom)
    (hψ : IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app
      ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)))) :
    IsIso (S.sectionsOverComparison d p U n) := by
  let EU := (derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)
  let adj := StacksDraft.TopDegreeExtendScalars.extAdj (S.limitProjection n)
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (S.limitProjection n)
  have hg : ν.app d.K ≫ S.sectionsOverToLevel d p U n =
      DerivedLimitQCoh.tensorLevelMap S d p n EU ≫
        (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map μ.hom := by
    rw [sectionsOverToLevel, ← Category.assoc, ← ν.naturality (S.levelMap d p n),
      Category.assoc, ← hsq]
    exact (Category.assoc _ _ _).symm
  have key : D.functor.map (ν.app d.K) ≫ S.sectionsOverComparison d p U n =
      (DerivedLimitQCoh.tensorBaseChange S d p n).app EU ≫ μ.hom := by
    have hL := Adjunction.homEquiv_naturality_left_symm adj (ν.app d.K)
      (S.sectionsOverToLevel d p U n)
    have hR := Adjunction.homEquiv_naturality_right_symm adj
      (DerivedLimitQCoh.tensorLevelMap S d p n EU) μ.hom
    exact hL.symm.trans ((congrArg _ hg).trans hR)
  have : IsIso (D.functor.map (ν.app d.K) ≫ S.sectionsOverComparison d p U n) := by
    rw [key]
    exact IsIso.comp_isIso' hψ (Iso.isIso_hom μ)
  exact IsIso.of_isIso_comp_left (D.functor.map (ν.app d.K)) _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The projection-formula square of the proof of [Stacks, Tag 0CTG]** at a quasi-compact open
`U` and a level `n`: a natural map `RΓ(X, - ⊗^𝐋 Rι_* 𝒪_U) ⟶ RΓ(U, -)`, invertible on
`D_QCoh(𝒪_X)` (the projection formula), and an isomorphism
`RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* Rι_* 𝒪_U) ≅ RΓ(Uₙ, ℱₙ)` of `D(Aₙ)` compatible with it at `iₙ,* ℱₙ`. Stated at
the standard model. -/
def ProjectionFormulaSquare (U : S.X.left.Opens) (n : ℕ) : Prop :=
  ∃ ν : (derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).flip.obj
      ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ⋙
        derivedGlobalSectionsOver S.X.hom ⟶ S.sectionsOver U,
    (∀ M : DerivedCategory S.X.left.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj M).IsQuasicoherent) →
        IsIso (ν.app M)) ∧
    ∃ μ : S.levelTensor n ((derivedPushforward U.ι.toLRSHom.toShHom).obj
        (derivedUnitObject U)) ≅ S.levelSectionsOver U n,
      S.levelRestrictionMap n
          ((derivedPushforward U.ι.toLRSHom.toShHom).obj (derivedUnitObject U)) ≫
          (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map μ.hom =
        ν.app (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≫
          (S.sectionsOverPushforwardIso U n).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTG] from [Stacks, Tag 0CTE] (1) and the projection-formula square.** For a
quasi-compact open `U`, the comparison `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` is invertible, granted
that the comparison of [Stacks, Tag 0CTE] (1) is invertible at perfect objects, and that the
projection formula `RΓ(X, - ⊗^𝐋 Rι_* 𝒪_U) ≅ RΓ(U, -)` on `D_QCoh(𝒪_X)` is compatible, at
`iₙ,* ℱₙ`, with an isomorphism `RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^* Rι_* 𝒪_U) ≅ RΓ(Uₙ, ℱₙ)` of `D(Aₙ)`. Stated
at the standard model. -/
theorem isIso_sectionsOverComparison_of_isIso_tensorBaseChange_of_square
    (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ)
    (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left))
    (h0CTE : ∀ E : DerivedCategory S.X.left.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
        IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app E))
    (hC : S.ProjectionFormulaSquare U n) :
    IsIso (S.sectionsOverComparison d p U n) := by
  obtain ⟨ν, hν, μ, hsq⟩ := hC
  exact S.isIso_sectionsOverComparison_of_isIso_tensorBaseChange d p n U ν
    (hν d.K d.quasicoherent) μ hsq
    (S.isIso_tensorBaseChange_app_derivedPushforward_unit d p n U hU h0CTE)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
