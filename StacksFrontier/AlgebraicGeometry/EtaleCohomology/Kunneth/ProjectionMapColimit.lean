module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.ProjectionMapConstructible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomologyNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Devissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfAFlatModule
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection map of Tag 0F1J and filtered colimits of sheaves of `𝔽_ℓ`-modules

The step of the proof of [Stacks, Tag 0F1J] which passes from constructible sheaves of
`𝔽_ℓ`-vector spaces to all of them: "We can write `ℰ` as a filtered colimit of constructible
sheaves of `𝔽_ℓ`-vector spaces on `X_étale` (Tag 03SA). Since tensor products commute with
filtered colimits and since higher direct images do too (Tag 09Z1) we may assume `ℰ` is a
constructible sheaf". Every sheaf of `𝔽_ℓ̲`-modules is flat, so on cohomology the two sides of the
projection map at `ℰ[-k]` are `H^n(ℰ ⊗ Rh_*B)` and `H^n(Rh_*((h⁻¹ℰ ⊗ H^j(B))[-j]))` for `B`
concentrated in degree `j`, and both commute with filtered colimits in `ℰ`.

## Main results

* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionMap_singleFunctor_of_isColimit` — the
  projection map is invertible at a filtered colimit of sheaves if it is at every term.
* `isIso_projectionMap_pullback_singleFunctor_of_compactSpace`
  — the projection map of Tag 0F1J at a single sheaf `ℰ` of `𝔽_ℓ`-vector spaces on a quasi-compact
  quasi-separated `X`, and a single sheaf on `T`.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_compactSpace` — Tag 0F1J
  for `n = ℓ` prime over a quasi-compact quasi-separated `X`.

Not registered: derived base change along `X ⟶ S` and along the finite `X`-schemes are explicit
arguments (Tag 0F1I for `S = Spec K`).

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` and `derivedPushforward` (`StacksFrontier/CategoryTheory/Sites/Cohomology/
-- DerivedPushforward/AdjunctionForRingedTopoi.lean:394`), through `pullback` and `pushforward`,
-- are stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

-- The imports bring `SheafOfModules.hasDerivedCategory`
-- (`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean:155`), the locally small model, which
-- would otherwise be found before `HasDerivedCategory.standard`.

/-- **A natural transformation into the derived category which is invertible at every term of a
diagram is invertible at its colimit**, as soon as the cohomology of its source and target
commute with that colimit: it is invertible exactly when it is on every cohomology object, and
there it is a transformation of colimit-preserving functors. -/
theorem isIso_app_of_isColimit_of_homology {J C A : Type*} [Category J] [Category C]
    [Category A] [Abelian A] [HasDerivedCategory A] (F G : C ⥤ DerivedCategory A) (α : F ⟶ G)
    {K : J ⥤ C} (c : Cocone K) (hc : IsColimit c)
    (hF : ∀ n : ℤ, PreservesColimit K (F ⋙ DerivedCategory.homologyFunctor A n))
    (hG : ∀ n : ℤ, PreservesColimit K (G ⋙ DerivedCategory.homologyFunctor A n))
    (h : ∀ j, IsIso (α.app (K.obj j))) : IsIso (α.app c.pt) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := hF n
  have := hG n
  exact Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_isColimit
    (F ⋙ DerivedCategory.homologyFunctor A n) (G ⋙ DerivedCategory.homologyFunctor A n)
    (Functor.whiskerRight α _) c hc (fun j => by
      change IsIso ((DerivedCategory.homologyFunctor A n).map (α.app (K.obj j)))
      have := h j
      infer_instance)

variable (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

/-- **The cohomology of `M[0] ⊗^L C` is `M ⊗ H^n(C)`, naturally in the sheaf `M`**, over `𝔽_ℓ`:
it is `M ⊗ H^n(C)` (`Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology`, the
cohomology sheaves of `C` being flat), naturally in `M`, and tensoring commutes with colimits. -/
def singleFunctorTensorHomologyIso (C : DerivedModules (ULift.{u + 1} (ZMod ℓ)) X) (n : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙
      (tensor (ULift.{u + 1} (ZMod ℓ)) X).flip.obj C ⋙ DerivedCategory.homologyFunctor _ n ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O).flip.obj
        ((DerivedCategory.homologyFunctor _ n).obj C) :=
  have hC : Stacks.DerivedTensor.RingedSite.HasFlatHomology
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O C :=
    fun i => isFlat_of_fact_prime ℓ _
  NatIso.ofComponents (fun A => (DerivedCategory.homologyFunctor _ n).mapIso
        (((tensor (ULift.{u + 1} (ZMod ℓ)) X).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app A)).app C) ≪≫
        Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology A C hC n)
      (fun {A A'} a => by
        have h1 := (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.naturality a
        have h2 : (DerivedCategory.homologyFunctor _ n).map
            (((tensor (ULift.{u + 1} (ZMod ℓ)) X).map (DerivedCategory.Q.map
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map a))).app C) ≫
            (Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology A' C hC n).hom =
          (Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology A C hC n).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor _).map a).app
              ((DerivedCategory.homologyFunctor _ n).obj C) :=
          Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology_hom_naturality
            a C hC n
        dsimp only [Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom, Functor.mapIso_hom,
          Iso.app_hom, Functor.comp_obj, Functor.flip_obj_obj] at h1 ⊢
        rw [← Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp, h1,
          Functor.map_comp, NatTrans.comp_app, Functor.map_comp]
        simp only [Category.assoc]
        exact congrArg (fun t => (DerivedCategory.homologyFunctor _ n).map
          (((tensor (ULift.{u + 1} (ZMod ℓ)) X).map
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app A)).app C) ≫ t) h2)

/-- **The cohomology of `M[0] ⊗^L C` commutes with colimits in the sheaf `M`**, over `𝔽_ℓ`
(`singleFunctorTensorHomologyIso`). -/
theorem preservesColimit_singleFunctor_tensor_homology {J : Type*} [Category J]
    (K : J ⥤ SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O))
    (C : DerivedModules (ULift.{u + 1} (ZMod ℓ)) X) (n : ℤ) :
    PreservesColimit K (DerivedCategory.singleFunctor _ 0 ⋙
      (tensor (ULift.{u + 1} (ZMod ℓ)) X).flip.obj C ⋙ DerivedCategory.homologyFunctor _ n) := by
  have := SheafOfModules.preservesColimitsOfSize_sheafTensor_flip_obj.{u + 1, u + 1, u + 1}
    (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O ((DerivedCategory.homologyFunctor _ n).obj C) K
  exact preservesColimit_of_natIso K (singleFunctorTensorHomologyIso ℓ C n).symm

/-- A functor all of whose values are zero objects preserves every colimit. -/
theorem preservesColimit_of_forall_isZero {J C D : Type*} [Category J] [Category C] [Category D]
    [HasZeroMorphisms D] (K : J ⥤ C) (G : C ⥤ D) (hG : ∀ X, IsZero (G.obj X)) :
    PreservesColimit K G :=
  ⟨fun {c} _ => ⟨{ desc := fun s => (hG c.pt).to_ s.pt
                   fac := fun _ _ => (hG _).eq_of_src _ _
                   uniq := fun _ _ _ => (hG c.pt).eq_of_src _ _ }⟩⟩

variable {Y X' : Scheme.{u}}

omit [Fact ℓ.Prime] in
/-- **The higher direct images of sheaves of `𝔽_ℓ̲`-modules along a quasi-compact
quasi-separated morphism commute with filtered colimits**, read as the cohomology of the derived
direct image of a sheaf placed in degree zero: on the underlying abelian sheaves, which detect
colimits, it is `R^n h_*` of the abelian sheaves (`pushforwardForgetPlusIso`), which commutes with
filtered colimits ([Stacks, Tag 09Z1] for a constant system,
`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs`). -/
@[sga "4 VI 5.1" "special case"]
theorem preservesColimit_singleFunctor_pushforward_homology (h : Y ⟶ X') [QuasiCompact h]
    [QuasiSeparated h] (n : ℤ) {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O)) :
    PreservesColimit K (DerivedCategory.singleFunctor _ 0 ⋙
      pushforward (ULift.{u + 1} (ZMod ℓ)) h ⋙ DerivedCategory.homologyFunctor _ n) := by
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let F := etaleToSheaf Λ X'
  let FY := etaleToSheaf Λ Y
  let P := smallEtalePushforwardAb h
  have : PreservesColimitsOfShape J FY := by
    have : PreservesColimitsOfShape J
        (SheafOfModules.toSheaf.{u + 1}
          (Stacks.EtaleCohomology.ProjectionFormulaConstant.etaleRing Λ Y)) :=
      SheafOfModules.preservesColimitsOfShape_toSheaf _
    infer_instance
  suffices H : PreservesColimit K ((DerivedCategory.singleFunctor _ 0 ⋙
      pushforward Λ h ⋙ DerivedCategory.homologyFunctor _ n) ⋙ F) from
    preservesColimit_of_reflects_of_preserves _ F
  let e : (DerivedCategory.singleFunctor _ 0 ⋙ pushforward Λ h ⋙
      DerivedCategory.homologyFunctor _ n) ⋙ F ≅ FY ⋙ P.rightDerivedPlus n :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).symm) ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((Functor.associator _ _ _) ≪≫
          pushforwardForgetPlusIso Λ h) _ ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle FY 0) _ ≪≫
      Functor.associator _ _ _
  suffices H' : PreservesColimit K (FY ⋙ P.rightDerivedPlus n) from
    preservesColimit_of_natIso K e.symm
  rcases lt_or_ge n 0 with hn | hn
  · refine preservesColimit_of_forall_isZero K _ fun X => ?_
    let Z := (DerivedCategory.Plus.singleFunctor _ 0).obj (FY.obj X)
    have : Z.IsGE 0 := inferInstance
    have := P.isGE_rightDerivedFunctorPlus_obj Z 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE' _ 0 n hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have : PreservesColimitsOfShape J (P.rightDerived m) :=
      Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs.{
        0}
        h m J
    have : PreservesColimitsOfShape J (P.rightDerivedPlus (m : ℤ)) :=
      preservesColimitsOfShape_of_natIso (Stacks.DerivedIndexing.rightDerivedIso P m)
    infer_instance

/-- **The derived inverse image of a sheaf of `𝔽_ℓ̲`-modules placed in degree zero is its inverse
image placed in degree zero, naturally.** Every sheaf of `𝔽_ℓ̲`-modules is flat
(`isFlat_of_fact_prime`), so placed in degree zero it is a K-flat complex with flat terms, at which
the derived inverse image is computed degreewise
(`Stacks.Sheaves.DerivedPullback.flatPullbackIso`, natural by
`Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality`). -/
def singleFunctorCompPullbackIso (h : Y ⟶ X') :
    DerivedCategory.singleFunctor _ 0 ⋙ pullback (ULift.{u + 1} (ZMod ℓ)) h ≅
      (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos ⋙
        DerivedCategory.singleFunctor _ 0 :=
  NatIso.ofComponents (fun N =>
    (pullback (ULift.{u + 1} (ZMod ℓ)) h).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫
      Stacks.Sheaves.DerivedPullback.flatPullbackIso (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h)
        (isMorphismOfSites_ringedToposHom _ h) _
        (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ N
          (isFlat_of_fact_prime ℓ N) 0)
        (Stacks.Sheaves.DerivedPullback.isFlat_single_X _ N (isFlat_of_fact_prime ℓ N) 0) ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos (ComplexShape.up ℤ) 0).app N) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O)) 0).app
          ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos.obj N)).symm)
    (fun {N N'} a => by
      have h1 := (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.naturality a
      have h2 := Stacks.Sheaves.DerivedPullback.flatPullbackIso_naturality
        (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h) (isMorphismOfSites_ringedToposHom _ h)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map a)
        (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ N
          (isFlat_of_fact_prime ℓ N) 0)
        (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ N'
          (isFlat_of_fact_prime ℓ N') 0)
        (Stacks.Sheaves.DerivedPullback.isFlat_single_X _ N (isFlat_of_fact_prime ℓ N) 0)
        (Stacks.Sheaves.DerivedPullback.isFlat_single_X _ N' (isFlat_of_fact_prime ℓ N') 0)
      have h3 := (HomologicalComplex.singleMapHomologicalComplex
        (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos (ComplexShape.up ℤ)
          0).hom.naturality a
      have h4 := (DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O))
          0).inv.naturality
          ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos.map a)
      dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h3 h4 ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
      rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
      refine congrArg (fun t => (pullback (ULift.{u + 1} (ZMod ℓ)) h).map
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app N) ≫ t) ?_
      refine ((reassoc_of% h2) _).trans ?_
      refine congrArg (fun t => _ ≫ t) ?_
      have h3' := congrArg DerivedCategory.Q.map h3
      simp only [Functor.map_comp] at h3'
      rw [reassoc_of% h3']
      exact congrArg (fun t => _ ≫ t) h4)

/-- **A functor into the derived category all of whose values are concentrated in one degree `j`
is its cohomology in degree `j` placed in degree `j`**, naturally: on such objects the truncation
maps `τ^{<j+1}E ⟶ E` and `τ^{<j+1}E ⟶ τ^{≥j}τ^{<j+1}E` are isomorphisms, and
`τ^{≥j}τ^{<j+1} ≅ H^j ⋙ single j`. -/
def isoHomologyFunctorCompSingleFunctorOfConcentrated {C A : Type*} [Category C] [Category A]
    [Abelian A] [HasDerivedCategory A] (K : C ⥤ DerivedCategory A) (j : ℤ)
    (hK : ∀ X, (K.obj X).IsGE j ∧ (K.obj X).IsLE j) :
    K ≅ K ⋙ DerivedCategory.homologyFunctor A j ⋙ DerivedCategory.singleFunctor A j :=
  have h₁ : ∀ X, IsIso ((Functor.whiskerLeft K
      (DerivedCategory.TStructure.t.truncLTι (j + 1))).app X) := fun X => by
    have := (hK X).2
    exact (DerivedCategory.TStructure.t.isLE_iff_isIso_truncLTι_app j (j + 1) rfl _).1 this
  have h₂ : ∀ X, IsIso ((Functor.whiskerLeft (K ⋙ DerivedCategory.TStructure.t.truncLT (j + 1))
      (DerivedCategory.TStructure.t.truncGEπ j)).app X) := fun X => by
    have := (hK X).1
    change IsIso ((DerivedCategory.TStructure.t.truncGEπ j).app
      ((DerivedCategory.TStructure.t.truncLT (j + 1)).obj (K.obj X)))
    infer_instance
  have : IsIso (Functor.whiskerLeft K (DerivedCategory.TStructure.t.truncLTι (j + 1))) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft (K ⋙ DerivedCategory.TStructure.t.truncLT (j + 1))
      (DerivedCategory.TStructure.t.truncGEπ j)) := NatIso.isIso_of_isIso_app _
  (asIso (Functor.whiskerLeft K (DerivedCategory.TStructure.t.truncLTι (j + 1)))).symm ≪≫
    (Functor.rightUnitor _).symm ≪≫
    asIso (Functor.whiskerLeft (K ⋙ DerivedCategory.TStructure.t.truncLT (j + 1))
      (DerivedCategory.TStructure.t.truncGEπ j)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft K (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor j)

/-- **Cohomology commuting with a colimit, from degree zero to every degree.** For a functor `Φ`
of derived categories commuting with the shift, if the cohomology of `Φ` of an object placed in
degree zero commutes with a colimit in every degree, so does the cohomology of `Φ` of an object
placed in any degree `j`: `single j = single 0 ⋙ [-j]`, `Φ` commutes with `[-j]`, and
`H^n ∘ [-j] = H^{n-j}`. -/
theorem preservesColimit_singleFunctor_comp_homology_of_commShift {J A C : Type*} [Category J]
    [Category A] [Abelian A] [HasDerivedCategory A] [Category C] [Abelian C] [HasDerivedCategory C]
    (Φ : DerivedCategory A ⥤ DerivedCategory C) [Φ.CommShift ℤ] (K : J ⥤ A)
    (h₀ : ∀ n : ℤ, PreservesColimit K
      (DerivedCategory.singleFunctor A 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor C n))
    (j n : ℤ) :
    PreservesColimit K
      (DerivedCategory.singleFunctor A j ⋙ Φ ⋙ DerivedCategory.homologyFunctor C n) := by
  have := h₀ (n - j)
  let e : DerivedCategory.singleFunctor A j ⋙ Φ ⋙ DerivedCategory.homologyFunctor C n ≅
      DerivedCategory.singleFunctor A 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor C (n - j) :=
    Functor.isoWhiskerRight ((DerivedCategory.singleFunctors A).shiftIso (-j) j 0
        (by omega)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Φ.commShiftIso (-j)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((DerivedCategory.homologyFunctor C 0).shiftIso (-j) n (n - j)
          (by omega)))
  exact preservesColimit_of_natIso K e.symm

/-- The inverse image of sheaves of `𝔽_ℓ̲`-modules, being a left adjoint, preserves colimits. -/
private theorem preservesColimitsOfSize_pullbackTopos (m : ℕ) {A B : Scheme.{u}} (f : A ⟶ B) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackTopos :=
  (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f)).leftAdjoint_preservesColimits

/-- **The cohomology of the target of the projection map commutes with filtered colimits in the
sheaf**: for `B ∈ D(Y_étale, 𝔽_ℓ)` concentrated in degree `j` and `h` quasi-compact and
quasi-separated, `N ↦ H^n(Rh_*(h⁻¹N[0] ⊗^L B))` commutes with filtered colimits of sheaves of
`𝔽_ℓ̲`-modules on `X'_étale`. It is `H^n(Rh_*((h⁻¹N ⊗ H^j(B))[j]))`
(`singleFunctorCompPullbackIso`, `singleFunctorTensorHomologyIso`,
`isoHomologyFunctorCompSingleFunctorOfConcentrated`), and each step commutes with filtered
colimits. -/
theorem preservesColimit_projectionMap_target (h : Y ⟶ X') [QuasiCompact h] [QuasiSeparated h]
    (B : DerivedModules (ULift.{u + 1} (ZMod ℓ)) Y) (j : ℤ)
    (hB : ∀ i, i ≠ j → IsZero ((DerivedCategory.homologyFunctor _ i).obj B)) (n : ℤ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X').O)) :
    PreservesColimit K ((DerivedCategory.singleFunctor _ 0 ⋙
      pullback (ULift.{u + 1} (ZMod ℓ)) h ⋙ (tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B ⋙
        pushforward (ULift.{u + 1} (ZMod ℓ)) h) ⋙ DerivedCategory.homologyFunctor _ n) := by
  have hT : ∀ N, ((DerivedCategory.singleFunctor _ 0 ⋙
      (tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B).obj N).IsGE j ∧
      ((DerivedCategory.singleFunctor _ 0 ⋙
        (tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B).obj N).IsLE j := fun N => by
    have hz : ∀ i, i ≠ j → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ 0 ⋙
          (tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B).obj N)) := fun i hi =>
      have := SheafOfModules.preservesColimitsOfSize_sheafTensor_obj.{u + 1, u + 1, u + 1}
        (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O N (Functor.empty _)
      IsZero.of_iso (IsInitial.isZero (IsInitial.isInitialObj
        ((Stacks.SheafOfModules.Tensor.sheafTensor (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O).obj
          N) _ (hB i hi).isInitial)) ((singleFunctorTensorHomologyIso ℓ B i).app N)
    exact ⟨(DerivedCategory.isGE_iff _ _).2 fun i hi => hz i (by omega),
      (DerivedCategory.isLE_iff _ _).2 fun i hi => hz i (by omega)⟩
  have e₁ := Functor.isoWhiskerRight (singleFunctorCompPullbackIso ℓ h)
    ((tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B ⋙ pushforward (ULift.{u + 1} (ZMod ℓ)) h ⋙
      DerivedCategory.homologyFunctor _ n)
  have e₂ := Functor.isoWhiskerLeft (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos
    (Functor.isoWhiskerRight (isoHomologyFunctorCompSingleFunctorOfConcentrated _ j hT)
      (pushforward (ULift.{u + 1} (ZMod ℓ)) h ⋙ DerivedCategory.homologyFunctor _ n))
  have e₃ := Functor.isoWhiskerLeft (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos
    (Functor.isoWhiskerRight (singleFunctorTensorHomologyIso ℓ B j)
      (DerivedCategory.singleFunctor _ j ⋙ pushforward (ULift.{u + 1} (ZMod ℓ)) h ⋙
        DerivedCategory.homologyFunctor _ n))
  have := preservesColimitsOfSize_pullbackTopos ℓ h
  have := preservesColimit_singleFunctor_comp_homology_of_commShift
    (pushforward (ULift.{u + 1} (ZMod ℓ)) h)
    ((K ⋙ (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos) ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
        (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O).flip.obj
        ((DerivedCategory.homologyFunctor _ j).obj B))
    (fun n => preservesColimit_singleFunctor_pushforward_homology ℓ h n _) j n
  have := SheafOfModules.preservesColimitsOfSize_sheafTensor_flip_obj.{u + 1, u + 1, u + 1}
    (ringedTopos (ULift.{u + 1} (ZMod ℓ)) Y).O ((DerivedCategory.homologyFunctor _ j).obj B)
    (K ⋙ (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) h).pullbackTopos)
  exact preservesColimit_of_natIso K (e₁ ≪≫ e₂ ≪≫ e₃).symm

/-- **The projection map at a filtered colimit of sheaves of `𝔽_ℓ̲`-modules**: for
`h : Y ⟶ X'` quasi-compact and quasi-separated, `B ∈ D(Y_étale, 𝔽_ℓ)` concentrated in one degree
and a filtered colimit `N = colim Nᵢ` of sheaves of `𝔽_ℓ̲`-modules on `X'_étale`, if the projection
map `Nᵢ[-k] ⊗^L Rh_*B ⟶ Rh_*(h⁻¹Nᵢ[-k] ⊗^L B)` is invertible for every `i`, it is invertible at
`N`. This is the step "since tensor products commute with filtered colimits and since higher
direct images do too ([Stacks, Tag 09Z1]) we may assume `ℰ` is constructible" of the proof of
[Stacks, Tag 0F1J]: both sides commute with the colimit on cohomology
(`preservesColimit_singleFunctor_tensor_homology`, `preservesColimit_projectionMap_target`). -/
theorem isIso_projectionMap_singleFunctor_of_isColimit (h : Y ⟶ X') [QuasiCompact h]
    [QuasiSeparated h] (B : DerivedModules (ULift.{u + 1} (ZMod ℓ)) Y) (j : ℤ)
    (hB : ∀ i, i ≠ j → IsZero ((DerivedCategory.homologyFunctor _ i).obj B)) (k : ℤ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X').O)) (c : Cocone K) (hc : IsColimit c)
    (hK : ∀ i, IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
      ((DerivedCategory.singleFunctor _ k).obj (K.obj i)) B)) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
      ((DerivedCategory.singleFunctor _ k).obj c.pt) B) :=
  isIso_app_of_isColimit_of_homology _ _
    (Functor.whiskerLeft (DerivedCategory.singleFunctor _ k)
      (projectionNatTrans (ULift.{u + 1} (ZMod ℓ)) h B)) c hc
    (fun n => preservesColimit_singleFunctor_comp_homology_of_commShift
      ((tensor (ULift.{u + 1} (ZMod ℓ)) X').flip.obj
        ((pushforward (ULift.{u + 1} (ZMod ℓ)) h).obj B)) K
      (fun n => preservesColimit_singleFunctor_tensor_homology ℓ K _ n) k n)
    (fun n => preservesColimit_singleFunctor_comp_homology_of_commShift
      (pullback (ULift.{u + 1} (ZMod ℓ)) h ⋙ (tensor (ULift.{u + 1} (ZMod ℓ)) Y).flip.obj B ⋙
        pushforward (ULift.{u + 1} (ZMod ℓ)) h) K
      (fun n => preservesColimit_projectionMap_target ℓ h B j hB n K) k n)
    hK

/-- **The derived inverse image of a sheaf of `𝔽_ℓ̲`-modules placed in degree `k` is its inverse
image placed in degree `k`**: `singleFunctorCompPullbackIso` and the compatibility of `p⁻¹` with
the shift. -/
def pullbackObjSingleFunctorObjIso (p : X' ⟶ X) (k : ℤ)
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O)) :
    (pullback (ULift.{u + 1} (ZMod ℓ)) p).obj ((DerivedCategory.singleFunctor _ k).obj M) ≅
      (DerivedCategory.singleFunctor _ k).obj
        ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) p).pullbackTopos.obj M) :=
  (pullback (ULift.{u + 1} (ZMod ℓ)) p).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso (-k) k 0 (by omega)).app M).symm ≪≫
    ((pullback (ULift.{u + 1} (ZMod ℓ)) p).commShiftIso (-k)).app _ ≪≫
    (shiftFunctor _ (-k)).mapIso ((singleFunctorCompPullbackIso ℓ p).app M) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (-k) k 0 (by omega)).app _

open Stacks.EtaleCohomology.BaseChangeOverField in
/-- **The projection map of [Stacks, Tag 0F1J] at a single sheaf of `𝔽_ℓ`-vector spaces, over a
quasi-compact quasi-separated `X`.** In the setting of Tag 0F1J (`X' = X ×_S S'`,
`Y = X' ×_{S'} T`, `g` quasi-compact and quasi-separated), for every sheaf `ℰ` of `𝔽_ℓ̲`-modules
on `X_étale` and every sheaf `𝒢` of `𝔽_ℓ̲`-modules on `T_étale`, the projection map

`p⁻¹ℰ[-k] ⊗^L Rh_*(e⁻¹𝒢[-j]) ⟶ Rh_*(h⁻¹p⁻¹ℰ[-k] ⊗^L e⁻¹𝒢[-j])`

is invertible. The source's argument: `ℰ` is a filtered colimit of constructible sheaves
([Stacks, Tag 03SA], `exists_isColimit_isConstructibleEtaleModule`), `p⁻¹` commutes with it, the
projection map is invertible at a filtered colimit if it is at every term
(`isIso_projectionMap_singleFunctor_of_isColimit`, Tag 09Z1), and at a constructible sheaf it is
`isIso_projectionMap_pullback_singleFunctor_of_isConstructibleEtaleModule`.

Not registered: derived base change along `X ⟶ S` and along every finite `X`-scheme are the
explicit arguments `hBC` and `hBCfin`. -/
theorem isIso_projectionMap_pullback_singleFunctor_of_compactSpace
    {S X' S' T Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX ℓ)
    (hBCfin : ∀ {Z : Scheme.{u}} (π : Z ⟶ X) [IsFinite π], DerivedBaseChangeHolds (π ≫ πX) ℓ)
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O))
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) T).O)) (k j : ℤ) :
    IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
      ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj ((DerivedCategory.singleFunctor _ k).obj M))
      ((pullback (ULift.{u + 1} (ZMod ℓ)) e).obj ((DerivedCategory.singleFunctor _ j).obj G))) := by
  have : QuasiCompact h := MorphismProperty.of_isPullback hY.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback hY.flip inferInstance
  let B := (pullback (ULift.{u + 1} (ZMod ℓ)) e).obj ((DerivedCategory.singleFunctor _ j).obj G)
  have hGE : B.IsGE j := isGE_pullback_obj _ e _ j inferInstance
  have hLE : B.IsLE j := isLE_pullback_obj _ e _ j inferInstance
  have hB : ∀ i, i ≠ j → IsZero ((DerivedCategory.homologyFunctor _ i).obj B) := fun i hi => by
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE B j i hi
    · exact DerivedCategory.isZero_of_isLE B j i hi
  have hbc := isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds ℓ πX hBC s p f'
    hX' g h e hY G j
  have hcons : ∀ D : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod ℓ)) X).O), IsConstructibleEtaleModule ℓ X D →
      IsIso (projectionMap (ULift.{u + 1} (ZMod ℓ)) h
        ((DerivedCategory.singleFunctor _ k).obj
          ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) p).pullbackTopos.obj D)) B) := by
    intro D hD
    refine (isIso_projectionMap_iff_of_iso _ h (pullbackObjSingleFunctorObjIso ℓ p k D) B).1 ?_
    refine (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _ hbc).1 ?_
    refine ((tensorBaseChangeNatTransRight _ f' g h e hY.w _).isIso_app_iff_of_iso
      (X := DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ j).obj G))
      (Y := (DerivedCategory.singleFunctor _ j).obj G)
      ((DerivedCategory.Plus.singleFunctorιIso _ j).app G)).1 ?_
    refine (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _
      (isIso_baseChangeMap_app_of_derivedBaseChangeHolds ℓ πX hBC s p f' hX' g h e hY
        ((DerivedCategory.Plus.singleFunctor _ j).obj G))).2 ?_
    exact isIso_projectionMap_pullback_singleFunctor_of_isConstructibleEtaleModule ℓ πX s p f' hX'
      g h e hY hBC hBCfin _ D hD k
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ := exists_isColimit_isConstructibleEtaleModule ℓ M
  have := preservesColimitsOfSize_pullbackTopos ℓ p
  refine (isIso_projectionMap_iff_of_iso _ h (pullbackObjSingleFunctorObjIso ℓ p k M) B).2 ?_
  exact isIso_projectionMap_singleFunctor_of_isColimit ℓ h B j hB k
    (D ⋙ (ringedToposHom (ULift.{u + 1} (ZMod ℓ)) p).pullbackTopos)
    ((ringedToposHom (ULift.{u + 1} (ZMod ℓ)) p).pullbackTopos.mapCocone (Cocone.mk M ι))
    (isColimitOfPreserves _ hc) (fun i => hcons _ (hD i))

open Stacks.EtaleCohomology.BaseChangeOverField in
/-- **[Stacks, Tag 0F1J] for `n = ℓ` prime over a quasi-compact quasi-separated `X`, from derived
base change.** In the setting of Tag 0F1J (`X' = X ×_S S'`, `Y = X' ×_{S'} T`, `g`
quasi-compact and quasi-separated), the canonical map

`p⁻¹E ⊗^L_{𝔽_ℓ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{𝔽_ℓ} e⁻¹F)`

is invertible for `E ∈ D(X_étale, 𝔽_ℓ)` of Tor amplitude in `[a, ∞]` and `F ∈ D⁺(T_étale, 𝔽_ℓ)`.
The first two paragraphs of the source's proof reduce to a single flat sheaf `ℰ` and a single
sheaf `𝒢` (`isIso_tensorBaseChangeMap_of_isIso_single`); there the base change map is invertible
(`hBC`), and the projection map is `isIso_projectionMap_pullback_singleFunctor_of_compactSpace`.

Not registered: derived base change along `X ⟶ S` and along every finite `X`-scheme are the
explicit arguments `hBC` and `hBCfin` ([Stacks, Tag 0F1I] for `S = Spec K`). -/
theorem isIso_tensorBaseChangeMap_of_compactSpace
    {S X' S' T Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (πX : X ⟶ S)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (hX' : IsPullback p f' πX s) (g : T ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (hBC : DerivedBaseChangeHolds πX ℓ)
    (hBCfin : ∀ {Z : Scheme.{u}} (π : Z ⟶ X) [IsFinite π], DerivedBaseChangeHolds (π ≫ πX) ℓ)
    (E : DerivedModules (ULift.{u + 1} (ZMod ℓ)) X) (a : ℤ)
    (hE : HasTorAmplitudeGE (ULift.{u + 1} (ZMod ℓ)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod ℓ)) T) (b : ℤ) (hF : F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod ℓ)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod ℓ)) p).obj E) F) :=
  isIso_tensorBaseChangeMap_of_isIso_single _ p f' g h e hY.w
    (fun M _ G i j => (isIso_tensorBaseChangeMap_iff_isIso_projectionMap _ f' g h e hY.w _ _
      (isIso_baseChangeMap_app_singleFunctor_of_derivedBaseChangeHolds ℓ πX hBC s p f' hX' g h e
        hY G j)).2
      (isIso_projectionMap_pullback_singleFunctor_of_compactSpace ℓ πX s p f' hX' g h e hY hBC
        hBCfin M G i j))
    E a hE F b hF

end Stacks.EtaleCohomology.EtaleCoefficients

end
