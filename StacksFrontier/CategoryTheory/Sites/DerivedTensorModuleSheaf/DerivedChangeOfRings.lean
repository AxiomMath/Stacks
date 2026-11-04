module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Basic
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings
public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.Homology.KFlat.BifunctorOneSided
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Derived change of rings for sheaves of modules

Let `(C, J)` be a site and `f : Λ →+* S` a homomorphism of commutative rings. Restriction of
scalars is exact, so it induces a functor `D(C, S) ⥤ D(C, Λ)` on derived categories. Extension
of scalars has a left derived functor `D(C, Λ) ⥤ D(C, S)`, computed on K-flat complexes:
extension of scalars carries quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. It satisfies the projection formula

`N ⊗_S^L (K ⊗_Λ^L S) ≅ N ⊗_Λ^L K`

in `D(C, Λ)`, for `K` in `D(C, Λ)` and `N` in `D(C, S)`.

## Main definitions

* `Stacks.ModuleSheaf.restrictScalarsTotalComplexIso`: the projection formula for total tensor
  complexes, `Tot(N ⊗_S (S ⊗_Λ P)) ≅ Tot(N ⊗_Λ P)` over `Λ`.
* `Stacks.ModuleSheaf.derivedExtendScalars`: the derived extension of scalars
  `K ↦ K ⊗_Λ^L S`.
* `Stacks.ModuleSheaf.derivedExtendScalarsObjIso`: on a K-flat complex it is extension of
  scalars applied termwise.

## Main results

* `Stacks.ModuleSheaf.kFlat_extendScalars`: extension of scalars preserves K-flatness.
* `Stacks.ModuleSheaf.acyclic_extendScalars_of_kFlat`,
  `Stacks.ModuleSheaf.quasiIso_extendScalars_map_of_kFlat`: extension of scalars carries acyclic
  K-flat complexes to acyclic complexes, and quasi-isomorphisms between K-flat complexes to
  quasi-isomorphisms.
* `Stacks.ModuleSheaf.nonempty_restrictScalars_tensor_derivedExtendScalars_iso`: the projection
  formula.
* `Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso`: read over `Λ`, the
  derived extension of scalars is the derived tensor product with the constant sheaf `S`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ S : Type w} [CommRing Λ] [CommRing S] [UnivLE.{max u v, w}] (f : Λ →+* S)

/-! ### Exactness of restriction of scalars -/

/-- Restriction of scalars of sheaves of modules preserves limits. -/
instance : PreservesLimitsOfSize.{w, w} (restrictScalars J f) :=
  (extendRestrictScalarsAdj J f).rightAdjoint_preservesLimits

/-- Restriction of scalars of sheaves of modules preserves colimits. -/
instance : PreservesColimitsOfSize.{w, w} (restrictScalars J f) :=
  (restrictCoextendScalarsAdj J f).leftAdjoint_preservesColimits

/-- Restriction of scalars of sheaves of modules preserves colimits indexed by categories in
universe `0`. -/
instance : PreservesColimitsOfSize.{0, 0} (restrictScalars J f) :=
  preservesColimitsOfSize_shrink _

/-- Restriction of scalars of sheaves of modules preserves finite limits. -/
instance : PreservesFiniteLimits (restrictScalars J f) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction of scalars of sheaves of modules preserves finite colimits. -/
instance : PreservesFiniteColimits (restrictScalars J f) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-! ### The projection formula on total complexes -/

/-- The bifunctor `(N, F) ↦ N ⊗_S (S ⊗_Λ F)`. -/
abbrev tensorExtendScalars :
    Sheaf J (ModuleCat.{w} S) ⥤ Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} S) :=
  curriedTensor _ ⋙ (Functor.whiskeringLeft _ _ _).obj (extendScalars J f)

/-- For fixed `N`, the functor `F ↦ N ⊗_S (S ⊗_Λ F)` is additive. -/
instance (N : Sheaf J (ModuleCat.{w} S)) : ((tensorExtendScalars J f).obj N).Additive :=
  inferInstanceAs (extendScalars J f ⋙ tensorLeft N).Additive

/-- The bifunctor `(N, F) ↦ N ⊗_S (S ⊗_Λ F)` is additive in `N`. -/
instance : (tensorExtendScalars J f).Additive where
  map_add {N N'} {g g'} := by
    ext F : 2
    exact MonoidalPreadditive.add_whiskerRight g g'

/-- **The projection formula for complexes**: for a complex `N` of sheaves of `S`-modules and a
complex `P` of sheaves of `Λ`-modules, the total complex `Tot(N ⊗_S (S ⊗_Λ P))`, read over `Λ`,
is `Tot(N ⊗_Λ P)`. Termwise this is the projection formula for sheaves,
`Stacks.ModuleSheaf.restrictScalarsTensorExtendScalarsIso`. -/
def restrictScalarsTotalComplexIso (N : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ)
    (P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    ((restrictScalars J f).mapHomologicalComplex _).obj
        (totalComplex (curriedTensor _) N
          (((extendScalars J f).mapHomologicalComplex _).obj P)) ≅
      totalComplex (curriedTensor _) (((restrictScalars J f).mapHomologicalComplex _).obj N)
        P :=
  Functor.mapBifunctorTotalIso (tensorExtendScalars J f) (curriedTensor _)
    (restrictScalars J f) (𝟭 _) (restrictScalars J f)
    (fun N F => (restrictScalarsTensorExtendScalarsIso J f).app (N, F))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (fun {N N'} g F => by
      simpa using (restrictScalarsTensorExtendScalarsIso J f).hom.naturality
        ((g, 𝟙 F) : (N, F) ⟶ (N', F)))
    (fun N {F F'} g => by
      simpa using (restrictScalarsTensorExtendScalarsIso J f).hom.naturality
        ((𝟙 N, g) : (N, F) ⟶ (N, F')))
    N P

/-! ### K-flatness -/

/-- If `Tot(N ⊗_Λ P)` is acyclic over `Λ`, then so is `Tot(N ⊗_S (S ⊗_Λ P))` over `S`. -/
private theorem acyclic_totalComplex_extendScalars_of_acyclic_restrictScalars
    {N : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (h : (totalComplex (curriedTensor _) (((restrictScalars J f).mapHomologicalComplex _).obj N)
      P).Acyclic) :
    (totalComplex (curriedTensor _) N
      (((extendScalars J f).mapHomologicalComplex _).obj P)).Acyclic :=
  (HomologicalComplex.acyclic_map_iff_of_preservesHomology _ (restrictScalars J f)).1
    fun n => (h n).of_iso (restrictScalarsTotalComplexIso J f N P).symm

/-- **Extension of scalars preserves K-flatness**: if `P` is a K-flat complex of sheaves of
`Λ`-modules, then `S ⊗_Λ P` is a K-flat complex of sheaves of `S`-modules. -/
theorem kFlat_extendScalars {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor _) P) :
    KFlat (curriedTensor _) (((extendScalars J f).mapHomologicalComplex _).obj P) := fun N hN =>
  acyclic_totalComplex_extendScalars_of_acyclic_restrictScalars J f
    (hP _ ((HomologicalComplex.acyclic_map_iff_of_preservesHomology N (restrictScalars J f)).2 hN))

/-- **Extension of scalars carries acyclic K-flat complexes to acyclic complexes.** -/
theorem acyclic_extendScalars_of_kFlat {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor _) P) (hac : P.Acyclic) :
    (((extendScalars J f).mapHomologicalComplex _).obj P).Acyclic := by
  let U := 𝟙_ (CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ)
  obtain ⟨Q, q, hQ, hq⟩ :=
    exists_kFlat_quasiIso (((restrictScalars J f).mapHomologicalComplex _).obj U)
  exact fun n => (acyclic_totalComplex_extendScalars_of_acyclic_restrictScalars J f
    (acyclic_totalComplex_of_kFlat_of_acyclic (curriedTensor _) hP hac q hq
      (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hQ)) n).of_iso (λ_ _)

/-- **Extension of scalars carries quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms.** -/
theorem quasiIso_extendScalars_map_of_kFlat {P P' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (φ : P ⟶ P') (hP : KFlat (curriedTensor _) P) (hP' : KFlat (curriedTensor _) P')
    (hφ : QuasiIso φ) : QuasiIso (((extendScalars J f).mapHomologicalComplex _).map φ) := by
  rw [quasiIso_iff_acyclic_mappingCone] at hφ ⊢
  have hcone : KFlat (curriedTensor _) (CochainComplex.mappingCone φ) :=
    kFlat_obj₃_of_distTriang _ _ _ _ (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      hP hP'
  exact fun n => (acyclic_extendScalars_of_kFlat J f hcone hφ n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ (extendScalars J f))

/-! ### Derived extension of scalars -/

section DerivedExtendScalars

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))]

/-- Extension of scalars on the K-flat objects of the homotopy category, landing in the derived
category. -/
abbrev extendScalarsKFlat :
    (kFlatObjects (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))).FullSubcategory ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} S)) :=
  (kFlatObjects _).ι ⋙ (extendScalars J f).mapHomotopyCategory _ ⋙ DerivedCategory.Qh

omit [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] in
/-- Extension of scalars on K-flat objects, landing in the derived category, inverts
quasi-isomorphisms. -/
theorem extendScalarsKFlat_inverts :
    (kFlatQuasiIso (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))).IsInvertedBy
      (extendScalarsKFlat J f) := by
  intro X Y φ hφ
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient _ _).map_surjective ((kFlatObjects _).ι.map φ)
  have hg' : QuasiIso g := by
    rwa [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      hg]
  have key : IsIso (DerivedCategory.Qh.map (((extendScalars J f).mapHomotopyCategory _).map
      ((HomotopyCategory.quotient _ _).map g))) := by
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2
          (quasiIso_extendScalars_map_of_kFlat J f g X.2 Y.2 hg')))
  show IsIso (DerivedCategory.Qh.map (((extendScalars J f).mapHomotopyCategory _).map
    ((kFlatObjects _).ι.map φ)))
  exact hg ▸ key

/-- **The derived extension of scalars** `D(C, Λ) ⥤ D(C, S)`, `K ↦ K ⊗_Λ^L S`: the descent of
termwise extension of scalars on K-flat complexes. -/
def derivedExtendScalars :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤ DerivedCategory (Sheaf J (ModuleCat.{w} S)) :=
  Localization.lift (extendScalarsKFlat J f) (extendScalarsKFlat_inverts J f)
    (kFlatQ (curriedTensor (Sheaf J (ModuleCat.{w} Λ))))

/-- **On a K-flat complex the derived extension of scalars is termwise extension of
scalars.** -/
def derivedExtendScalarsObjIso {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor _) P) :
    (derivedExtendScalars J f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((extendScalars J f).mapHomologicalComplex _).obj P) :=
  (derivedExtendScalars J f).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    (Localization.fac (extendScalarsKFlat J f) (extendScalarsKFlat_inverts J f)
      (kFlatQ (curriedTensor (Sheaf J (ModuleCat.{w} Λ))))).app
        ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩ ≪≫
    DerivedCategory.Qh.mapIso (((extendScalars J f).mapHomotopyCategoryFactors _).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

end DerivedExtendScalars

/-! ### The derived projection formula -/

section Derived

variable {J}

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} S))]

/-- **The derived projection formula.** For `K` in `D(C, Λ)` and `N` in `D(C, S)`, the derived
tensor product `N ⊗_S^L (K ⊗_Λ^L S)`, read over `Λ`, is `N ⊗_Λ^L K`. -/
theorem nonempty_restrictScalars_tensor_derivedExtendScalars_iso
    (N : DerivedCategory (Sheaf J (ModuleCat.{w} S)))
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    Nonempty ((restrictScalars J f).mapDerivedCategory.obj (N ⊗ (derivedExtendScalars J f).obj K) ≅
      (restrictScalars J f).mapDerivedCategory.obj N ⊗ K) := by
  let R := restrictScalars J f
  obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let eP : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let N₀ := DerivedCategory.Q.objPreimage N
  let eN : DerivedCategory.Q.obj N₀ ≅ N := DerivedCategory.Q.objObjPreimageIso N
  exact ⟨R.mapDerivedCategory.mapIso ((eN.symm ⊗ᵢ ((derivedExtendScalars J f).mapIso eP.symm ≪≫
        derivedExtendScalarsObjIso J f hP)) ≪≫
      derivedTensorIsoOfKFlat N₀ (kFlat_extendScalars J f hP)) ≪≫
    R.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (restrictScalarsTotalComplexIso J f N₀ P) ≪≫
    (derivedTensorIsoOfKFlat _ hP).symm ≪≫
    (((R.mapDerivedCategoryFactors.app N₀).symm ≪≫ R.mapDerivedCategory.mapIso eN) ⊗ᵢ eP)⟩

/-- **The derived extension of scalars, read over `Λ`, is the derived tensor product with `S`**:
`K ⊗_Λ^L S` regarded in `D(C, Λ)` is `S ⊗_Λ^L K`, with `S` the constant sheaf in degree zero. -/
theorem nonempty_restrictScalars_derivedExtendScalars_iso
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    Nonempty ((restrictScalars J f).mapDerivedCategory.obj ((derivedExtendScalars J f).obj K) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J (ModuleCat.{w} Λ)).obj
        ((ModuleCat.restrictScalars.{w} f).obj (ModuleCat.of S S))) ⊗ K) := by
  let R := restrictScalars J f
  obtain ⟨e⟩ := nonempty_restrictScalars_tensor_derivedExtendScalars_iso f
    (𝟙_ (DerivedCategory (Sheaf J (ModuleCat.{w} S)))) K
  refine ⟨R.mapDerivedCategory.mapIso (λ_ _).symm ≪≫ e ≪≫ (?_ ⊗ᵢ Iso.refl K)⟩
  exact R.mapDerivedCategory.mapIso
      (CochainComplex.KFlatMonoidal.derivedUnitIso _ (exists_kFlat_quasiIso (J := J) (Λ := S)) ≪≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).symm.app _) ≪≫
    (R.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((restrictScalarsConstantSheafIso J f).app (ModuleCat.of S S))

end Derived

end Stacks.ModuleSheaf
