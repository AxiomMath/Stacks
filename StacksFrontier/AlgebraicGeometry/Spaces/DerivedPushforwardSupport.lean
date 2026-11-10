module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Derived direct image preserves supports over a closed subset

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `T ⊆ |X|` a closed
subset. If every cohomology sheaf of `E ∈ D(𝒪_Y)` is supported on `|f|⁻¹T`, then every
cohomology sheaf of `Rf_*E` is supported on `T`, so `Rf_*` carries `D_{|f^{-1}T|}(𝒪_Y)` into
`D_T(𝒪_X)` (Stacks 0AFJ).

## Main definitions

* `AlgebraicGeometry.Space.preimageOpenSubspaceHom`: the projection `f⁻¹U ⟶ U` of the inverse
  image of an open subspace.

## Main results

* `AlgebraicGeometry.Space.isPullback_preimageOpenSubspace`: `f⁻¹U` is the fibre product
  `Y ×_X U` in the category of algebraic spaces.
* `AlgebraicGeometry.Space.supportOfSheaf_homology_modulePushforward_subset`: the statement on a
  K-injective complex.
* `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward`: the
  statement, for any right derived functor of `modulePushforward` and any model of the derived
  categories. At the standard model the support condition is
  `AlgebraicGeometry.Space.CohomologySupportedOn` of Stacks 08GF, by
  `AlgebraicGeometry.Space.cohomologySupportedOn_eq_derivedCategoryB`.

## References

* [Stacks Project, Tag 0AFJ](https://stacks.math.columbia.edu/tag/0AFJ)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image of an open subspace as a fibre product -/

section Preimage

variable {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (U : Subfunctor X.1)
  (hU : IsOpenSubspace B S hS U)

/-- The projection `f⁻¹U ⟶ U` from the inverse image of an open subspace. -/
def preimageOpenSubspaceHom :
    openSubspaceSpace B S hS (U.preimage f.hom)
        (isOpenSubspace_preimage B S hS f.hom U X.2 Y.2 hU) ⟶
      openSubspaceSpace B S hS U hU :=
  ObjectProperty.homMk (U.fromPreimage f.hom)

/-- **The inverse image of an open subspace is the fibre product** `Y ×_X U`, in the category of
algebraic spaces. -/
theorem isPullback_preimageOpenSubspace :
    IsPullback
      (openSubspaceHom B S hS (U.preimage f.hom)
        (isOpenSubspace_preimage B S hS f.hom U X.2 Y.2 hU))
      (preimageOpenSubspaceHom B S hS f U hU) f (openSubspaceHom B S hS U hU) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (Subfunctor.isPullback_preimage f.hom U).w.symm)
    (Subfunctor.isPullback_preimage f.hom U).flip

end Preimage

/-- A point of the inverse image `f⁻¹U` of a subfunctor maps into the points of `U`. -/
theorem pointsMap_preimage_mem_range {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X)
    (U : Subfunctor X) (v : points B S hS (U.preimage f).toFunctor) :
    pointsMap B S hS Y f (pointsMap B S hS _ (U.preimage f).ι v) ∈
      Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  have e1 := pointsMap_comp_apply B S hS (U.fromPreimage f) U.ι v
  have e2 := pointsMap_comp_apply B S hS (U.preimage f).ι f v
  rw [Subfunctor.fromPreimage_ι] at e1
  exact ⟨_, e1.symm.trans e2⟩

/-! ### Supports -/

section Support

variable {X : AlgebraicSpaces B S hS}

/-- Supports are invariant under isomorphism of modules. -/
theorem supportOfSheaf_toSheaf_eq_of_iso {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) :=
  have : Mono e.hom := @IsIso.mono_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
  have : Mono e.inv := @IsIso.mono_of_iso _ _ _ _ e.inv (Iso.isIso_inv e)
  (supportOfSheaf_toSheaf_subset_of_mono B S hS X e.hom).antisymm
    (supportOfSheaf_toSheaf_subset_of_mono B S hS X e.inv)

/-- The support of the `n`-th cohomology of an object of the derived category only depends on
a representing complex. -/
private theorem supportOfSheaf_homologyFunctor_eq {X : AlgebraicSpaces B S hS}
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    {A : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    {K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ} (e : A ≅ DerivedCategory.Q.obj K)
    (n : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj A)) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (K.homology n)) :=
  supportOfSheaf_toSheaf_eq_of_iso B S hS
    ((DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _)

end Support

section Pushforward

variable {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- **The cohomology of `f_*I` is supported on a closed subset `T`** when `I` is a K-injective
complex of `𝒪_Y`-modules whose cohomology is supported on `|f|⁻¹T`. -/
theorem supportOfSheaf_homology_modulePushforward_subset (T : Set (points B S hS X.1))
    (hT : IsClosed T) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hI : CochainComplex.IsKInjective I)
    (hIT : ∀ n, supportOfSheaf B S hS Y.1
      ((SheafOfModules.toSheaf _).obj (I.homology n)) ⊆ pointsMap B S hS Y.1 f.hom ⁻¹' T)
    (n : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      ((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology n))
      ⊆ T := by
  let W := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  have hW : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) = Tᶜ := by
    rw [← openSubspacesOrderIso_apply B S hS X.1 X.2 W]
    simp [W]
  let U := W.1
  have hU : IsOpenSubspace B S hS U := W.2
  have hV := isOpenSubspace_preimage B S hS f.hom U X.2 Y.2 hU
  let j := openSubspaceHom B S hS U hU
  let hj := isEtale_openSubspaceHom B S hS U hU
  let i := openSubspaceHom B S hS (U.preimage f.hom) hV
  let hi := isEtale_openSubspaceHom B S hS (U.preimage f.hom) hV
  let f' := preimageOpenSubspaceHom B S hS f U hU
  have sq := isPullback_preimageOpenSubspace B S hS f U hU
  have := etaleModulePullback_additive B S hS j hj
  have := preservesFiniteLimits_etaleModulePullback B S hS j hj
  have := preservesFiniteColimits_etaleModulePullback B S hS j hj
  have := etaleModulePullback_additive B S hS i hi
  have := preservesFiniteLimits_etaleModulePullback B S hS i hi
  have := preservesFiniteColimits_etaleModulePullback B S hS i hi
  let J := ((etaleModulePullback.{u, u} B S hS i hi).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have hJK : CochainComplex.IsKInjective J := isKInjective_etaleModulePullback B S hS i hi
    (etaleModuleLowerShriekAdjunction B S hS i hi) I hI
  have hJ : J.Acyclic := by
    intro m
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine IsZero.of_iso ?_
      (((etaleModulePullback.{u, u} B S hS i hi).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) m).app I)
    refine (supportOfSheaf_eq_empty_iff_isZero B S hS _ _).1 ?_
    refine Set.eq_empty_of_forall_notMem fun v hv => ?_
    have h := pointsMap_preimage_mem_range B S hS f.hom U v
    rw [hW] at h
    exact h (hIT m ((Set.ext_iff.1
      (supportOfSheaf_toSheaf_etaleModulePullback B S hS i hi (I.homology m)) v).1 hv))
  have hJ0 : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id]
    exact (HomotopyCategory.quotient_map_eq_zero_iff (𝟙 J)).2
      (hJK.nonempty_homotopy_zero (𝟙 J) hJ)
  have hZ : IsZero ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
    ((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ)).map_isZero hJ0
  have hZn : IsZero ((((modulePushforward B S hS f').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J).homology n) :=
    ((HomotopyCategory.homologyFunctor _ (ComplexShape.up ℤ) n).map_isZero hZ).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) n).app _).symm
  let e : ((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((modulePushforward B S hS f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
    ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (modulePushforward B S hS f ⋙ etaleModulePullback.{u, u} B S hS j hj))
        (ComplexShape.up ℤ)).app I).symm ≪≫
      ((NatIso.mapHomologicalComplex (modulePushforwardEtaleBaseChangeIso B S hS i f' f j sq hj)
        (ComplexShape.up ℤ)).app I).symm ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePullback.{u, u} B S hS i
            (isEtale_of_isPullback B S hS f' i j f sq.flip hj) ⋙
          modulePushforward B S hS f')) (ComplexShape.up ℤ)).app I
  have hjZ : IsZero ((etaleModulePullback.{u, u} B S hS j hj).obj
      ((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
        n)) :=
    hZn.of_iso ((((etaleModulePullback.{u, u} B S hS j hj).mapHomologicalComplexHomologyIso
      (ComplexShape.up ℤ) n).app _).symm ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso e)
  intro x hx
  by_contra hxT
  obtain ⟨w, rfl⟩ : x ∈ Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := hW ▸ hxT
  have hw := (Set.ext_iff.1 (supportOfSheaf_toSheaf_etaleModulePullback B S hS j hj
    ((((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
      n)) w).2 hx
  rwa [(supportOfSheaf_eq_empty_iff_isZero B S hS _ _).2 hjZ] at hw

/-- **Derived direct image preserves supports over a closed subset.** Let `f : Y ⟶ X` be a
morphism of algebraic spaces, `T ⊆ |X|` closed, and `Rf` any right derived functor of
`AlgebraicGeometry.Space.modulePushforward`, presented by its unit `αf`, for any models of the
derived categories. If every cohomology sheaf of `E ∈ D(𝒪_Y)` is supported on `|f|⁻¹T`, then
every cohomology sheaf of `Rf E` is supported on `T`. -/
theorem derivedCategoryB_supportedModules_derivedPushforward
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
    [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (Rf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : DerivedCategoryB.derivedCategoryB
      (supportedModules B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T)) E) :
    DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) (Rf.obj E) := by
  obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2
    (DerivedCategory.Q.objPreimage E)
  have eE : E ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map g)
  have hα := isIso_app_of_isKInjective_modulePushforward B S hS f DerivedCategory.Qh Rf αf I hI
  have eR : Rf.obj E ≅ DerivedCategory.Q.obj
      (((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    Rf.mapIso (eE ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm) ≪≫
      (asIso (αf.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  intro n
  change supportOfSheaf B S hS X.1 _ ⊆ T
  rw [supportOfSheaf_homologyFunctor_eq B S hS eR]
  refine supportOfSheaf_homology_modulePushforward_subset B S hS f T hT I hI (fun m => ?_) n
  have h := hE m
  change supportOfSheaf B S hS Y.1 _ ⊆ _ at h
  rwa [supportOfSheaf_homologyFunctor_eq B S hS eE] at h

end Pushforward

end AlgebraicGeometry.Space

end
