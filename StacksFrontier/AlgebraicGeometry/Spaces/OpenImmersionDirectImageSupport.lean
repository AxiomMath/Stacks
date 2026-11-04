module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePresentationOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits

/-!
# Direct image along an open immersion of a module supported in the open

Let `j : U ⟶ X` be an open immersion of algebraic spaces.  A module on `X` whose support is closed
and contained in `|U|` is determined by its restriction to `U`, and a module on `U` whose support
has closed image in `|X|` has a direct image as well behaved as itself.  This file proves the
statements of that kind used by the Quot functor of an open subspace, Stacks 0DP3, where the
supports in question are those of quotients with support proper over the base.

Restriction along `j` is exact and its counit `j^*j_* ⟶ 𝟭` is an isomorphism (Stacks 03LV), so a
morphism into, respectively out of, a module supported in `|U|` is an epimorphism, respectively a
monomorphism, as soon as its restriction is: the cokernel, respectively the kernel, is supported in
`|U|` and restricts to zero.  This gives the surjectivity of `A ⟶ j_*Q` for the adjoint of a
surjection `j^*A ⟶ Q`; the invertibility of the unit `M ⟶ j_*j^*M` for `M` with closed support in
`|U|` is `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset`.

## Main results

* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.mono_of_mono_modulePullback_of_isOpenImmersion`: epimorphisms into and
  monomorphisms out of modules supported in `|U|` are detected after restriction.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion`:
  `Supp(j_*Q) = |j|(Supp Q)` when the right side is closed.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePushforward_of_isOpenImmersion`,
  `AlgebraicGeometry.Space.isFlatOver_modulePushforward_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.hasProperSupport_modulePushforward_of_isOpenImmersion`: finite
  presentation, flatness over a base and proper support pass to `j_*Q`.
* `AlgebraicGeometry.Space.conjSubobject_extendSubobject` and
  `AlgebraicGeometry.Space.extendSubobject_eq_of_isIso_unit`: restriction of quotients and direct
  image of quotients are mutually inverse on the quotients concerned.

## Implementation notes

Finite presentation of `j_*Q` is local on the cover of `X` by `U` and by the complement of the
image of the support of `Q`, on which `j_*Q` vanishes; that locality is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isOpenImmersion_cover`.  Flatness is read on
geometric stalks, a geometric point of `X` with image in `|U|` lifting to `U`.

The cokernels in the last section are those of the abelian structure on the modules, the ones the
quotients of Stacks 082M are formed with; the separately constructed cokernel instance of
`AlgebraicGeometry.Space.hasCokernel_modules` is removed there for that reason.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-- Inverse image along an étale morphism is left exact. -/
theorem preservesFiniteLimits_modulePullback_of_isEtale (f : U ⟶ X)
    (hf : IsEtale B S hS f.hom) : PreservesFiniteLimits (modulePullback B S hS f) :=
  have := preservesFiniteLimits_etaleModulePullback B S hS f hf
  preservesFiniteLimits_of_natIso (modulePullbackIsoEtaleModulePullback B S hS f hf).symm

/-- The restriction of the adjoint of a morphism `j^*A ⟶ Q`, followed by the counit, is that
morphism. -/
theorem modulePullback_map_homEquiv_comp_counit (j : U ⟶ X) (A : Modules.{u, u} B S hS X.1 X.2)
    (Q : Modules.{u, u} B S hS U.1 U.2) (ψ : (modulePullback B S hS j).obj A ⟶ Q) :
    (modulePullback B S hS j).map ((modulePullbackAdjunction B S hS j).homEquiv A Q ψ) ≫
      (modulePullbackAdjunction B S hS j).counit.app Q = ψ := by
  have h := (modulePullbackAdjunction B S hS j).homEquiv_counit
    (X := A) (Y := Q) (g := (modulePullbackAdjunction B S hS j).homEquiv A Q ψ)
  exact h.symm.trans (Equiv.symm_apply_apply _ _)

/-- A module supported in the image of an open immersion vanishes as soon as its restriction
does. -/
theorem isZero_of_supportOfSheaf_subset_range_of_isZero_modulePullback (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS U.1 j.hom))
    (h : IsZero ((modulePullback B S hS j).obj M)) : IsZero M := by
  refine isZero_of_supportOfSheaf_eq_empty B S hS X M ?_
  have h0 : supportOfSheaf B S hS U.1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS j).obj M)) = ∅ :=
    (supportOfSheaf_eq_empty_iff_isZero B S hS U _).mpr h
  rw [supportOfSheaf_modulePullback_of_isEtale B S hS j (isEtale_of_isOpenImmersion B S hS hj)]
    at h0
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨y, rfl⟩ := hM hx
  exact (Set.eq_empty_iff_forall_notMem.mp h0) y hx

/-- **A morphism into a module supported in the image of an open immersion is an epimorphism as
soon as its restriction is.** The cokernel is supported in the support of the target, and its
restriction is the cokernel of the restriction, which vanishes. -/
theorem epi_of_epi_modulePullback_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hN : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS U.1 j.hom))
    (h : Epi ((modulePullback B S hS j).map φ)) : Epi φ := by
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS j) :=
    (modulePullbackAdjunction B S hS j).leftAdjoint_preservesColimits
  have : (modulePullback B S hS j).IsLeftAdjoint := ⟨_, ⟨modulePullbackAdjunction B S hS j⟩⟩
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback B S hS j)
  refine (Preadditive.epi_iff_isZero_cokernel φ).mpr ?_
  refine isZero_of_supportOfSheaf_subset_range_of_isZero_modulePullback B S hS j hj _
    ((supportOfSheaf_toSheaf_subset_of_epi B S hS X (cokernel.π φ)).trans hN) ?_
  exact (Iso.isZero_iff (PreservesCokernel.iso (modulePullback B S hS j) φ)).mpr
    ((Preadditive.epi_iff_isZero_cokernel _).mp h)

/-- **A morphism out of a module supported in the image of an open immersion is a monomorphism as
soon as its restriction is.** The kernel is supported in the support of the source, and its
restriction is the kernel of the restriction, which vanishes. -/
theorem mono_of_mono_modulePullback_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hM : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS U.1 j.hom))
    (h : Mono ((modulePullback B S hS j).map φ)) : Mono φ := by
  have := preservesFiniteLimits_modulePullback_of_isEtale B S hS j
    (isEtale_of_isOpenImmersion B S hS hj)
  have : (modulePullback B S hS j).IsLeftAdjoint := ⟨_, ⟨modulePullbackAdjunction B S hS j⟩⟩
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback B S hS j)
  refine (Preadditive.mono_iff_isZero_kernel φ).mpr ?_
  refine isZero_of_supportOfSheaf_subset_range_of_isZero_modulePullback B S hS j hj _
    ((supportOfSheaf_toSheaf_subset_of_mono B S hS X (kernel.ι φ)).trans hM) ?_
  exact (Iso.isZero_iff (PreservesKernel.iso (modulePullback B S hS j) φ)).mpr
    ((Preadditive.mono_iff_isZero_kernel _).mp h)

/-- **The support of the direct image along an open immersion of a module whose support has
closed image is that image**: `Supp(j_*Q) = |j|(Supp Q)`.  One inclusion is
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_of_isClosed`; for the other, the
counit `j^*j_*Q ⟶ Q` is an isomorphism, so `Supp Q = Supp(j^*j_*Q) ⊆ |j|⁻¹ Supp(j_*Q)`. -/
theorem supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (Q : Modules.{u, u} B S hS U.1 U.2)
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS j).obj Q)) =
      pointsMap B S hS U.1 j.hom ''
        supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q) := by
  refine subset_antisymm (supportOfSheaf_modulePushforward_subset_of_isClosed B S hS j Q _ hcl
    (Set.subset_preimage_image _ _)) ?_
  have := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS j hj Q
  have e : (modulePullback B S hS j).obj ((modulePushforward B S hS j).obj Q) ≅ Q :=
    asIso ((modulePullbackAdjunction B S hS j).counit.app Q)
  rw [Set.image_subset_iff, ← supportOfSheaf_eq_of_iso B S hS U e]
  exact (supportOfSheaf_modulePullback_of_isEtale B S hS j
    (isEtale_of_isOpenImmersion B S hS hj) _).le

/-- **A geometric point whose image lies in the image of an open immersion lifts through it**,
with the same field. -/
theorem exists_geometricPointMap_eq_of_isOpenImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : G ⟶ F) (hi : IsOpenImmersion B S hS i) (ybar : GeometricPoint B S hS F)
    (hy : ybar.image ∈ Set.range (pointsMap B S hS G i)) :
    ∃ xbar : GeometricPoint B S hS G, geometricPointMap i xbar = ybar := by
  obtain ⟨⟨K, hK, tK, vK⟩, hp⟩ := ybar
  obtain ⟨x, hx⟩ := hy
  obtain ⟨q, rfl⟩ := Quot.exists_rep x
  obtain ⟨a, ha⟩ := exists_lift_fieldPoint_of_isOpenImmersion B S hS i hi
    ⟨K, hK, tK, vK⟩ q hx
  refine ⟨⟨⟨K, hK, tK, yonedaEquiv a⟩, hp⟩, ?_⟩
  apply Subtype.ext
  show FieldValuedPoint.map B S hS G i ⟨K, hK, tK, yonedaEquiv a⟩ = ⟨K, hK, tK, vK⟩
  have hv : i.app _ (yonedaEquiv a) = vK := by
    rw [← yonedaEquiv_comp, ha, Equiv.apply_symm_apply]
  exact congrArg (fun v => (⟨K, hK, tK, v⟩ : FieldValuedPoint B S hS F)) hv

/-- **Flatness of the direct image along an open immersion of a module whose support has closed
image.**  At a geometric point in the image of the open immersion the stalk is that of the module
itself, since the open immersion is flat and the counit `j^*j_*Q ⟶ Q` is an isomorphism; at any
other geometric point the stalk vanishes, the support of `j_*Q` lying in the image. -/
theorem isFlatOver_modulePushforward_of_isOpenImmersion {Y : AlgebraicSpaces B S hS}
    (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom) (g : X ⟶ Y)
    (Q : Modules.{u, u} B S hS U.1 U.2)
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q)))
    (hqc : ((modulePushforward B S hS j).obj Q).IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS U.2 (j ≫ g).hom Q) :
    IsFlatOver B S hS X.2 g.hom ((modulePushforward B S hS j).obj Q) := by
  have := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS j hj Q
  let e : (modulePullback B S hS j).obj ((modulePushforward B S hS j).obj Q) ≅ Q :=
    asIso ((modulePullbackAdjunction B S hS j).counit.app Q)
  have hqc' : ((modulePullback B S hS j).obj
      ((modulePushforward B S hS j).obj Q)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j _ hqc
  have hflat' : IsFlatOver B S hS U.2 (j ≫ g).hom
      ((modulePullback B S hS j).obj ((modulePushforward B S hS j).obj Q)) :=
    IsFlatOver.of_iso B S hS U.2 e.symm hflat
  have := hqc
  have := hqc'
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint] at hflat' ⊢
  intro ybar
  by_cases hy : ybar.image ∈ Set.range (pointsMap B S hS U.1 j.hom)
  · obtain ⟨xbar, rfl⟩ := exists_geometricPointMap_eq_of_isOpenImmersion B S hS j.hom hj ybar hy
    exact (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS j g _ xbar
      (isFlatAt_of_isFlat B S hS j.hom (isFlat_of_isEtale B S hS
        (isEtale_of_isOpenImmersion B S hS hj)) xbar.image)).mpr (hflat' xbar)
  · refine isFlatOverAtGeometricPoint_of_subsingleton_geometricModuleStalk B S hS g _ ybar ?_
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    have hmem : ybar.image ∈ supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS j).obj Q)) :=
      (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X _ _).mpr ⟨ybar, rfl, hnt⟩
    rw [supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS j hj Q hcl] at hmem
    obtain ⟨x, -, hx⟩ := hmem
    exact hy ⟨x, hx⟩

/-- **Finite presentation of the direct image along an open immersion of a module whose support
has closed image.**  The open immersion and the complement of the image of the support cover the
target; the restriction of `j_*Q` to the first is `Q`, by the counit of Stacks 03LU, and to the
second is zero, its support being the image of the support of `Q`. -/
theorem isFinitePresentationOnSite_modulePushforward_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (Q : Modules.{u, u} B S hS U.1 U.2)
    (hQ : Q.IsFinitePresentationOnSite)
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    ((modulePushforward B S hS j).obj Q).IsFinitePresentationOnSite := by
  set Z := pointsMap B S hS U.1 j.hom ''
    supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q)
  let W := openPointsSubspace B S hS X Zᶜ hcl.isOpen_compl
  let w := openPointsSubspaceHom B S hS X Zᶜ hcl.isOpen_compl
  have hw : IsOpenImmersion B S hS w.hom :=
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 Zᶜ hcl.isOpen_compl).2
  let Uf : ULift.{u} Bool → AlgebraicSpaces B S hS := fun k ↦ bif k.down then U else W
  let jf : ∀ k, Uf k ⟶ X := fun k ↦ by
    rcases k with ⟨_ | _⟩
    exacts [w, j]
  have hjf : ∀ k, IsOpenImmersion B S hS (jf k).hom := fun k ↦ by
    rcases k with ⟨_ | _⟩
    exacts [hw, hj]
  refine isFinitePresentationOnSite_of_isOpenImmersion_cover B S hS jf hjf ?_ _ ?_
  · intro x
    by_cases hx : x ∈ Z
    · obtain ⟨y, -, rfl⟩ := hx
      exact ⟨ULift.up true, y, rfl⟩
    · refine ⟨ULift.up false, ?_⟩
      show x ∈ Set.range (pointsMap B S hS W.1 w.hom)
      rwa [range_pointsMap_openPointsSubspaceHom]
  · rintro ⟨_ | _⟩
    · refine SheafOfModules.IsFinitePresentationOnSite.of_isZero
        (isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf B S hS X _ Zᶜ hcl.isOpen_compl ?_)
      rw [supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS j hj Q hcl]
      exact Set.compl_inter_self Z
    · exact SheafOfModules.IsFinitePresentationOnSite.of_iso
        ((etaleModulePullbackCounitIso B S hS j hj).app Q).symm hQ

/-! ### Proper support -/

section ProperSupport

variable {T : AlgebraicSpaces B S hS}

/-- Having support proper over the base depends on the morphism to the base only, not on the way
it is written. -/
theorem hasProperSupport_of_eq {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X') (hY : IsAlgebraicSpace B S hS Y') {f f' : X' ⟶ Y'}
    (h : f = f') (hf : IsLocallyOfFiniteType B S hS f) (hf' : IsLocallyOfFiniteType B S hS f')
    {F : Sheaf (SmallEtale.topology B S hS X') AddCommGrpCat.{u}}
    (hF : HasProperSupport B S hS hX hY f hf F) : HasProperSupport B S hS hX hY f' hf' F := by
  subst h
  exact hF

/-- **Proper support of the direct image along an open immersion.**  If `Q` has support proper
over `T` along `j ≫ g` and `g` is separated, then `j_*Q` has support proper over `T`: the image
of the support of `Q` is closed and proper over `T` by Stacks 0CZG, and it is the support of
`j_*Q`. -/
theorem hasProperSupport_modulePushforward_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (g : X ⟶ T) (hg : IsLocallyOfFiniteType B S hS g.hom)
    (hjg : IsLocallyOfFiniteType B S hS (j ≫ g).hom) (hsep : IsSeparated B S hS g.hom)
    (Q : Modules.{u, u} B S hS U.1 U.2)
    (hQ : HasProperSupport B S hS U.2 T.2 (j ≫ g).hom hjg ((SheafOfModules.toSheaf _).obj Q)) :
    HasProperSupport B S hS X.2 T.2 g.hom hg
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS j).obj Q)) := by
  obtain ⟨hcl, hproper⟩ := hQ
  have himcl := isClosed_image_of_isProperOver B S hS U.2 X.2 T.2 j.hom (j ≫ g).hom g.hom rfl hjg
    hg hsep _ hcl hproper
  unfold HasProperSupport
  rw [supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS j hj Q himcl]
  exact ⟨himcl, isProperOver_image_of_isSeparated B S hS U.2 X.2 T.2 j.hom (j ≫ g).hom g.hom rfl
    hjg hg hsep _ hcl hproper himcl⟩

end ProperSupport

/-! ### Extension of quotients along an open immersion -/

section Extension

-- The ambient-universe abelian structure on modules over a site cannot describe the modules
-- here, whose sections are in the universe of the schemes; left in place it is selected ahead
-- of `SheafOfModules.instAbelian` and leaves the module universe of the kernels unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- The cokernels below must be the ones of the abelian structure, as for the quotients of
-- Stacks 082M; the separately constructed cokernels of `𝒪`-modules are equal to them only
-- through an expensive unfolding.
attribute [-instance] AlgebraicGeometry.Space.hasCokernel_modules

variable {C : Type*} [Category* C] {P₁ : C ⥤ Modules.{u, u} B S hS X.1 X.2}
  {P₂ : C ⥤ Modules.{u, u} B S hS U.1 U.2}

/-- **The direct image along an open immersion of a quotient of a restriction, as a quotient.**
Given a comparison `e : P₂ ≅ P₁ ⋙ j^*` and a projection `p : P₂ M ⟶ Q`, the kernel of the adjoint
`P₁ M ⟶ j_*Q` of `j^*P₁ M ≅ P₂ M ⟶ Q`. -/
def extendSubobject (j : U ⟶ X) (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j) {M : C}
    {Q : Modules.{u, u} B S hS U.1 U.2} (p : P₂.obj M ⟶ Q) : Subobject (P₁.obj M) :=
  kernelSubobject ((modulePullbackAdjunction B S hS j).homEquiv (P₁.obj M) Q (e.inv.app M ≫ p))

/-- The adjoint of an epimorphism `j^*A ⟶ Q` along an open immersion is an epimorphism as soon as
the support of `j_*Q` lies in the image of the open immersion. -/
theorem epi_homEquiv_of_isOpenImmersion (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (A : Modules.{u, u} B S hS X.1 X.2) (Q : Modules.{u, u} B S hS U.1 U.2)
    (ψ : (modulePullback B S hS j).obj A ⟶ Q) (hψ : Epi ψ)
    (hQ : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      ((modulePushforward B S hS j).obj Q)) ⊆ Set.range (pointsMap B S hS U.1 j.hom)) :
    Epi ((modulePullbackAdjunction B S hS j).homEquiv A Q ψ) := by
  refine epi_of_epi_modulePullback_of_isOpenImmersion B S hS j hj _ hQ ?_
  have hε := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS j hj Q
  have hfac : (modulePullback B S hS j).map ((modulePullbackAdjunction B S hS j).homEquiv A Q ψ) =
      ψ ≫ inv ((modulePullbackAdjunction B S hS j).counit.app Q) := by
    rw [IsIso.eq_comp_inv, modulePullback_map_homEquiv_comp_counit]
  rw [hfac]
  exact epi_comp' hψ (IsIso.epi_of_iso _)

/-- The adjoint `P₁ M ⟶ j_*Q` of the projection onto a quotient of the restriction is an
epimorphism when the support of the quotient has closed image. -/
theorem epi_extendSubobject_projection (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j) {M : C} {Q : Modules.{u, u} B S hS U.1 U.2}
    (p : P₂.obj M ⟶ Q) [Epi p]
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    Epi ((modulePullbackAdjunction B S hS j).homEquiv (P₁.obj M) Q (e.inv.app M ≫ p)) :=
  epi_homEquiv_of_isOpenImmersion B S hS j hj (P₁.obj M) Q (e.inv.app M ≫ p)
    (epi_comp' (IsIso.epi_of_iso _) inferInstance)
    (by
      rw [supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS j hj _ hcl]
      exact Set.image_subset_range _ _)

/-- **The quotient by the direct image of a quotient is the direct image of the quotient.** -/
def extendSubobjectCokernelIso (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j) {M : C} {Q : Modules.{u, u} B S hS U.1 U.2}
    (p : P₂.obj M ⟶ Q) [Epi p]
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    cokernel (extendSubobject B S hS j e p).arrow ≅ (modulePushforward B S hS j).obj Q :=
  have := epi_extendSubobject_projection B S hS j hj e p hcl
  Abelian.cokernelKernelSubobjectIso _

/-- The support of the quotient by the direct image of a quotient is the image of the support of
the quotient. -/
theorem supportOfSheaf_cokernel_extendSubobject (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j) {M : C} {Q : Modules.{u, u} B S hS U.1 U.2}
    (p : P₂.obj M ⟶ Q) [Epi p]
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (cokernel (extendSubobject B S hS j e p).arrow : Modules.{u, u} B S hS X.1 X.2)) =
      pointsMap B S hS U.1 j.hom ''
        supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q) := by
  rw [supportOfSheaf_eq_of_iso B S hS X (extendSubobjectCokernelIso B S hS j hj e p hcl),
    supportOfSheaf_modulePushforward_eq_image_of_isOpenImmersion B S hS j hj _ hcl]

/-- **The restriction of the direct image of a quotient is that quotient**, when the support of
the quotient has closed image. -/
theorem conjSubobject_extendSubobject (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j) {M : C} {Q : Modules.{u, u} B S hS U.1 U.2}
    (p : P₂.obj M ⟶ Q) [Epi p]
    (hcl : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj Q))) :
    Functor.conjSubobject e (extendSubobject B S hS j e p) = kernelSubobject p := by
  have hepi := epi_extendSubobject_projection B S hS j hj e p hcl
  have hε := isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS j hj Q
  have hα : e.hom.app M ≫ (modulePullback B S hS j).map
      ((modulePullbackAdjunction B S hS j).homEquiv (P₁.obj M) Q (e.inv.app M ≫ p)) ≫
        (asIso ((modulePullbackAdjunction B S hS j).counit.app Q)).hom = p := by
    rw [asIso_hom, modulePullback_map_homEquiv_comp_counit, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp]
  exact Functor.conjSubobject_kernelSubobject_eq e _ p _ hα

/-- **The direct image of the restriction of a quotient is that quotient**, when the unit of
Stacks 03LU is an isomorphism at the quotient — which is the case when its support is closed and
lies in the image of the open immersion.  The restriction is given by an epimorphism
`p : P₂ M ⟶ Q` identified, by `θ`, with the conjugate projection of `L`. -/
theorem extendSubobject_eq_of_isIso_unit (j : U ⟶ X) (e : P₂ ≅ P₁ ⋙ modulePullback B S hS j)
    {M : C} (L : Subobject (P₁.obj M)) {Q : Modules.{u, u} B S hS U.1 U.2} (p : P₂.obj M ⟶ Q)
    (θ : Q ≅ (modulePullback B S hS j).obj (cokernel L.arrow))
    (hθ : p ≫ θ.hom = Functor.conjQuotientProjection e L)
    (hη : IsIso ((modulePullbackAdjunction B S hS j).unit.app (cokernel L.arrow))) :
    extendSubobject B S hS j e p = L := by
  set adj := modulePullbackAdjunction B S hS j
  have hψ : (e.inv.app M ≫ p) ≫ θ.hom = (modulePullback B S hS j).map (cokernel.π L.arrow) := by
    rw [Category.assoc, hθ, Functor.conjQuotientProjection, ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]
  have key : adj.homEquiv (P₁.obj M) Q (e.inv.app M ≫ p) ≫ (modulePushforward B S hS j).map θ.hom =
      cokernel.π L.arrow ≫ adj.unit.app (cokernel L.arrow) := by
    rw [← Adjunction.homEquiv_naturality_right, hψ, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality (cokernel.π L.arrow)).symm
  have hiso : IsIso ((modulePushforward B S hS j).map θ.hom) := Functor.map_isIso _ _
  have hm : Mono ((modulePushforward B S hS j).map θ.hom) := IsIso.mono_of_iso _
  have hm' : Mono (adj.unit.app (cokernel L.arrow)) := IsIso.mono_of_iso _
  calc extendSubobject B S hS j e p
      = kernelSubobject (adj.homEquiv (P₁.obj M) Q (e.inv.app M ≫ p) ≫
          (modulePushforward B S hS j).map θ.hom) :=
        (@kernelSubobject_comp_mono _ _ _ _ _ _ _ _ _ hm).symm
    _ = kernelSubobject (cokernel.π L.arrow ≫ adj.unit.app (cokernel L.arrow)) := by
        simp only [key]
    _ = kernelSubobject (cokernel.π L.arrow) := @kernelSubobject_comp_mono _ _ _ _ _ _ _ _ _ hm'
    _ = L := kernelSubobject_cokernel_π L

end Extension

end AlgebraicGeometry.Space

end
