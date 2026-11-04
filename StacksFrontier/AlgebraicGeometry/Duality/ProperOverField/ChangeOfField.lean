module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# The dualizing complex of a proper scheme over a field under change of base field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, and let
`ω_X^• = a(𝒪_{Spec k})` and `ω_X = H^{-dim X}(ω_X^•)` be as in [Stacks, Tag 0FVV]: in this
library they are `Stacks.Duality.relativeDualizingComplex f _ (derivedStructureSheaf (Spec k))`
and `Stacks.Duality.relativeDualizingModule f _ (derivedStructureSheaf (Spec k))`, `a` being the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})` ([Stacks, Tag 0A9E]). This file
proves [Stacks, Tag 0FW1]:

1. if `f` factors as `X ⟶ Spec k' ⟶ Spec k` for a field `k'`, then `ω_X^•` and `ω_X` are
   isomorphic to the dualizing complex and module constructed from `f' : X ⟶ Spec k'`;
2. if `K/k` is a field extension, the pullbacks of `ω_X^•` and `ω_X` to `X_K = X ×_k K` are
   isomorphic to the dualizing complex and module constructed from `X_K ⟶ Spec K`.

## Main results

* `Stacks.Duality.nonempty_iso_relativeDualizing_of_factorization` — part (1).
* `Stacks.Duality.nonempty_iso_relativeDualizing_baseChange` — part (2).

## References

* [Stacks Project, Tag 0FW1](https://stacks.math.columbia.edu/tag/0FW1)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.ProperOverField

section FieldExtension

variable {k k' : Type u} [Field k] [Field k'] (φ : k →+* k')

/-- For a finite extension `φ : k →+* k'` of fields, the `k'`-module `Hom_k(k', k)` (the
coextension of scalars of `k`) is free of rank one. -/
theorem nonempty_linearEquiv_coextendScalars
    [Module.Finite k ((ModuleCat.restrictScalars φ).obj (ModuleCat.of k' k'))] :
    Nonempty (k' ≃ₗ[k'] ((ModuleCat.restrictScalars φ).obj (ModuleCat.of k' k') →ₗ[k] k)) := by
  set V := (ModuleCat.restrictScalars φ).obj (ModuleCat.of k' k')
  let e : k' → V := id
  have he : ∀ (c : k) (x : k'), c • e x = e (φ c * x) := fun _ _ => rfl
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual k V, l (e 1) ≠ 0 := by
    by_contra! h
    exact (one_ne_zero : (1 : k') ≠ 0) ((Module.forall_dual_apply_eq_zero_iff k (e 1)).1 h)
  let T : k' →ₗ[k'] (V →ₗ[k] k) := LinearMap.toSpanSingleton k' (V →ₗ[k] k) l
  let T' : V →ₗ[k] (V →ₗ[k] k) :=
    { toFun := fun x => T x
      map_add' := fun x y => T.map_add x y
      map_smul' := fun c x => by
        ext y
        change l (e ((show k' from y) * (φ c * (show k' from x)))) =
          c * l (e ((show k' from y) * (show k' from x)))
        rw [show (show k' from y) * (φ c * (show k' from x)) =
          φ c * ((show k' from y) * (show k' from x)) by ring, ← he]
        exact l.map_smul c _ }
  have hinj : Function.Injective T' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    by_contra hs0
    apply hl
    have := LinearMap.congr_fun hs (e (show k' from s)⁻¹)
    change l (e ((show k' from s)⁻¹ * (show k' from s))) = 0 at this
    rwa [inv_mul_cancel₀ (show (show k' from s) ≠ 0 from hs0)] at this
  exact ⟨LinearEquiv.ofBijective T ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k) (V := V)).symm).1 hinj⟩⟩

/-- If `X` is nonempty and `X ⟶ Spec k' ⟶ Spec k` is locally of finite type, then `k'` is a
finite extension of `k`. -/
theorem moduleFinite_restrictScalars_of_factorization {X : Scheme.{u}} [Nonempty X]
    (f' : X ⟶ Spec (.of k')) (φ : CommRingCat.of k ⟶ CommRingCat.of k')
    [LocallyOfFiniteType (f' ≫ Spec.map φ)] :
    Module.Finite k ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of k' k')) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let α : k' →+* Γ(X, U) := ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appLE ⊤ U (by simp)).hom
  let β : k →+* Γ(X, U) := α.comp φ.hom
  have hβ : β = ((Scheme.ΓSpecIso (.of k)).inv ≫
      (f' ≫ Spec.map φ).appLE ⊤ U (by simp)).hom := by
    have h1 : (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map φ).appTop =
        φ ≫ (Scheme.ΓSpecIso (.of k')).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Scheme.ΓSpecIso_naturality]
    have h2 : (Scheme.ΓSpecIso (.of k)).inv ≫ (f' ≫ Spec.map φ).appLE ⊤ U (by simp) =
        φ ≫ (Scheme.ΓSpecIso (.of k')).inv ≫ f'.appLE ⊤ U (by simp) := by
      rw [show (f' ≫ Spec.map φ).appLE ⊤ U (by simp) =
          (Spec.map φ).appTop ≫ f'.appLE ⊤ U (by simp) from Scheme.Hom.comp_appLE _ _ _ _ _,
        ← Category.assoc, h1, Category.assoc]
    rw [h2]
    rfl
  let : Algebra k Γ(X, U) := β.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := by
    change β.FiniteType
    rw [hβ]
    exact ((f' ≫ Spec.map φ).finiteType_appLE (isAffineOpen_top _) hU _).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, U)
  let : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (Γ(X, U) ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      (Ideal.Quotient.mkₐ_surjective k m)
  have : Module.Finite k (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let toK : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of k' k') → k' := id
  let ι : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of k' k') →ₗ[k] Γ(X, U) ⧸ m :=
    { toFun := fun s => Ideal.Quotient.mk m (α (toK s))
      map_add' := fun s t => by
        change Ideal.Quotient.mk m (α (toK s + toK t)) = _
        rw [map_add, map_add]
      map_smul' := fun c s => by
        change Ideal.Quotient.mk m (α (φ.hom c * toK s)) = c • Ideal.Quotient.mk m (α (toK s))
        rw [Algebra.smul_def, map_mul, map_mul]
        rfl }
  exact Module.Finite.of_injective ι ((Ideal.Quotient.mk m).comp α).injective

end FieldExtension

section SpecField

variable {k k' : Type u} [Field k] [Field k']

/-- For a finite extension of fields `φ : k ⟶ k'`, the twisted inverse image of
`Spec φ : Spec k' ⟶ Spec k` sends `𝒪_{Spec k}` to `𝒪_{Spec k'}`. -/
theorem nonempty_twistedInverseImage_specMap_structureSheaf_iso
    (φ : CommRingCat.of k ⟶ CommRingCat.of k')
    [Module.Finite k ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of k' k'))] :
    Nonempty ((twistedInverseImage (Spec.map φ)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ))).obj
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      DerivedPushforward.derivedStructureSheaf (Spec (.of k'))) := by
  obtain ⟨e⟩ :=
    AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom φ
      (twistedInverseImageAdjunction (Spec.map φ)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
  obtain ⟨eV⟩ := nonempty_linearEquiv_coextendScalars φ.hom
  let eM : ModuleCat.of k' k' ≅ (ModuleCat.coextendScalars φ.hom).obj (ModuleCat.of k k) :=
    (eV ≪≫ₗ (ModuleCat.CoextendScalars.equiv φ.hom (ModuleCat.of k k)).symm).toModuleIso
  exact ⟨(twistedInverseImage _ _).mapIso (derivedStructureSheafIsoDerivedTilde (.of k)) ≪≫
    e.app _ ≪≫
    (derivedTilde (.of k')).mapIso
      (((Dualizing.AnyModel.coextendScalarsMapDerivedCategoryIsoDerivedHom φ.hom).app _).symm ≪≫
        ((ModuleCat.coextendScalars φ.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eM.symm) ≪≫
    (derivedStructureSheafIsoDerivedTilde (.of k')).symm⟩

end SpecField

section Empty

/-- On the empty scheme every module is zero. -/
theorem isZero_modules_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M : X.Modules) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have : Subsingleton Γ(M, U) := Module.subsingleton Γ(X, U) _
  exact Subsingleton.elim _ _

/-- On the empty scheme every object of the derived category is zero. -/
theorem isZero_derivedCategory_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (E : DerivedCategory X.Modules) : IsZero E :=
  isZero_of_forall_isZero_homology E fun _ => isZero_modules_of_isEmpty _

end Empty

section Parts

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- `ω_X^•` for `f = f' ≫ g` is isomorphic to `ω_X^•` for `f'`. -/
theorem nonempty_relativeDualizingComplex_iso_of_factorization {k' : Type u} [Field k']
    (f' : X ⟶ Spec (.of k')) (g : Spec (.of k') ⟶ Spec (.of k)) (h : f' ≫ g = f) :
    haveI : IsProper f' := haveI : IsProper (f' ≫ g) := h ▸ ‹IsProper f›; IsProper.of_comp f' g
    Nonempty (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      relativeDualizingComplex f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k')))) := by
  have : IsProper (f' ≫ g) := h ▸ ‹IsProper f›
  have : IsProper f' := IsProper.of_comp f' g
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨ObjectProperty.isoMk _
      ((isZero_derivedCategory_of_isEmpty _).iso (isZero_derivedCategory_of_isEmpty _))⟩
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  subst h
  have := moduleFinite_restrictScalars_of_factorization f' φ
  obtain ⟨e⟩ := nonempty_twistedInverseImage_specMap_structureSheaf_iso φ
  exact ⟨(twistedInverseImageCompIso f' (Spec.map φ) _ _ _).app _ ≪≫
    (twistedInverseImage f' _).mapIso e⟩

/-- `ω_X` for `f = f' ≫ g` is isomorphic to `ω_X` for `f'`. -/
theorem nonempty_relativeDualizingModule_iso_of_factorization {k' : Type u} [Field k']
    (f' : X ⟶ Spec (.of k')) (g : Spec (.of k') ⟶ Spec (.of k)) (h : f' ≫ g = f) :
    haveI : IsProper f' := haveI : IsProper (f' ≫ g) := h ▸ ‹IsProper f›; IsProper.of_comp f' g
    Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      relativeDualizingModule f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k')))) := by
  obtain ⟨e⟩ := nonempty_relativeDualizingComplex_iso_of_factorization f f' g h
  exact ⟨(DerivedCategory.homologyFunctor X.Modules _).mapIso ((ObjectProperty.ι _).mapIso e)⟩

/-- The derived pullback of `ω_X^•` to `X_K` is `ω_{X_K}^•`. -/
theorem nonempty_derivedPullback_relativeDualizingComplex_iso (K : Type u) [Field K]
    [Algebra k K] :
    Nonempty ((quasiCoherentDerivedPullback'
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ≅
      relativeDualizingComplex (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of K)))) := by
  set L := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have sq := IsPullback.of_hasPullback f L
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace ↥(pullback f L : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f L)
  have : QuasiSeparatedSpace ↥(pullback f L : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f L)
  have hTor : TorIndependent f L := torIndependent_of_flat_left f L
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have hiso : IsIso ((twistedInverseImageBaseChangeMap (pullback.fst f L) (pullback.snd f L) f L
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs L) sq).app
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) :=
    isIso_twistedInverseImageBaseChangeMap_app_of_flat sq hTor _
  let eO : (quasiCoherentDerivedPullback' L).obj
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
        DerivedPushforward.derivedStructureSheaf (Spec (.of K)) :=
    ObjectProperty.isoMk _ (derivedPullbackStructureSheafIso L)
  exact ⟨@asIso _ _ _ _ _ hiso ≪≫ (twistedInverseImage _ _).mapIso eO⟩

/-- The pullback of `ω_X` to `X_K` is `ω_{X_K}`. -/
theorem nonempty_pullback_relativeDualizingModule_iso (K : Type u) [Field K] [Algebra k K] :
    Nonempty ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ≅
      relativeDualizingModule (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of K)))) := by
  set L := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨e⟩ := nonempty_derivedPullback_relativeDualizingComplex_iso f K
  have : PreservesFiniteLimits (Scheme.Modules.pullback (pullback.fst f L)) :=
    preservesFiniteLimits_modulesPullback_of_flat _
  have hdim : topologicalKrullDim ↥(pullback f L : Scheme.{u}) = topologicalKrullDim X :=
    topologicalKrullDim_pullback_spec_algebraMap k K f
  refine ⟨homologyDerivedPullbackIso (pullback.fst f L) _ _ ≪≫
    (DerivedCategory.homologyFunctor _ _).mapIso ((ObjectProperty.ι _).mapIso e) ≪≫
    eqToIso ?_⟩
  simp only [relativeDualizingModule, hdim]
  rfl

end Parts

end Stacks.Duality.ProperOverField

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Let `X` be proper over a field `k` with structure morphism `f`, and suppose `f` factors as
`f' ≫ g` with `f' : X ⟶ Spec k'` for a field `k'`. Then `ω_X^•` and `ω_X` of [Stacks, Tag 0FVV]
for `f` are isomorphic to those constructed for `f'`. -/
@[stacks 0FW1 "(1): ω_X^• and ω_X are as in 0FVV for a factorization X → Spec k' → Spec k"]
theorem nonempty_iso_relativeDualizing_of_factorization {k' : Type u} [Field k']
    (f' : X ⟶ Spec (.of k')) (g : Spec (.of k') ⟶ Spec (.of k)) (h : f' ≫ g = f) :
    haveI : IsProper f' := haveI : IsProper (f' ≫ g) := h ▸ ‹IsProper f›; IsProper.of_comp f' g
    Nonempty (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      relativeDualizingComplex f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k')))) ∧
    Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k))) ≅
      relativeDualizingModule f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k')))) :=
  ⟨ProperOverField.nonempty_relativeDualizingComplex_iso_of_factorization f f' g h,
    ProperOverField.nonempty_relativeDualizingModule_iso_of_factorization f f' g h⟩

/-- Let `X` be proper over a field `k` with structure morphism `f`, let `K/k` be a field extension
and `X_K = X ×_{Spec k} Spec K`, with projections `g' : X_K ⟶ X` and `f_K : X_K ⟶ Spec K`. Then
the pullbacks `L(g')^* ω_X^•` and `(g')^* ω_X` are isomorphic to the dualizing complex and module
of [Stacks, Tag 0FVV] constructed for `f_K`. -/
@[stacks 0FW1 "(2): the pullbacks of ω_X^• and ω_X to X_K are as in 0FVV for X_K → Spec K"]
theorem nonempty_iso_relativeDualizing_baseChange (K : Type u) [Field K] [Algebra k K] :
    Nonempty ((quasiCoherentDerivedPullback'
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ≅
      relativeDualizingComplex (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of K)))) ∧
    Nonempty ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) ≅
      relativeDualizingModule (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of K)))) :=
  ⟨ProperOverField.nonempty_derivedPullback_relativeDualizingComplex_iso f K,
    ProperOverField.nonempty_pullback_relativeDualizingModule_iso f K⟩

end Stacks.Duality

end
