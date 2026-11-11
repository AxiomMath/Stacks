module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ClosedRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ExtOfComplementDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistTransport
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeFour.ClosedImmersionBaseChangeOffImage
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent

/-!
# Excision along an étale neighbourhood of a closed subscheme

Let `ψ : U ⟶ X` be étale, `z : Z ⟶ X` a closed immersion and `k : T ⟶ U` its base change along
`ψ`, with `T ⟶ Z` an isomorphism (`ψ` is an étale neighbourhood of `Z`). For a sheaf `M` of
`Λ`-modules on `Z`, the counit `ψ_! ψ⁻¹ (z_* M) ⟶ z_* M` is an isomorphism
(`isIso_extensionByZeroAdj_counit_app_directImage`), and therefore
`ψ⁻¹ : Ext^n_X(z_* M, A) ⟶ Ext^n_U(ψ⁻¹ z_* M, ψ⁻¹ A)` is injective
(`injective_mapExactFunctor_inverseImage_of_isPullback`). This is the injective half of excision
for étale neighbourhoods, `H^n_Z(X, -) ≅ H^n_T(U, ψ⁻¹ -)`, read on `Ext` out of sheaves supported
on `Z`; surjectivity, and so the isomorphism, is not proved in this file.

The counit is checked on the cover of `X` by `Z` and its open complement `X ∖ Z`
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleInverseImage_family`).

* On `X ∖ Z` both sides vanish: maps out of the restriction of `ψ_! ψ⁻¹ z_* M` are maps
  `ψ⁻¹ z_* M ⟶ ψ⁻¹ n_* G`, from a sheaf supported on `T` (`ψ⁻¹ z_* ≅ k_* ψ_T⁻¹`, the base change
  of the closed restriction, `Stacks.EtaleCohomology.closedRestrictionInverseImageIso`) to a
  direct image from `U ∖ T` (étale base change of a direct image).
* On `Z`, by Yoneda and the two adjunctions, `z⁻¹` of the counit is invertible exactly when
  `ψ⁻¹` is bijective on `Hom(z_* M, z_* G)`; and `z_* ⋙ ψ⁻¹ ≅ ψ_T⁻¹ ⋙ k_*` is fully faithful.

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_extensionByZeroAdj_counit_app_directImage`
* `Stacks.EtaleCohomology.Purity.injective_mapExactFunctor_inverseImage_of_isPullback`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] moduleCat_hasLimitsOfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {U X Z T : Scheme.{u}} (ψ : U ⟶ X) [Etale ψ]
  (z : Z ⟶ X) [IsClosedImmersion z] (k : T ⟶ U) [IsClosedImmersion k] (ψT : T ⟶ Z)
  (sq : IsPullback k ψT ψ z)

/-- The open complement of a closed immersion `z`. -/
local notation "complementOpens " z:max =>
  Stacks.AlgebraicGeometry.EmbeddedPoints.complementOpens (Set.range z)
    (Topology.IsClosedEmbedding.isClosed_range (Scheme.Hom.isClosedEmbedding z))

/-- The open complement of a closed immersion `z : Z ⟶ X` has image the complement of the image
of `z`. -/
theorem range_complementOpens_ι :
    Set.range (complementOpens z).ι.base = (Set.range z.base)ᶜ := by
  show Set.range (complementOpens z).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

omit [Etale ψ] [IsClosedImmersion k] in
include sq in
/-- For a pullback square with `k` the base change of `z` along `ψ`, the preimage under `ψ` of
the open complement of `z` has image the complement of the image of `k`. -/
theorem range_preimage_complementOpens_ι :
    Set.range (ψ ⁻¹ᵁ complementOpens z).ι.base = (Set.range k.base)ᶜ := by
  show Set.range (ψ ⁻¹ᵁ complementOpens z).ι = _
  rw [Scheme.Opens.range_ι,
    Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback sq]
  rfl

variable [IsIso ψT]

omit [Etale ψ] [IsIso ψT] in
include sq in
/-- **`ψ⁻¹ z_* ≅ k_* ψ_T⁻¹`**: the inverse image of a sheaf supported on `Z` along an étale
neighbourhood is the direct image of its inverse image. -/
theorem nonempty_directImage_comp_inverseImage_iso :
    Nonempty (etaleModuleDirectImage.{u, 0} Λ z ⋙ etaleModuleInverseImage.{u, 0} Λ ψ ≅
      etaleModuleInverseImage.{u, 0} Λ ψT ⋙ etaleModuleDirectImage.{u, 0} Λ k) := by
  have hcz : IsIso (etaleModuleInverseImageAdj.{u, 0} Λ z).counit := by
    let ff := etaleModuleDirectImageFullyFaithful.{u, 0} Λ z
    let _ := ff.full
    let _ := ff.faithful
    infer_instance
  let ε := asIso (etaleModuleInverseImageAdj.{u, 0} Λ z).counit
  let zs := etaleModuleDirectImage.{u, 0} Λ z
  let zi := etaleModuleInverseImage.{u, 0} Λ z
  let ψi := etaleModuleInverseImage.{u, 0} Λ ψ
  let ki := etaleModuleInverseImage.{u, 0} Λ k
  let ks := etaleModuleDirectImage.{u, 0} Λ k
  let ψTi := etaleModuleInverseImage.{u, 0} Λ ψT
  let c : (zi ⋙ zs) ⋙ ψi ≅ ψi ⋙ (ki ⋙ ks) :=
    closedRestrictionInverseImageIso Λ ψ z (complementOpens z).ι (range_complementOpens_ι z)
      k (ψ ⁻¹ᵁ complementOpens z).ι (range_preimage_complementOpens_ι ψ z k ψT sq) ψT sq.w
      (ψ ∣_ complementOpens z) (morphismRestrict_ι ψ (complementOpens z)).symm
  let e1 : zs ≅ zs ⋙ (zi ⋙ zs) :=
    (Functor.leftUnitor zs).symm ≪≫ Functor.isoWhiskerRight ε.symm zs ≪≫ Functor.associator _ _ _
  let e2 : (zs ⋙ ψi) ⋙ ki ≅ zs ⋙ (zi ⋙ ψTi) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft zs
      ((etaleModuleInverseImageCompIso.{u, 0} Λ k ψ).symm ≪≫
        eqToIso (congrArg (etaleModuleInverseImage.{u, 0} Λ) sq.w) ≪≫
        etaleModuleInverseImageCompIso.{u, 0} Λ ψT z)
  let e3 : zs ⋙ (zi ⋙ ψTi) ≅ ψTi :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ε ψTi ≪≫ Functor.leftUnitor ψTi
  let s4 : zs ⋙ (ψi ⋙ (ki ⋙ ks)) ≅ ((zs ⋙ ψi) ⋙ ki) ⋙ ks :=
    Functor.isoWhiskerLeft zs (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _).symm ks
  exact ⟨Functor.isoWhiskerRight e1 ψi ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft zs c ≪≫ s4 ≪≫
    Functor.isoWhiskerRight e2 ks ≪≫ Functor.isoWhiskerRight e3 ks⟩

omit [Etale ψ] in
include sq in
/-- `ψ⁻¹` is bijective on morphisms between sheaves supported on `Z`. -/
theorem bijective_inverseImage_map_directImage (M G : EtaleModules.{u, 0} Λ Z) :
    Function.Bijective (fun h : (etaleModuleDirectImage.{u, 0} Λ z).obj M ⟶
        (etaleModuleDirectImage.{u, 0} Λ z).obj G =>
          (etaleModuleInverseImage.{u, 0} Λ ψ).map h) := by
  obtain ⟨β⟩ := nonempty_directImage_comp_inverseImage_iso Λ ψ z k ψT sq
  have : (etaleModuleDirectImage.{u, 0} Λ ψT).IsEquivalence :=
    isEquivalence_smallEtalePushforward_hom (asIso ψT) (ModuleCat.{u + 1} Λ)
  have : (etaleModuleInverseImage.{u, 0} Λ ψT).IsEquivalence :=
    (etaleModuleInverseImageAdj.{u, 0} Λ ψT).isEquivalence_left_of_isEquivalence_right
  let ff₁ :
      (etaleModuleInverseImage.{u, 0} Λ ψT ⋙ etaleModuleDirectImage.{u, 0} Λ k).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful _).comp (etaleModuleDirectImageFullyFaithful.{u, 0} Λ k)
  let ff₂ := ff₁.ofIso β.symm
  let ffz := etaleModuleDirectImageFullyFaithful.{u, 0} Λ z
  refine ⟨fun h₁ h₂ e => ?_, fun g => ?_⟩
  · simp only at e
    rw [← ffz.map_preimage h₁, ← ffz.map_preimage h₂] at e ⊢
    exact congrArg _ (ff₂.map_injective e)
  · exact ⟨(etaleModuleDirectImage.{u, 0} Λ z).map (ff₂.preimage g), ff₂.map_preimage g⟩

include sq in
/-- The restriction along `ψ` is bijective on morphisms between sheaves supported on `Z`. -/
theorem bijective_restriction_map_directImage (M G : EtaleModules.{u, 0} Λ Z) :
    Function.Bijective (fun h : (etaleModuleDirectImage.{u, 0} Λ z).obj M ⟶
        (etaleModuleDirectImage.{u, 0} Λ z).obj G =>
          (etaleModuleRestriction.{u, 0} Λ ψ).map h) := by
  let e := etaleModuleInverseImageRestrictionIso.{u, 0} Λ ψ
  have he : (fun h : (etaleModuleDirectImage.{u, 0} Λ z).obj M ⟶
      (etaleModuleDirectImage.{u, 0} Λ z).obj G => (etaleModuleRestriction.{u, 0} Λ ψ).map h) =
      (e.app ((etaleModuleDirectImage.{u, 0} Λ z).obj M)).homCongr
        (e.app ((etaleModuleDirectImage.{u, 0} Λ z).obj G)) ∘
      (fun h : (etaleModuleDirectImage.{u, 0} Λ z).obj M ⟶
        (etaleModuleDirectImage.{u, 0} Λ z).obj G =>
          (etaleModuleInverseImage.{u, 0} Λ ψ).map h) := by
    funext h
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.app_inv, Iso.app_hom]
    rw [e.hom.naturality h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [he]
  exact (Equiv.bijective _).comp (bijective_inverseImage_map_directImage Λ ψ z k ψT sq M G)

omit [IsIso ψT] in
include sq in
/-- On the complement of `Z`, the extension by zero of `ψ⁻¹ z_* M` vanishes. -/
theorem isZero_inverseImage_complement_extensionByZero (M : EtaleModules.{u, 0} Λ Z) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ (complementOpens z).ι).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ ψ).obj ((etaleModuleRestriction.{u, 0} Λ ψ).obj
        ((etaleModuleDirectImage.{u, 0} Λ z).obj M)))) := by
  obtain ⟨β⟩ := nonempty_directImage_comp_inverseImage_iso Λ ψ z k ψT sq
  let n := (complementOpens z).ι
  let adjn := etaleModuleInverseImageAdj.{u, 0} Λ n
  let adjL := etaleModuleExtensionByZeroAdj.{u, 0} Λ ψ
  let R := etaleModuleRestriction.{u, 0} Λ ψ
  let F := (etaleModuleDirectImage.{u, 0} Λ z).obj M
  have hrange : Set.range (pullback.fst ψ n).base = (Set.range k.base)ᶜ := by
    show Set.range (pullback.fst ψ n) = _
    rw [Scheme.Pullback.range_fst]
    show ψ.base ⁻¹' Set.range n.base = _
    rw [range_complementOpens_ι, Set.preimage_compl,
      ← Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback sq]
  have hsub : ∀ G : EtaleModules.{u, 0} Λ (complementOpens z).toScheme,
      Subsingleton (R.obj F ⟶ R.obj ((etaleModuleDirectImage.{u, 0} Λ n).obj G)) := by
    intro G
    let e₁ : R.obj F ≅ (etaleModuleDirectImage.{u, 0} Λ k).obj
        ((etaleModuleInverseImage.{u, 0} Λ ψT).obj M) :=
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ ψ).app F).symm ≪≫ β.app M
    let e₂ : R.obj ((etaleModuleDirectImage.{u, 0} Λ n).obj G) ≅
        (etaleModuleDirectImage.{u, 0} Λ (pullback.fst ψ n)).obj
          ((etaleModuleRestriction.{u, 0} Λ (pullback.snd ψ n)).obj G) :=
      ((Stacks.EtaleCohomology.smallEtaleRestrictionPushforwardBaseChangeIso ψ n
        (ModuleCat.{u + 1} Λ)).app G).symm
    have := subsingleton_hom_etaleModuleDirectImage_complement Λ k (pullback.fst ψ n) hrange
      ((etaleModuleInverseImage.{u, 0} Λ ψT).obj M)
      ((etaleModuleRestriction.{u, 0} Λ (pullback.snd ψ n)).obj G)
    exact (Iso.homCongr e₁ e₂).subsingleton
  rw [IsZero.iff_id_eq_zero]
  have : Subsingleton ((etaleModuleInverseImage.{u, 0} Λ n).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ ψ).obj (R.obj F)) ⟶
        (etaleModuleInverseImage.{u, 0} Λ n).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ ψ).obj (R.obj F))) := by
    have := hsub ((etaleModuleInverseImage.{u, 0} Λ n).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ ψ).obj (R.obj F)))
    exact ((adjn.homEquiv _ _).trans (adjL.homEquiv _ _)).subsingleton
  exact Subsingleton.elim _ _

include sq in
/-- **Excision for an étale neighbourhood, on sheaves**: the counit `ψ_! ψ⁻¹ z_* M ⟶ z_* M` is
an isomorphism. -/
theorem isIso_extensionByZeroAdj_counit_app_directImage (M : EtaleModules.{u, 0} Λ Z) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ ψ).counit.app
      ((etaleModuleDirectImage.{u, 0} Λ z).obj M)) := by
  let n := (complementOpens z).ι
  let adjL := etaleModuleExtensionByZeroAdj.{u, 0} Λ ψ
  let adjz := etaleModuleInverseImageAdj.{u, 0} Λ z
  let R := etaleModuleRestriction.{u, 0} Λ ψ
  let L := etaleModuleExtensionByZero.{u, 0} Λ ψ
  let zs := etaleModuleDirectImage.{u, 0} Λ z
  let F := zs.obj M
  let εF : L.obj (R.obj F) ⟶ F := adjL.counit.app F
  let Tf : ULift.{u} Bool → Scheme.{u} := fun a => cond a.down Z (complementOpens z).toScheme
  let gf : ∀ a, Tf a ⟶ X := fun a => match a with
    | ⟨true⟩ => z
    | ⟨false⟩ => n
  refine isIso_of_isIso_etaleModuleInverseImage_family Λ gf ?_ εF fun a => ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ Set.range z.base
    · exact ⟨⟨true⟩, hx⟩
    · refine ⟨⟨false⟩, ?_⟩
      change x ∈ Set.range n.base
      rwa [range_complementOpens_ι]
  · match a with
    | ⟨false⟩ =>
      have h₁ := isZero_inverseImage_complement_extensionByZero Λ ψ z k ψT sq M
      have h₂ : IsZero ((etaleModuleInverseImage.{u, 0} Λ n).obj F) :=
        (isZero_etaleModuleRestriction_etaleModuleDirectImage Λ z n (range_complementOpens_ι z)
          M).of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ n).app F)
      exact isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    | ⟨true⟩ =>
      refine isIso_of_coyoneda_map_bijective _ fun G => ?_
      have key : (fun x : (etaleModuleInverseImage.{u, 0} Λ z).obj F ⟶ G =>
          (etaleModuleInverseImage.{u, 0} Λ z).map εF ≫ x) =
          (adjz.homEquiv (L.obj (R.obj F)) G).symm ∘ (adjL.homEquiv (R.obj F) (zs.obj G)).symm ∘
            (fun h : F ⟶ zs.obj G => R.map h) ∘ adjz.homEquiv F G := by
        have h1 : ∀ h : F ⟶ zs.obj G, (adjL.homEquiv (R.obj F) (zs.obj G)).symm (R.map h) =
            εF ≫ h := fun h => by
          rw [Adjunction.homEquiv_counit]
          exact adjL.counit_naturality h
        funext x
        simp only [Function.comp_apply]
        rw [h1, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
      change Function.Bijective (fun x : (etaleModuleInverseImage.{u, 0} Λ z).obj F ⟶ G =>
          (etaleModuleInverseImage.{u, 0} Λ z).map εF ≫ x)
      rw [key]
      exact (Equiv.bijective _).comp ((Equiv.bijective _).comp
        ((bijective_restriction_map_directImage Λ ψ z k ψT sq M G).comp (Equiv.bijective _)))

include sq in
/-- **The injective half of excision for an étale neighbourhood, on `Ext`**, for the restriction
functor: `x ↦ x.mapExactFunctor (etaleModuleRestriction Λ ψ)` is injective. -/
theorem injective_mapExactFunctor_restriction_of_isPullback (M : EtaleModules.{u, 0} Λ Z)
    (A : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    Function.Injective (fun x : Ext ((etaleModuleDirectImage.{u, 0} Λ z).obj M) A n =>
      x.mapExactFunctor (etaleModuleRestriction.{u, 0} Λ ψ)) := by
  let adjL := etaleModuleExtensionByZeroAdj.{u, 0} Λ ψ
  let R := etaleModuleRestriction.{u, 0} Λ ψ
  let L := etaleModuleExtensionByZero.{u, 0} Λ ψ
  let F := (etaleModuleDirectImage.{u, 0} Λ z).obj M
  have hε := isIso_extensionByZeroAdj_counit_app_directImage Λ ψ z k ψT sq M
  have key : ∀ x : Ext F A n, (Ext.mk₀ (adjL.counit.app F)).comp x (zero_add n) =
      ((x.mapExactFunctor R).mapExactFunctor L).comp (Ext.mk₀ (adjL.counit.app A))
        (add_zero n) := by
    intro x
    rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
      ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adjL.counit F n x,
      Stacks.ExtFunctorial.mapExactFunctor_id]
  intro x y hxy
  have h := key x
  rw [show x.mapExactFunctor R = y.mapExactFunctor R from hxy, ← key y] at h
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (adjL.counit.app F) n).1 h

include sq in
/-- **The injective half of excision for an étale neighbourhood, on `Ext`**: for `ψ : U ⟶ X`
étale whose base change `T ⟶ Z` along the closed immersion `z : Z ⟶ X` is an isomorphism,
`ψ⁻¹ : Ext^n_X(z_* M, A) ⟶ Ext^n_U(ψ⁻¹ z_* M, ψ⁻¹ A)` is injective. -/
theorem injective_mapExactFunctor_inverseImage_of_isPullback (M : EtaleModules.{u, 0} Λ Z)
    (A : EtaleModules.{u, 0} Λ X) (n : ℕ) :
    Function.Injective (fun x : Ext ((etaleModuleDirectImage.{u, 0} Λ z).obj M) A n =>
      x.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ ψ)) := by
  let e := etaleModuleInverseImageRestrictionIso.{u, 0} Λ ψ
  let F := (etaleModuleDirectImage.{u, 0} Λ z).obj M
  intro x y hxy
  have hxy' : x.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ ψ) =
      y.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ ψ) := hxy
  apply injective_mapExactFunctor_restriction_of_isPullback Λ ψ z k ψT sq M A n
  apply (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (e.hom.app F) n).1
  change (Ext.mk₀ (e.hom.app F)).comp (x.mapExactFunctor (etaleModuleRestriction.{u, 0} Λ ψ))
      (zero_add n) =
    (Ext.mk₀ (e.hom.app F)).comp (y.mapExactFunctor (etaleModuleRestriction.{u, 0} Λ ψ))
      (zero_add n)
  rw [Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.hom F n x,
    Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.hom F n y, hxy']

end Stacks.EtaleCohomology.Purity

end
