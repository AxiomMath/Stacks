module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change for quasi-coherent modules on nested affine opens

Let `X` be a scheme, let `M` be a quasi-coherent `𝒪_X`-module and let `U ≤ U'` be affine opens
of `X`. This file proves that the restriction map on sections `Γ(M, U') → Γ(M, U)` exhibits
`Γ(M, U)` as the base change of `Γ(M, U')` along the restriction map of rings
`Γ(X, U') → Γ(X, U)`, i.e. that `Γ(M, U) = Γ(M, U') ⊗_{Γ(X, U')} Γ(X, U)`.

## Main definitions

* `moduleOfLE` and `algebraOfLE` record the module and algebra structures on sections obtained
  by restricting scalars along a restriction map of the structure sheaf, and `restrictₗ` is the
  restriction map on sections of `M` as a linear map for these structures.
* `baseChangeEquiv` is the resulting linear equivalence
  `Γ(X, U) ⊗_{Γ(X, U')} Γ(M, U') ≃ₗ[Γ(X, U)] Γ(M, U)`.

## Main results

* `isLocalizedModule_restrictₗ`: for `U` an affine open and `a : Γ(X, U)`, the sections of a
  quasi-coherent `M` over `X.basicOpen a` are the localization of `Γ(M, U)` away from `a`.
* `isBaseChange_of_span`: being a base change is local on the base; this is the purely
  algebraic local-to-global step.
* `isBaseChange_restrictₗ`: the main result, as described above.

## Implementation notes

For `U ≤ V` the ring `Γ(X, U)` is not an algebra over `Γ(X, V)` by instance search (the
relation `U ≤ V` is not recoverable from the types), so the relevant `Algebra`, `Module` and
`IsScalarTower` instances are provided explicitly by `algebraOfLE`, `moduleOfLE` and
`isScalarTowerOfLE`, and appear as `letI`s in the statements below. Mathlib's instance
`AlgebraicGeometry.Scheme.algebra_section_section_basicOpen` is the special case
`algebraOfLE X (X.basicOpen_le f)` of `algebraOfLE`.

The basic-open case `isLocalizedModule_restrictₗ` is obtained from Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing` by restricting `M` along
`IsAffineOpen.fromSpec`; `smul_restrict` is the computation identifying the `Γ(X, U)`-action
on the sections of that restriction with restriction of scalars along `𝒪_X`.

The passage from basic opens to a general affine open `U ≤ U'` is a local-to-global argument:
the basic opens `X.basicOpen a` for `a : Γ(X, U')` that are contained in `U` cover `U`, their
restrictions to `U` generate the unit ideal of `Γ(X, U)`, and bijectivity of the canonical map
`Γ(X, U) ⊗_{Γ(X, U')} Γ(M, U') → Γ(M, U)` may be checked after localizing at each of them.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Restriction of sections of a module along the inclusion of a standard open, as a map of
modules over the sections of the structure sheaf. -/
public noncomputable def basicOpenSectionMap {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (r : Γ(X, U)) :
    letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen r) := by
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
  refine { (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom with
    map_smul' := ?_ }
  intro a m
  change (M.presheaf.map (homOfLE (X.basicOpen_le r)).op) (a • m) =
    X.presheaf.map (homOfLE (X.basicOpen_le r)).op a •
      (M.presheaf.map (homOfLE (X.basicOpen_le r)).op) m
  exact M.map_smul (homOfLE (X.basicOpen_le r)) a m

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X : Scheme.{u}}

/-- The `Γ(X, V)`-algebra structure on `Γ(X, U)` for `U ≤ V`. -/
@[instance_reducible]
noncomputable def algebraOfLE (X : Scheme.{u}) {U V : X.Opens} (h : U ≤ V) :
    Algebra Γ(X, V) Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- The `Γ(X, V)`-module structure on `Γ(M, U)` for `U ≤ V`. -/
@[instance_reducible]
noncomputable def moduleOfLE (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Module Γ(X, V) Γ(M, U) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

/-- Restriction of sections, as a `Γ(X, V)`-linear map. -/
noncomputable def restrictₗ (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    letI := moduleOfLE M h
    Γ(M, V) →ₗ[Γ(X, V)] Γ(M, U) :=
  letI := moduleOfLE M h
  { toFun := M.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x ↦ M.map_smul (homOfLE h) r x }

/-- Restriction of sections over an affine scheme, as a linear map over the base ring. -/
noncomputable def specRestrictₗ {R : CommRingCat.{u}} (M : (Spec R).Modules)
    {U V : (Spec R).Opens} (h : U ≤ V) : Γ(M, V) →ₗ[R] Γ(M, U) where
  toFun := M.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := M.map_smul_Spec (homOfLE h).op r x

/-- On `Spec R`, the sections of a quasi-coherent module over a basic open are the localization
of its global sections. -/
theorem specIsLocalizedModule {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a : R) {W : (Spec R).Opens} (hW : W = PrimeSpectrum.basicOpen a) :
    IsLocalizedModule.Away a (specRestrictₗ M (le_top (a := W))) := by
  subst hW
  exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance a

/-- The image under `IsAffineOpen.fromSpec` of an open of `Spec Γ(X, U)` lands in `U`. -/
theorem fromSpec_image_le {U : X.Opens} (hU : IsAffineOpen U) (W : (Spec Γ(X, U)).Opens) :
    hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

/-- The `Γ(X, U)`-action on the sections of the restriction of `M` to `Spec Γ(X, U)` is the
one obtained by restricting sections of `𝒪_X` from `U`. -/
theorem smul_restrict (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) (x : Γ((M.restrict hU.fromSpec), W)) :
    (Scheme.Modules.restrictAppIso hU.fromSpec M W).hom (r • x) =
      (X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r) •
        ((Scheme.Modules.restrictAppIso hU.fromSpec M W).hom x) := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_restrictAppIso_hom_apply]
  congr 1
  have h : X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op ≫ (hU.fromSpec.appIso W).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
      Category.assoc, ← Functor.map_comp]
    rfl
  rw [← Iso.eq_comp_inv] at h
  exact congr($(h.symm).hom r)

/-- Sections of the restriction of `M` to `Spec Γ(X, U)` are the sections of `M` on the image. -/
noncomputable def restrictSectionsEquiv (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) :
    letI := moduleOfLE M (fromSpec_image_le hU W)
    Γ((M.restrict hU.fromSpec), W) ≃ₗ[Γ(X, U)] Γ(M, hU.fromSpec ''ᵁ W) :=
  letI := moduleOfLE M (fromSpec_image_le hU W)
  { toFun := (Scheme.Modules.restrictAppIso hU.fromSpec M W).hom
    invFun := (Scheme.Modules.restrictAppIso hU.fromSpec M W).inv
    map_add' := map_add _
    map_smul' := smul_restrict M hU W
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Transport of sections along an equality of opens. -/
noncomputable def sectionsCongr (M : X.Modules) {U V V' : X.Opens} (hVV' : V = V')
    (hV : V ≤ U) (hV' : V' ≤ U) :
    letI := moduleOfLE M hV
    letI := moduleOfLE M hV'
    Γ(M, V) ≃ₗ[Γ(X, U)] Γ(M, V') :=
  letI := moduleOfLE M hV
  letI := moduleOfLE M hV'
  { toFun := M.presheaf.map (eqToHom hVV'.symm).op
    invFun := M.presheaf.map (eqToHom hVV').op
    map_add' := map_add _
    map_smul' := fun r x ↦ by
      have hring : (X.presheaf.map (eqToHom hVV'.symm).op) ((X.presheaf.map (homOfLE hV).op) r)
          = (X.presheaf.map (homOfLE hV').op) r := by
        rw [← Functor.map_comp_apply]; rfl
      refine (M.map_smul (eqToHom hVV'.symm) (X.presheaf.map (homOfLE hV).op r) x).trans ?_
      rw [hring]
      rfl
    left_inv := fun _ ↦ by
      rw [← Functor.map_comp_apply,
        show (eqToHom hVV'.symm).op ≫ (eqToHom hVV').op = 𝟙 _ from rfl, M.presheaf.map_id]
      rfl
    right_inv := fun _ ↦ by
      rw [← Functor.map_comp_apply,
        show (eqToHom hVV').op ≫ (eqToHom hVV'.symm).op = 𝟙 _ from rfl, M.presheaf.map_id]
      rfl }

/-- Transport of sections along an equality identifying an open with the ambient affine open. -/
noncomputable def sectionsCongrSelf (M : X.Modules) {U V : X.Opens} (hVU' : V = U)
    (hVU : V ≤ U) :
    letI := moduleOfLE M hVU
    Γ(M, V) ≃ₗ[Γ(X, U)] Γ(M, U) :=
  letI := moduleOfLE M hVU
  { toFun := M.presheaf.map (eqToHom hVU'.symm).op
    invFun := M.presheaf.map (eqToHom hVU').op
    map_add' := map_add _
    map_smul' := fun r x ↦ by
      refine (M.map_smul (eqToHom hVU'.symm) (X.presheaf.map (homOfLE hVU).op r) x).trans ?_
      congr 1
      rw [← Functor.map_comp_apply,
        show (homOfLE hVU).op ≫ (eqToHom hVU'.symm).op = 𝟙 _ from rfl, X.presheaf.map_id]
      rfl
    left_inv := fun _ ↦ by
      rw [← Functor.map_comp_apply,
        show (eqToHom hVU'.symm).op ≫ (eqToHom hVU').op = 𝟙 _ from rfl, M.presheaf.map_id]
      rfl
    right_inv := fun _ ↦ by
      rw [← Functor.map_comp_apply,
        show (eqToHom hVU').op ≫ (eqToHom hVU'.symm).op = 𝟙 _ from rfl, M.presheaf.map_id]
      rfl }

/-- Applying two restriction maps of sections of a module in a row is a single restriction map. -/
private theorem map_map_apply (M : X.Modules) {U V W : X.Opens} (f : op V ⟶ op U)
    (g : op W ⟶ op V) (k : op W ⟶ op U) (x : Γ(M, W)) :
    M.presheaf.map f (M.presheaf.map g x) = M.presheaf.map k x := by
  rw [← Functor.map_comp_apply]
  rfl

/-- Sections of a quasi-coherent module over a basic open of an affine open are the localization
of its sections over that affine open. -/
theorem isLocalizedModule_restrictₗ (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) {V : X.Opens} (hV : V = X.basicOpen a) (hVU : V ≤ U) :
    letI := moduleOfLE M hVU
    IsLocalizedModule.Away a (restrictₗ M hVU) := by
  let := moduleOfLE M hVU
  have hWb : (hU.fromSpec ⁻¹ᵁ X.basicOpen a) = PrimeSpectrum.basicOpen a :=
    hU.fromSpec_preimage_basicOpen a
  have hWimg : hU.fromSpec ''ᵁ (hU.fromSpec ⁻¹ᵁ X.basicOpen a) = V := by
    rw [hWb, hU.fromSpec_image_basicOpen, hV]
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  set ι₁ := (restrictSectionsEquiv M hU ⊤).trans
    (sectionsCongrSelf M hTop (fromSpec_image_le hU ⊤)) with hι₁
  set ι₂ := (restrictSectionsEquiv M hU (hU.fromSpec ⁻¹ᵁ X.basicOpen a)).trans
    (sectionsCongr M hWimg (fromSpec_image_le hU _) hVU) with hι₂
  have hψ : IsLocalizedModule.Away a
      (specRestrictₗ (M.restrict hU.fromSpec)
        (le_top (a := hU.fromSpec ⁻¹ᵁ X.basicOpen a))) :=
    specIsLocalizedModule _ a hWb
  have h1 : IsLocalizedModule.Away a (ι₂.toLinearMap ∘ₗ
      specRestrictₗ (M.restrict hU.fromSpec)
        (le_top (a := hU.fromSpec ⁻¹ᵁ X.basicOpen a))) :=
    have := hψ
    IsLocalizedModule.of_linearEquiv (Submonoid.powers a) _ ι₂
  have heq : ι₂.toLinearMap ∘ₗ
      specRestrictₗ (M.restrict hU.fromSpec)
        (le_top (a := hU.fromSpec ⁻¹ᵁ X.basicOpen a)) =
      restrictₗ M hVU ∘ₗ ι₁.toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ : ∃ y : Γ(M, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)), y = x := ⟨x, rfl⟩
    exact (map_map_apply M _ _ (homOfLE (hVU.trans hTop.ge)).op y).trans
      (map_map_apply M _ _ _ y).symm
  rw [heq] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers a)
    ι₁.toLinearMap ι₁.bijective).mp h1

/-- Being a base change is local on the base: if `A → B` is a ring map, `res : N →ₗ[A] P` with
`P` a `B`-module, and there is a family `s` of elements of `B` generating the unit ideal such
that after localizing at each `r ∈ s` the map `res` becomes a base change, then `res` itself
exhibits `P` as the base change of `N`. -/
theorem isBaseChange_of_span
    {A B N P : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] [Module B P]
    [IsScalarTower A B P] (res : N →ₗ[A] P)
    (s : Set B) (hs : Ideal.span s = ⊤)
    (T : s → Type u) [∀ r : s, CommRing (T r)] [∀ r : s, Algebra A (T r)]
    [∀ r : s, Algebra B (T r)] [∀ r : s, IsScalarTower A B (T r)]
    [∀ r : s, IsLocalization.Away r.1 (T r)]
    (Q : s → Type u) [∀ r : s, AddCommGroup (Q r)] [∀ r : s, Module A (Q r)]
    [∀ r : s, Module B (Q r)] [∀ r : s, Module (T r) (Q r)]
    [∀ r : s, IsScalarTower A (T r) (Q r)] [∀ r : s, IsScalarTower B (T r) (Q r)]
    (n : ∀ r : s, N →ₗ[A] Q r) (p : ∀ r : s, P →ₗ[B] Q r)
    (hn : ∀ r : s, IsBaseChange (T r) (n r))
    [∀ r : s, IsLocalizedModule.Away r.1 (p r)]
    (hcomp : ∀ (r : s) (x : N), p r (res x) = n r x) :
    IsBaseChange B res := by
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (res.liftBaseChange B) ?_) (fun x ↦ ?_)
  · refine bijective_of_isLocalized_span s hs (fun r ↦ TensorProduct A (T r) N)
      (fun r ↦ TensorProduct.AlgebraTensorModule.rTensor A N (Algebra.linearMap B (T r))) Q p
      (res.liftBaseChange B) (fun r ↦ ?_)
    have key : IsLocalizedModule.map (Submonoid.powers r.1)
        (TensorProduct.AlgebraTensorModule.rTensor A N (Algebra.linearMap B (T r))) (p r)
        (res.liftBaseChange B)
        = LinearMap.restrictScalars B (hn r).equiv.toLinearMap := by
      refine IsLocalizedModule.linearMap_ext (Submonoid.powers r.1)
        (TensorProduct.AlgebraTensorModule.rTensor A N (Algebra.linearMap B (T r))) (p r) ?_
      rw [IsLocalizedModule.map_comp]
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.inductionOn with
      | tmul b x => simp [hcomp, IsBaseChange.equiv_tmul, algebraMap_smul]
      | add z w h1 h2 => simp only [map_add, h1, h2]
    rw [key]
    exact (hn r).equiv.bijective
  · simp

/-- The scalar tower `Γ(X, V) → Γ(X, U) → Γ(M, U)` for `U ≤ V`. -/
theorem isScalarTowerOfLE (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    letI := algebraOfLE X h
    letI := moduleOfLE M h
    IsScalarTower Γ(X, V) Γ(X, U) Γ(M, U) :=
  let := algebraOfLE X h
  let := moduleOfLE M h
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The restriction map on sections of a quasi-coherent module between nested affine opens
exhibits the smaller sections as the base change of the larger ones. -/
theorem isBaseChange_restrictₗ (M : X.Modules) [M.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algebraOfLE X h
    letI := moduleOfLE M h
    letI := isScalarTowerOfLE M h
    IsBaseChange Γ(X, U) (restrictₗ M h) := by
  let := algebraOfLE X h
  let := moduleOfLE M h
  let := isScalarTowerOfLE M h
  set s : Set Γ(X, U) :=
    {r | ∃ a : Γ(X, U'), X.basicOpen a ≤ U ∧ r = X.presheaf.map (homOfLE h).op a} with hsdef
  have hex : ∀ r : s, ∃ a : Γ(X, U'),
      X.basicOpen a ≤ U ∧ (r : Γ(X, U)) = X.presheaf.map (homOfLE h).op a := fun r ↦ r.2
  choose aa haa1 haa2 using hex
  have hbasic : ∀ r : s, X.basicOpen (r : Γ(X, U)) = X.basicOpen (aa r) := fun r ↦ by
    rw [haa2 r, Scheme.basicOpen_res, inf_eq_right.mpr (haa1 r)]
  have hle : ∀ r : s, X.basicOpen (r : Γ(X, U)) ≤ U' := fun r ↦ (X.basicOpen_le _).trans h
  let : ∀ r : s, Algebra Γ(X, U') Γ(X, X.basicOpen (r : Γ(X, U))) :=
    fun r ↦ algebraOfLE X (hle r)
  let : ∀ r : s, Module Γ(X, U') Γ(M, X.basicOpen (r : Γ(X, U))) :=
    fun r ↦ moduleOfLE M (hle r)
  let : ∀ r : s, Module Γ(X, U) Γ(M, X.basicOpen (r : Γ(X, U))) :=
    fun r ↦ moduleOfLE M (X.basicOpen_le _)
  let : ∀ r : s, IsScalarTower Γ(X, U') Γ(X, X.basicOpen (r : Γ(X, U)))
      Γ(M, X.basicOpen (r : Γ(X, U))) := fun r ↦ isScalarTowerOfLE M (hle r)
  let : ∀ r : s, IsScalarTower Γ(X, U) Γ(X, X.basicOpen (r : Γ(X, U)))
      Γ(M, X.basicOpen (r : Γ(X, U))) := fun r ↦ isScalarTowerOfLE M (X.basicOpen_le _)
  let : ∀ r : s, IsLocalization.Away (r : Γ(X, U)) Γ(X, X.basicOpen (r : Γ(X, U))) :=
    fun r ↦ hU.isLocalization_basicOpen _
  let : ∀ r : s, IsScalarTower Γ(X, U') Γ(X, U) Γ(X, X.basicOpen (r : Γ(X, U))) := fun r ↦
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change (X.presheaf.map (homOfLE (hle r)).op) c =
        (X.presheaf.map (homOfLE (X.basicOpen_le (r : Γ(X, U)))).op)
          ((X.presheaf.map (homOfLE h).op) c)
      rw [← Functor.map_comp_apply]
      rfl
  let : ∀ r : s, IsLocalizedModule.Away (r : Γ(X, U))
      (restrictₗ M (X.basicOpen_le (r : Γ(X, U)))) :=
    fun r ↦ isLocalizedModule_restrictₗ M hU _ rfl _
  refine isBaseChange_of_span (restrictₗ M h) s ?_
    (fun r ↦ Γ(X, X.basicOpen (r : Γ(X, U)))) (fun r ↦ Γ(M, X.basicOpen (r : Γ(X, U))))
    (fun r ↦ restrictₗ M (hle r)) (fun r ↦ restrictₗ M (X.basicOpen_le _)) (fun r ↦ ?_) ?_
  · rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf₁, hf₂⟩ := hU'.exists_basicOpen_le (⟨x, hx⟩ : U) (h hx)
    refine Opens.mem_iSup.mpr ⟨⟨X.presheaf.map (homOfLE h).op f, f, hf₁, rfl⟩, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hf₂⟩
  · have : IsLocalization.Away (aa r) Γ(X, X.basicOpen (r : Γ(X, U))) :=
      hU'.isLocalization_of_eq_basicOpen (aa r) (homOfLE (hle r)) (hbasic r)
    have : IsLocalizedModule.Away (aa r) (restrictₗ M (hle r)) :=
      isLocalizedModule_restrictₗ M hU' (aa r) (hbasic r) (hle r)
    exact IsLocalizedModule.isBaseChange (Submonoid.powers (aa r))
      Γ(X, X.basicOpen (r : Γ(X, U))) (restrictₗ M (hle r))
  · intro r x
    exact map_map_apply ..

/-- For a quasi-coherent module `M` on a scheme `X` and affine opens `U ≤ U'` of `X`, the
sections of `M` over `U` are the base change of the sections over `U'` along the restriction
map `Γ(X, U') ⟶ Γ(X, U)`. -/
noncomputable def baseChangeEquiv (M : X.Modules) [M.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algebraOfLE X h
    TensorProduct Γ(X, U') Γ(X, U) Γ(M, U') ≃ₗ[Γ(X, U)] Γ(M, U) :=
  letI := algebraOfLE X h
  letI := moduleOfLE M h
  letI := isScalarTowerOfLE M h
  (isBaseChange_restrictₗ M hU hU' h).equiv

/-- The equivalence `baseChangeEquiv` sends `1 ⊗ x` to the restriction of the section `x` of
`M` from `U'` to `U`. -/
@[simp]
theorem baseChangeEquiv_one_tmul (M : X.Modules) [M.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') (x : Γ(M, U')) :
    letI := algebraOfLE X h
    baseChangeEquiv M hU hU' h (1 ⊗ₜ[Γ(X, U')] x) = M.presheaf.map (homOfLE h).op x :=
  let := algebraOfLE X h
  let := moduleOfLE M h
  let := isScalarTowerOfLE M h
  ((isBaseChange_restrictₗ M hU hU' h).equiv_tmul 1 x).trans (one_smul _ _)

end Stacks.AlgebraicGeometry.QuasicoherentBaseChange

end
