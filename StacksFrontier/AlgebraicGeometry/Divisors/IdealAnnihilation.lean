module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealActionSections
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishingOpenImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice

/-!
# Modules annihilated by an ideal sheaf

A module `M` on a scheme `X` is annihilated by an ideal sheaf `J` when every local function in
`J` kills every local section of `M`. By [Stacks, Tag 08KS] this says exactly that `M` is a
direct image from the closed subscheme `V(J)`.

## Main definitions

* `Stacks.Divisors.IsAnnihilatedBy`: `J` kills every local section of `M`.

## Main results

* `Stacks.Divisors.isAnnihilatedBy_iff_essImage`: `M` is killed by `J` exactly when it is a direct
  image from `V(J)`.
* `Stacks.Divisors.IsAnnihilatedBy.pullback`: annihilation is preserved by inverse image along an
  arbitrary morphism, for quasi-coherent `M`.
* `Stacks.Divisors.isAnnihilatedBy_of_cover`: annihilation is local on an open cover.
* `Stacks.Divisors.idealAction_comp_cokernelπ_eq_zero`: if `J` kills `coker φ`, the action of
  `ℐ_J` dies modulo `φ`.
* `Stacks.Divisors.isAnnihilatedBy_cokernel_of_sections`: a pole bound stated on sections gives
  annihilation of the cokernel.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- A module is annihilated by an ideal sheaf `J` when every local function in `J` kills every
local section of it. -/
def IsAnnihilatedBy (J : X.IdealSheafData) (M : X.Modules) : Prop :=
  ∀ (U : X.Opens) (a : Γ(X, U)), J.subschemeι.app U a = 0 → ∀ m : Γ(M, U), a • m = 0

/-- `M` is killed by `J` exactly when it is a direct image from `V(J)`. -/
theorem isAnnihilatedBy_iff_essImage (J : X.IdealSheafData) (M : X.Modules) :
    IsAnnihilatedBy J M ↔ (Scheme.Modules.pushforward J.subschemeι).essImage M :=
  (Stacks.ClosedImmersion.pushforward_essImage_iff J.subschemeι M).symm

/-- Annihilation is invariant under isomorphism. -/
theorem IsAnnihilatedBy.of_iso {J : X.IdealSheafData} {M N : X.Modules} (h : IsAnnihilatedBy J M)
    (e : M ≅ N) : IsAnnihilatedBy J N := by
  rw [isAnnihilatedBy_iff_essImage] at h ⊢
  exact (Scheme.Modules.pushforward J.subschemeι).essImage.prop_of_iso e h

/-- The zero module is killed by every ideal sheaf. -/
theorem isAnnihilatedBy_of_isZero (J : X.IdealSheafData) {M : X.Modules} (hM : IsZero M) :
    IsAnnihilatedBy J M := by
  intro U a _ m
  have : Subsingleton Γ(M, U) := by
    refine ⟨fun x y ↦ ?_⟩
    have h := hM.eq_of_src (𝟙 M) 0
    have hx : x = (𝟙 M : M ⟶ M).app U x := rfl
    have hy : y = (𝟙 M : M ⟶ M).app U y := rfl
    rw [hx, hy, h]
    simp
  exact Subsingleton.elim _ _

/-- The closed subscheme cut out by the inverse image of an ideal sheaf is the inverse image of the
closed subscheme. -/
theorem isPullback_comap_subschemeι {Y : Scheme.{u}} (h : Y ⟶ X) (J : X.IdealSheafData) :
    IsPullback (Scheme.IdealSheafData.subschemeMap (J.comap h) J h (J.le_map_comap h))
      (J.comap h).subschemeι J.subschemeι h :=
  (AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])).flip

/-- **Annihilation by an ideal sheaf is preserved by inverse image**, for a quasi-coherent module:
if `J` kills `M`, then `h⁻¹J` kills `h^*M`. -/
theorem IsAnnihilatedBy.pullback {Y : Scheme.{u}} (h : Y ⟶ X) {J : X.IdealSheafData}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsAnnihilatedBy J M) :
    IsAnnihilatedBy (J.comap h) ((Scheme.Modules.pullback h).obj M) := by
  have hu := Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero J.subschemeι M hM
  have hN : ((Scheme.Modules.pullback J.subschemeι).obj M).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ M
  have hbc := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_comap_subschemeι h J) ((Scheme.Modules.pullback J.subschemeι).obj M)
  rw [isAnnihilatedBy_iff_essImage]
  exact ⟨_, ⟨((Scheme.Modules.pullback h).mapIso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app M)) ≪≫
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (isPullback_comap_subschemeι h J).w).app _)).symm⟩⟩

/-- A function killed by a morphism of schemes stays killed after restriction. -/
theorem app_presheaf_map_eq_zero {A B : Scheme.{u}} (g : A ⟶ B) {W₁ W₂ : B.Opens} (i : W₁ ⟶ W₂)
    (x : Γ(B, W₂)) (hx : g.app W₂ x = 0) : g.app W₁ (B.presheaf.map i.op x) = 0 := by
  have := ConcreteCategory.congr_hom (g.naturality i.op) x
  simp only [CategoryTheory.comp_apply] at this
  rw [this, hx, map_zero]

/-- To show `J` kills a section `m`, it suffices to do so locally around every point, after
restricting a function `a` killed by `J`. -/
private theorem smul_eq_zero_of_locally_annihilated (J : X.IdealSheafData) (M : X.Modules)
    {U : X.Opens} (a : Γ(X, U)) (m : Γ(M, U)) (ha : J.subschemeι.app U a = 0)
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (g : W ⟶ U), y ∈ W ∧
      (J.subschemeι.app W (X.presheaf.map g.op a) = 0 →
        X.presheaf.map g.op a • M.presheaf.map g.op m = 0)) :
    a • m = 0 := by
  refine Stacks.SheafOfModules.eq_zero_of_locally_zero' M _ fun y hy ↦ ?_
  obtain ⟨W, g, hyW, hW⟩ := h y hy
  refine ⟨W, g, hyW, ?_⟩
  change M.presheaf.map g.op (a • m) = 0
  rw [Scheme.Modules.map_smul]
  exact hW (app_presheaf_map_eq_zero _ _ a ha)

/-- **Annihilation by an ideal sheaf is local**: if over every member of an open cover the
restriction of `M` is killed by the restriction of `J`, then `M` is killed by `J`. -/
theorem isAnnihilatedBy_of_cover (J : X.IdealSheafData) (M : X.Modules) {ι : Type*}
    (V : ι → X.Opens) (hV : iSup V = ⊤)
    (h : ∀ k, IsAnnihilatedBy (J.comap (V k).ι) (M.restrict (V k).ι)) :
    IsAnnihilatedBy J M := by
  intro U a ha m
  refine smul_eq_zero_of_locally_annihilated J M a m ha fun y hy ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k, y ∈ V k :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hV]; trivial)
  set W' : (V k).toScheme.Opens := (V k).ι ⁻¹ᵁ U
  have hWU : (V k).ι ''ᵁ W' ≤ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
  have hyW : y ∈ (V k).ι ''ᵁ W' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hk, hy⟩
  refine ⟨_, homOfLE hWU, hyW, fun haW ↦ ?_⟩
  set aW := X.presheaf.map (homOfLE hWU).op a
  have hw := (isPullback_comap_subschemeι (V k).ι J).w
  have h1 : ((Scheme.IdealSheafData.subschemeMap (J.comap (V k).ι) J (V k).ι
      (J.le_map_comap (V k).ι) ≫ J.subschemeι).app ((V k).ι ''ᵁ W')) aW = 0 := by
    change (Scheme.IdealSheafData.subschemeMap (J.comap (V k).ι) J (V k).ι
      (J.le_map_comap (V k).ι)).app _ (J.subschemeι.app _ aW) = 0
    rw [haW, map_zero]
  have h2 : (((J.comap (V k).ι).subschemeι ≫ (V k).ι).app ((V k).ι ''ᵁ W')) aW = 0 := by
    rwa [← hw]
  change (J.comap (V k).ι).subschemeι.app _ ((V k).ι.app _ aW) = 0 at h2
  have hiso := ConcreteCategory.congr_hom (Scheme.Hom.appIso_hom (V k).ι W') aW
  rw [Scheme.Opens.ι_appIso] at hiso
  change aW = _ at hiso
  have ha' : (J.comap (V k).ι).subschemeι.app W' aW = 0 := by
    rw [hiso]
    exact app_presheaf_map_eq_zero _ _ _ h2
  have hres := h k W' aW ha' (M.presheaf.map (homOfLE hWU).op m)
  have e := Scheme.Modules.smul_restrictAppIso_hom_apply (f := (V k).ι) M W' aW
    (M.presheaf.map (homOfLE hWU).op m)
  rw [Scheme.Opens.ι_appIso] at e
  simp only [Iso.refl_inv] at e
  exact e.symm.trans ((congrArg (M.restrictAppIso (V k).ι W').hom hres).trans (map_zero _))

section Cokernel

variable {F G : X.Modules} (φ : F ⟶ G) (J : X.IdealSheafData)

/-- **The pole bound in annihilator form.** If the cokernel of `φ : F ⟶ G` is killed by `J`,
then the action of `ℐ_J` on `G` dies in the cokernel: `ℐ_J · G ⊆ φ(F)`. -/
theorem idealAction_comp_cokernelπ_eq_zero (h : IsAnnihilatedBy J (cokernel φ)) :
    idealAction J G ≫ cokernel.π φ = 0 :=
  idealAction_comp_eq_zero _ (cokernel.π φ) fun U r s ↦
    (congrArg (fun z ↦ (((cokernel.π φ).val.app U).hom) z)
      (idealAction_val_app_toTensorSheafSection J G U r s)).trans (by
        change (cokernel.π φ).app U.unop (idealSheafSection J r • (show Γ(G, U.unop) from s)) = 0
        rw [Scheme.Modules.Hom.app_smul]
        exact h U.unop _ (subschemeι_app_idealSheafSection J r) _)

/-- **The annihilator form of a pole bound stated on sections.** If the cokernel map of
`φ : F ⟶ G` kills `t • s` for every local section `t` of `ℐ_J` and every local section `s` of
`G`, then `J` kills the cokernel of `φ`. -/
theorem isAnnihilatedBy_cokernel_of_sections
    (h : ∀ (V : X.Opens) (r : (negativeTwist' J).val.obj (op V)) (s : Γ(G, V)),
      (cokernel.π φ).app V (idealSheafSection J r • s) = 0) :
    IsAnnihilatedBy J (cokernel φ) := by
  intro U a ha m
  have hepi : Epi (cokernel.π φ) := inferInstance
  obtain ⟨S, hS, hlift⟩ :=
    @Stacks.SheafOfModules.EpiMono.exists_covering_of_epi _ _ _ _ _ _ G (cokernel φ)
      (cokernel.π φ) hepi U m
  refine smul_eq_zero_of_locally_annihilated J _ a m ha fun y hy ↦ ?_
  obtain ⟨W, g, hg, hyW⟩ := hS y hy
  refine ⟨W, g, hyW, fun haW ↦ ?_⟩
  obtain ⟨t, ht⟩ := hlift g hg
  obtain ⟨r, hr⟩ := (subschemeι_app_eq_zero_iff_exists_idealSheafSection J _).1 haW
  have ht' : (cokernel.π φ).app W (show Γ(G, W) from t) = (cokernel φ).presheaf.map g.op m := ht
  rw [← ht', ← hr, ← Scheme.Modules.Hom.app_smul]
  exact h W r t

end Cokernel

end Stacks.Divisors
