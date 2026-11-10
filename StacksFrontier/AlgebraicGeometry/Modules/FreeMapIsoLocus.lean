module

public import StacksFrontier.AlgebraicGeometry.Modules.FreeSectionsBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank

/-!
# Morphisms out of a finite free module given by global sections, and their iso locus

A family `s : Fin r → Γ(M, ⊤)` of global sections of a module `M` on a scheme `Z` defines a
morphism `𝒪_Z^r ⟶ M` sending the `i`-th basis section to `s i`. This file records how such
morphisms behave under composition and pullback, when they are isomorphisms, and where a
morphism `𝒪_Z^r ⟶ M` into a module of finite type becomes an isomorphism after base change.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.freeHomOfSections`: the morphism `𝒪_Z^r ⟶ M` given by a
  family of global sections.

## Main results

* `AlgebraicGeometry.Scheme.Modules.freeHomOfSections_comp`: composing with `τ : M ⟶ N` maps the
  sections through `τ`.
* `AlgebraicGeometry.Scheme.Modules.bijective_app_top_freeHomOfSections`: the morphism given by a
  basis of `Γ(M, ⊤)` is bijective on global sections.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_app_top`: an endomorphism of `𝒪_Z^r`
  which is bijective on global sections is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.pullback_map_freeHomOfSections`: pulling back the morphism
  given by sections is the morphism given by the pulled back sections.
* `AlgebraicGeometry.Scheme.Modules.exists_isoLocus`: **the iso locus.** For `M` of finite type
  and `φ : 𝒪_Z^r ⟶ M` there is an open `U ⊆ Z` such that, for every `h : T ⟶ Z` along which `M`
  pulls back to a finite locally free module of rank `r`, `h^*φ` is an isomorphism exactly when
  `h` factors through `U`.

## Implementation notes

The free module is written `Scheme.Modules.free Z ι`, so that the module structure of its
sections over `Γ(Z, ⊤)` is found, and its global sections are read through the basis
`AlgebraicGeometry.freeSectionsBasis`. A morphism out of `𝒪_Z^r` is determined by the images of
these basis sections (`free_hom_ext`), which is how every identity between such morphisms here is
proved; in particular no matrix calculus is needed for `isIso_of_bijective_app_top`, the inverse
being the morphism given by the preimages of the basis sections.

The iso locus is the complement of the support of `cokernel φ`, closed because the cokernel is of
finite type. Pullback is right exact and the support of a pullback of a module of finite type is
the preimage of the support (Stacks 056J), so `h^*φ` is surjective exactly over that complement;
when source and target of `h^*φ` are finite locally free of the same rank `r`, surjectivity is
equivalent to invertibility (Stacks 089Q).

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Z : Scheme.{u}} {r : ℕ}

/-- The morphism `𝒪_Z^r ⟶ M` sending the `i`-th basis section to `s i`. -/
def freeHomOfSections (M : Z.Modules) (s : Fin r → Γ(M, ⊤)) :
    Scheme.Modules.free Z (ULift.{u} (Fin r)) ⟶ M :=
  (_root_.SheafOfModules.freeHomEquiv M).symm fun i ↦
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M isTerminalTop).symm
      (s i.down)

/-- On the `j`-th basis section, `freeHomOfSections M s` is `s j`. -/
@[simp]
theorem freeHomOfSections_app_freeSectionsBasis (M : Z.Modules) (s : Fin r → Γ(M, ⊤))
    (j : Fin r) :
    (freeHomOfSections M s).app ⊤ (freeSectionsBasis Z r j) = s j := by
  rw [freeSectionsBasis_apply]
  have h := congrArg (fun t : M.sections ↦ t.val (op ⊤))
    (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i : ULift.{u} (Fin r) ↦
        (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M isTerminalTop).symm
          (s i.down)) ⟨j⟩)
  exact h.trans ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
    isTerminalTop).apply_symm_apply (s j))

/-- Two morphisms out of `𝒪_Z^r` agreeing on the basis sections are equal. -/
theorem free_hom_ext {N : Z.Modules} {f g : Scheme.Modules.free Z (ULift.{u} (Fin r)) ⟶ N}
    (h : ∀ j, f.app ⊤ (freeSectionsBasis Z r j) = g.app ⊤ (freeSectionsBasis Z r j)) :
    f = g := by
  apply (_root_.SheafOfModules.freeHomEquiv N).injective
  funext i
  apply (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N isTerminalTop).injective
  have hj := h i.down
  rw [freeSectionsBasis_apply] at hj
  exact hj

/-- **Composing with a morphism of modules** maps the sections through it. -/
theorem freeHomOfSections_comp {M N : Z.Modules} (s : Fin r → Γ(M, ⊤)) (τ : M ⟶ N) :
    freeHomOfSections M s ≫ τ = freeHomOfSections N (fun i ↦ τ.app ⊤ (s i)) :=
  free_hom_ext fun j ↦ by
    rw [freeHomOfSections_app_freeSectionsBasis]
    exact congrArg (τ.app ⊤) (freeHomOfSections_app_freeSectionsBasis M s j)

/-- If `s` is a basis of `Γ(M, ⊤)`, then `freeHomOfSections M s` is bijective on global
sections. -/
theorem bijective_app_top_freeHomOfSections_of_basis (M : Z.Modules)
    (b : Module.Basis (Fin r) Γ(Z, ⊤) Γ(M, ⊤)) :
    Function.Bijective ((freeHomOfSections M b).app ⊤) := by
  let L : Γ(Scheme.Modules.free Z (ULift.{u} (Fin r)), ⊤) →ₗ[Γ(Z, ⊤)] Γ(M, ⊤) :=
    { toFun := (freeHomOfSections M b).app ⊤
      map_add' := map_add _
      map_smul' := Hom.app_smul _ }
  have hL : L = ((freeSectionsBasis Z r).equiv b (Equiv.refl _)).toLinearMap := by
    refine (freeSectionsBasis Z r).ext fun j ↦ ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact freeHomOfSections_app_freeSectionsBasis M b j
  change Function.Bijective L
  rw [hL]
  exact LinearEquiv.bijective _

/-- If `s` is linearly independent and spans `Γ(M, ⊤)`, then `freeHomOfSections M s` is
bijective on global sections. -/
theorem bijective_app_top_freeHomOfSections (M : Z.Modules) (s : Fin r → Γ(M, ⊤))
    (hli : LinearIndependent Γ(Z, ⊤) s) (hsp : Submodule.span Γ(Z, ⊤) (Set.range s) = ⊤) :
    Function.Bijective ((freeHomOfSections M s).app ⊤) := by
  have := bijective_app_top_freeHomOfSections_of_basis M (Module.Basis.mk hli hsp.ge)
  rwa [Module.Basis.coe_mk] at this

/-- If `e ≫ e' = 𝟙 M`, then `e'` undoes `e` on global sections. -/
private theorem app_top_comp_eq_self {M N : Z.Modules} (e : M ⟶ N) (e' : N ⟶ M) (h : e ≫ e' = 𝟙 M)
    (x : Γ(M, ⊤)) : e'.app ⊤ (e.app ⊤ x) = x :=
  congrArg (fun φ ↦ φ.app ⊤ x) h

/-- An endomorphism of `𝒪_Z^r` which is bijective on global sections is an isomorphism. -/
theorem isIso_of_bijective_app_top
    (ψ : Scheme.Modules.free Z (ULift.{u} (Fin r)) ⟶ Scheme.Modules.free Z (ULift.{u} (Fin r)))
    (hψ : Function.Bijective (ψ.app ⊤)) : IsIso ψ := by
  let g := Equiv.ofBijective _ hψ
  let χ := freeHomOfSections (Scheme.Modules.free Z (ULift.{u} (Fin r)))
    (fun j ↦ g.symm (freeSectionsBasis Z r j))
  have h₁ : χ ≫ ψ = 𝟙 _ := free_hom_ext fun j ↦ by
    rw [Hom.comp_app, CategoryTheory.comp_apply, freeHomOfSections_app_freeSectionsBasis]
    exact g.apply_symm_apply _
  exact ⟨χ, free_hom_ext fun j ↦
    hψ.1 (app_top_comp_eq_self χ ψ h₁ _), h₁⟩

/-- **Pulling back the morphism given by sections** gives the morphism given by the pulled back
sections, once the pullback of `𝒪_Z^r` is identified with `𝒪_T^r`. -/
theorem pullback_map_freeHomOfSections {T : Scheme.{u}} (h : T ⟶ Z) (M : Z.Modules)
    (s : Fin r → Γ(M, ⊤)) :
    (Scheme.Modules.pullback h).map (freeHomOfSections M s) =
      (schemeModulesPullbackObjFreeIso h (ULift.{u} (Fin r))).hom ≫
        freeHomOfSections ((Scheme.Modules.pullback h).obj M)
          (fun i ↦ pullbackSectionHom h M ⊤ ⊤ le_top (s i)) := by
  let e : (Scheme.Modules.pullback h).obj (Scheme.Modules.free Z (ULift.{u} (Fin r))) ≅
      Scheme.Modules.free T (ULift.{u} (Fin r)) :=
    schemeModulesPullbackObjFreeIso h (ULift.{u} (Fin r))
  refine (Iso.inv_comp_eq e).1 (free_hom_ext fun j ↦ ?_)
  rw [freeHomOfSections_app_freeSectionsBasis, Hom.comp_app, CategoryTheory.comp_apply,
    ← schemeModulesPullbackObjFreeIso_hom_pullbackSectionHom h r le_top j]
  refine (congrArg _ (app_top_comp_eq_self e.hom e.inv e.hom_inv_id _)).trans ?_
  exact (pullbackSectionHom_naturality_apply h (freeHomOfSections M s) ⊤ ⊤ le_top _).trans
    (congrArg _ (freeHomOfSections_app_freeSectionsBasis M s j))

/-! ### The locus where a morphism `𝒪_Z^r ⟶ M` becomes an isomorphism -/

/-- A module on a scheme is zero exactly when its support is empty. -/
theorem isZero_iff_supp_eq_empty {X : Scheme.{u}} (N : X.Modules) :
    IsZero N ↔ _root_.SheafOfModules.supp N = ∅ :=
  ⟨fun hN ↦ _root_.SheafOfModules.supp_eq_empty_of_isZero hN,
    fun hN ↦ _root_.SheafOfModules.isZero_of_supp_eq_empty N hN⟩

/-- **The pullback of a morphism into a module of finite type is surjective exactly over the
complement of the support of its cokernel.** -/
theorem epi_pullback_map_iff_range_subset {X T : Scheme.{u}} {N P : X.Modules} [P.IsFiniteType]
    (p : N ⟶ P) (h : T ⟶ X) :
    Epi ((Scheme.Modules.pullback h).map p) ↔
      Set.range h ⊆ (_root_.SheafOfModules.supp (cokernel p))ᶜ := by
  have : (cokernel p).IsFiniteType := isFiniteType_cokernel p ‹_›
  let F := Scheme.Modules.pullback h
  let : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction h).leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel, ← (PreservesCokernel.iso F p).isZero_iff,
    isZero_iff_supp_eq_empty, Stacks.Modules.supp_pullback]
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_preimage, Set.range_subset_iff,
    Set.mem_compl_iff]
  exact Iff.rfl

/-- **The iso locus of a morphism `𝒪_Z^r ⟶ M` into a module of finite type.** There is an open
`U` of `Z` such that for every morphism `h : T ⟶ Z` along which `M` pulls back to a finite
locally free module of rank `r`, the pullback of `φ` is an isomorphism exactly when `h` factors
through `U`. The open `U` is the complement of the support of the cokernel of `φ`. -/
theorem exists_isoLocus {Z : Scheme.{u}} (M : Z.Modules) [M.IsFiniteType] {r : ℕ}
    (φ : _root_.SheafOfModules.free (ULift.{u} (Fin r)) ⟶ M) :
    ∃ U : Z.Opens, ∀ {T : Scheme.{u}} (h : T ⟶ Z),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback h).obj M) r →
      (IsIso ((Scheme.Modules.pullback h).map φ) ↔ Set.range h ⊆ U) := by
  let φ' : Scheme.Modules.free Z (ULift.{u} (Fin r)) ⟶ M := φ
  refine ⟨⟨(_root_.SheafOfModules.supp (cokernel φ'))ᶜ,
    (isClosed_supp_cokernel φ' ‹_›).isOpen_compl⟩, fun {T} h hrank ↦ ?_⟩
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj (Scheme.Modules.free Z (ULift.{u} (Fin r)))) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (schemeModulesPullbackObjFreeIso h (ULift.{u} (Fin r))).symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv _ r Equiv.ulift)
  exact (@Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    T.toLocallyRingedSpace.toRingedSpace inferInstance inferInstance _ _ r hF hrank
    ((Scheme.Modules.pullback h).map φ')).trans (epi_pullback_map_iff_range_subset φ' h)

end AlgebraicGeometry.Scheme.Modules

end
