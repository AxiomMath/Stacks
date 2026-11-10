module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AnnihilatorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# The quotient of a module by the sections annihilated by a power of an ideal sheaf

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals of finite type and let `F` be a
quasi-coherent `𝒪_X`-module.  Write `F_n` for the subsheaf of sections annihilated by `Iⁿ`.
This file constructs the quotient `F / F_n` and establishes the two properties of it that
[Stacks, Tag 01PQ] uses: its sections over an open are the sections of `F` modulo `F_n`, and
over an open missing the support of `I` the projection `F ⟶ F / F_n` is bijective on sections.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.annihilatorι`: the inclusion `F_n ⟶ F`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientModule`: the quotient `F / F_n`, formed as
  the cokernel of that inclusion.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientπ`: the projection `F ⟶ F / F_n`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientMap`: for `n ≤ m`, the induced map
  `F / F_n ⟶ F / F_m`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.exact_annihilatorι_app`: over every open the
  sections of `F_n` are the kernel of the projection on sections.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.eq_zero_of_mem_annihilator_of_le_compl_support`:
  `F_n` has no nonzero sections over an open missing the support of `I`, because `Iⁿ` is the
  whole structure sheaf there.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.bijective_quotientπ_app_of_le_compl_support`: the
  projection is therefore bijective on sections over such an open, and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientSectionsEquiv` packages the bijection as
  an isomorphism of additive groups.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientSectionsAffineEquiv`: over an affine open
  `V` the sections of `F / F_n` are `M / M_n`, where `M = Γ(F, V)` and `M_n` is the
  `I(V)ⁿ`-torsion submodule.  This is the step [Stacks, Tag 01PQ] records as "`F_n|_W = M̃_n`
  (details omitted)".

## Implementation notes

**Why a cokernel.** The category `X.Modules` is abelian, so `F / F_n` is available as
`cokernel (annihilatorι I F n)` with no construction of a quotient presheaf and no
sheafification.  What the abstract cokernel does not give for free is its sections, and the two
facts above are exactly the two halves of that.  The kernel half is formal: `F_n ⟶ F` is a
monomorphism, so it is a kernel of its own cokernel
(`CategoryTheory.Abelian.monoLift`), and the sections functor preserves kernels
(`Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel`).  The surjectivity half is not formal —
it is the `H¹`-vanishing of [Stacks, Tag 01XB] in the form
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, available on an affine open, glued up
to an arbitrary open on which `F_n` vanishes so that the local lifts are unique.  This is where
finite generation of `I` is used, through the quasi-coherence of `F_n`.

**The exponent is not uniform.** `F / F_n` is *not* free of `Iⁿ`-power torsion: its sections
annihilated by `I^m` are `F_(n+m) / F_n`.  That is why Tag 01PQ takes a colimit over `n` of
`Hom(Iⁿ, F / F_n)` rather than working at a single exponent, and why
`Stacks.AlgebraicGeometry.IdealPowerColimit.NoIdealTorsion` does not hold for the quotient.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB) (the affine surjectivity)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The inclusion of a submodule subsheaf -/

/-- **The inclusion of a submodule subsheaf is a monomorphism of `𝒪_X`-modules.** -/
instance mono_submoduleι_toSheafOfModules {M : X.Modules} (N : M.Submodule) :
    Mono (N.ι : (N.toSheafOfModules : X.Modules) ⟶ M) :=
  Functor.mono_of_mono_map (Scheme.Modules.toPresheafOfModules X)
    (inferInstanceAs (Mono N.toSubmodule.ι))

/-- The inclusion of a smaller submodule subsheaf into a larger one, followed by the inclusion of
the larger one, is the inclusion of the smaller one. -/
theorem homOfLE_comp_ι {M : X.Modules} {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    (SheafOfModules.Submodule.homOfLE hle :
          (N₁.toSheafOfModules : X.Modules) ⟶ N₂.toSheafOfModules) ≫ N₂.ι = N₁.ι := by
  ext W z
  rfl

/-- The inclusion `F_n ⟶ F` of the sections annihilated by `Iⁿ`. -/
noncomputable abbrev annihilatorι (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    annihilatorModule I F n ⟶ F :=
  (idealPowerAnnihilator I.unitSubmodule F n).ι

/-- The inclusion `F_n ⟶ F` is a monomorphism. -/
instance mono_annihilatorι (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    Mono (annihilatorι I F n) :=
  mono_submoduleι_toSheafOfModules (M := F) (idealPowerAnnihilator I.unitSubmodule F n)

/-- The inclusion `F_n ⟶ F` sends a section of `F_n` to the underlying section of `F`. -/
theorem annihilatorι_app (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) (W : X.Opens)
    (z : Γ(annihilatorModule I F n, W)) :
    (annihilatorι I F n).app W z = annihilatorVal z := rfl

/-- The inclusion `F_n ⟶ F_m` for `n ≤ m`: a section annihilated by `Iⁿ` is annihilated by
`I^m`. -/
noncomputable abbrev annihilatorLE (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ}
    (h : n ≤ m) : annihilatorModule I F n ⟶ annihilatorModule I F m :=
  SheafOfModules.Submodule.homOfLE (idealPowerAnnihilator_monotone I.unitSubmodule F h)

/-- For `n ≤ m`, the inclusion `F_n ⟶ F_m` followed by `F_m ⟶ F` is the inclusion `F_n ⟶ F`. -/
theorem annihilatorLE_comp_annihilatorι (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    annihilatorLE I F h ≫ annihilatorι I F m = annihilatorι I F n :=
  homOfLE_comp_ι _

/-! ### The quotient `F / F_n` -/

/-- The quotient `F / F_n` of `F` by the subsheaf of sections annihilated by `Iⁿ`, formed as the
cokernel of the inclusion in the abelian category `X.Modules`. -/
noncomputable abbrev quotientModule (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) : X.Modules :=
  cokernel (annihilatorι I F n)

/-- The projection `F ⟶ F / F_n`. -/
noncomputable abbrev quotientπ (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    F ⟶ quotientModule I F n :=
  cokernel.π (annihilatorι I F n)

/-- The quotient of a quasi-coherent module by the annihilator of a power of an ideal sheaf of
finite type is quasi-coherent. -/
theorem isQuasicoherent_quotientModule (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) :
    (quotientModule I F n).IsQuasicoherent :=
  let : (annihilatorModule I F n).IsQuasicoherent :=
    isQuasicoherent_annihilatorModule_of_fg I F n hFG
  inferInstance

/-! ### The sections of the quotient -/

/-- The canonical map from the kernel of the projection back to the annihilator subsheaf: the
inclusion `F_n ⟶ F` is a monomorphism, hence a kernel of its own cokernel. -/
noncomputable def kernelQuotientπToAnnihilator (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    kernel (quotientπ I F n) ⟶ annihilatorModule I F n :=
  Abelian.monoLift (annihilatorι I F n) (kernel.ι (quotientπ I F n)) (kernel.condition _)

/-- The map `kernelQuotientπToAnnihilator` followed by the inclusion `F_n ⟶ F` is the inclusion
of the kernel of the projection `F ⟶ F / F_n`. -/
theorem kernelQuotientπToAnnihilator_comp (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    kernelQuotientπToAnnihilator I F n ≫ annihilatorι I F n = kernel.ι (quotientπ I F n) :=
  Abelian.monoLift_comp (annihilatorι I F n) (kernel.ι (quotientπ I F n)) (kernel.condition _)

/-- **The sections of `F_n` are the kernel of the projection on sections.** Over every open `W`
the pair of maps on sections induced by `F_n ⟶ F` and `F ⟶ F / F_n` is exact. -/
theorem exact_annihilatorι_app (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) (W : X.Opens) :
    Function.Exact ((annihilatorι I F n).app W) ((quotientπ I F n).app W) := by
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (QcohLimits.exact_app_kernel (quotientπ I F n) W y).mp hy
    refine ⟨(kernelQuotientπToAnnihilator I F n).app W x, ?_⟩
    rw [← hx, ← kernelQuotientπToAnnihilator_comp I F n, Scheme.Modules.Hom.comp_app]
    rfl
  · rintro ⟨z, rfl⟩
    have h : (annihilatorι I F n ≫ quotientπ I F n).app W z = 0 := by
      rw [cokernel.condition]
      simp
    exact h

/-- **A section of `F` dies in `F / F_n` exactly when it is annihilated by `Iⁿ`.** -/
theorem quotientπ_app_eq_zero_iff (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    {W : X.Opens} (y : Γ(F, W)) :
    (quotientπ I F n).app W y = 0 ↔
      y ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W) := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ (exact_annihilatorι_app I F n W y).mpr
    ⟨annihilatorMk I F n y hy, rfl⟩⟩
  obtain ⟨z, rfl⟩ := (exact_annihilatorι_app I F n W y).mp hy
  exact annihilatorVal_mem z

/-- A section of `F` whose image in `F / F_n` vanishes is annihilated by `Iⁿ`. -/
theorem mem_annihilator_of_quotientπ_app_eq_zero (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    {W : X.Opens} (y : Γ(F, W)) (hy : (quotientπ I F n).app W y = 0) :
    y ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W) :=
  (quotientπ_app_eq_zero_iff I F n y).mp hy

/-! ### Away from the support of `I` -/

/-- **`F_n` vanishes away from the support of `I`.** Over an open missing the support of `I` the
subsheaf `Iⁿ` is the whole structure sheaf, so a section annihilated by it is zero. -/
theorem eq_zero_of_mem_annihilator_of_le_compl_support (I : X.IdealSheafData) (F : X.Modules)
    (n : ℕ) {W : X.Opens} (hW : W ≤ (I.support.compl : X.Opens)) (s : Γ(F, W))
    (hs : s ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W)) :
    s = 0 := by
  have htop : (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.obj (op W) = ⊤ := by
    rw [idealPower_unitSubmodule I n]
    exact idealPowerMultiple_obj_eq_top_of_disjoint_support I n (structureModule X)
      (W := (I.support.compl : X.Opens)) disjoint_compl_left hW
  have h1 : (1 : Γ(X, W)) ∈
      (AlgebraicGeometry.idealPower I.unitSubmodule n).toSubmodule.obj (op W) := by
    rw [htop]
    trivial
  have h := hs (op W) (𝟙 (op W)) 1 h1
  have hid : (ConcreteCategory.hom (F.val.presheaf.map (𝟙 (op W)))) s = s := by
    simp only [CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at h
  exact (one_smul Γ(X, W) s).symm.trans h

/-- The projection is injective on sections over an open missing the support of `I`. -/
theorem injective_quotientπ_app_of_le_compl_support (I : X.IdealSheafData) (F : X.Modules)
    (n : ℕ) {W : X.Opens} (hW : W ≤ (I.support.compl : X.Opens)) :
    Function.Injective ((quotientπ I F n).app W) :=
  (injective_iff_map_eq_zero (AddCommGrpCat.Hom.hom ((quotientπ I F n).app W))).mpr fun y hy ↦
    eq_zero_of_mem_annihilator_of_le_compl_support I F n hW y
      (mem_annihilator_of_quotientπ_app_eq_zero I F n y hy)

/-- The projection is surjective on sections over an open missing the support of `I`: it is
surjective over every affine open because `F` and `F / F_n` are quasi-coherent, and the local
lifts are unique because `F_n` vanishes, so they glue. -/
theorem surjective_quotientπ_app_of_le_compl_support (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) {W : X.Opens}
    (hW : W ≤ (I.support.compl : X.Opens)) :
    Function.Surjective ((quotientπ I F n).app W) := by
  classical
  let := isQuasicoherent_quotientModule I F n hFG
  intro t
  set ι := {V : X.Opens // V ≤ W ∧ IsAffineOpen V}
  have hVW : ∀ i : ι, (i : X.Opens) ≤ W := fun i ↦ i.2.1
  have hcov : W ≤ ⨆ i : ι, (i : X.Opens) := by
    intro x hx
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVW'⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (W : Set X) from hx) W.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨V, hVW', hVaff⟩, hxV⟩
  have hlift : ∀ i : ι, ∃ y : Γ(F, (i : X.Opens)),
      (quotientπ I F n).app (i : X.Opens) y
        = (quotientModule I F n).presheaf.map (homOfLE (hVW i)).op t :=
    fun i ↦ Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X (quotientπ I F n)
      (i : X.Opens) i.2.2 _
  choose y hy using hlift
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf (fun i : ι ↦ (i : X.Opens)) y := by
    intro i j
    change F.presheaf.map
        (homOfLE (inf_le_left : (i : X.Opens) ⊓ (j : X.Opens) ≤ (i : X.Opens))).op (y i)
      = F.presheaf.map
        (homOfLE (inf_le_right : (i : X.Opens) ⊓ (j : X.Opens) ≤ (j : X.Opens))).op (y j)
    refine injective_quotientπ_app_of_le_compl_support I F n
      (inf_le_left.trans ((hVW i).trans hW)) ?_
    simp only [QcohLimits.app_naturality, hy, Stacks.AlgebraicGeometry.GabberColimit.res_res]
  obtain ⟨g, hg⟩ : ∃ g : Γ(F, W), ∀ i : ι, F.presheaf.map (homOfLE (hVW i)).op g = y i :=
    (TopCat.Sheaf.existsUnique_gluing' (F := QcqsLocalization.abSheaf F)
      (fun i : ι ↦ (i : X.Opens)) W (fun i ↦ homOfLE (hVW i)) hcov y hcompat).exists
  refine ⟨g, sub_eq_zero.mp (eq_zero_of_locally_zero _ fun x hx ↦ ?_)⟩
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcov hx)
  refine ⟨(i : X.Opens), hVW i, hxi, ?_⟩
  rw [map_sub, sub_eq_zero, ← QcohLimits.app_naturality (quotientπ I F n) (hVW i), hg i, hy i]

/-- **The projection is bijective on sections over an open missing the support of `I`.** -/
theorem bijective_quotientπ_app_of_le_compl_support (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) {W : X.Opens}
    (hW : W ≤ (I.support.compl : X.Opens)) :
    Function.Bijective ((quotientπ I F n).app W) :=
  ⟨injective_quotientπ_app_of_le_compl_support I F n hW,
    surjective_quotientπ_app_of_le_compl_support I F n hFG hW⟩

/-- The sections of `F` and of `F / F_n` over an open missing the support of `I` agree. -/
noncomputable def quotientSectionsEquiv (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) {W : X.Opens}
    (hW : W ≤ (I.support.compl : X.Opens)) :
    Γ(F, W) ≃+ Γ(quotientModule I F n, W) :=
  AddEquiv.ofBijective (AddCommGrpCat.Hom.hom ((quotientπ I F n).app W))
    (bijective_quotientπ_app_of_le_compl_support I F n hFG hW)

/-- The equivalence `quotientSectionsEquiv` is the projection `F ⟶ F / F_n` on sections. -/
@[simp]
theorem quotientSectionsEquiv_apply (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) {W : X.Opens}
    (hW : W ≤ (I.support.compl : X.Opens)) (y : Γ(F, W)) :
    quotientSectionsEquiv I F n hFG hW y = (quotientπ I F n).app W y := rfl

/-- The projection `F ⟶ F / F_n` sends the preimage of a section under `quotientSectionsEquiv`
back to that section. -/
@[simp]
theorem quotientSectionsEquiv_symm_apply (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG) {W : X.Opens}
    (hW : W ≤ (I.support.compl : X.Opens)) (z : Γ(quotientModule I F n, W)) :
    (quotientπ I F n).app W ((quotientSectionsEquiv I F n hFG hW).symm z) = z :=
  (quotientSectionsEquiv I F n hFG hW).apply_symm_apply z

/-! ### The sections of the quotient over an affine open -/

/-- The kernel of the projection on sections over an affine open `V` is the `I(V)ⁿ`-torsion
submodule of `Γ(F, V)`. -/
theorem ker_appₗ_quotientπ (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (V : X.affineOpens) :
    LinearMap.ker (QcohLimits.appₗ (quotientπ I F n) V.1)
      = Submodule.torsionBySet Γ(X, V.1) Γ(F, V.1)
          ((I.ideal V ^ n : Ideal Γ(X, V.1)) : Set Γ(X, V.1)) := by
  rw [← idealPowerAnnihilator_obj_affineOpen I F n V]
  exact Submodule.ext fun y ↦ quotientπ_app_eq_zero_iff I F n y

/-- **The sections of `F / F_n` over an affine open.** Writing `M = Γ(F, V)` and
`M_n = {x ∈ M | I(V)ⁿ x = 0}`, the sections of `F / F_n` over an affine open `V` are `M / M_n`.

This is the step the source of [Stacks, Tag 01PQ] records as "`F_n|_W = M̃_n` (details
omitted)": the projection is surjective on sections over an affine open by the `H¹`-vanishing of
[Stacks, Tag 01XB], and its kernel is the torsion submodule by `ker_appₗ_quotientπ`. -/
noncomputable def quotientSectionsAffineEquiv (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ V : X.affineOpens, (I.ideal V).FG)
    (V : X.affineOpens) :
    (Γ(F, V.1) ⧸ Submodule.torsionBySet Γ(X, V.1) Γ(F, V.1)
          ((I.ideal V ^ n : Ideal Γ(X, V.1)) : Set Γ(X, V.1)))
        ≃ₗ[Γ(X, V.1)] Γ(quotientModule I F n, V.1) :=
  letI := isQuasicoherent_quotientModule I F n hFG
  (Submodule.quotEquivOfEq _ _ (ker_appₗ_quotientπ I F n V).symm).trans
    (LinearMap.quotKerEquivOfSurjective (QcohLimits.appₗ (quotientπ I F n) V.1)
      (Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X (quotientπ I F n) V.1 V.2))

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
