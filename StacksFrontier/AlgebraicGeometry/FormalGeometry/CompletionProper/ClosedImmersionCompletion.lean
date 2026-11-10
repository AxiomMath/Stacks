module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AdicTowerSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient

/-!
# The completion functor and the direct image along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes, let `ℐ ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals and let `ℐ 𝒪_Z = ℐ.comap i` be its inverse image. For a coherent
`𝒪_Z`-module `G` the two ways of forming an adic tower agree:

`(i_* G) / ℐ ⁿ (i_* G) ≅ i_* (G / (ℐ 𝒪_Z) ⁿ G)`,

compatibly with the quotient projections out of `i_* G`, and therefore

`(i_* G) ^∧ ≅ i_* (G ^∧)`

as inverse systems, naturally in `G`. This is the comparison the proof of [Stacks, Tag 088A]
glosses over when it reads hypothesis (1) — an assertion about the closed subschemes `X_e` — as
an assertion about the `𝒦 ᵉ`-annihilated objects of `Coh(X, ℐ)`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_le_of_basis` — an inclusion `ℐ ⁿ M ≤ N` may be
  checked on a family of affine opens which is only a *basis* of the topology, rather than on
  every affine open; the sheaf condition on `N` does the rest.
* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_basis` — its case `N = ⊥`, stated
  elementwise.
* `Stacks.Algebraization.exists_affineOpen_preimage_le` — the preimages of the affine opens of
  `X` are such a basis on a closed subscheme `Z`.
* `Stacks.Algebraization.ideal_comap_preimage` — the ideal of `ℐ 𝒪_Z` on the preimage of an
  affine open is the image of the ideal of `ℐ` under the comorphism.
* `Stacks.Algebraization.pushforwardAdicQuotientMap` and
  `Stacks.Algebraization.isIso_pushforwardAdicQuotientMap` — **the comparison of the two adic
  quotients, and that it is an isomorphism.**
* `Stacks.Algebraization.pushforwardCompletionIso`,
  `Stacks.Algebraization.pushforwardCompletionIso_projection` and
  `Stacks.Algebraization.pushforwardCompletionIso_naturality` — **the resulting isomorphism of
  inverse systems**, its compatibility with the projections out of `i_* G`, and its naturality
  in `G`.

## Implementation notes

The comparison map exists because `ℐ ⁿ (i_* G)` is killed by the direct image of the projection
`G ⟶ G / (ℐ 𝒪_Z) ⁿ G`: over an affine open `U` of `X` the sections of `i_* G` are the sections of
`G` over the affine open `i ⁻¹ U`, a scalar `r ∈ ℐ(U)` acts through the comorphism, and the image
of `ℐ(U)` generates the ideal of `ℐ 𝒪_Z` on `i ⁻¹ U`.

That it is invertible is proved *without* any exactness property of `i_*`. Write
`N = (i_* G) / ℐ ⁿ (i_* G)` and `π_X : i_* G ⟶ N` for the projection. Then `N` is coherent and
killed by the ideal of `i`, so [Stacks, Tag 087T] writes it as `i_* S` for a coherent
`𝒪_Z`-module `S`, and full faithfulness of `i_*` ([Stacks, Tag 08KS]) turns `π_X` into a
morphism `ρ : G ⟶ S`. A faithful functor reflects epimorphisms, so `ρ` is one; and `ρ` kills
`(ℐ 𝒪_Z) ⁿ G`, which is where the basis lemma is needed — the charts on which `ρ` is known are
the preimages `i ⁻¹ U`, not all the affine opens of `Z`. So `ρ` factors as `σ` through the
projection `π_Z`, while the comparison map itself corresponds under `i_*` to a morphism `τ` back;
`ρ ≫ τ = π_Z` then makes `σ` and `τ` mutually inverse, by cancelling the two epimorphisms `π_Z`
and `ρ`.

The isomorphism of inverse systems is assembled with `CategoryTheory.NatTrans.ofOpSequence`,
which asks for the naturality squares only at the successor steps; each square is checked after
cancelling the epimorphism `Stacks.Algebraization.completionProjection`, which reduces it to the
compatibility of the projections with the transition maps. The same cancellation proves
naturality in `G`.

The sections of a direct image are *definitionally* the sections upstairs
(`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`), with the scalar action restricted along
the comorphism, which is why the elementwise steps below are `rfl` or `show`.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Algebraization

/-! ### Checking an ideal-power inclusion on a basis of affine opens -/

/-- **An inclusion `ℐ ⁿ M ≤ N` may be checked on a basis of affine opens.** The definition of
`ℐ ⁿ M` quantifies over *all* affine opens; since `N` is a subsheaf, a family of affine opens
which is a basis of the topology suffices.

For an affine open `V`, a scalar `r ∈ ℐ(V) ⁿ` and a section `x` of `M` over `V`, the product
`r • x` restricts into `N` over each basis element contained in `V` — the restriction of `r`
lies in `ℐ ⁿ` of that element by
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` — and those elements cover `V`. -/
public theorem idealPowerMultiple_le_of_basis {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) (N : M.Submodule) {J : Type v} (B : J → X.affineOpens)
    (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ j, x ∈ (B j).1 ∧ (B j).1 ≤ W)
    (h : ∀ j, I.ideal (B j) ^ n • (⊤ : Submodule Γ(X, (B j).1) Γ(M, (B j).1)) ≤
      N.toSubmodule.obj (op (B j).1)) :
    idealPowerMultiple I n M ≤ N := by
  refine (idealPowerMultiple_le_iff I n M N).2 fun V => ?_
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  refine N.isSheaf (r • x) ?_
  rw [Opens.mem_grothendieckTopology]
  intro z hz
  obtain ⟨j, hzj, hjV⟩ := hbasis V.1 z hz
  refine ⟨(B j).1, homOfLE hjV, ?_, hzj⟩
  have hrj : (X.presheaf.map (homOfLE hjV).op).hom r ∈ I.ideal (B j) ^ n := by
    rw [← I.map_ideal (U := B j) (V := V) hjV, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hr
  have hmem := Submodule.smul_le.mp (h j) _ hrj
    (M.val.map (homOfLE hjV).op x) Submodule.mem_top
  exact Eq.mpr (congrArg (fun y => y ∈ N.toSubmodule.obj (op (B j).1))
    (M.val.map_smul (homOfLE hjV).op r x)) hmem

/-- **Annihilation by `ℐ ⁿ` may be checked on a basis of affine opens.** The case `N = ⊥` of
`Stacks.Algebraization.idealPowerMultiple_le_of_basis`, stated elementwise. -/
public theorem idealPowerMultiple_eq_bot_of_basis {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) {J : Type v} (B : J → X.affineOpens)
    (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ j, x ∈ (B j).1 ∧ (B j).1 ≤ W)
    (h : ∀ j, ∀ r ∈ I.ideal (B j) ^ n, ∀ x : Γ(M, (B j).1), r • x = 0) :
    idealPowerMultiple I n M = ⊥ := by
  refine le_antisymm (idealPowerMultiple_le_of_basis I n M ⊥ B hbasis fun j => ?_) bot_le
  rw [bot_submodule_obj_eq_bot]
  exact ((ideal_smul_top_eq_bot_iff (I.ideal (B j) ^ n)).mpr (h j)).le

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### The charts of a closed subscheme coming from the ambient scheme -/

/-- **The preimages of the affine opens of `X` form a basis of the topology of a closed
subscheme `Z`.** Given an open `W` of `Z` and a point `z` of `W`, the image of the complement of
`W` is closed in `X` and misses `i z`, so an affine open neighbourhood of `i z` inside its
complement has preimage inside `W`. -/
public theorem exists_affineOpen_preimage_le (W : Z.Opens) (z : Z) (hz : z ∈ W) :
    ∃ U : X.affineOpens, z ∈ i ⁻¹ᵁ U.1 ∧ i ⁻¹ᵁ U.1 ≤ W := by
  have hcl : IsClosed (i.base '' (Wᶜ : Set Z)) :=
    (IsClosedImmersion.isClosedEmbedding i).isClosedMap _
      (by simpa using W.2.isClosed_compl)
  have hmem : i.base z ∈ (i.base '' (Wᶜ : Set Z))ᶜ := by
    rintro ⟨y, hy, hxy⟩
    exact hy ((IsClosedImmersion.isClosedEmbedding i).injective hxy ▸ hz)
  obtain ⟨V, ⟨U, hU, rfl⟩, hzU, hUO⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hmem hcl.isOpen_compl
  refine ⟨⟨U, hU⟩, hzU, fun y hy => ?_⟩
  by_contra hyW
  exact hUO hy ⟨y, hyW, rfl⟩

/-- **The ideal of `ℐ 𝒪_Z` on the preimage of an affine open.** It is the image of the ideal of
`ℐ` under the comorphism, which is `Stacks.IdealSheaf.ideal_comap_appLE` for the pair of charts
`(U, i ⁻¹ U)`. -/
public theorem ideal_comap_preimage (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ = Ideal.map (i.app U.1).hom (I.ideal U) := by
  rw [Stacks.IdealSheaf.ideal_comap_appLE I i U ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ le_rfl]
  congr 1
  simp [Scheme.Hom.appLE]

/-! ### The comparison of the two adic quotients -/

/-- The `m`-th power of the ideal of `ℐ 𝒪_Z` on `i ⁻¹ U` is the image of that of `ℐ(U)`. -/
private theorem map_ideal_pow_eq_comap_ideal_pow (I : X.IdealSheafData) (m : ℕ)
    (U : X.affineOpens) :
    Ideal.map (i.app U.1).hom (I.ideal U ^ m) =
      (I.comap i).ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ ^ m := by
  rw [Ideal.map_pow, ideal_comap_preimage i I U]

/-- `ℐ ᵐ (i_* G)` is killed by the direct image of the projection `G ⟶ G / (ℐ 𝒪_Z) ᵐ G`. -/
public theorem idealPowerMultiple_pushforward_comp_eq_zero
    (I : X.IdealSheafData) (m : ℕ) (G : Z.Modules) :
    (idealPowerMultiple I m ((Scheme.Modules.pushforward i).obj G)).ι ≫
      (Scheme.Modules.pushforward i).map
        (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) m G).ι) = 0 := by
  rw [submodule_ι_comp_eq_zero_iff]
  refine (idealPowerMultiple_le_iff I m _ _).2 fun U => ?_
  refine Submodule.smul_le.mpr fun r hr x _ => ?_
  have hV : IsAffineOpen (i ⁻¹ᵁ U.1) := U.2.preimage i
  have hr' : (i.app U.1).hom r ∈ (I.comap i).ideal ⟨i ⁻¹ᵁ U.1, hV⟩ ^ m := by
    rw [← map_ideal_pow_eq_comap_ideal_pow i I m U]
    exact Ideal.mem_map_of_mem _ hr
  have hle : (I.comap i).ideal ⟨i ⁻¹ᵁ U.1, hV⟩ ^ m •
      (⊤ : Submodule Γ(Z, i ⁻¹ᵁ U.1) Γ(G, i ⁻¹ᵁ U.1)) ≤
      (idealPowerMultiple (I.comap i) m G).toSubmodule.obj (op (i ⁻¹ᵁ U.1)) :=
    (idealPowerMultiple_le_iff (I.comap i) m G _).1 le_rfl ⟨i ⁻¹ᵁ U.1, hV⟩
  have hker := (submodule_ι_comp_eq_zero_iff (idealPowerMultiple (I.comap i) m G)
      (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) m G).ι)).1
    (cokernel.condition (C := Z.Modules) _)
  exact hker _ (hle (Submodule.smul_mem_smul hr' Submodule.mem_top))

/-- **The comparison map `(i_* G) / ℐ ᵐ (i_* G) ⟶ i_* (G / (ℐ 𝒪_Z) ᵐ G)`.** -/
public def pushforwardAdicQuotientMap (I : X.IdealSheafData) (m : ℕ) (G : Z.Modules) :
    idealPowerQuotient I m ((Scheme.Modules.pushforward i).obj G) ⟶
      (Scheme.Modules.pushforward i).obj (idealPowerQuotient (I.comap i) m G) :=
  cokernel.desc (C := X.Modules) _ _ (idealPowerMultiple_pushforward_comp_eq_zero i I m G)

/-- The comparison map reads the direct image of the projection on `Z` as a map out of the
quotient on `X`. -/
@[simp]
public theorem pushforwardAdicQuotientMap_π (I : X.IdealSheafData) (m : ℕ) (G : Z.Modules) :
    cokernel.π (C := X.Modules)
        (idealPowerMultiple I m ((Scheme.Modules.pushforward i).obj G)).ι ≫
      pushforwardAdicQuotientMap i I m G =
    (Scheme.Modules.pushforward i).map
      (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) m G).ι) :=
  cokernel.π_desc (C := X.Modules) _ _ _

/-- **A morphism out of `G` kills `(ℐ 𝒪_Z) ᵐ G` once it kills the scalars pulled back from `X`.**
It suffices to check the products `i^♯ a • y` for `a ∈ ℐ(U) ᵐ` on the preimages `i ⁻¹ U` of the
affine opens `U` of `X`, since these preimages form a basis of `Z`. -/
private theorem idealPowerMultiple_comap_ι_comp_eq_zero
    (I : X.IdealSheafData) (m : ℕ) {G S : Z.Modules} (ρ : G ⟶ S)
    (h : ∀ (U : X.affineOpens), ∀ a ∈ I.ideal U ^ m, ∀ y : Γ(G, i ⁻¹ᵁ U.1),
      ρ.app (i ⁻¹ᵁ U.1) ((i.app U.1).hom a • y) = 0) :
    (idealPowerMultiple (I.comap i) m G).ι ≫ ρ = 0 := by
  rw [submodule_ι_comp_eq_zero_iff]
  refine idealPowerMultiple_le_of_basis _ _ _ _
    (fun U : X.affineOpens => (⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ : Z.affineOpens))
    (fun W z hz => exists_affineOpen_preimage_le i W z hz) fun U => ?_
  rw [← map_ideal_pow_eq_comap_ideal_pow i I m U]
  refine Submodule.smul_le.mpr fun c hc y _ => ?_
  change ρ.app (i ⁻¹ᵁ U.1) (c • y) = 0
  refine Submodule.span_induction
    (p := fun (c : Γ(Z, i ⁻¹ᵁ U.1)) _ =>
      ∀ w : Γ(G, i ⁻¹ᵁ U.1), ρ.app (i ⁻¹ᵁ U.1) (c • w) = 0)
    ?_ ?_ ?_ ?_ hc y
  · rintro _ ⟨a, ha, rfl⟩
    exact h U a ha
  · intro w
    rw [zero_smul, map_zero]
  · intro c d _ _ hcw hdw w
    rw [add_smul, map_add, hcw w, hdw w, add_zero]
  · intro a c _ hcw w
    rw [smul_assoc, Scheme.Modules.Hom.app_smul, hcw w, smul_zero]

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- The direct image of a coherent module along a closed immersion into a locally Noetherian
scheme is coherent. This is the object half of [Stacks, Tag 087T], re-enabled as an instance so
that the completion functor may be applied to `i_* G`. -/
public instance isCoherent_pushforward_closedImmersion (G : Z.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pushforward i).obj G).IsCoherent :=
  have _ : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i G

/-- **The comparison map is an isomorphism.** -/
public theorem isIso_pushforwardAdicQuotientMap (I : X.IdealSheafData) (n : ℕ) (G : Z.Modules)
    [G.IsCoherent] :
    IsIso (C := X.Modules) (pushforwardAdicQuotientMap i I (n + 1) G) := by
  have hGq : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  set M := (Scheme.Modules.pushforward i).obj G
  have hMcoh : M.IsCoherent := isCoherent_pushforward_closedImmersion i G
  have hMann : Stacks.AlgebraicGeometry.Tag087TCoherentImage.AnnihilatedByKer i M :=
    Stacks.AlgebraicGeometry.Tag087TCoherentImage.annihilatedByKer_pushforward i G
  have hMq : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  set N := idealPowerQuotient I (n + 1) M
  set piX := cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M).ι
  have hNprop : Stacks.Coherent.coherentAnnihilatedBy I (n + 1) N :=
    Stacks.Coherent.coherentAnnihilatedBy_idealPowerQuotient I n M hMcoh
  have hNcoh : N.IsCoherent := hNprop.1
  have hMann1 : idealPowerMultiple i.ker 1 M = ⊥ :=
    idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U a ha x =>
      hMann U a (by rwa [pow_one] at ha) x
  have hNann : Stacks.AlgebraicGeometry.Tag087TCoherentImage.AnnihilatedByKer i N :=
    fun U a ha x => affine_sections_annihilated_of_idealPowerMultiple_eq_bot
      (idealPowerMultiple_eq_bot_of_epi i.ker 1 piX hMann1) U (by rwa [pow_one]) x
  obtain ⟨S, hS, ⟨eN⟩⟩ :=
    Stacks.AlgebraicGeometry.Tag087TCoherentImage.exists_isCoherent_pushforward_iso i N hNann
  let ff := Stacks.ClosedImmersion.fullyFaithfulPushforward i
  have := Stacks.ClosedImmersion.faithful_pushforward i
  set rho := ff.preimage (piX ≫ eN.inv)
  have hrhomap : (Scheme.Modules.pushforward i).map rho = piX ≫ eN.inv := ff.map_preimage _
  have hrhoepi : Epi rho := (Scheme.Modules.pushforward i).epi_of_epi_map <| by
    rw [hrhomap]
    infer_instance
  set piZ := cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) (n + 1) G).ι
  have hrhoker : (idealPowerMultiple (I.comap i) (n + 1) G).ι ≫ rho = 0 := by
    refine idealPowerMultiple_comap_ι_comp_eq_zero i I (n + 1) rho fun U a ha y => ?_
    have h1 : rho.app (i ⁻¹ᵁ U.1) ((i.app U.1).hom a • y) =
        (piX ≫ eN.inv).app U.1 (a • (show Γ(M, U.1) from y)) := by
      rw [← hrhomap]
      rfl
    rw [h1, Scheme.Modules.Hom.comp_app]
    change eN.inv.app U.1 (piX.app U.1 (a • (show Γ(M, U.1) from y))) = 0
    rw [Scheme.Modules.Hom.app_smul,
      affine_sections_annihilated_of_idealPowerMultiple_eq_bot hNprop.2 U ha _, map_zero]
  set sigma := cokernel.desc (C := Z.Modules) _ rho hrhoker
  have hsigmapi : piZ ≫ sigma = rho := cokernel.π_desc (C := Z.Modules) _ _ _
  set tau := ff.preimage (eN.hom ≫ pushforwardAdicQuotientMap i I (n + 1) G)
  have htaumap : (Scheme.Modules.pushforward i).map tau =
      eN.hom ≫ pushforwardAdicQuotientMap i I (n + 1) G := ff.map_preimage _
  have hrhotau : rho ≫ tau = piZ := by
    refine (Scheme.Modules.pushforward i).map_injective ?_
    rw [Functor.map_comp, hrhomap, htaumap, Category.assoc, Iso.inv_hom_id_assoc,
      pushforwardAdicQuotientMap_π]
  have htauiso : IsIso tau := ⟨sigma,
    (cancel_epi rho).mp (by rw [← Category.assoc, hrhotau, hsigmapi, Category.comp_id]),
    (cancel_epi piZ).mp (by rw [← Category.assoc, hsigmapi, hrhotau, Category.comp_id])⟩
  rw [← isIso_comp_left_iff eN.hom, ← htaumap]
  infer_instance

/-! ### The resulting isomorphism of inverse systems -/

/-- The projection onto the `n`-th term of the completion, unfolded: it is the quotient
projection followed by the identification of that term with the ideal-power quotient. -/
public theorem completionProjection_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ) :
    completionProjection Y I F n =
      cokernel.π (C := Y.Modules) (idealPowerMultiple I (n + 1) F.obj).ι ≫
        eqToHom (completionFunctor_obj Y I F n).symm :=
  rfl

/-- The direct image of a coherent module along a closed immersion, as a coherent module. -/
public def pushforwardCoherentObj
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  haveI : G.obj.IsCoherent := G.property
  ⟨(Scheme.Modules.pushforward i).obj G.obj,
    isCoherent_pushforward_closedImmersion i G.obj⟩

omit [IsLocallyNoetherian Z] in
/-- Its underlying module is the direct image. -/
public theorem pushforwardCoherentObj_obj
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    (pushforwardCoherentObj i G).obj = (Scheme.Modules.pushforward i).obj G.obj :=
  rfl

/-- The comparison of the `n`-th term of the completion of `i_* G` with the direct image of the
`n`-th term of the completion of `G`, as an isomorphism. -/
public def pushforwardCompletionComponentIso (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    ((completionFunctor X I).obj (pushforwardCoherentObj i G)).obj.obj (op n) ≅
      (((completionFunctor Z (I.comap i)).obj G).obj ⋙
        Scheme.Modules.pushforward i).obj (op n) :=
  haveI : G.obj.IsCoherent := G.property
  haveI hiso : IsIso (C := X.Modules) (pushforwardAdicQuotientMap i I (n + 1) G.obj) :=
    isIso_pushforwardAdicQuotientMap i I n G.obj
  eqToIso (completionFunctor_obj X I (pushforwardCoherentObj i G) n) ≪≫
    (@asIso X.Modules _ _ _ _ hiso) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (eqToIso (completionFunctor_obj Z (I.comap i) G n).symm)

/-- The component at `n` of the comparison of the completion of `i_* G` with the direct image of
the completion of `G`. -/
public def pushforwardCompletionHom (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    ((completionFunctor X I).obj (pushforwardCoherentObj i G)).obj.obj (op n) ⟶
      (((completionFunctor Z (I.comap i)).obj G).obj ⋙
        Scheme.Modules.pushforward i).obj (op n) :=
  (pushforwardCompletionComponentIso i I G n).hom

/-- **The comparison component reads the direct image of the projection on `Z` as a map out of
the completion on `X`.** -/
public theorem completionProjection_comp_pushforwardCompletionHom (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    completionProjection X I (pushforwardCoherentObj i G) n ≫
        pushforwardCompletionHom i I G n =
      (Scheme.Modules.pushforward i).map
        (completionProjection Z (I.comap i) G n) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (pushforwardAdicQuotientMap i I (n + 1) G.obj ≫
          (Scheme.Modules.pushforward i).map
            (eqToHom (completionFunctor_obj Z (I.comap i) G n).symm)))
        (Stacks.Algebraization.completionProjection_comp_eqToHom_cokernelπ I
          (pushforwardCoherentObj i G) n)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward i).map
              (eqToHom (completionFunctor_obj Z (I.comap i) G n).symm))
            (pushforwardAdicQuotientMap_π i I (n + 1) G.obj)).trans
          (((Scheme.Modules.pushforward i).map_comp _ _).symm.trans
            (congrArg (Scheme.Modules.pushforward i).map
              (completionProjection_eq (I.comap i) G n).symm)))))

/-- The comparison components are compatible with the transition maps, so they assemble into a
morphism of inverse systems. -/
public theorem pushforwardCompletionHom_naturality (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    ((completionFunctor X I).obj (pushforwardCoherentObj i G)).obj.map
        (homOfLE (n.le_add_right 1)).op ≫ pushforwardCompletionHom i I G n =
      pushforwardCompletionHom i I G (n + 1) ≫
        (((completionFunctor Z (I.comap i)).obj G).obj ⋙
          Scheme.Modules.pushforward i).map (homOfLE (n.le_add_right 1)).op := by
  have hepi := epi_completionProjection X I (pushforwardCoherentObj i G) (n + 1)
  refine (@cancel_epi _ _ _ _ _
    (completionProjection X I (pushforwardCoherentObj i G) (n + 1)) hepi _ _).mp ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pushforwardCompletionHom i I G n)
        (completionProjection_transition X I (pushforwardCoherentObj i G) n)).trans
      ((completionProjection_comp_pushforwardCompletionHom i I G n).trans
        ((congrArg (Scheme.Modules.pushforward i).map
            (completionProjection_transition Z (I.comap i) G n).symm).trans
          (((Scheme.Modules.pushforward i).map_comp _ _).trans
            ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward i).map
                  (((completionFunctor Z (I.comap i)).obj G).obj.map
                    (homOfLE (Nat.le_succ n)).op))
                (completionProjection_comp_pushforwardCompletionHom i I G (n + 1)).symm).trans
              (Category.assoc _ _ _))))))

/-- The comparison components are isomorphisms. -/
public instance isIso_pushforwardCompletionHom (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    IsIso (pushforwardCompletionHom i I G n) :=
  inferInstanceAs (IsIso (pushforwardCompletionComponentIso i I G n).hom)

/-- The morphism of inverse systems assembled from the comparison components. -/
public def pushforwardCompletionNatTrans (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ((completionFunctor X I).obj (pushforwardCoherentObj i G)).obj ⟶
      ((completionFunctor Z (I.comap i)).obj G).obj ⋙ Scheme.Modules.pushforward i :=
  NatTrans.ofOpSequence (pushforwardCompletionHom i I G)
    (pushforwardCompletionHom_naturality i I G)

/-- Its components are the comparison components. -/
@[simp]
public theorem pushforwardCompletionNatTrans_app (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    (pushforwardCompletionNatTrans i I G).app (op n) = pushforwardCompletionHom i I G n :=
  rfl

/-- It is an isomorphism, being one in every degree. -/
public instance isIso_pushforwardCompletionNatTrans (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    IsIso (pushforwardCompletionNatTrans i I G) := by
  have _ : ∀ m : ℕᵒᵖ, IsIso ((pushforwardCompletionNatTrans i I G).app m) := fun m =>
    isIso_pushforwardCompletionHom i I G m.unop
  exact NatIso.isIso_of_isIso_app _

/-- **The completion of `i_* G` is the direct image of the completion of `G`.** -/
public def pushforwardCompletionIso (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ((completionFunctor X I).obj (pushforwardCoherentObj i G)).obj ≅
      ((completionFunctor Z (I.comap i)).obj G).obj ⋙ Scheme.Modules.pushforward i :=
  asIso (pushforwardCompletionNatTrans i I G)

/-- The component of the isomorphism of systems is the comparison component. -/
@[simp]
public theorem pushforwardCompletionIso_hom_app (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    (pushforwardCompletionIso i I G).hom.app (op n) = pushforwardCompletionHom i I G n :=
  rfl

/-- **The isomorphism of systems is compatible with the projections out of `i_* G`.** -/
public theorem pushforwardCompletionIso_projection (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) (n : ℕ) :
    completionProjection X I (pushforwardCoherentObj i G) n ≫
        (pushforwardCompletionIso i I G).hom.app (op n) =
      (Scheme.Modules.pushforward i).map (completionProjection Z (I.comap i) G n) :=
  completionProjection_comp_pushforwardCompletionHom i I G n

/-- The direct image of a morphism of coherent modules, as a morphism of coherent modules. -/
public def pushforwardCoherentMap {G G' : AlgebraicGeometry.SheafOfModules.CoherentModules
    Z.ringCatSheaf} (f : G ⟶ G') : pushforwardCoherentObj i G ⟶ pushforwardCoherentObj i G' :=
  ObjectProperty.homMk ((Scheme.Modules.pushforward i).map f.hom)

omit [IsLocallyNoetherian Z] in
/-- Its underlying morphism is the direct image. -/
@[simp]
public theorem pushforwardCoherentMap_hom
    {G G' : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf} (f : G ⟶ G') :
    (pushforwardCoherentMap i f).hom = (Scheme.Modules.pushforward i).map f.hom :=
  rfl

/-- **The isomorphism of systems is natural in `G`.** -/
public theorem pushforwardCompletionIso_naturality (I : X.IdealSheafData)
    {G G' : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf} (f : G ⟶ G')
    (n : ℕ) :
    ((completionFunctor X I).map (pushforwardCoherentMap i f)).hom.app (op n) ≫
        (pushforwardCompletionIso i I G').hom.app (op n) =
      (pushforwardCompletionIso i I G).hom.app (op n) ≫
        (Scheme.Modules.pushforward i).map
          (((completionFunctor Z (I.comap i)).map f).hom.app (op n)) := by
  have hepi := epi_completionProjection X I (pushforwardCoherentObj i G) n
  refine (@cancel_epi _ _ _ _ _
    (completionProjection X I (pushforwardCoherentObj i G) n) hepi _ _).mp ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (pushforwardCompletionIso i I G').hom.app (op n))
        (completionFunctor_map_quotient X I (pushforwardCoherentMap i f) n)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (Scheme.Modules.pushforward i).map f.hom ≫ k)
            (pushforwardCompletionIso_projection i I G' n)).trans
          (((Scheme.Modules.pushforward i).map_comp _ _).symm.trans
            ((congrArg (Scheme.Modules.pushforward i).map
                (completionFunctor_map_quotient Z (I.comap i) f n).symm).trans
              (((Scheme.Modules.pushforward i).map_comp _ _).trans
                ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward i).map
                      (((completionFunctor Z (I.comap i)).map f).hom.app (op n)))
                    (pushforwardCompletionIso_projection i I G n).symm).trans
                  (Category.assoc _ _ _))))))))

end ClosedImmersion

end Stacks.Algebraization

end
