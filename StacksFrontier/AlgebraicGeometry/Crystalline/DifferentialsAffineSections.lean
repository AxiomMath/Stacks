module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections

/-!
# The sections of the divided power differentials over an affine open

Let `(T, J, δ)` be a divided power scheme and `f : T → Y` a morphism of schemes.  For an affine
open `W ⊆ T` lying over an affine open `V ⊆ Y` the sections of the sheaf `Ω_{T/Y,δ}` of divided
power differentials over `W` are the ring-theoretic module `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` of divided
power differentials, compatibly with the universal derivations.  This is the second assertion of
[Stacks, Tag 07IY].

## Main definitions

* `Crystalline.affineKaehlerIso` and `Crystalline.affineKaehlerEquiv` — the identification of
  [Stacks, Tag 01UT] of the sections of `Ω_{T/Y}` over an affine open with the Kähler
  differentials of the corresponding ring map, as a morphism of `ModuleCat` and as a linear
  equivalence over `Γ(W, 𝒪_T)`.
* `Crystalline.affineDpComparison` — that identification followed by the quotient by the
  ring-level divided power relations.
* `Crystalline.affineQuotientComparison` — the comparison from `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` to the
  sections of `Ω_{T/Y} / R` over `W`, given by the ring-level universal property.
* `Crystalline.affineSectionsEquiv` — the identification of the sections of `Ω_{T/Y,δ}` over an
  affine open with `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`.

## Main results

* `Crystalline.dpRelationSubmodule_isQuasicoherent` — the subsheaf of divided power relations is
  quasi-coherent.
* `Crystalline.mem_dpRelationSpan_of_mem_dpRelationSubmodule` — over an affine open a section of
  that subsheaf is a combination of the divided power relations there.
* `Crystalline.surjective_dpQuotientMk_app` and `Crystalline.ker_dpQuotientMk_app` — the quotient
  map `Ω_{T/Y} → Ω_{T/Y} / R` is surjective on the sections over an affine open, with kernel the
  span of the divided power relations.
* `Crystalline.bijective_affineQuotientComparison` — the comparison at an affine open is
  bijective.
* `Crystalline.affineSectionsEquiv_apply` and `Crystalline.affineSectionsEquiv_symm_dpd` — the
  identification carries `d_{T/Y,δ}` to `d_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` and back.

## Implementation notes

The identification is a `LinearEquiv` over `Γ(W, 𝒪_T)` rather than an isomorphism in `ModuleCat`.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### Evaluation at an affine open -/

private theorem exact_app_of_isAffineOpen {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Exact (g.app U) ((cokernel.π (C := X.Modules) g).app U) := by
  let F : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  let _ : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  have him : (Abelian.image (C := X.Modules) g).IsQuasicoherent := by
    dsimp [Abelian.image]
    infer_instance
  have hs := surjective_app_of_epi_of_isAffineOpen
    (Abelian.factorThruImage (C := X.Modules) g) hU
  have hex := (ShortComplex.exact_kernel (C := X.Modules)
    (cokernel.π (C := X.Modules) g)).map_of_mono_of_preservesKernel F inferInstance inferInstance
  have hh := (ShortComplex.moduleCat_exact_iff _).mp hex
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hh y hy
    obtain ⟨x, hx⟩ := hs z
    refine ⟨x, ?_⟩
    have he := congrArg (fun φ : M ⟶ N => φ.app U x) (Abelian.image.fac (C := X.Modules) g)
    exact he.symm.trans
      ((congrArg (fun w => (kernel.ι (C := X.Modules)
        (cokernel.π (C := X.Modules) g)).app U w) hx).trans hz)
  · rintro ⟨x, rfl⟩
    exact congrArg (fun φ : M ⟶ cokernel (C := X.Modules) g => φ.app U x)
      (cokernel.condition (C := X.Modules) g)

/-- A submodule of a sheaf of modules is the kernel of the quotient map onto the cokernel of its
inclusion. -/
noncomputable def submoduleIsoKernel {X : Scheme.{u}}
    {M : _root_.SheafOfModules.{u} X.ringCatSheaf} (N : M.Submodule) :
    N.toSheafOfModules ≅ kernel (cokernel.π N.ι) :=
  asIso (Abelian.factorThruImage N.ι)

/-! ### A localization lemma -/

private theorem exists_pow_smul_mem_of_mem_span_image
    {A : Type u} [CommRing A] {Aa : Type u} [CommRing Aa] [Algebra A Aa] (a : A)
    [IsLocalization.Away a Aa]
    {M : Type u} [AddCommGroup M] [Module A M] {Ma : Type u} [AddCommGroup Ma]
    [Module A Ma] [Module Aa Ma] [IsScalarTower A Aa Ma]
    (ρ : M →ₗ[A] Ma) [IsLocalizedModule (Submonoid.powers a) ρ]
    (P : Submodule A M) {ι : Type*} (g : ι → M) (hg : ∀ i, g i ∈ P) {z : M}
    (hz : ρ z ∈ Submodule.span Aa (Set.range fun i ↦ ρ (g i))) : ∃ n : ℕ, a ^ n • z ∈ P := by
  have hsm : ∀ (r : A) (x : Ma), r • x = (algebraMap A Aa) r • x :=
    fun r x ↦ (IsScalarTower.algebraMap_smul Aa r x).symm
  have key : ∀ w ∈ Submodule.span Aa (Set.range fun i ↦ ρ (g i)),
      ∃ (n : ℕ) (p : M), p ∈ P ∧ a ^ n • w = ρ p := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨0, g i, hg i, by rw [pow_zero, one_smul]⟩
    | zero => exact ⟨0, 0, P.zero_mem, by rw [smul_zero, map_zero]⟩
    | add u v _ _ ihu ihv =>
        obtain ⟨n, p, hp, hup⟩ := ihu
        obtain ⟨m, q, hq, hvq⟩ := ihv
        refine ⟨n + m, a ^ m • p + a ^ n • q, P.add_mem (P.smul_mem _ hp) (P.smul_mem _ hq), ?_⟩
        have hpow : ∀ (n m : ℕ) (w : Ma), a ^ (n + m) • w = a ^ m • (a ^ n • w) :=
          fun n m w ↦ by rw [smul_smul, ← pow_add, add_comm]
        rw [smul_add, hpow n m, add_comm n m, hpow m n, hup, hvq, map_add, map_smul, map_smul]
    | smul c u _ ihu =>
        obtain ⟨n, p, hp, hup⟩ := ihu
        obtain ⟨⟨b, d⟩, hbd⟩ := IsLocalization.surj (Submonoid.powers a) c
        obtain ⟨k, hk⟩ := d.2
        have hk' : a ^ k = (d : A) := hk
        refine ⟨n + k, b • p, P.smul_mem _ hp, ?_⟩
        have hc : (algebraMap A Aa) (a ^ k) * c = (algebraMap A Aa) b := by
          rw [hk']
          exact (mul_comm c ((algebraMap A Aa) (d : A))).symm.trans hbd
        have e1 : a ^ (n + k) • (c • u) = ((algebraMap A Aa) (a ^ k) * c) • (a ^ n • u) := by
          rw [hsm (a ^ (n + k)) (c • u), hsm (a ^ n) u, smul_smul, smul_smul, pow_add, map_mul]
          congr 1
          ring
        rw [e1, hup, hc, ← hsm, map_smul]
  obtain ⟨n, p, hp, hnp⟩ := key (ρ z) hz
  rw [← map_smul] at hnp
  obtain ⟨m, hmz⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) ρ).mp
    (show ρ (a ^ n • z - p) = 0 by rw [map_sub, hnp, sub_self])
  obtain ⟨k, hk⟩ := m.2
  have hk' : a ^ k = (m : A) := hk
  refine ⟨k + n, ?_⟩
  have hz0 : a ^ k • (a ^ n • z - p) = 0 := by rwa [hk']
  rw [smul_sub, sub_eq_zero] at hz0
  rw [pow_add, mul_smul, hz0]
  exact P.smul_mem _ hp

/-! ### The relation subsheaf on an affine open -/

section Relations

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- Two successive restrictions of a section of `Ω_{T/Y}` are one restriction. -/
private theorem relDiffMapMap {W V V' : T.scheme.Opens} (h₁ : V ≤ W) (h₂ : V' ≤ V)
    (s : Γ(Scheme.Hom.relativeDifferentials f, W)) :
    (Scheme.Hom.relativeDifferentials f).val.map (homOfLE h₂).op
        ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h₁).op s) =
      (Scheme.Hom.relativeDifferentials f).val.map (homOfLE (h₂.trans h₁)).op s :=
  ((Scheme.Hom.relativeDifferentials f).val.map_comp_apply (homOfLE h₁).op (homOfLE h₂).op s).symm

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange in
/-- **Local generation of the divided power ideal over a basic open.**  Every section of the
divided power ideal over a basic open of an affine open `W₀` lies in the submodule generated by
the restrictions of the sections over `W₀`. -/
private theorem sectionIdeal_mem_span' (W₀ : T.scheme.Opens) (hW₀ : IsAffineOpen W₀)
    (a : Γ(T.scheme, W₀))
    (y : ↥(sectionIdeal T.scheme.sheaf T.ideal (op (T.scheme.basicOpen a)))) :
    (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) ∈
      Submodule.span ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))
        (Set.range fun x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W₀)) ↦
          (DividedPowerStructure.restrict T.ideal
            (homOfLE (T.scheme.basicOpen_le a)).op x :
              ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))))  := by
  have hle : T.scheme.basicOpen a ≤ W₀ := T.scheme.basicOpen_le a
  let := moduleOfLE (dpIdealModule T) hle
  have hloc := isLocalizedModule_restrictₗ (dpIdealModule T) hW₀ a rfl hle
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj
    (restrictₗ (dpIdealModule T) hle) a y
  obtain ⟨u, hu⟩ : IsUnit (id (T.scheme.presheaf.map (homOfLE hle).op a) :
      ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) :=
    T.scheme.toRingedSpace.isUnit_res_basicOpen a
  have hcoe : (id (T.scheme.presheaf.map (homOfLE hle).op a) :
        ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) ^ n *
      (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
      (DividedPowerStructure.restrict T.ideal (homOfLE hle).op x :
        ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) := by
    have h : (id (T.scheme.presheaf.map (homOfLE hle).op (a ^ n)) :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) *
        (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
        (DividedPowerStructure.restrict T.ideal (homOfLE hle).op x :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) :=
      congrArg (fun w : ↥(sectionIdeal T.scheme.sheaf T.ideal
        (op (T.scheme.basicOpen a))) ↦ (w : ↑(T.scheme.sheaf.obj.obj
          (op (T.scheme.basicOpen a))))) hx
    rwa [map_pow] at h
  have hy : (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
      ((u⁻¹ : _) ^ n : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) •
        (DividedPowerStructure.restrict T.ideal (homOfLE hle).op x :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) := by
    rw [← hcoe, smul_eq_mul, ← mul_assoc, ← hu, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  rw [hy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self x))

/-- **Every divided power relation over a basic open of an affine open is a combination of the
restrictions of the relations over the whole open.** -/
private theorem dpRelationSpan_basicOpen_le (W₀ : T.scheme.Opens) (hW₀ : IsAffineOpen W₀)
    (a : Γ(T.scheme, W₀)) :
    dpRelationSpan T Y f (T.scheme.basicOpen a) ≤
      Submodule.span ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))
        (Set.range fun z : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W₀)) × ℕ ↦
          (Scheme.Hom.relativeDifferentials f).val.map
            (homOfLE (T.scheme.basicOpen_le a)).op (dpRelationSection T Y f W₀ z.1 z.2)) := by
  have hle : T.scheme.basicOpen a ≤ W₀ := T.scheme.basicOpen_le a
  refine (Submodule.span_le (R := ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a))))
    (s := dpRelationSet T Y f (T.scheme.basicOpen a))).mpr ?_
  rintro _ ⟨⟨y, m⟩, rfl⟩
  refine SetLike.mem_coe.mpr (dpRelation_mem_of_mem_span
    (hJ := T.dividedPowers.dividedPowers (op (T.scheme.basicOpen a)))
    (D := (Scheme.Hom.universalRelativeDerivation f).d (X := op (T.scheme.basicOpen a)))
    (fun b c ↦ (Scheme.Hom.universalRelativeDerivation f).d_mul
      (X := op (T.scheme.basicOpen a)) b c)
    (Submodule.span ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))
      (Set.range fun z : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W₀)) × ℕ ↦
        (Scheme.Hom.relativeDifferentials f).val.map
          (homOfLE (T.scheme.basicOpen_le a)).op (dpRelationSection T Y f W₀ z.1 z.2)))
    (S := Set.range fun x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W₀)) ↦
      (DividedPowerStructure.restrict T.ideal (homOfLE hle).op x :
        ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))))
    ?_ ?_ (sectionIdeal_mem_span' T W₀ hW₀ a y) m)
  · rintro _ ⟨x, rfl⟩
    exact (DividedPowerStructure.restrict T.ideal (homOfLE hle).op x).2
  · rintro _ ⟨x, rfl⟩ k
    exact Submodule.subset_span ⟨(x, k), map_dpRelationSection T Y f (homOfLE hle).op x k⟩

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange in
/-- If the restriction of a section `s` of `Ω_{T/Y}` over an affine open `W₀` to the basic open of
`a` lies in the span of the divided power relations there, then `a ^ n • s` lies in the span of the
divided power relations over `W₀` for some `n`. -/
private theorem exists_pow_smul_mem_dpRelationSpan (W₀ : T.scheme.Opens)
    (hW₀ : IsAffineOpen W₀) (a : Γ(T.scheme, W₀))
    {s : Γ(Scheme.Hom.relativeDifferentials f, W₀)}
    (hs : (Scheme.Hom.relativeDifferentials f).val.map
        (homOfLE (T.scheme.basicOpen_le a)).op s ∈
      dpRelationSpan T Y f (T.scheme.basicOpen a)) :
    ∃ n : ℕ, a ^ n • s ∈ dpRelationSpan T Y f W₀ := by
  have hle : T.scheme.basicOpen a ≤ W₀ := T.scheme.basicOpen_le a
  let := algebraOfLE T.scheme hle
  let := moduleOfLE (Scheme.Hom.relativeDifferentials f) hle
  have : IsLocalization.Away a Γ(T.scheme, T.scheme.basicOpen a) :=
    hW₀.isLocalization_basicOpen a
  have : IsLocalizedModule.Away a (restrictₗ (Scheme.Hom.relativeDifferentials f) hle) :=
    isLocalizedModule_restrictₗ (Scheme.Hom.relativeDifferentials f) hW₀ a rfl hle
  have : IsScalarTower Γ(T.scheme, W₀) Γ(T.scheme, T.scheme.basicOpen a)
      Γ(Scheme.Hom.relativeDifferentials f, T.scheme.basicOpen a) :=
    isScalarTowerOfLE (Scheme.Hom.relativeDifferentials f) hle
  exact exists_pow_smul_mem_of_mem_span_image (Aa := Γ(T.scheme, T.scheme.basicOpen a)) a
    (restrictₗ (Scheme.Hom.relativeDifferentials f) hle)
    (dpRelationSpan T Y f W₀)
    (fun z : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W₀)) × ℕ ↦
      dpRelationSection T Y f W₀ z.1 z.2)
    (fun z ↦ dpRelationSection_mem_span T Y f W₀ z.1 z.2)
    (dpRelationSpan_basicOpen_le T Y f W₀ hW₀ a hs)

/-- **A section of the relation subsheaf over an affine open is a combination of the relations
there.** -/
theorem mem_dpRelationSpan_of_mem_dpRelationSubmodule (W₀ : T.scheme.Opens)
    (hW₀ : IsAffineOpen W₀)
    {s : Γ(Scheme.Hom.relativeDifferentials f, W₀)}
    (hs : s ∈ (dpRelationSubmodule T Y f).obj (op W₀)) :
    s ∈ dpRelationSpan T Y f W₀ := by
  set G : Set Γ(T.scheme, W₀) :=
    {a | (Scheme.Hom.relativeDifferentials f).val.map
      (homOfLE (T.scheme.basicOpen_le a)).op s ∈ dpRelationSpan T Y f (T.scheme.basicOpen a)}
    with hG
  have hspan : Ideal.span G = ⊤ := by
    rw [← hW₀.self_le_iSup_basicOpen_iff]
    intro p hp
    obtain ⟨Vp, hVple, hpV, hmem⟩ := hs p hp
    obtain ⟨b, hbV, hpb⟩ := hW₀.exists_basicOpen_le (⟨p, hpV⟩ : Vp) hp
    refine Opens.mem_iSup.mpr ⟨⟨b, ?_⟩, hpb⟩
    have h2 := dpRelationSpan_map T Y f (homOfLE hbV).op hmem
    rwa [relDiffMapMap T Y f hVple hbV s] at h2
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ G hspan s ?_
  rintro ⟨b, hb⟩
  exact exists_pow_smul_mem_dpRelationSpan T Y f W₀ hW₀ b hb

/-- The subsheaf of divided power relations is the kernel of the comparison map onto the
quotient. -/
def dpRelationSubmoduleIsoKernel :
    (dpRelationSubmodule T Y f).toSheafOfModules ≅
      kernel (C := T.scheme.Modules) (dpQuotientMk T Y f) :=
  submoduleIsoKernel (X := T.scheme) (dpRelationSubmodule T Y f)

/-- **The subsheaf of divided power relations is quasi-coherent.** -/
instance dpRelationSubmodule_isQuasicoherent :
    ((dpRelationSubmodule T Y f).toSheafOfModules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.scheme.ringCatSheaf).prop_of_iso
    (dpRelationSubmoduleIsoKernel T Y f).symm inferInstance

/-- **The quotient map is surjective on the sections over an affine open.** -/
theorem surjective_dpQuotientMk_app (W : T.scheme.Opens) (hW : IsAffineOpen W) :
    Function.Surjective ((dpQuotientMk T Y f).app W) :=
  have : Epi (dpQuotientMk T Y f) :=
    epi_cokernelπ (X := T.scheme) (dpRelationSubmodule T Y f).ι
  surjective_app_of_epi_of_isAffineOpen (dpQuotientMk T Y f) hW

/-- **The kernel of the quotient map on the sections over an affine open is the span of the
divided power relations there.** -/
theorem ker_dpQuotientMk_app (W : T.scheme.Opens) (hW : IsAffineOpen W) :
    LinearMap.ker (Scheme.Modules.sectionsLinearMap (dpQuotientMk T Y f) W) =
      dpRelationSpan T Y f W := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨y, hy⟩ :=
      (exact_app_of_isAffineOpen (dpRelationSubmodule T Y f).ι hW x).mp hx
    rw [← hy]
    exact mem_dpRelationSpan_of_mem_dpRelationSubmodule T Y f W hW y.2
  · rintro _ ⟨⟨x, n⟩, rfl⟩
    exact dpQuotientMk_apply_eq_zero T Y f W (dpRelationSection_mem_submodule T Y f W x n)

end Relations

/-! ### The sections over an affine open -/

section Affine

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  {W : T.scheme.Opens} (hW : IsAffineOpen W) {V : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

/-- The sections of `Ω_{T/Y}` over an open, as a module over the ring of sections of `𝒪_T` there
in the spelling the ring-level objects use. -/
instance relDiffGammaModule (W' : T.scheme.Opens) :
    Module Γ(T.scheme, W') ↑((Scheme.Hom.relativeDifferentials f).val.obj (op W')) :=
  ((Scheme.Hom.relativeDifferentials f).val.obj (op W')).isModule

/-- **The sections of `Ω_{T/Y}` over an affine open lying over an affine open of the base are the
Kähler differentials of the corresponding ring map**: the identification of [Stacks, Tag 01UT]. -/
def affineKaehlerIso : (Scheme.Hom.relativeDifferentials f).val.obj (op W) ≅
    CommRingCat.KaehlerDifferential (f.appLE V W h) :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hW h hV).choose

/-- The identification carries the universal relative derivation to the universal derivation. -/
theorem affineKaehlerIso_hom_d (b : Γ(T.scheme, W)) :
    (affineKaehlerIso T Y f hW h hV).hom.hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      CommRingCat.KaehlerDifferential.d b :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hW h hV).choose_spec.1 b

/-- The identification carries the universal derivation back to the universal relative
derivation. -/
theorem affineKaehlerIso_inv_d (b : Γ(T.scheme, W)) :
    (affineKaehlerIso T Y f hW h hV).inv.hom (CommRingCat.KaehlerDifferential.d b) =
      (Scheme.Hom.universalRelativeDerivation f).d b :=
  Stacks.AlgebraicGeometry.AffineDifferentials.inv_hom_apply_d f V W h _
    (affineKaehlerIso_hom_d T Y f hW h hV) b

/-- **The sections of `Ω_{T/Y}` over an affine open are the Kähler differentials**, as a linear
equivalence over the ring of sections of `𝒪_T` there. -/
def affineKaehlerEquiv : ↑((Scheme.Hom.relativeDifferentials f).val.obj (op W)) ≃ₗ[Γ(T.scheme, W)]
    ↑(CommRingCat.KaehlerDifferential (f.appLE V W h)) :=
  { toFun := (affineKaehlerIso T Y f hW h hV).hom.hom
    map_add' := map_add _
    map_smul' := map_smul _
    invFun := (affineKaehlerIso T Y f hW h hV).inv.hom
    left_inv := fun z ↦ congrArg
      (fun φ : (Scheme.Hom.relativeDifferentials f).val.obj (op W) ⟶
        (Scheme.Hom.relativeDifferentials f).val.obj (op W) ↦ φ.hom z)
      (affineKaehlerIso T Y f hW h hV).hom_inv_id
    right_inv := fun w ↦ congrArg
      (fun φ : CommRingCat.KaehlerDifferential (f.appLE V W h) ⟶
        CommRingCat.KaehlerDifferential (f.appLE V W h) ↦ φ.hom w)
      (affineKaehlerIso T Y f hW h hV).inv_hom_id }

/-- **The comparison from the sections of `Ω_{T/Y}` over an affine open to the divided power
differentials of the rings**: the identification of [Stacks, Tag 01UT], followed by the quotient
by the divided power relations. -/
def affineDpComparison : ↑((Scheme.Hom.relativeDifferentials f).val.obj (op W)) →ₗ[Γ(T.scheme, W)]
    ↑(dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))) :=
  (dpMkQ (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))).hom.comp
    (affineKaehlerEquiv T Y f hW h hV).toLinearMap

/-- The comparison carries the universal relative derivation to the universal divided power
derivation of the rings. -/
@[simp]
theorem affineDpComparison_d (b : Γ(T.scheme, W)) :
    affineDpComparison T Y f hW h hV ((Scheme.Hom.universalRelativeDerivation f).d b) =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b :=
  congrArg (fun z ↦ (dpMkQ (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))).hom z)
    (affineKaehlerIso_hom_d T Y f hW h hV b)

/-- The comparison from the sections of `Ω_{T/Y}` to the divided power differentials of the rings
is surjective. -/
theorem surjective_affineDpComparison :
    Function.Surjective (affineDpComparison T Y f hW h hV) :=
  (dpRelations (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))).mkQ_surjective.comp
    (affineKaehlerEquiv T Y f hW h hV).surjective

/-- **The divided power relations over an affine open die in the divided power differentials of
the rings.** -/
theorem dpRelationSpan_le_ker_affineDpComparison :
    dpRelationSpan T Y f W ≤ LinearMap.ker (affineDpComparison T Y f hW h hV) := by
  refine (Submodule.span_le (R := Γ(T.scheme, W))
    (s := dpRelationSet T Y f W)).mpr ?_
  rintro _ ⟨⟨x, n⟩, rfl⟩
  have hx : (x : ↑(T.scheme.sheaf.obj.obj (op W))) ∈ T.ideal.obj (op W) := x.2
  have hcast : dpRelationSection T Y f W x n =
      (Scheme.Hom.universalRelativeDerivation f).d
          ((T.dividedPowers.dividedPowers (op W)).dpow (n + 1)
            (x : ↑(T.scheme.sheaf.obj.obj (op W)))) -
        (id ((T.dividedPowers.dividedPowers (op W)).dpow n
            (x : ↑(T.scheme.sheaf.obj.obj (op W)))) : Γ(T.scheme, W)) •
          (Scheme.Hom.universalRelativeDerivation f).d
            (x : ↑(T.scheme.sheaf.obj.obj (op W))) := rfl
  have key : affineDpComparison T Y f hW h hV (dpRelationSection T Y f W x n) = 0 := by
    rw [hcast, map_sub, map_smul]
    refine (congrArg₂ (· - ·) (affineDpComparison_d T Y f hW h hV _)
      (congrArg (fun w ↦ (id ((T.dividedPowers.dividedPowers (op W)).dpow n
          (x : ↑(T.scheme.sheaf.obj.obj (op W)))) : Γ(T.scheme, W)) • w)
        (affineDpComparison_d T Y f hW h hV _))).trans ?_
    exact sub_eq_zero.mpr
      (dpd_dpow (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) n
        (x : ↑(T.scheme.sheaf.obj.obj (op W))) hx)
  exact SetLike.mem_coe.mpr (LinearMap.mem_ker.mpr key)

include hW h hV in
/-- **The universal relative differentials span the sections of `Ω_{T/Y}` over an affine
open.** -/
theorem span_range_relDiff_d_eq_top :
    Submodule.span Γ(T.scheme, W)
        (Set.range fun b : Γ(T.scheme, W) ↦
          (Scheme.Hom.universalRelativeDerivation f).d b) = ⊤ := by
  set P := Submodule.span Γ(T.scheme, W)
    (Set.range fun b : Γ(T.scheme, W) ↦ (Scheme.Hom.universalRelativeDerivation f).d b) with hP
  have hq : ModuleCat.ofHom (P.mkQ.comp
        (affineKaehlerEquiv T Y f hW h hV).symm.toLinearMap) =
      (0 : CommRingCat.KaehlerDifferential (f.appLE V W h) ⟶
        ModuleCat.of Γ(T.scheme, W)
          (↑((Scheme.Hom.relativeDifferentials f).val.obj (op W)) ⧸ P)) := by
    refine CommRingCat.KaehlerDifferential.ext fun b ↦ ?_
    change P.mkQ ((affineKaehlerEquiv T Y f hW h hV).symm
      (CommRingCat.KaehlerDifferential.d b)) = 0
    rw [show (affineKaehlerEquiv T Y f hW h hV).symm
        (CommRingCat.KaehlerDifferential.d b) =
      (Scheme.Hom.universalRelativeDerivation f).d b from
        affineKaehlerIso_inv_d T Y f hW h hV b]
    exact (Submodule.Quotient.mk_eq_zero P).mpr (Submodule.subset_span ⟨b, rfl⟩)
  refine eq_top_iff.mpr fun y _ ↦ ?_
  refine (Submodule.Quotient.mk_eq_zero P).mp ?_
  have hy := congrArg (fun φ : CommRingCat.KaehlerDifferential (f.appLE V W h) ⟶
      ModuleCat.of Γ(T.scheme, W) (↑((Scheme.Hom.relativeDifferentials f).val.obj (op W)) ⧸ P) ↦
    φ.hom (affineKaehlerEquiv T Y f hW h hV y)) hq
  change P.mkQ ((affineKaehlerEquiv T Y f hW h hV).symm
    (affineKaehlerEquiv T Y f hW h hV y)) = 0 at hy
  rwa [LinearEquiv.symm_apply_apply] at hy

/-- **The divided power derivation on the sections of `Ω_{T/Y} / R` over an open, relative to the
sections of the base over an open it maps into.** -/
def affineQuotientDerivation :
    (ModuleCat.of Γ(T.scheme, W) Γ(dpQuotient T Y f, W)).Derivation (f.appLE V W h) :=
  ModuleCat.Derivation.mk (dpQuotientApp T Y f W) (dpQuotientApp_add T Y f W)
    (dpQuotientApp_mul T Y f W) (fun a ↦ dpQuotientApp_appLE T Y f W V h a)

/-- **The comparison map from the divided power differentials of the rings to the sections of the
quotient `Ω_{T/Y} / R` over an open**, given by the ring-level universal property. -/
def affineQuotientComparison :
    dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) ⟶
      ModuleCat.of Γ(T.scheme, W) Γ(dpQuotient T Y f, W) :=
  dpDesc (affineQuotientDerivation T Y f h)
    (fun n x hx ↦ dpQuotientApp_dpow T Y f W n ⟨x, hx⟩)

/-- The comparison carries the universal divided power derivation of the rings to the derivation
on the sections of the quotient. -/
@[simp]
theorem affineQuotientComparison_dpd (b : Γ(T.scheme, W)) :
    (affineQuotientComparison T Y f h).hom
        (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b) =
      dpQuotientApp T Y f W b :=
  dpDesc_d (affineQuotientDerivation T Y f h) _ b

/-- **The comparison factors the quotient map on the sections over an affine open.** -/
theorem affineQuotientComparison_affineDpComparison
    (y : ↑((Scheme.Hom.relativeDifferentials f).val.obj (op W))) :
    (affineQuotientComparison T Y f h).hom (affineDpComparison T Y f hW h hV y) =
      Scheme.Modules.sectionsLinearMap (dpQuotientMk T Y f) W y := by
  have hcomp : ((affineQuotientComparison T Y f h).hom.comp
        (affineDpComparison T Y f hW h hV)) =
      Scheme.Modules.sectionsLinearMap (dpQuotientMk T Y f) W := by
    refine LinearMap.ext_on (span_range_relDiff_d_eq_top T Y f hW h hV) ?_
    rintro _ ⟨b, rfl⟩
    exact (congrArg (fun z ↦ (affineQuotientComparison T Y f h).hom z)
      (affineDpComparison_d T Y f hW h hV b)).trans
        (affineQuotientComparison_dpd T Y f h b)
  exact congrArg (fun φ : ↑((Scheme.Hom.relativeDifferentials f).val.obj (op W)) →ₗ[Γ(T.scheme, W)]
    Γ(dpQuotient T Y f, W) ↦ φ y) hcomp

include hW hV in
/-- **The sections of `Ω_{T/Y} / R` over an affine open lying over an affine open of the base are
the divided power differentials of the corresponding rings.** -/
theorem bijective_affineQuotientComparison :
    Function.Bijective (affineQuotientComparison T Y f h).hom := by
  refine ⟨fun m m' hmm ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := surjective_affineDpComparison T Y f hW h hV m
    obtain ⟨y', rfl⟩ := surjective_affineDpComparison T Y f hW h hV m'
    have hzero : Scheme.Modules.sectionsLinearMap (dpQuotientMk T Y f) W (y - y') = 0 :=
      (map_sub (Scheme.Modules.sectionsLinearMap (dpQuotientMk T Y f) W) y y').trans
        (sub_eq_zero.mpr ((affineQuotientComparison_affineDpComparison T Y f hW h hV y).symm.trans
          (hmm.trans (affineQuotientComparison_affineDpComparison T Y f hW h hV y'))))
    have hker : y - y' ∈ dpRelationSpan T Y f W := by
      rw [← ker_dpQuotientMk_app T Y f W hW]
      exact hzero
    exact sub_eq_zero.mp ((map_sub (affineDpComparison T Y f hW h hV) y y').symm.trans
      (dpRelationSpan_le_ker_affineDpComparison T Y f hW h hV hker))
  · obtain ⟨y, hyz⟩ := surjective_dpQuotientMk_app T Y f W hW z
    exact ⟨affineDpComparison T Y f hW h hV y,
      (affineQuotientComparison_affineDpComparison T Y f hW h hV y).trans hyz⟩

include hW hV in
/-- The sections of the quotient `Ω_{T/Y} / R` over an affine open, as a module over the sections
of `𝒪_T` there, are the divided power differentials of the rings. -/
def affineQuotientSectionsEquiv :
    ↑(dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))) ≃ₗ[Γ(T.scheme, W)]
      Γ(dpQuotient T Y f, W) :=
  LinearEquiv.ofBijective (affineQuotientComparison T Y f h).hom
    (bijective_affineQuotientComparison T Y f hW h hV)

/-- The sections over an open of the sheaf of divided power differentials are the sections of the
quotient `Ω_{T/Y} / R` there. -/
def sectionsIsoQuotient (U : T.scheme.Opens) :
    Γ(dpDifferentialsSheaf T Y f, U) ≃ₗ[Γ(T.scheme, U)] Γ(dpQuotient T Y f, U) :=
  LinearEquiv.ofLinearMap
    (Scheme.Modules.sectionsLinearMap (dpDifferentialsIsoQuotient T Y f).hom U)
    (Scheme.Modules.sectionsLinearMap (dpDifferentialsIsoQuotient T Y f).inv U)
    (LinearMap.ext fun z ↦
      congrArg (fun φ : dpQuotient T Y f ⟶ dpQuotient T Y f ↦ φ.app U z)
        (dpDifferentialsIsoQuotient T Y f).inv_hom_id)
    (LinearMap.ext fun z ↦
      congrArg (fun φ : dpDifferentialsSheaf T Y f ⟶ dpDifferentialsSheaf T Y f ↦ φ.app U z)
        (dpDifferentialsIsoQuotient T Y f).hom_inv_id)

include hW hV in
/-- For an affine open `W` of a divided power scheme `T` lying over an affine open `V` of the base
`Y`, the sections of the sheaf `Ω_{T/Y,δ}` of divided power differentials over `W` are the module
`Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` of divided power differentials of the corresponding rings. -/
@[stacks 07IY "clause (2): the sections over an affine open"]
def affineSectionsEquiv :
    Γ(dpDifferentialsSheaf T Y f, W) ≃ₗ[Γ(T.scheme, W)]
      ↑(dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))) :=
  (sectionsIsoQuotient T Y f W).trans (affineQuotientSectionsEquiv T Y f hW h hV).symm

/-- The identification carries the universal divided power derivation `d_{T/Y,δ}` to the
universal divided power differential of the rings. -/
theorem affineSectionsEquiv_apply (b : Γ(T.scheme, W)) :
    affineSectionsEquiv T Y f hW h hV ((universalDPSchemeDerivation T Y f).app W b) =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b := by
  refine (affineQuotientSectionsEquiv T Y f hW h hV).injective ?_
  refine Eq.trans ((affineQuotientSectionsEquiv T Y f hW h hV).apply_symm_apply _) ?_
  change Scheme.Modules.sectionsLinearMap (dpDifferentialsIsoQuotient T Y f).hom W
      ((universalDPSchemeDerivation T Y f).app W b) =
    (affineQuotientComparison T Y f h).hom
      (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b)
  exact (differentialsToDpQuotient_app T Y f W b).trans
    (affineQuotientComparison_dpd T Y f h b).symm

/-- The identification carries the universal divided power differential of the rings back to the
universal divided power derivation `d_{T/Y,δ}`. -/
theorem affineSectionsEquiv_symm_dpd (b : Γ(T.scheme, W)) :
    (affineSectionsEquiv T Y f hW h hV).symm
        (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b) =
      (universalDPSchemeDerivation T Y f).app W b :=
  (affineSectionsEquiv T Y f hW h hV).injective
    (((affineSectionsEquiv T Y f hW h hV).apply_symm_apply _).trans
      (affineSectionsEquiv_apply T Y f hW h hV b).symm)

end Affine

end Crystalline

end
