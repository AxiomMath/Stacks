module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Duality.SheafSubquotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple

/-!
# Ideal-power multiples of a submodule, and Artin-Rees for them

For a quasi-coherent sheaf of ideals `𝓘` on a scheme `X` and a submodule `N` of an `𝒪_X`-module
`L`, the submodule `𝓘 ^ n N` of `L` is the image of `𝓘 ^ n` applied to `N`. Its sections over an
affine open are `𝓘(U) ^ n N(U)` when `N` is quasi-coherent. The Artin-Rees theorem for coherent
sheaves then takes the form of a containment of submodules of `L`: for one constant `c` and all
`n ≥ c`,

`𝓘 ^ n L ⊓ N ≤ 𝓘 ^ (n - c) N`.

An epimorphism of quasi-coherent modules carries `𝓘 ^ n` of its source onto `𝓘 ^ n` of its target,
and a map of subquotients of `L` is a monomorphism as soon as the subobject downstairs is cut out
of the one upstairs.

## Main definitions

* `AlgebraicGeometry.secs` and `AlgebraicGeometry.secMap` — the sections of a submodule and the map
  on sections of a morphism, with scalars read as `Γ(X, U)`.
* `AlgebraicGeometry.idealPowerSub` — the submodule `𝓘 ^ n N` of `L`.

## Main results

* `AlgebraicGeometry.idealPowerSub_obj_affine` — the sections of `𝓘 ^ n N` over an affine open.
* `AlgebraicGeometry.exists_idealPowerSub_artinRees` — the Artin-Rees containment above.
* `AlgebraicGeometry.imageSubmodule_idealPowerMultiple_of_epi` — the image of `𝓘 ^ n` of the source
  of an epimorphism of quasi-coherent modules is `𝓘 ^ n` of its target.
* `AlgebraicGeometry.mono_of_injective_app_affine` — a morphism injective on the sections over
  every affine open is a monomorphism, and `AlgebraicGeometry.mono_subqMap` the resulting criterion
  for a map of subquotients.

## Implementation notes

The scalars on `Γ(M, U)` are declared over `X.ringCatSheaf.obj.obj (op U)`, which instance search
does not recognise as `Γ(X, U)` across the `TopCat.Sheaf` definition. `secs` and `secMap` are those
same data ascribed at the `Γ(X, U)` spelling, which is the one the Artin-Rees statement and the
`Submodule` API are phrased in; each identity below is stated in the spelling of its own goal and
discharged by `exact`, since `rw` works at a transparency that does not see through
`AlgebraicGeometry.Scheme.Modules`.

## References

* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Sections with scalars read on the scheme -/

/-- The module structure of `Γ(M, U)` over `Γ(X, U)`. The scalars on `Γ(M, U)` are declared over
`X.ringCatSheaf.obj.obj (op U)`, which instance search does not recognise as `Γ(X, U)` across the
`TopCat.Sheaf` definition; this is that same module structure at the `Γ(X, U)` spelling. -/
local instance sectionsModuleΓSheaf (M : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    Module Γ(X, U) Γ(M, U) := (M.val.obj (op U)).isModule

/-- The sections of a submodule over an open, with the scalars read as `Γ(X, U)`. -/
def secs {L : X.Modules} (N : L.Submodule) (U : X.Opens) : Submodule Γ(X, U) Γ(L, U) :=
  N.toSubmodule.obj (op U)

/-- The map on sections over `U` induced by a morphism, with the scalars read as `Γ(X, U)`. -/
def secMap {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (f.val.app (op U)).hom

/-- The map on sections of a composite is the composite of the maps on sections. -/
lemma secMap_comp {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) (U : X.Opens) :
    secMap (a ≫ b) U = (secMap b U) ∘ₗ (secMap a U) := rfl

/-- The sections of an intersection are the intersection of the sections. -/
lemma secs_inf {L : X.Modules} (N N' : L.Submodule) (U : X.Opens) :
    secs (N ⊓ N') U = secs N U ⊓ secs N' U := rfl

/-- The sections of a submodule are the image of the sections of its inclusion. -/
lemma secs_eq_range {L : X.Modules} (N : L.Submodule) (U : X.Opens) :
    secs N U = LinearMap.range (secMap (subι N) U) :=
  (range_submodule_ι_app N U).symm

/-- The sections of `𝓘 ^ n M` over an affine open. -/
lemma secs_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (hM : M.IsQuasicoherent) (U : X.affineOpens) :
    secs (Stacks.Algebraization.idealPowerMultiple I n M) U.1 =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) :=
  have := hM
  Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine I n M U

/-- Over an affine open the sectionwise image of a morphism of quasi-coherent modules is the image
of its sections. -/
lemma imageSubmodule_obj_affine {M N : X.Modules} (q : M ⟶ N) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (U : X.affineOpens) :
    secs (imageSubmodule q) U.1 = LinearMap.range (secMap q U.1) := by
  have := hM
  have := hN
  have hqc : ((imageSubmodule q).toSheafOfModules : X.Modules).IsQuasicoherent :=
    isQuasicoherent_imageSubmodule q
  have hfac : ∀ x : Γ(M, U.1), secMap q U.1 x = ((secMap (toImageSubmodule q) U.1) x).1 :=
    fun x => (congrArg (fun k : M ⟶ N => secMap k U.1 x) (toImageSubmodule_comp_subι q)).symm
  refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨x, hx⟩ := Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen
      (toImageSubmodule q) U ⟨s, hs⟩
    refine ⟨x, ?_⟩
    have hx' : (secMap (toImageSubmodule q) U.1) x = ⟨s, hs⟩ := hx
    rw [hfac x, hx']
  · obtain ⟨x, rfl⟩ := hs
    rw [hfac x]
    exact ((secMap (toImageSubmodule q) U.1) x).2

/-- The sectionwise image of the inclusion of a submodule is that submodule. -/
lemma imageSubmodule_subι {L : X.Modules} (N : L.Submodule) : imageSubmodule (subι N) = N := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
  obtain ⟨W, rfl⟩ : ∃ W₀ : X.Opens, op W₀ = W := ⟨W.unop, rfl⟩
  have h : secs (imageSubmodule (subι N)) W = secs N W :=
    (imageSubmodule_obj (subι N) (mono_subι N) W).trans (secs_eq_range N W).symm
  exact h

/-! ### The ideal-power multiple of a submodule -/

/-- The submodule `𝓘 ^ n N` of `L`, for a submodule `N` of an `𝒪_X`-module `L`. -/
def idealPowerSub (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule) :
    L.Submodule :=
  imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I n
    (N.toSheafOfModules : X.Modules)) ≫ subι N)

/-- `𝓘 ^ n N` is a submodule of `N`. -/
lemma idealPowerSub_le (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule) :
    idealPowerSub I n N ≤ N :=
  (imageSubmodule_comp_le _ (subι N)).trans (le_of_eq (imageSubmodule_subι N))

/-- The range of the sections of `𝓘 ^ n M ⟶ L` over an affine open is `𝓘(U) ^ n` times that
of `j`. -/
private lemma range_secMap_subι_comp_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ)
    {M L : X.Modules} (j : M ⟶ L) (hM : M.IsQuasicoherent) (U : X.affineOpens) :
    LinearMap.range (secMap (subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ j) U.1) =
      I.ideal U ^ n • LinearMap.range (secMap j U.1) :=
  ((congrArg (fun t => LinearMap.range t)
        (secMap_comp (subι (Stacks.Algebraization.idealPowerMultiple I n M)) j U.1)).trans
      (LinearMap.range_comp _ _)).trans
    ((congrArg (Submodule.map (secMap j U.1))
        ((secs_eq_range (Stacks.Algebraization.idealPowerMultiple I n M) U.1).symm.trans
          (secs_idealPowerMultiple I n M hM U))).trans
      ((Submodule.map_smul'' _ _ _).trans
        (congrArg (fun t : Submodule Γ(X, U.1) Γ(L, U.1) => I.ideal U ^ n • t)
          (Submodule.map_top _))))

/-- The sections over an affine open of the image under `j` of `𝓘 ^ n M` are
`𝓘(U) ^ n j(M(U))`. -/
lemma secs_imageSubmodule_idealPowerMultiple_comp (I : X.IdealSheafData) (n : ℕ)
    {M L : X.Modules} (j : M ⟶ L) (hj : Mono j) (hM : M.IsQuasicoherent) (U : X.affineOpens) :
    secs (imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ j)) U.1 =
      I.ideal U ^ n • LinearMap.range (secMap j U.1) :=
  (imageSubmodule_subι_comp_obj j hj _ U.1).trans
    (range_secMap_subι_comp_idealPowerMultiple I n j hM U)

/-- The sections of `𝓘 ^ n N` over an affine open are `𝓘(U) ^ n N(U)`. -/
lemma idealPowerSub_obj_affine (I : X.IdealSheafData) (n : ℕ) {L : X.Modules} (N : L.Submodule)
    (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent) (U : X.affineOpens) :
    secs (idealPowerSub I n N) U.1 = I.ideal U ^ n • secs N U.1 :=
  (secs_imageSubmodule_idealPowerMultiple_comp I n (subι N) (mono_subι N) hN U).trans
    (congrArg (fun t : Submodule Γ(X, U.1) Γ(L, U.1) => I.ideal U ^ n • t)
      (secs_eq_range N U.1).symm)

/-- `𝓘 ^ n M` decreases as `n` grows. -/
lemma idealPowerMultiple_antitone (I : X.IdealSheafData) (M : X.Modules) {m n : ℕ} (h : m ≤ n) :
    Stacks.Algebraization.idealPowerMultiple I n M ≤
      Stacks.Algebraization.idealPowerMultiple I m M :=
  (Stacks.Algebraization.idealPowerMultiple_le_iff I n M _).2 fun U =>
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right h)).trans
      ((Stacks.Algebraization.idealPowerMultiple_le_iff I m M _).1 le_rfl U)

/-- `𝓘 ^ n N` decreases as `n` grows. -/
lemma idealPowerSub_antitone (I : X.IdealSheafData) {L : X.Modules} (N : L.Submodule) {m n : ℕ}
    (h : m ≤ n) : idealPowerSub I n N ≤ idealPowerSub I m N :=
  imageSubmodule_subι_comp_mono (subι N) (idealPowerMultiple_antitone I _ h)

/-! ### Artin-Rees as a containment of submodules -/

/-- **Artin-Rees for a coherent sheaf**, as a containment of submodules of `L`: one constant `c`
works for all `n ≥ c`. -/
lemma exists_idealPowerSub_artinRees [IsNoetherian X] (I : X.IdealSheafData) (L : X.Modules)
    (hL : L.IsCoherent) (N : L.Submodule)
    (hN : (N.toSheafOfModules : X.Modules).IsQuasicoherent) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      Stacks.Algebraization.idealPowerMultiple I n L ⊓ N ≤ idealPowerSub I (n - c) N := by
  have := hL
  have := hN
  have hLq : L.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).1
  have : (Stacks.Algebraization.kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom)).toSheafOfModules.IsQuasicoherent :=
    Stacks.Algebraization.idealKernel_isQuasicoherent I
  obtain ⟨c₀, hc₀⟩ := exists_ideal_pow_smul_inf_eq L N
    (Stacks.Algebraization.kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
      I.subschemeι.toRingCatSheafHom))
  refine ⟨c₀ + 1, Nat.succ_pos c₀, fun n hn => ?_⟩
  refine Stacks.Algebraization.submodule_le_of_affine _ _ fun U => ?_
  have hid : (show Ideal Γ(X, U.1) from (Stacks.Algebraization.kernelSubmodule
      (SheafOfModules.unitToPushforwardObjUnit
        I.subschemeι.toRingCatSheafHom)).toSubmodule.obj (op U.1)) = I.ideal U :=
    Stacks.Algebraization.kernelSubmodule_obj_affine I U
  have heq := hc₀ n (by omega) U
  rw [hid] at heq
  have heq' : I.ideal U ^ (n - c₀) •
        (I.ideal U ^ c₀ • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) ⊓ secs N U.1) =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) ⊓ secs N U.1 := heq
  have h1 : secs (Stacks.Algebraization.idealPowerMultiple I n L ⊓ N) U.1 =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) ⊓ secs N U.1 := by
    rw [secs_inf, secs_idealPowerMultiple I n L hLq U]
  have h2 : I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(L, U.1)) ⊓ secs N U.1 ≤
      I.ideal U ^ (n - (c₀ + 1)) • secs N U.1 := by
    rw [← heq']
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right
  exact h1.le.trans (h2.trans (idealPowerSub_obj_affine I (n - (c₀ + 1)) N hN U).ge)

/-! ### Ideal powers along an epimorphism -/

/-- An epimorphism of quasi-coherent modules carries `𝓘 ^ n` of its source onto `𝓘 ^ n` of its
target. -/
lemma imageSubmodule_idealPowerMultiple_of_epi (I : X.IdealSheafData) (m : ℕ)
    {Z H : X.Modules} (hZ : Z.IsQuasicoherent) (hH : H.IsQuasicoherent) (π : Z ⟶ H)
    (hπ : Epi π) :
    imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I m Z) ≫ π) =
      Stacks.Algebraization.idealPowerMultiple I m H := by
  have := hZ
  have := hH
  have := hπ
  have hZm : ((Stacks.Algebraization.idealPowerMultiple I m Z).toSheafOfModules :
      X.Modules).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I m Z
  have key : ∀ U : X.affineOpens,
      secs (imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I m Z) ≫ π)) U.1 =
        secs (Stacks.Algebraization.idealPowerMultiple I m H) U.1 := by
    intro U
    have hsurj : Function.Surjective (secMap π U.1) :=
      Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen π U
    exact (imageSubmodule_obj_affine _ hZm hH U).trans
      ((range_secMap_subι_comp_idealPowerMultiple I m π hZ U).trans
        ((congrArg (fun t : Submodule Γ(X, U.1) Γ(H, U.1) => I.ideal U ^ m • t)
            (LinearMap.range_eq_top.2 hsurj)).trans
          (secs_idealPowerMultiple I m H hH U).symm))
  exact le_antisymm (Stacks.Algebraization.submodule_le_of_affine _ _ fun U => (key U).le)
    (Stacks.Algebraization.submodule_le_of_affine _ _ fun U => (key U).ge)

/-! ### Monomorphisms detected on affine opens -/

/-- A morphism of modules on a scheme injective on the sections over every affine open is a
monomorphism: the sections it kills vanish on an affine cover, and vanishing is local. -/
lemma mono_of_injective_app_affine {A B : X.Modules} (f : A ⟶ B)
    (hf : ∀ U : X.affineOpens, Function.Injective (secMap f U.1)) : Mono f := by
  have hinj : ∀ W : X.Opens, Function.Injective (secMap f W) := by
    intro W a b hab
    have hz : secMap f W (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h0 : (a - b) ∈ (Stacks.Algebraization.kernelSubmodule f).toSubmodule.obj (op W) :=
      (mem_kernelSubmodule_iff f W (a - b)).2 hz
    have hmem : (a - b) ∈
        (Stacks.Algebraization.kernelSubmodule (𝟙 A)).toSubmodule.obj (op W) := by
      refine Stacks.Algebraization.mem_submodule_of_affine _ W (a - b) fun V i => ?_
      have hV := val_map_mem_submodule (Stacks.Algebraization.kernelSubmodule f) i.op h0
      have hV' : secMap f V.1 (A.val.map i.op (a - b)) = 0 :=
        (mem_kernelSubmodule_iff f V.1 _).1 hV
      exact (mem_kernelSubmodule_iff (𝟙 A) V.1 _).2
        (hf V (hV'.trans (map_zero (secMap f V.1)).symm))
    exact sub_eq_zero.1 ((mem_kernelSubmodule_iff (𝟙 A) W (a - b)).1 hmem)
  exact ⟨fun a b hab => by
    refine SheafOfModules.hom_ext (PresheafOfModules.Hom.ext (funext fun W => ?_))
    refine ModuleCat.Hom.ext (LinearMap.ext fun x => ?_)
    exact hinj W.unop (congrArg (fun k => (k.val.app W).hom x) hab)⟩

/-! ### Sections of the inclusion between submodules -/

/-- The inclusion between comparable submodules is a monomorphism. -/
lemma mono_subHom {L : X.Modules} {N M : L.Submodule} (h : N ≤ M) : Mono (subHom h) :=
  mono_of_mono_fac (homOfLE_comp_subι h)

/-- A section of `M` lies in the image of the inclusion of `N` exactly when it lies in `N`. -/
lemma mem_range_subHom_app {L : X.Modules} {N M : L.Submodule} (h : N ≤ M) (U : X.Opens)
    (z : Γ((M.toSheafOfModules : X.Modules), U)) :
    z ∈ LinearMap.range (secMap (subHom h) U) ↔ z.1 ∈ secs N U :=
  ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hz => ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩⟩

/-- A section of `M` dies in `M / N` exactly when it lies in `N`. -/
lemma subqπ_app_eq_zero_iff {L : X.Modules} (N M : L.Submodule) (h : N ≤ M) (U : X.Opens)
    (z : Γ((M.toSheafOfModules : X.Modules), U)) :
    secMap (subqπ N M h) U z = 0 ↔ z.1 ∈ secs N U := by
  have himg : secs (imageSubmodule (subHom h)) U = LinearMap.range (secMap (subHom h) U) :=
    imageSubmodule_obj (subHom h) (mono_subHom h) U
  have hker : secMap (subqπ N M h) U z = 0 ↔ z ∈ secs (imageSubmodule (subHom h)) U :=
    (mem_kernelSubmodule_iff (cokernel.π (C := X.Modules) (subHom h)) U z).symm
  rw [hker, himg]
  exact mem_range_subHom_app h U z

/-! ### Monomorphisms between subquotients -/

/-- The map `M / N ⟶ M' / N'` is a monomorphism when `N` is cut out of `M` by `N'`. -/
lemma mono_subqMap {L : X.Modules} {N M N' M' : L.Submodule} (h : N ≤ M) (h' : N' ≤ M')
    (hM : M ≤ M') (hN : N ≤ N')
    (hqM : (M.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hqN : (N.toSheafOfModules : X.Modules).IsQuasicoherent)
    (hinf : M ⊓ N' ≤ N) :
    Mono (subqMap h h' hM hN) := by
  have := hqM
  have := hqN
  have hsq : (subq N M h).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (subHom h)
  have hepi : Epi (subqπ N M h) := epi_subqπ N M h
  refine mono_of_injective_app_affine _ fun U => ?_
  intro a b hab
  refine sub_eq_zero.1 ?_
  have h0 : secMap (subqMap h h' hM hN) U.1 (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hsurj : Function.Surjective (secMap (subqπ N M h) U.1) :=
    @Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen X
      (M.toSheafOfModules : X.Modules) (subq N M h) hqM hsq (subqπ N M h) hepi U
  obtain ⟨x, hx'⟩ := hsurj (a - b)
  have hco : secMap (subqπ N M h ≫ subqMap h h' hM hN) U.1 x =
      secMap (subHom hM ≫ subqπ N' M' h') U.1 x :=
    congrArg (fun k : (M.toSheafOfModules : X.Modules) ⟶ subq N' M' h' => secMap k U.1 x)
      (subqπ_comp_subqMap h h' hM hN)
  have hstep : secMap (subqπ N' M' h') U.1 (secMap (subHom hM) U.1 x) = 0 := by
    rw [← show secMap (subHom hM ≫ subqπ N' M' h') U.1 x =
        secMap (subqπ N' M' h') U.1 (secMap (subHom hM) U.1 x) from rfl, ← hco,
      show secMap (subqπ N M h ≫ subqMap h h' hM hN) U.1 x =
        secMap (subqMap h h' hM hN) U.1 (secMap (subqπ N M h) U.1 x) from rfl, hx']
    exact h0
  rw [subqπ_app_eq_zero_iff N' M' h'] at hstep
  rw [← hx', subqπ_app_eq_zero_iff N M h]
  exact PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp hinf) (op U.1)
    ⟨x.2, hstep⟩

end AlgebraicGeometry

end
