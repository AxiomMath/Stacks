module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness and directed colimits

Let `{R_i, φ_{ii'}}` be a system of commutative rings over a directed set `I`, and let
`R = colim_i R_i` be its direct limit.

1. If `M` is an `R`-module which is flat as an `R_i`-module for every `i`, via the
   structure map `R_i → R`, then `M` is flat as an `R`-module.
2. For each `i` let `M_i` be a flat `R_i`-module, and for `i ≤ i'` let
   `f_{ii'} : M_i → M_{i'}` be a `φ_{ii'}`-semilinear map with `f_{ii} = id` and
   `f_{i'i''} ∘ f_{ii'} = f_{ii''}`. Then `M = colim_i M_i` is a flat `R`-module.

Over a fixed commutative ring, a directed colimit of flat modules is flat, and a directed
colimit of faithfully flat algebras is faithfully flat.

## Main definitions

* `StacksColimitRingsFlat.ColimitRing`: the colimit ring `colim_i R_i`.
* `StacksColimitRingsFlat.ColimitModule`: the colimit `colim_i M_i` of a semilinear system of
  modules, as the `R`-module `colim_i (R ⊗_{R_i} M_i)`.

## Main results

* `StacksColimitRingsFlat.flat_of_forall_flat`: part (1).
* `StacksColimitRingsFlat.colimitModule_flat`: part (2).
* `StacksColimitRingsFlat.flat_directLimit`, `directLimit_flat` and `colimit_flat_of_flat`:
  over a fixed commutative ring, a directed colimit of flat modules is flat.
* `StacksColimitRingsFlat.colimitStructMap_comp`: the cocone maps into `ColimitModule` are
  compatible with the transition maps.
* `faithfullyFlat_directLimit_of_faithfullyFlat`: a directed colimit of faithfully flat
  `R`-algebras is faithfully flat over `R`.
* `directLimit_map_injective`: a map of direct limits induced by injective component maps is
  injective.
-/

@[expose] public section

namespace StacksColimitRingsFlat

/-! ### A directed colimit of flat modules over a fixed ring -/

/-- If `g i : G i →ₗ[R] G' i` are injective and commute with the transition maps of two
directed systems (the target system being a `DirectedSystem`), then the induced map
`Module.DirectLimit.map g hg` on the colimits is injective. -/
private theorem flat_directLimit.map_inj_aux
    {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] [DecidableEq ι] [Nonempty ι]
    [IsDirectedOrder ι]
    {G : ι → Type*} [(i : ι) → AddCommMonoid (G i)] [(i : ι) → Module R (G i)]
    {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j}
    {G' : ι → Type*} [(i : ι) → AddCommMonoid (G' i)] [(i : ι) → Module R (G' i)]
    {f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j}
    [DirectedSystem G' (fun i j h => (f' i j h : G' i → G' j))]
    (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hinj : ∀ i, Function.Injective (g i)) :
    Function.Injective (Module.DirectLimit.map g hg) := by
  intro z w hzw
  obtain ⟨i, x, y, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [Module.DirectLimit.map_apply_of, Module.DirectLimit.map_apply_of] at hzw
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq hzw
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hg i j hij] at hj
  rw [← Module.DirectLimit.of_f (hij := hij), ← Module.DirectLimit.of_f (hij := hij) (x := y),
    hinj j hj]

/-- Tensoring a directed system by a fixed module `M` yields a directed system, with transition
maps `LinearMap.lTensor M (f i j h)`. -/
private theorem flat_directLimit.lTensor_directedSystem
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    {G : ι → Type*} [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [hds : DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (M : Type*) [AddCommGroup M] [Module R M] :
    DirectedSystem (fun i => TensorProduct R M (G i))
      (fun i j h => (LinearMap.lTensor M (f i j h) :
        TensorProduct R M (G i) → TensorProduct R M (G j))) := by
  constructor
  · intro i x
    have hid : f i i le_rfl = LinearMap.id := by ext y; exact hds.map_self y
    simp [hid]
  · intro k j i hij hjk x
    have hcomp : f j k hjk ∘ₗ f i j hij = f i k (le_trans hij hjk) := by
      ext y; exact hds.map_map hij hjk y
    change (LinearMap.lTensor M (f j k hjk)) ((LinearMap.lTensor M (f i j hij)) x)
        = (LinearMap.lTensor M (f i k (le_trans hij hjk))) x
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp]

/-- **Engine lemma.** Over a fixed commutative ring `R`, a `Module.DirectLimit` of a
directed system `{Gᵢ}` of flat `R`-modules is flat.

By `Module.Flat.iff_rTensor_injective` it suffices to show that for every finitely
generated ideal `𝔞 ⊆ R`, the canonical map `𝔞 ⊗_R (colim Gᵢ) → colim Gᵢ`,
i.e. `LinearMap.rTensor (colim Gᵢ) 𝔞.subtype`, is injective. Tensoring with the
fixed module `𝔞` commutes with the directed colimit: by `TensorProduct.directLimitRight`
there is an `R`-linear iso `𝔞 ⊗_R (colim Gᵢ) ≃ colim (𝔞 ⊗_R Gᵢ)`, and likewise
`R ⊗_R (colim Gᵢ) ≃ colim (R ⊗_R Gᵢ)`, under which `rTensor (colim Gᵢ) 𝔞.subtype`
becomes `Module.DirectLimit.map` of the stagewise maps `rTensor Gᵢ 𝔞.subtype`
(naturality of `lTensor`/`rTensor` w.r.t. the transition maps). Each stagewise map
`𝔞 ⊗_R Gᵢ → R ⊗_R Gᵢ` is injective because `Gᵢ` is `R`-flat
(`Module.Flat.iff_rTensor_injective`/`lTensor_injective`). A directed colimit of
injective maps is injective: if `Module.DirectLimit.map g _ z = 0` with `z` coming
from stage `i` (via `Module.DirectLimit.exists_of`, using `[Nonempty ι]` and the
directedness), then `g i (z.preimage)` dies in the colimit `colim (R ⊗ Gᵢ)`, hence
by `DirectLimit.exists_eq_zero` (Stacks 00D7) it is killed by some transition map to a
stage `j ≥ i`; commuting `g` past that transition (naturality) and using injectivity
of `g i` and of the transition on `𝔞 ⊗ Gᵢ` forces the preimage to already be `0` at
stage `i`, so `z = 0`. Therefore `rTensor (colim Gᵢ) 𝔞.subtype` is injective. -/
@[ega "0 6.1.2",
  ega "0 6.2.3" "constant ring system",
  sga "3 V 4.1.2" "partial",
  sga "4 V 1.2" "special case",
  sga "4 VI 8.6.4" "special case",
  sga "4 XVII 5.5.1.2" "partial"]
theorem flat_directLimit
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [DecidableEq ι]
    (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (hf : ∀ i, Module.Flat R (G i)) :
    Module.Flat R (Module.DirectLimit G f) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  set LI := TensorProduct.directLimitRight f (I : Submodule R R) with hLI
  set LR := TensorProduct.directLimitRight f R with hLR
  have := flat_directLimit.lTensor_directedSystem f (I : Submodule R R)
  have := flat_directLimit.lTensor_directedSystem f R
  set g : (i : ι) → TensorProduct R (I : Submodule R R) (G i) →ₗ[R] TensorProduct R R (G i) :=
    fun i ↦ LinearMap.rTensor (G i) (Submodule.subtype I) with hg_def
  have hgnat : ∀ (i j : ι) (h : i ≤ j),
      g j ∘ₗ (LinearMap.lTensor (I : Submodule R R) (f i j h))
        = (LinearMap.lTensor R (f i j h)) ∘ₗ g i := by
    intro i j h
    rw [hg_def, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hginj : ∀ i, Function.Injective (g i) := fun i ↦
    Module.Flat.iff_rTensor_injective.mp (hf i) hI
  have hkey : (LR : _ →ₗ[R] _) ∘ₗ
      (LinearMap.rTensor (Module.DirectLimit G f) (Submodule.subtype I))
      = (Module.DirectLimit.map g hgnat) ∘ₗ (LI : _ →ₗ[R] _) := by
    apply TensorProduct.ext'
    intro a z
    induction z using Module.DirectLimit.induction_on with
    | _ i x =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, LinearEquiv.coe_coe]
      rw [hLR, TensorProduct.directLimitRight_tmul_of, hLI, TensorProduct.directLimitRight_tmul_of,
        Module.DirectLimit.map_apply_of, hg_def]
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
  have hfac : (LinearMap.rTensor (Module.DirectLimit G f) (Submodule.subtype I))
      = (LR.symm : _ →ₗ[R] _) ∘ₗ (Module.DirectLimit.map g hgnat) ∘ₗ (LI : _ →ₗ[R] _) := by
    rw [← hkey]
    ext w
    simp
  rw [hfac]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact LR.symm.injective.comp ((flat_directLimit.map_inj_aux g hgnat hginj).comp LI.injective)

/-! ### The colimit ring and its structure maps -/

variable {ι : Type*} [Preorder ι]
variable (G : ι → Type*) [(i : ι) → CommRing (G i)]
variable (φ : (i j : ι) → i ≤ j → G i →+* G j)

/-- The colimit ring `R = colim_i R_i`, as a `Ring.DirectLimit` (Stacks 00D6). -/
@[ega "0 1.4.5" "more general"]
abbrev ColimitRing : Type _ := Ring.DirectLimit G (fun i j h => (φ i j h : G i → G j))

/-- The structure ring homomorphism `R_i → R`. -/
noncomputable abbrev structHom (i : ι) : G i →+* ColimitRing G φ :=
  Ring.DirectLimit.of G (fun i j h => (φ i j h : G i → G j)) i

/-- Each `R_i` is canonically an algebra over `R` via the structure map `R_i → R`. -/
noncomputable instance algebraColimit (i : ι) : Algebra (G i) (ColimitRing G φ) :=
  (structHom G φ i).toAlgebra

/-- The structure maps are compatible with the transition maps:
`(R_j → R) ∘ φ_{ij} = (R_i → R)`. -/
theorem algebraMap_structHom_comp (i j : ι) (h : i ≤ j) (a : G i) :
    algebraMap (G j) (ColimitRing G φ) (φ i j h a)
      = algebraMap (G i) (ColimitRing G φ) a :=
  Ring.DirectLimit.of_f h a

/-! ### Flatness over every `R_i` implies flatness over the colimit ring -/

/-- If `M` is an `R`-module that is flat as an `R_i`-module for every
`i` (via the structure map `R_i → R`), then `M` is flat as an `R`-module. -/
@[stacks 05UU "(1)", ega "0 6.2.3" "special case"]
theorem flat_of_forall_flat
    [Nonempty ι] [IsDirected ι (· ≤ ·)] [DirectedSystem G (fun i j h => (φ i j h : G i → G j))]
    (M : Type*) [AddCommGroup M] [Module (ColimitRing G φ) M]
    (hflat : ∀ i : ι, @Module.Flat (G i) M _ _ (Module.compHom M (structHom G φ i))) :
    Module.Flat (ColimitRing G φ) M := by
  classical
  rw [Module.Flat.iff_forall_exists_factorization]
  intro l f₀ x hx
  have hlift : ∀ j : Fin l, ∃ i : ι, ∃ c : G i, structHom G φ i c = f₀ j := fun j ↦
    Ring.DirectLimit.exists_of (f₀ j)
  choose iidx cval hcval using hlift
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image iidx)
  have hile : ∀ j : Fin l, iidx j ≤ i := fun j ↦
    hi (iidx j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  set fi : Fin l →₀ G i :=
    Finsupp.equivFunOnFinite.symm (fun j ↦ φ (iidx j) i (hile j) (cval j)) with hfi_def
  have hfi_apply : ∀ j, fi j = φ (iidx j) i (hile j) (cval j) := by
    intro j; rw [hfi_def]; simp
  have hfi_struct : ∀ j, structHom G φ i (fi j) = f₀ j := by
    intro j
    rw [hfi_apply j, show structHom G φ i (φ (iidx j) i (hile j) (cval j))
          = structHom G φ (iidx j) (cval j) from
        algebraMap_structHom_comp G φ (iidx j) i (hile j) (cval j)]
    exact hcval j
  let inst_i : Module (G i) M := Module.compHom M (structHom G φ i)
  have hsmul_i : ∀ (c : G i) (m : M), c • m = structHom G φ i c • m := fun _ _ ↦ rfl
  let x' : (Fin l →₀ G i) →ₗ[G i] M :=
    Finsupp.linearCombination (G i) (fun j ↦ x (Finsupp.single j 1))
  have hxsum_i : ∀ c : Fin l →₀ G i,
      x' c = ∑ j : Fin l, (c j) • (x (Finsupp.single j 1)) := by
    intro c
    change (Finsupp.linearCombination (G i) (fun j ↦ x (Finsupp.single j 1))) c = _
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro j; simp
  have hx'fi : x' fi = 0 := by
    rw [hxsum_i fi]
    have : ∀ j : Fin l, (fi j) • (x (Finsupp.single j 1))
        = (f₀ j) • (x (Finsupp.single j 1)) := by
      intro j; rw [hsmul_i, hfi_struct j]
    rw [Finset.sum_congr rfl (fun j _ ↦ this j)]
    have hxeq :
        x = Finsupp.linearCombination (ColimitRing G φ) (fun j ↦ x (Finsupp.single j 1)) := by
      ext j; simp [Finsupp.linearCombination_single]
    have hR : x f₀ = ∑ j : Fin l, f₀ j • x (Finsupp.single j 1) := by
      conv_lhs => rw [hxeq]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro j; simp
    rw [← hR, hx]
  obtain ⟨k, a', y', hfac, ha'⟩ :=
    Module.Flat.iff_forall_exists_factorization.mp (hflat i) hx'fi
  set up : (Fin l →₀ G i) → (Fin l →₀ ColimitRing G φ) :=
    fun c ↦ c.mapRange (structHom G φ i) (map_zero _) with hup_def
  set upk : (Fin k →₀ G i) → (Fin k →₀ ColimitRing G φ) :=
    fun d ↦ d.mapRange (structHom G φ i) (map_zero _) with hupk_def
  set a : (Fin l →₀ ColimitRing G φ) →ₗ[ColimitRing G φ] (Fin k →₀ ColimitRing G φ) :=
    Finsupp.linearCombination (ColimitRing G φ)
      (fun j ↦ upk (a' (Finsupp.single j 1))) with ha_def
  set y : (Fin k →₀ ColimitRing G φ) →ₗ[ColimitRing G φ] M :=
    Finsupp.linearCombination (ColimitRing G φ)
      (fun t ↦ y' (Finsupp.single t 1)) with hy_def
  have hsmul_up : ∀ (b : G i) (c : Fin l →₀ G i),
      up (b • c) = structHom G φ i b • up c := by
    intro b c
    ext j
    simp only [hup_def, Finsupp.mapRange_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  have hsmul_upk : ∀ (b : G i) (d : Fin k →₀ G i),
      upk (b • d) = structHom G φ i b • upk d := by
    intro b d
    ext t
    simp only [hupk_def, Finsupp.mapRange_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  have ha_mapRange : ∀ c : Fin l →₀ G i, a (up c) = upk (a' c) := by
    have hsingle : ∀ (j : Fin l) (b : G i),
        a (up (Finsupp.single j b)) = upk (a' (Finsupp.single j b)) := by
      intro j b
      have hup_single : up (Finsupp.single j b) = Finsupp.single j (structHom G φ i b) := by
        simp [hup_def, Finsupp.mapRange_single]
      have ha_single : a (Finsupp.single j (structHom G φ i b))
          = structHom G φ i b • upk (a' (Finsupp.single j 1)) := by
        rw [ha_def, Finsupp.linearCombination_single]
      have ha'_single : a' (Finsupp.single j b) = b • a' (Finsupp.single j 1) := by
        rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hup_single, ha_single, ha'_single, hsmul_upk]
    intro c
    induction c using Finsupp.induction with
    | zero => simp [hup_def, hupk_def, ha_def]
    | single_add j b c hjc hb hind =>
      have hup_add : up (Finsupp.single j b + c) = up (Finsupp.single j b) + up c := by
        simp only [hup_def]
        exact Finsupp.mapRange_add (map_add _) _ _
      rw [hup_add, map_add, map_add, hind, hsingle]
      simp only [hupk_def]
      exact (Finsupp.mapRange_add (map_add _) _ _).symm
  have hy_mapRange : ∀ d : Fin k →₀ G i, y (upk d) = y' d := by
    have hsingle : ∀ (t : Fin k) (b : G i),
        y (upk (Finsupp.single t b)) = y' (Finsupp.single t b) := by
      intro t b
      have hupk_single : upk (Finsupp.single t b) = Finsupp.single t (structHom G φ i b) := by
        simp [hupk_def, Finsupp.mapRange_single]
      have hy_single : y (Finsupp.single t (structHom G φ i b))
          = structHom G φ i b • y' (Finsupp.single t 1) := by
        rw [hy_def, Finsupp.linearCombination_single]
      have hy'_single : y' (Finsupp.single t b) = b • y' (Finsupp.single t 1) := by
        rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hupk_single, hy_single, hy'_single, hsmul_i]
    intro d
    induction d using Finsupp.induction with
    | zero => simp [hupk_def, hy_def]
    | single_add t b d htd hb hind =>
      have hupk_add : upk (Finsupp.single t b + d) = upk (Finsupp.single t b) + upk d := by
        simp only [hupk_def]
        exact Finsupp.mapRange_add (map_add _) _ _
      rw [hupk_add, map_add, map_add, hind, hsingle]
  have hup_fi : up fi = f₀ := by
    ext j
    simp only [hup_def, Finsupp.mapRange_apply]
    exact hfi_struct j
  refine ⟨k, a, y, ?_, ?_⟩
  · refine Finsupp.lhom_ext' fun j ↦ LinearMap.ext fun r ↦ ?_
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    have hsingle_up : (Finsupp.single j r : Fin l →₀ ColimitRing G φ)
        = r • up (Finsupp.single j 1) := by
      rw [hup_def]
      simp [Finsupp.mapRange_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle_up, map_smul, map_smul, ha_mapRange, map_smul, hy_mapRange]
    congr 1
    have hup1 : up (Finsupp.single j 1) = Finsupp.single j 1 := by
      rw [hup_def]; simp [Finsupp.mapRange_single]
    rw [hup1]
    have hx'1 : x' (Finsupp.single j 1) = x (Finsupp.single j 1) := by
      change (Finsupp.linearCombination (G i) (fun j ↦ x (Finsupp.single j 1)))
          (Finsupp.single j 1) = x (Finsupp.single j 1)
      rw [Finsupp.linearCombination_single, one_smul]
    have hfac1 : x' (Finsupp.single j 1) = y' (a' (Finsupp.single j 1)) := by
      rw [hfac]; rfl
    rw [← hfac1, hx'1]
  · rw [← hup_fi, ha_mapRange, ha']
    simp [hupk_def]

/-! ### The colimit of a semilinear system of modules -/

section ColimitModule

variable {G φ}
variable (M : ι → Type*) [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module (G i) (M i)]
variable (f : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[φ i j h] M j)

/-- For `i ≤ j`, the `R_i`-linear map `x ↦ 1 ⊗ f(x) : M_i → R ⊗_{R_j} M_j`. -/
noncomputable def baseChangeStep (i j : ι) (h : i ≤ j) :
    M i →ₗ[G i] TensorProduct (G j) (ColimitRing G φ) (M j) where
  toFun x := 1 ⊗ₜ[G j] f i j h x
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' a x := by
    simp only [map_smulₛₗ, RingHom.id_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one, algebraMap_structHom_comp]

/-- The `R`-linear base-change transition map `R ⊗_{R_i} M_i → R ⊗_{R_j} M_j`. -/
noncomputable def baseChangeMap (i j : ι) (h : i ≤ j) :
    TensorProduct (G i) (ColimitRing G φ) (M i) →ₗ[ColimitRing G φ]
      TensorProduct (G j) (ColimitRing G φ) (M j) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r ↦ r • baseChangeStep M f i j h
      map_add' := fun r s ↦ by ext x; simp [add_smul]
      map_smul' := fun r s ↦ by ext x; simp [smul_smul] }

/-- The base-changed system of `R`-modules: `N i = R ⊗_{R_i} M_i`. -/
abbrev baseChangedModule (i : ι) : Type _ :=
  TensorProduct (G i) (ColimitRing G φ) (M i)

/-- The colimit `R`-module `M = colim_i M_i`, realized as the direct limit
(Stacks 00D6) of the base-changed system `R ⊗_{R_i} M_i`. -/
@[ega "0 6.2.3"]
noncomputable abbrev ColimitModule [DecidableEq ι] : Type _ :=
  Module.DirectLimit (R := ColimitRing G φ) (baseChangedModule M) (baseChangeMap M f)

/-- The canonical embedding of `M_i` into the base change `R ⊗_{R_i} M_i`,
`x ↦ 1 ⊗ x`; this is `φ_i`-semilinear (along the structure map `R_i → R`). -/
noncomputable def baseChangeUnit (i : ι) :
    M i →ₛₗ[structHom G φ i] TensorProduct (G i) (ColimitRing G φ) (M i) where
  toFun x := 1 ⊗ₜ[G i] x
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' a x := by
    change (1 : ColimitRing G φ) ⊗ₜ[G i] (a • x)
        = (structHom G φ i) a • (1 : ColimitRing G φ) ⊗ₜ[G i] x
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, mul_one, Algebra.smul_def, mul_one]
    rfl

/-- The colimit cocone structure map `M_i → M = colim_i M_i`, `φ_i`-semilinear
along the structure map `R_i → R`. It is the composite `M_i → R ⊗_{R_i} M_i → M`. -/
@[ega "0 6.2.3"]
noncomputable def colimitStructMap [DecidableEq ι] (i : ι) :
    M i →ₛₗ[structHom G φ i] ColimitModule M f :=
  (Module.DirectLimit.of (ColimitRing G φ) ι (fun i ↦ TensorProduct (G i) (ColimitRing G φ) (M i))
    (baseChangeMap M f) i).comp (baseChangeUnit M i)

/-- Computation of `baseChangeMap` on a simple tensor `1 ⊗ₜ x`. -/
theorem baseChangeMap_one_tmul (i j : ι) (h : i ≤ j) (x : M i) :
    baseChangeMap M f i j h (1 ⊗ₜ[G i] x) = 1 ⊗ₜ[G j] f i j h x := by
  unfold baseChangeMap
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul]
  rfl

/-- The cocone structure maps are compatible with the transition maps of the system:
`g_j ∘ f_{ij} = g_i`. -/
theorem colimitStructMap_comp [DecidableEq ι] (i j : ι) (h : i ≤ j) (x : M i) :
    colimitStructMap M f j (f i j h x) = colimitStructMap M f i x := by
  unfold colimitStructMap
  simp only [LinearMap.coe_comp, Function.comp_apply]
  change Module.DirectLimit.of (ColimitRing G φ) ι _ (baseChangeMap M f) j (1 ⊗ₜ[G j] f i j h x)
      = Module.DirectLimit.of (ColimitRing G φ) ι _ (baseChangeMap M f) i (1 ⊗ₜ[G i] x)
  rw [← baseChangeMap_one_tmul M f i j h x]
  exact Module.DirectLimit.of_f (f := baseChangeMap M f) (hij := h)

/-- Each base-changed module `R ⊗_{R_i} M_i` is flat over `R = ColimitRing G φ`,
being the base change of the flat `R_i`-module `M_i`. -/
theorem baseChangedModule_flat (hflat : ∀ i : ι, Module.Flat (G i) (M i)) (i : ι) :
    Module.Flat (ColimitRing G φ) (TensorProduct (G i) (ColimitRing G φ) (M i)) := by
  have := hflat i
  exact Module.Flat.baseChange (G i) (ColimitRing G φ) (M i)

/-- The base-change transition maps `baseChangeMap M f` form a `DirectedSystem`:
`baseChangeMap M f i i le_rfl = id` and the composition law holds. -/
theorem baseChangeMap_directedSystem
    (hf_id : ∀ (i : ι) (x : M i), f i i le_rfl x = x)
    (hf_comp : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : M i),
      f j k hjk (f i j hij x) = f i k (hij.trans hjk) x) :
    DirectedSystem (baseChangedModule M)
      (fun i j h => (baseChangeMap M f i j h : baseChangedModule M i → baseChangedModule M j)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i x
    have hmap : baseChangeMap M f i i le_rfl = LinearMap.id := by
      apply LinearMap.ext
      intro t
      apply TensorProduct.induction_on (motive := fun t ↦
          baseChangeMap M f i i le_rfl t = LinearMap.id t)
      · simp
      · intro r y
        have hrx : r ⊗ₜ[G i] y = r • (1 : ColimitRing G φ) ⊗ₜ[G i] y := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change baseChangeMap M f i i le_rfl (r ⊗ₜ[G i] y) = r ⊗ₜ[G i] y
        rw [hrx, map_smul, baseChangeMap_one_tmul, hf_id]
      · intro a b ha hb
        rw [map_add, map_add, ha, hb]
    exact LinearMap.congr_fun hmap x
  · intro i j k hij hjk x
    have hmap : (baseChangeMap M f j i hjk).comp (baseChangeMap M f k j hij)
        = baseChangeMap M f k i (hij.trans hjk) := by
      apply LinearMap.ext
      intro t
      apply TensorProduct.induction_on (motive := fun t ↦
          (baseChangeMap M f j i hjk).comp (baseChangeMap M f k j hij) t
            = baseChangeMap M f k i (hij.trans hjk) t)
      · simp
      · intro r y
        have hrx : r ⊗ₜ[G k] y = r • (1 : ColimitRing G φ) ⊗ₜ[G k] y := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change (baseChangeMap M f j i hjk) ((baseChangeMap M f k j hij) (r ⊗ₜ[G k] y))
            = (baseChangeMap M f k i (hij.trans hjk)) (r ⊗ₜ[G k] y)
        rw [hrx, map_smul, map_smul, map_smul, baseChangeMap_one_tmul,
            baseChangeMap_one_tmul, baseChangeMap_one_tmul, hf_comp]
      · intro a b ha hb
        rw [map_add, map_add, ha, hb]
    exact LinearMap.congr_fun hmap x

end ColimitModule

/-- If each `M_i` is a flat `R_i`-module and the `f_{ii'}` are a
compatible system of `φ_{ii'}`-semilinear maps, then the colimit
`M = colim_i M_i` is a flat `R`-module. -/
@[stacks 05UU "(2)", ega "0 6.1.2" "more general", ega "0 6.2.3", sga "4 VI 8.6.4" "special case"]
theorem colimitModule_flat
    [Nonempty ι] [IsDirected ι (· ≤ ·)] [DecidableEq ι]
    [DirectedSystem G (fun i j h => (φ i j h : G i → G j))]
    (M : ι → Type*) [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module (G i) (M i)]
    (hflat : ∀ i : ι, Module.Flat (G i) (M i))
    (f : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[φ i j h] M j)
    (hf_id : ∀ (i : ι) (x : M i), f i i le_rfl x = x)
    (hf_comp : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : M i),
      f j k hjk (f i j hij x) = f i k (hij.trans hjk) x) :
    Module.Flat (ColimitRing G φ) (ColimitModule M f) := by
  have := baseChangeMap_directedSystem M f hf_id hf_comp
  exact flat_directLimit (R := ColimitRing G φ) (baseChangedModule M) (baseChangeMap M f)
    (baseChangedModule_flat M hflat)

end StacksColimitRingsFlat


/-! ### A colimit of faithfully flat algebras is faithfully flat -/

@[expose] public section

/-- The `rTensor` of a directed system is again a directed system. -/
private theorem rTensor_directedSystem {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    {G : ι → Type*} [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (N : Type*) [AddCommGroup N] [Module R N] :
    DirectedSystem (fun x => TensorProduct R (G x) N)
      (fun i j h => (LinearMap.rTensor N (f i j h))) := by
  refine ⟨?_, ?_⟩
  · intro i x
    have hid : f i i (le_refl i) = LinearMap.id := by
      ext y
      exact DirectedSystem.map_self (f := fun i j h ↦ (f i j h : G i → G j)) y
    change LinearMap.rTensor N (f i i (le_refl i)) x = x
    rw [hid, LinearMap.rTensor_id]
    rfl
  · intro k j i hij hjk x
    have hmm : f j k hjk ∘ₗ f i j hij = f i k (le_trans hij hjk) := by
      ext y
      exact DirectedSystem.map_map (f := fun i j h ↦ (f i j h : G i → G j)) hij hjk y
    change LinearMap.rTensor N (f j k hjk) (LinearMap.rTensor N (f i j hij) x)
        = LinearMap.rTensor N (f i k (le_trans hij hjk)) x
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hmm]

open scoped Classical in
/-- A directed colimit of flat `R`-modules is flat.

Write `M = colim_i G_i`. By the flatness criterion
`Module.Flat.iff_rTensor_injectiveₛ` it suffices to show that for every `R`-module `P`
and submodule `N ⊆ P` the map `N ⊗ M → P ⊗ M` induced by `N.subtype` is injective.

Tensoring commutes with directed colimits, so `TensorProduct.directLimitRight` gives
`R`-linear isomorphisms `N ⊗ M ≃ colim_i (N ⊗ G_i)` and `P ⊗ M ≃ colim_i (P ⊗ G_i)`.
Under them the map in question is conjugate to `Module.DirectLimit.map` of the
componentwise maps `N ⊗ G_i → P ⊗ G_i`: this is naturality of `directLimitRight` in the
second tensor factor, and on a pure tensor `n ⊗ of_i y` both sides return
`of_i (N.subtype n ⊗ y)`.

Each component is injective because `G_i` is flat, and componentwise injectivity
propagates to the colimit map: an element of the source colimit comes from some stage,
and if two such have equal images then their images agree already at a later stage,
where injectivity at that stage applies. Conjugating back gives the claim. -/
@[ega "0 6.1.2",
  ega "0 6.2.3" "constant ring system",
  sga "3 V 4.1.2" "partial",
  sga "4 V 1.2" "special case",
  sga "4 VI 8.6.4" "special case",
  sga "4 XVII 5.5.1.2" "partial"]
theorem directLimit_flat
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [DecidableEq ι]
    {G : ι → Type*} [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (hflat : ∀ i, Module.Flat R (G i)) :
    Module.Flat R (Module.DirectLimit G f) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ N
  set eN := TensorProduct.directLimitRight f (N : Type _) with heN
  set eP := TensorProduct.directLimitRight f P with heP
  set g : (i : ι) → TensorProduct R N (G i) →ₗ[R] TensorProduct R P (G i) :=
    fun i ↦ LinearMap.rTensor (G i) N.subtype with hg
  have hgc : ∀ (i j : ι) (h : i ≤ j),
      g j ∘ₗ LinearMap.lTensor (N : Type _) (f i j h)
        = LinearMap.lTensor P (f i j h) ∘ₗ g i := by
    intro i j h
    ext x y
    simp [hg]
  have hds : DirectedSystem (fun i ↦ TensorProduct R P (G i))
      (fun i j h ↦ LinearMap.lTensor P (f i j h)) := inferInstance
  have hinj : ∀ i, Function.Injective (g i) := fun i ↦
    Module.Flat.rTensor_preserves_injective_linearMap (M := G i) N.subtype N.injective_subtype
  have heq : LinearMap.rTensor (Module.DirectLimit G f) N.subtype
      = (eP.symm.toLinearMap ∘ₗ (Module.DirectLimit.map g hgc).comp eN.toLinearMap) := by
    apply TensorProduct.ext'
    intro n x
    induction x using Module.DirectLimit.induction_on with
    | _ i y =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
      rw [heN, TensorProduct.directLimitRight_tmul_of, Module.DirectLimit.map_apply_of, heP,
        show g i (n ⊗ₜ y) = (N.subtype n) ⊗ₜ y from by simp [hg],
        ← TensorProduct.directLimitRight_tmul_of f P (N.subtype n) y]
      simp
  rw [heq]
  exact eP.symm.injective.comp
    ((StacksColimitRingsFlat.flat_directLimit.map_inj_aux g hgc hinj).comp eN.injective)

open scoped Classical in
/-- A directed colimit of faithfully flat `R`-algebras is faithfully flat over `R`: if each
`R → Sᵢ` is faithfully flat and the transition maps are `R`-algebra maps, then the induced
map from `R` to `colim Sᵢ` is faithfully flat. -/
@[stacks 090N, sga "3 VIB 11.17.1" "constant base"]
theorem faithfullyFlat_directLimit_of_faithfullyFlat
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : Type*) [CommRing R]
    (S : ι → Type*) [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
    (φ : (i j : ι) → i ≤ j → S i →+* S j)
    [DirectedSystem S (fun i j h => φ i j h)]
    -- transition maps are R-algebra maps:
    (hφ : ∀ i j (h : i ≤ j), (φ i j h).comp (algebraMap R (S i)) = algebraMap R (S j))
    -- each Sᵢ is faithfully flat over R:
    (hff : ∀ i, (algebraMap R (S i)).FaithfullyFlat) :
    ((Ring.DirectLimit.of S (fun i j h => φ i j h) (Classical.arbitrary ι)).comp
      (algebraMap R (S (Classical.arbitrary ι)))).FaithfullyFlat := by
  classical
  set f : (i j : ι) → i ≤ j → S i → S j := fun i j h ↦ φ i j h with hf
  set T := Ring.DirectLimit S f with hT
  set i₀ := Classical.arbitrary ι with hi₀
  set σ : R →+* T := (Ring.DirectLimit.of S f i₀).comp (algebraMap R (S i₀)) with hσ
  set ψ : (i j : ι) → i ≤ j → S i →ₗ[R] S j := fun i j h ↦
    { toFun := φ i j h
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        exact congrArg (· * φ i j h x) (RingHom.congr_fun (hφ i j h) r) } with hψ
  let instMod : Module R T := σ.toModule
  have key_of : ∀ (i : ι) (r : R), (Ring.DirectLimit.of S f i) (algebraMap R (S i) r) = σ r := by
    have step : ∀ (i j : ι) (h : i ≤ j) (r : R),
        (Ring.DirectLimit.of S f j) (algebraMap R (S j) r)
          = (Ring.DirectLimit.of S f i) (algebraMap R (S i) r) := by
      intro i j h r
      have hfr : f i j h (algebraMap R (S i) r) = algebraMap R (S j) r := by
        simp only [hf]
        exact RingHom.congr_fun (hφ i j h) r
      calc (Ring.DirectLimit.of S f j) (algebraMap R (S j) r)
          = (Ring.DirectLimit.of S f j) (f i j h (algebraMap R (S i) r)) := by rw [hfr]
        _ = (Ring.DirectLimit.of S f i) (algebraMap R (S i) r) :=
            Ring.DirectLimit.of_f h (algebraMap R (S i) r)
    intro i r
    obtain ⟨k, hik, hi₀k⟩ := directed_of (· ≤ ·) i i₀
    rw [hσ, RingHom.comp_apply, ← step i k hik r, ← step i₀ k hi₀k r]
  set gφ : (i : ι) → S i →ₗ[R] T := fun i ↦
    { toFun := Ring.DirectLimit.of S f i
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, key_of i r]
        rfl } with hgφ
  have hcompat : ∀ (i j : ι) (h : i ≤ j) (x : S i), gφ j (ψ i j h x) = gφ i x := by
    intro i j h x
    simp only [hgφ, hψ, LinearMap.coe_mk, AddHom.coe_mk]
    change (Ring.DirectLimit.of S f j) (φ i j h x) = (Ring.DirectLimit.of S f i) x
    have : f i j h x = φ i j h x := by simp only [hf]
    rw [← this]
    exact Ring.DirectLimit.of_f h x
  set toT : Module.DirectLimit S ψ →ₗ[R] T :=
    Module.DirectLimit.lift R ι S ψ gφ hcompat with htoT
  have htoT_of : ∀ (i : ι) (x : S i),
      toT (Module.DirectLimit.of R ι S ψ i x) = Ring.DirectLimit.of S f i x := by
    intro i x
    rw [htoT, Module.DirectLimit.lift_of]
    rfl
  have hbij : Function.Bijective toT := by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      simp only [LinearMap.mem_ker] at hz
      obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
      rw [htoT_of i x] at hz
      obtain ⟨j, hij, hxj⟩ := Ring.DirectLimit.of.zero_exact (f' := φ) hz
      simp only [Submodule.mem_bot]
      have : Module.DirectLimit.of R ι S ψ i x
          = Module.DirectLimit.of R ι S ψ j (ψ i j hij x) := by
        rw [Module.DirectLimit.of_f]
      rw [this]
      have hψ0 : ψ i j hij x = 0 := by
        simp only [hψ, LinearMap.coe_mk, AddHom.coe_mk]
        exact hxj
      rw [hψ0, map_zero]
    · intro z
      obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
      exact ⟨Module.DirectLimit.of R ι S ψ i x, htoT_of i x⟩
  set e : Module.DirectLimit S ψ ≃ₗ[R] T := LinearEquiv.ofBijective toT hbij with he
  have hffM : ∀ i, Module.FaithfullyFlat R (S i) := fun i ↦
    RingHom.faithfullyFlat_algebraMap_iff.mp (hff i)
  have hflat_i : ∀ i, Module.Flat R (S i) := fun i ↦ (hffM i).toFlat
  have hM : Module.FaithfullyFlat R (Module.DirectLimit S ψ) := by
    rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
    refine ⟨directLimit_flat ψ hflat_i, fun I hI ↦ ?_⟩
    have psi_maps : ∀ (J : Ideal R) (i j : ι) (h : i ≤ j) (y : S i),
        y ∈ J • (⊤ : Submodule R (S i)) → ψ i j h y ∈ J • (⊤ : Submodule R (S j)) := by
      intro J i j h y hy
      have hmap : Submodule.map (ψ i j h) (J • (⊤ : Submodule R (S i)))
          ≤ J • (⊤ : Submodule R (S j)) := by
        rw [Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact hmap (Submodule.mem_map_of_mem hy)
    have lift_lemma : ∀ (J : Ideal R) (z : Module.DirectLimit S ψ),
        z ∈ J • (⊤ : Submodule R (Module.DirectLimit S ψ)) →
        ∃ (j : ι) (y : S j), Module.DirectLimit.of R ι S ψ j y = z ∧
          y ∈ J • (⊤ : Submodule R (S j)) := by
      intro J z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨j, x, rfl⟩ := Module.DirectLimit.exists_of n
        refine ⟨j, r • x, ?_, ?_⟩
        · rw [map_smul]
        · exact Submodule.smul_mem_smul hr Submodule.mem_top
      · rintro z₁ z₂ ⟨j₁, y₁, rfl, hy₁⟩ ⟨j₂, y₂, rfl, hy₂⟩
        obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j₁ j₂
        refine ⟨k, ψ j₁ k hk₁ y₁ + ψ j₂ k hk₂ y₂, ?_, ?_⟩
        · rw [map_add, Module.DirectLimit.of_f, Module.DirectLimit.of_f]
        · exact Submodule.add_mem _ (psi_maps J j₁ k hk₁ y₁ hy₁)
            (psi_maps J j₂ k hk₂ y₂ hy₂)
    intro hITop
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    have hmTop : m • (⊤ : Submodule R (Module.DirectLimit S ψ)) = ⊤ := by
      refine le_antisymm le_top ?_
      calc (⊤ : Submodule R (Module.DirectLimit S ψ)) = I • ⊤ := hITop.symm
        _ ≤ m • ⊤ := Submodule.smul_mono hIm le_rfl
    have h1mem : Module.DirectLimit.of R ι S ψ i₀ 1
        ∈ m • (⊤ : Submodule R (Module.DirectLimit S ψ)) := by
      rw [hmTop]; exact Submodule.mem_top
    obtain ⟨j, y, hjy, hymem⟩ := lift_lemma m _ h1mem
    obtain ⟨k, hjk, hi₀k⟩ := directed_of (· ≤ ·) j i₀
    have heq2 : Module.DirectLimit.of R ι S ψ k (ψ j k hjk y)
        = Module.DirectLimit.of R ι S ψ k (ψ i₀ k hi₀k 1) := by
      rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f, hjy]
    obtain ⟨k', hkk', hψeq⟩ := Module.DirectLimit.exists_eq_of_of_eq heq2
    have hLHS : ψ k k' hkk' (ψ j k hjk y) ∈ m • (⊤ : Submodule R (S k')) :=
      psi_maps m k k' hkk' _ (psi_maps m j k hjk y hymem)
    have hRHS1 : ψ k k' hkk' (ψ i₀ k hi₀k 1) = 1 := by
      simp only [hψ, LinearMap.coe_mk, AddHom.coe_mk, map_one]
    rw [hψeq, hRHS1] at hLHS
    have hcontra : m • (⊤ : Submodule R (S k')) = ⊤ := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at hLHS
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff]
      exact Ideal.eq_top_of_isUnit_mem _ hLHS isUnit_one
    exact (hffM k').submodule_ne_top hm hcontra
  change Module.FaithfullyFlat R T
  exact Module.FaithfullyFlat.of_linearEquiv R (Module.DirectLimit S ψ) e.symm

/-! ### A colimit of flat modules is flat -/

@[expose] public section

open Module

/-- A map of direct limits induced by injective component maps is injective. -/
theorem directLimit_map_injective
    {R : Type*} [Ring R]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {G : ι → Type*} [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    {f : (i j : ι) → i ≤ j → G i →ₗ[R] G j}
    {G' : ι → Type*} [(i : ι) → AddCommGroup (G' i)] [(i : ι) → Module R (G' i)]
    {f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j}
    [DirectedSystem G' (fun i j h => f' i j h)]
    (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hinj : ∀ i, Function.Injective (g i)) :
    Function.Injective (Module.DirectLimit.map g hg) := by
  exact StacksColimitRingsFlat.flat_directLimit.map_inj_aux g hg hinj

/-- Stacks 05UT: the direct limit (colimit) of a directed system of flat
$R$-modules is flat. -/
@[stacks 05UT,
  ega "0 6.1.2",
  ega "0 6.2.3" "constant ring system",
  ega "0 6.3.4" "partial",
  sga "3 V 4.1.2" "partial",
  sga "4 V 1.2" "special case",
  sga "4 VI 8.6.4" "special case",
  sga "4 XVII 5.5.1.2" "partial",
  sga "4 XVII 5.5.6.3" "partial"]
theorem colimit_flat_of_flat
    {R : Type*} [CommRing R]
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => f i j h)]
    [∀ i, Module.Flat R (G i)] :
    Module.Flat R (Module.DirectLimit G f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ p hp
  set e : TensorProduct R N (Module.DirectLimit G f) ≃ₗ[R]
      Module.DirectLimit (fun i ↦ TensorProduct R N (G i))
        (fun i j h ↦ LinearMap.lTensor N (f i j h)) :=
    TensorProduct.directLimitRight f N with he
  set e' : TensorProduct R N' (Module.DirectLimit G f) ≃ₗ[R]
      Module.DirectLimit (fun i ↦ TensorProduct R N' (G i))
        (fun i j h ↦ LinearMap.lTensor N' (f i j h)) :=
    TensorProduct.directLimitRight f N' with he'
  set g : (i : ι) → TensorProduct R N (G i) →ₗ[R] TensorProduct R N' (G i) :=
    fun i ↦ LinearMap.rTensor (G i) p with hgdef
  have hg : ∀ (i j : ι) (h : i ≤ j),
      g j ∘ₗ (LinearMap.lTensor N (f i j h)) =
        (LinearMap.lTensor N' (f i j h)) ∘ₗ g i := by
    intro i j h
    simp only [hgdef, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hginj : ∀ i, Function.Injective (g i) := fun _ ↦
    Module.Flat.rTensor_preserves_injective_linearMap p hp
  have hDinj : Function.Injective (Module.DirectLimit.map g hg) :=
    directLimit_map_injective g hg hginj
  have hsq : (LinearMap.rTensor (Module.DirectLimit G f) p) ∘ₗ (e.symm : _ →ₗ[R] _) =
      (e'.symm : _ →ₗ[R] _) ∘ₗ (Module.DirectLimit.map g hg) := by
    refine LinearMap.ext fun z ↦ Module.DirectLimit.induction_on z fun i nx ↦ ?_
    refine nx.induction_on ?_ (fun n x ↦ ?_) (fun a b ha hb ↦ ?_)
    · simp
    · have hgix : g i (n ⊗ₜ[R] x) = p n ⊗ₜ[R] x := by
        simp only [hgdef, LinearMap.rTensor_tmul]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, he',
        TensorProduct.directLimitRight_symm_of_tmul, LinearMap.rTensor_tmul,
        Module.DirectLimit.map_apply_of, hgix]
    · simp only [map_add, LinearMap.comp_apply] at *
      rw [ha, hb]
  have hcomp : Function.Injective
      ((LinearMap.rTensor (Module.DirectLimit G f) p) ∘ₗ (e.symm.toLinearMap)) := by
    rw [hsq]
    exact e'.symm.injective.comp hDinj
  intro a b hab
  refine e.injective (hcomp ?_)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply] using hab
