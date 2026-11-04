module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import StacksFrontier.Homology.Perfect.Defs

@[expose] public section

/-!
# Perfect modules, finite projective resolutions and flat base change

Let `R` be a commutative ring. An `R`-module is perfect, in the sense of
`StacksDraft.Perfect.IsPerfectModule`, exactly when it admits a finite resolution by finite
projective `R`-modules. This characterization is then used to show that extension of scalars
along a flat homomorphism of commutative rings sends perfect modules to perfect modules.

## Main results

* `StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution`: an `R`-module is
  perfect if and only if it has a finite resolution by finite projective `R`-modules
  ([stacks 066Q]).
* `StacksDraft.Perfect.isPerfectModule_tensorProduct_of_flat`: flat base change preserves perfect
  modules ([stacks 066X]).

## Implementation notes

A resolution `0 → F_d → ⋯ → F_0 → M → 0` is recorded as a `ModuleResolution`, that is an
augmented chain complex resolving `M`, whose terms above degree `d` are zero; exactness of the
augmented complex then includes the injectivity of its leftmost displayed differential.

The base-changed module is written as `B ⊗[A] M`, using the standard left scalar-extension
convention; it is canonically isomorphic to the Stacks Project's `M ⊗_A B`.

## References

* [Stacks Project, Tag 066Q](https://stacks.math.columbia.edu/tag/066Q)
* [Stacks Project, Tag 066X](https://stacks.math.columbia.edu/tag/066X)
-/

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

-- Several proofs below rewrite through `let`-bound complexes and augmentations; unification has
-- to unfold those definitions, so reducible-transparency `isDefEq` is disabled in this file.
set_option backward.isDefEq.respectTransparency false

/-- If a cochain complex `P` is exact in degree `i + 1`, then
`0 → Z^i(P) → P^i → Z^{i+1}(P) → 0` is a short exact sequence. -/
private theorem shortExact_cycles_of_exactAt
    {C : Type*} [Category* C] [Abelian C]
    (P : CochainComplex C ℤ) (i : ℤ) (h : P.ExactAt (i + 1)) :
    (ShortComplex.mk (P.iCycles i) (P.toCycles i (i + 1)) (by
      rw [← cancel_mono (P.iCycles (i + 1)), Category.assoc,
        HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])).ShortExact where
  exact := by
    refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
      (fun {W} k hk => P.liftCycles' k (i + 1) (by simp) ?_) ?_ ?_)
    · rw [← HomologicalComplex.toCycles_i (K := P) (i := i) (j := i + 1),
        ← Category.assoc, hk, zero_comp]
    · intro W k hk
      simp
    · intro W k hk m hm
      rw [← cancel_mono (P.iCycles i)]
      simpa using hm
  mono_f := inferInstance
  epi_g := Preadditive.epi_of_isZero_cokernel' _
    (P.homologyIsCokernel (i := i) (j := i + 1) (by simp)) h.isZero_homology

/-- Let `P` be a cochain complex of `R`-modules vanishing strictly above degree `b`, whose terms
in degrees `≥ k` are projective and which is exact in degrees `> k`. If `P^k` is moreover a
finite module, then the module of `k`-cycles of `P` is finite and projective: descending
induction splits off one projective term at a time. -/
private theorem finite_projective_cycles_of_boundedAbove
    {R : Type u} [Ring R] (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (k b : ℤ) [P.IsStrictlyLE b] [Module.Finite R (P.X k)]
    (hprojective : ∀ i, k ≤ i → Module.Projective R (P.X i))
    (hexact : ∀ i, k < i → P.ExactAt i) :
    Module.Finite R (P.cycles k) ∧ Module.Projective R (P.cycles k) := by
  have h : ∀ (n : ℕ) (i : ℤ), k ≤ i → b < i + n →
      Module.Projective R (P.cycles i) := by
    intro n
    induction n with
    | zero =>
      intro i hi hb
      have hz : IsZero (P.cycles i) :=
        IsZero.of_mono (P.iCycles i) (P.isZero_of_isStrictlyLE b i (by simpa using hb))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact Module.Projective.of_free
    | succ n ih =>
      intro i hi hb
      have := ih (i + 1) (by omega) (by push_cast at hb ⊢; omega)
      let s := (shortExact_cycles_of_exactAt P i (hexact (i + 1) (by omega))).splittingOfProjective
      have := hprojective i hi
      exact Module.Projective.of_split (P.iCycles i).hom s.r.hom
        (ModuleCat.hom_ext_iff.mp s.f_r)
  have := h (b - k).toNat (k + 1) (by omega) (by omega)
  let s := (shortExact_cycles_of_exactAt P k (hexact (k + 1) (by omega))).splittingOfProjective
  have hsplit : s.r.hom.comp (P.iCycles k).hom = LinearMap.id :=
    ModuleCat.hom_ext_iff.mp s.f_r
  have := hprojective k le_rfl
  exact ⟨Module.Finite.of_surjective s.r.hom
      (fun x => ⟨(P.iCycles k).hom x, LinearMap.congr_fun hsplit x⟩),
    Module.Projective.of_split (P.iCycles k).hom s.r.hom hsplit⟩

/-- A chain complex of `R`-modules which is exact in every positive degree and whose degree-zero
homology is identified with `M` underlies a resolution of `M`. -/
private theorem exists_resolution_of_homology
    {R : Type u} [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (e : C.homology 0 ≅ ModuleCat.of R M)
    (hexact : ∀ n : ℕ, C.ExactAt (n + 1)) :
    ∃ F : ModuleResolution R M, F.complex = C := by
  let q := C.isoHomologyι₀.symm ≪≫ e
  let α : C.X 0 ⟶ ModuleCat.of R M := C.pOpcycles 0 ≫ q.hom
  have hα : C.d 1 0 ≫ α = 0 := by simp [α]
  let π := (C.toSingle₀Equiv (ModuleCat.of R M)).symm ⟨α, hα⟩
  have hπ : QuasiIso π := by
    refine ⟨fun n => ?_⟩
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)]
      show (ShortComplex.mk (C.d 1 0) α hα).Exact ∧ Epi α
      refine ⟨?_, inferInstance⟩
      let S := ShortComplex.mk (C.d 1 0) (C.pOpcycles 0) (C.d_pOpcycles 1 0)
      let T := ShortComplex.mk (C.d 1 0) α hα
      let f : S ⟶ T := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := q.hom }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp
        (ShortComplex.exact_of_g_is_cokernel S (C.opcyclesIsCokernel 1 0 (by simp)))
    | succ n =>
      exact (quasiIsoAt_iff_exactAt' π (n + 1)
        (ChainComplex.exactAt_succ_single_obj (ModuleCat.of R M) n)).mpr (hexact n)
  exact ⟨⟨C, fun _ => inferInstance, π, hπ⟩, rfl⟩

/-- A resolution of `M` by finite projective modules which vanishes above degree `d` witnesses
that `M` is perfect: extend it to a cochain complex supported in degrees `[-d, 0]`. -/
private theorem resolution_isPerfectModule
    {R : Type u} [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (d : ℕ) (F : ModuleResolution R M)
    (hF : ∀ i : ℕ, Module.Finite R (F.complex.X i) ∧ Module.Projective R (F.complex.X i))
    (hzero : ∀ i : ℕ, d < i → IsZero (F.complex.X i)) :
    IsPerfectModule (R := R) M := by
  let P := F.complex.extend ComplexShape.embeddingDownNat
  have : QuasiIso F.π := F.quasiIso
  have : Subsingleton ↑(HomologicalComplex.extend.X F.complex none) :=
    ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
  refine ⟨P, -(d : ℤ), 0, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    show IsZero (HomologicalComplex.extend.X F.complex
      (ComplexShape.embeddingDownNat.r i))
    cases hn : ComplexShape.embeddingDownNat.r i with
    | some n =>
      apply hzero n
      have hf := ComplexShape.Embedding.f_eq_of_r_eq_some _ hn
      change -(n : ℤ) = i at hf
      omega
    | none => exact isZero_zero _
  · intro i
    show Module.Finite R ↑(HomologicalComplex.extend.X F.complex
      (ComplexShape.embeddingDownNat.r i))
    cases ComplexShape.embeddingDownNat.r i with
    | some n => exact (hF n).1
    | none => exact Module.Finite.of_finite
  · intro i
    show Module.Projective R ↑(HomologicalComplex.extend.X F.complex
      (ComplexShape.embeddingDownNat.r i))
    cases ComplexShape.embeddingDownNat.r i with
    | some n => exact (hF n).2
    | none => exact Module.Projective.of_free
  · let singleIso := HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat (ModuleCat.of R M) 0 0 rfl
    let q := HomologicalComplex.extendMap F.π ComplexShape.embeddingDownNat ≫ singleIso.hom
    have hq : QuasiIso q := by
      dsimp [q]
      infer_instance
    exact ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app
      (ModuleCat.of R M) ≪≫ (asIso (DerivedCategory.Q.map q)).symm⟩

/-- **Stacks 066Q.** An `R`-module is perfect if and only if it has a finite resolution by finite
projective `R`-modules. -/
@[stacks 066Q]
theorem isPerfectModule_iff_exists_finite_projective_resolution
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    IsPerfectModule (R := R) M ↔
      ∃ (d : ℕ) (F : ModuleResolution R M),
        (∀ i : ℕ, Module.Finite R (F.complex.X i) ∧ Module.Projective R (F.complex.X i)) ∧
          ∀ i : ℕ, d < i → IsZero (F.complex.X i) := by
  constructor
  · rintro ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩
    let H (i : ℤ) : P.homology i ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M)) :=
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app P).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm
    have hexact : ∀ i : ℤ, i ≠ 0 → P.ExactAt i := by
      intro i hi
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      apply IsZero.of_iso _ (H i)
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    have := hfinite 0
    obtain ⟨hfin0, hproj0⟩ := finite_projective_cycles_of_boundedAbove P 0 b
      (fun i _ => hprojective i) (fun i hi => hexact i (by omega))
    let emb := ComplexShape.embeddingUpIntLE 0
    let C := P.truncLE' emb
    let E (n : ℕ) : C.homology n ≅ P.homology (-(n : ℤ)) := by
      have : QuasiIsoAt (P.ιTruncLE 0) (-(n : ℤ)) :=
        P.quasiIsoAt_ιTruncLE 0 (-(n : ℤ)) (by omega)
      exact (C.extendHomologyIso emb (j := n) (by simp [emb])).symm ≪≫
        (HomologicalComplex.homologyFunctor _ _ (-(n : ℤ))).mapIso
          (P.truncLEIso emb).symm ≪≫
        asIso (HomologicalComplex.homologyMap (P.ιTruncLE 0) (-(n : ℤ)))
    let e0 : C.homology 0 ≅ ModuleCat.of R M :=
      E 0 ≪≫ H 0 ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).app
          (ModuleCat.of R M)
    obtain ⟨F, hF⟩ := exists_resolution_of_homology M C e0 (fun n => by
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact IsZero.of_iso (hexact (-((n + 1 : ℕ) : ℤ)) (by omega)).isZero_homology
        (E (n + 1)))
    have hiso {X Y : ModuleCat.{v} R} (e : X ≅ Y) [Module.Finite R Y] [Module.Projective R Y] :
        Module.Finite R X ∧ Module.Projective R X :=
      ⟨Module.Finite.equiv e.toLinearEquiv.symm, Module.Projective.of_equiv e.toLinearEquiv.symm⟩
    refine ⟨(-a).toNat, F, ?_, ?_⟩
    · intro n
      rw [hF]
      cases n with
      | zero =>
        have := hfin0
        have := hproj0
        let eC : C.X 0 ≅ P.cycles 0 := P.truncLE'XIsoCycles emb (by simp [emb])
          (by simp [emb, ComplexShape.boundaryLE_embeddingUpIntLE_iff])
        exact hiso eC
      | succ n =>
        let eC : C.X (n + 1) ≅ P.X (-((n + 1 : ℕ) : ℤ)) :=
          P.truncLE'XIso emb (by simp [emb])
            (by simp [emb, ComplexShape.boundaryLE_embeddingUpIntLE_iff])
        have := hfinite (-((n + 1 : ℕ) : ℤ))
        have := hprojective (-((n + 1 : ℕ) : ℤ))
        exact hiso eC
    · intro n hn
      rw [hF]
      let eC : C.X n ≅ P.X (-(n : ℤ)) := P.truncLE'XIso emb (by simp [emb])
        (by simpa [emb, ComplexShape.boundaryLE_embeddingUpIntLE_iff] using (by omega : n ≠ 0))
      exact IsZero.of_iso (P.isZero_of_isStrictlyGE a (-(n : ℤ)) (by omega)) eC
  · rintro ⟨d, F, hF, hzero⟩
    exact resolution_isPerfectModule M d F hF hzero

/-- **Stacks 066X.** Flat base change preserves perfect modules. -/
@[stacks 066X]
theorem isPerfectModule_tensorProduct_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Flat A B]
    (hM : IsPerfectModule (R := A) M) :
    IsPerfectModule (R := B) (B ⊗[A] M) := by
  let G : ModuleCat.{w} A ⥤ ModuleCat.{max v w} B :=
    { obj := fun X => ModuleCat.of B (B ⊗[A] X)
      map := fun f => ModuleCat.ofHom (f.hom.baseChange B)
      map_id := fun X => ModuleCat.hom_ext (LinearMap.baseChange_id)
      map_comp := fun f g => ModuleCat.hom_ext (LinearMap.baseChange_comp _ _) }
  have : G.Additive := ⟨fun {X Y f g} => ModuleCat.hom_ext (LinearMap.baseChange_add _ _)⟩
  have : G.PreservesHomology := (Functor.exact_tfae G).out 2 3 |>.mp (by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    show Function.Exact (LinearMap.baseChange B S.f.hom) (LinearMap.baseChange B S.g.hom)
    simpa only [LinearMap.baseChange_eq_ltensor] using Module.Flat.lTensor_exact B hS)
  obtain ⟨d, F, hFP, hzero⟩ :=
    (isPerfectModule_iff_exists_finite_projective_resolution M).mp hM
  apply (isPerfectModule_iff_exists_finite_projective_resolution (B ⊗[A] M)).mpr
  have (i : ℕ) : F.complex.HasHomology i := F.hasHomology i
  have : QuasiIso F.π := F.quasiIso
  let e := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).app
    (ModuleCat.of A M)
  let π := (G.mapHomologicalComplex (ComplexShape.down ℕ)).map F.π ≫ e.hom
  let F' : ModuleResolution B (B ⊗[A] M) :=
    { complex := (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj F.complex
      hasHomology := fun i => inferInstance
      π := π
      quasiIso := inferInstance }
  refine ⟨d, F', ?_, ?_⟩
  · intro i
    obtain ⟨_, _⟩ := hFP i
    exact ⟨inferInstanceAs (Module.Finite B (B ⊗[A] F.complex.X i)),
      inferInstanceAs (Module.Projective B (B ⊗[A] F.complex.X i))⟩
  · exact fun i hi => G.map_isZero (hzero i hi)

end StacksDraft.Perfect
