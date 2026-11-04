module

public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Generators.TensorGloballyGenerated
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 09NC: an ample invertible sheaf from globally generated affine nonvanishing loci

A quasi-compact scheme every point of which lies in an affine nonvanishing locus `X_s` of a
global section `s` of some *globally generated* invertible sheaf carries an ample invertible
sheaf ([Stacks, Tag 09NC]).

## Main results

* `Stacks.SheafOfModules.tensorSections`: the tensor product of two global sections.
* `Stacks.SheafOfModules.nonvanishingLocus_tensorSections`: `X_{s ⊗ t} = X_s ∩ X_t`.
* `Stacks.SheafOfModules.exists_generatingSection_nonvanishing`: a generating family of global
  sections of an invertible sheaf has, at every point, a member nonvanishing there.
* `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_globallyGenerated_affine_nonvanishing`:
  **Tag 09NC**.
* `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one`: **Tag 09ND**,
  which Tag 09NC discharges the hypothesis of.

## References

* [Stacks Project, Tag 09NC](https://stacks.math.columbia.edu/tag/09NC)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpStalk grpGerm)
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

section TensorSections

variable {X : RingedSpace.{u, u}}

/-- **The tensor product of two global sections.** Over every open it is the image of the
elementary tensor of the two restrictions under the canonical map from the presheaf tensor
product into the sheafified one. -/
noncomputable def tensorSections (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : F.sections) (t : G.sections) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G))).sections :=
  PresheafOfModules.sectionsMk
    (fun U => Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U
      (s.eval U ⊗ₜ[X.presheaf.obj U] t.eval U))
    (by
      intro U V f
      have hs := PresheafOfModules.sections_property s f
      have ht := PresheafOfModules.sections_property t f
      have h := PresheafOfModules.naturality_apply
        (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
          ((PresheafOfModules.tensorObj (O := (X).presheaf) (F.val) (G.val)))) f
        (s.eval U ⊗ₜ[X.presheaf.obj U] t.eval U)
      change Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G V
          (((F.val).restrictₛₗ (f)) (s.eval U)
            ⊗ₜ[X.presheaf.obj V]
            ((G.val).restrictₛₗ (f)) (t.eval U)) =
        ConcreteCategory.hom
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj
            G).val.map f)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U
            (s.eval U ⊗ₜ[X.presheaf.obj U] t.eval U)) at h
      change ((F.val).restrictₛₗ (f)) (s.eval U) = _ at hs
      change ((G.val).restrictₛₗ (f)) (t.eval U) = _ at ht
      rw [hs, ht] at h
      exact h.symm)

/-- Over an open `U`, `tensorSections F G s t` is the image of `s.eval U ⊗ t.eval U` in the
sheafified tensor product. -/
@[simp]
theorem tensorSections_eval (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : F.sections) (t : G.sections) (U : (Opens X.carrier)ᵒᵖ) :
    (tensorSections F G s t).eval U =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U
        (s.eval U ⊗ₜ[X.presheaf.obj U] t.eval U) := rfl

end TensorSections

section Algebra

/-- Over a field, an elementary tensor of two nonzero vectors is nonzero. -/
theorem tmul_ne_zero_of_ne_zero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[K] w ≠ (0 : V ⊗[K] W) := by
  classical
  let B := Module.Free.chooseBasis K V
  let C := Module.Free.chooseBasis K W
  have hB : B.repr v ≠ 0 := fun h => hv (B.repr.injective (by simpa using h))
  have hC : C.repr w ≠ 0 := fun h => hw (C.repr.injective (by simpa using h))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hB
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hC
  intro h
  have h' := congrArg ((TensorProduct.lid K K).toLinearMap.comp
    (TensorProduct.map (B.coord i) (C.coord j))) h
  exact (mul_ne_zero hi hj) (by simpa using h')

/-- The class of `m` in `(R ⧸ 𝔪) ⊗ M` is nonzero exactly when `m ∉ 𝔪 M`. -/
private theorem one_tmul_ne_zero_iff_notMem_maximalIdeal_smul_top {R M : Type*} [CommRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] (m : M) :
    ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] m ≠ 0) ↔
      m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  rw [ne_eq, ← LinearEquiv.map_eq_zero_iff
      (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)),
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- **An elementary tensor escapes `𝔪 (M ⊗ N)` exactly when both factors escape `𝔪 M` and
`𝔪 N`.** Reducing modulo the maximal ideal turns the tensor product over the local ring into a
tensor product over its residue field, where an elementary tensor vanishes only if one of its
factors does. -/
theorem tmul_notMem_maximalIdeal_smul_top_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsLocalRing R] (m : M) (n : N) :
    m ⊗ₜ[R] n ∉ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (M ⊗[R] N))) ↔
      m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ∧
      n ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) := by
  classical
  let I : Ideal R := IsLocalRing.maximalIdeal R
  let K : Type _ := R ⧸ I
  let P : Submodule R (M ⊗[R] N) := I • (⊤ : Submodule R (M ⊗[R] N))
  let _ : Field K := Ideal.Quotient.field I
  let e₁ : ((M ⊗[R] N) ⧸ P) ≃ₗ[R] K ⊗[R] (M ⊗[R] N) :=
    (TensorProduct.quotTensorEquivQuotSMul (M ⊗[R] N) I).symm
  let e₂ : K ⊗[R] (M ⊗[R] N) ≃ₗ[K] (K ⊗[R] M) ⊗[K] (K ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.distribBaseChange R K M N
  let e : ((M ⊗[R] N) ⧸ P) ≃ (K ⊗[R] M) ⊗[K] (K ⊗[R] N) := e₁.toEquiv.trans e₂.toEquiv
  have he : e (Submodule.Quotient.mk (m ⊗ₜ[R] n)) =
      ((1 : K) ⊗ₜ[R] m) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] n) := by
    show TensorProduct.AlgebraTensorModule.distribBaseChange R K M N
      (1 ⊗ₜ[R] (m ⊗ₜ[R] n)) = _
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  have hz : e (Submodule.Quotient.mk (m ⊗ₜ[R] n)) = (0 : (K ⊗[R] M) ⊗[K] (K ⊗[R] N)) ↔
      Submodule.Quotient.mk (m ⊗ₜ[R] n) = (0 : (M ⊗[R] N) ⧸ P) := by
    refine ⟨fun h => e.injective ?_, fun h => by simp [e, h]⟩
    show e (Submodule.Quotient.mk (m ⊗ₜ[R] n)) = e 0
    simpa [e] using h
  have hpure : (((1 : K) ⊗ₜ[R] m) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] n) ≠ 0) ↔
      ((1 : K) ⊗ₜ[R] m ≠ 0) ∧ ((1 : K) ⊗ₜ[R] n ≠ 0) :=
    ⟨fun h => ⟨fun hm => h (by simp [hm]), fun hn => h (by simp [hn])⟩,
      fun ⟨hm, hn⟩ => tmul_ne_zero_of_ne_zero hm hn⟩
  have hL : m ⊗ₜ[R] n ∉ P ↔ e (Submodule.Quotient.mk (m ⊗ₜ[R] n)) ≠ 0 :=
    (not_congr (Submodule.Quotient.mk_eq_zero P)).symm.trans (not_congr hz).symm
  rw [hL, he, hpure, one_tmul_ne_zero_iff_notMem_maximalIdeal_smul_top,
    one_tmul_ne_zero_iff_notMem_maximalIdeal_smul_top]

/-- If a family spans a module over a local ring and `𝔪 M ≠ M`, some member escapes `𝔪 M`. -/
theorem exists_notMem_maximalIdeal_smul_top_of_span_eq_top
    {R M I : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] (f : I → M)
    (hspan : Submodule.span R (Set.range f) = ⊤)
    (hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤) :
    ∃ i, f i ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  by_contra h
  push Not at h
  refine hproper (le_antisymm le_top ?_)
  simpa [hspan] using
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i :
      Set.range f ⊆ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) : Submodule R M))

/-- Membership in `𝔪 M` is transported along an equality of module structures. Stated with the
two module structures as parameters, so that `cases` discharges it; rewriting one instance in
place inside `𝔪 • ⊤` produces a type-incorrect motive, because the `IsScalarTower` field of the
scalar action on submodules depends on it. -/
theorem mem_maximalIdeal_smul_top_iff_of_module_eq
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    (m : M) (inst₁ inst₂ : Module R M) (h : inst₁ = inst₂) :
    (letI : Module R M := inst₁;
      m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) ↔
    (letI : Module R M := inst₂;
      m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) := by
  cases h
  rfl

/-- `𝔪 M = M` is transported along an equality of module structures. -/
theorem maximalIdeal_smul_top_eq_top_iff_of_module_eq
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    (inst₁ inst₂ : Module R M) (h : inst₁ = inst₂) :
    (letI : Module R M := inst₁;
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤) ↔
    (letI : Module R M := inst₂;
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤) := by
  cases h
  rfl

end Algebra

section Nonvanishing

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The nonvanishing locus of a tensor product of sections is the intersection of the two
nonvanishing loci**, `X_{s ⊗ t} = X_s ∩ X_t`. On stalks the germ of `s ⊗ t` is the elementary
tensor of the two germs (Tag 01CB), and an elementary tensor over a local ring escapes
`𝔪 (M ⊗ N)` exactly when both factors escape. -/
@[ega "0 5.5.3" "more general"]
theorem nonvanishingLocus_tensorSections
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (s : F.sections) (t : G.sections) :
    nonvanishingLocus ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G)))
      (tensorSections F G s t) =
      nonvanishingLocus F s ∩ nonvanishingLocus G t := by
  ext x
  -- `tensorStalkIso` states its source over `Tensor.ringSheaf`, which is not reducible, so
  -- instance search does not reach `stalkModule` there; name it, as that statement itself does.
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G).val x
  have hs : Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G
      (grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj
          G).val x ⊤ (Opens.mem_top x)
        ((tensorSections F G s t).eval (op ⊤))) =
      grpGerm X F.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) ⊗ₜ[ringStalk X x]
        grpGerm X G.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) := by
    rw [tensorSections_eval]
    exact Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ X x F G ⊤
      (Opens.mem_top x) (s.eval (op ⊤)) (t.eval (op ⊤))
  simp only [Set.mem_inter_iff, nonvanishingLocus, Set.mem_ofPred_eq]
  rw [← mem_smul_top_iff_of_linearEquiv (IsLocalRing.maximalIdeal (ringStalk X x))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G), hs]
  exact tmul_notMem_maximalIdeal_smul_top_iff _ _

/-- **The maximal ideal does not kill the stalk of an invertible sheaf.** There is a local
section whose germ escapes `𝔪_x L_x`. -/
theorem maximalIdeal_smul_top_ne_top_of_isInvertible
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (x : X.carrier) :
    IsLocalRing.maximalIdeal (ringStalk X x) •
      (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) ≠ ⊤ := by
  obtain ⟨W, hxW, a, ha⟩ := exists_notMem_maximalIdeal_smul_top_of_isInvertible L x
  exact fun h => ha (by simp [h])

end Nonvanishing

/-- **A generating family of global sections of an invertible sheaf has, at every point, a
member that does not vanish there.** The germs of the family span the stalk (Tag 01AN), and the
stalk is not killed by the maximal ideal because the sheaf is invertible, so not every germ can
lie in `𝔪_x L_x`. -/
theorem exists_generatingSection_nonvanishing {X : Scheme.{u}} (L : X.Modules)
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (g : L.GeneratingSections) (x : X) :
    ∃ i : g.I, x ∈ nonvanishingOpen (X := X.toRingedSpace) L (g.s i) := by
  classical
  have hproper := maximalIdeal_smul_top_ne_top_of_isInvertible
    (X := X.toRingedSpace) L x
  have hinst := stalkModule_eq (X := X.toRingedSpace) L.val x
  let _ : Module (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace L.val x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.toRingedSpace.presheaf) L.val x
  have hproper' : IsLocalRing.maximalIdeal (ringStalk X.toRingedSpace x) •
      (⊤ : Submodule (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace L.val x)) ≠ ⊤ :=
    fun h => hproper ((maximalIdeal_smul_top_eq_top_iff_of_module_eq
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val x) _
        hinst).mpr h)
  have hspanRaw := (AlgebraicGeometry.generates_iff_stalkwise_generates
    (structureSheafRing X.toRingedSpace) L g.s).mp g.epi x
  have hspan : Submodule.span (ringStalk X.toRingedSpace x)
      (Set.range fun i : g.I => grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x)
        ((g.s i).eval (op ⊤))) = ⊤ :=
    span_eq_top_of_ringEquiv _ _
      (SemilinearStalk.commStalkRingEquiv X.toRingedSpace.presheaf x)
      (AlgebraicGeometry.SheafOfModules.commStalk_smul_eq X.toRingedSpace.presheaf x L.val)
      _ hspanRaw
  obtain ⟨i, hi⟩ := exists_notMem_maximalIdeal_smul_top_of_span_eq_top _ hspan hproper'
  exact ⟨i, fun hmem => hi ((mem_maximalIdeal_smul_top_iff_of_module_eq
    (grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) ((g.s i).eval (op ⊤)))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val x) _ hinst).mp
      hmem)⟩

section FiniteTensor

variable {X : RingedSpace.{u, u}}

/-- The tensor product `L 0 ⊗ ⋯ ⊗ L n` of a finite family of sheaves of modules. -/
noncomputable def finiteTensor : (n : ℕ) →
    (L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing X)) →
    _root_.SheafOfModules.{u} (structureSheafRing X)
  | 0, L => L 0
  | n + 1, L => (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((L 0))).obj ((finiteTensor n (fun i => L i.succ))))

/-- The tensor product `s 0 ⊗ ⋯ ⊗ s n` of a finite family of global sections. -/
noncomputable def finiteTensorSection : (n : ℕ) →
    (L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing X)) →
    ((i : Fin (n + 1)) → (L i).sections) → (finiteTensor n L).sections
  | 0, _, s => s 0
  | n + 1, L, s => tensorSections (L 0) (finiteTensor n (fun i => L i.succ)) (s 0)
      (finiteTensorSection n (fun i => L i.succ) (fun i => s i.succ))

/-- A finite tensor product of invertible sheaves of modules is invertible. -/
theorem isInvertible_finiteTensor : (n : ℕ) →
    (L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing X)) →
    (∀ i, IsInvertible X.presheaf (structureSheafRing X).property (L i)) →
    IsInvertible X.presheaf (structureSheafRing X).property (finiteTensor n L)
  | 0, _, hL => hL 0
  | n + 1, L, hL =>
      have _h0 := hL 0
      have _ht := isInvertible_finiteTensor n (fun i => L i.succ) (fun i => hL i.succ)
      isInvertible_tensorSheaf X.presheaf (structureSheafRing X).property
        (L 0) (finiteTensor n (fun i => L i.succ))

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The nonvanishing locus of a finite tensor product of sections is the intersection of the
nonvanishing loci.** -/
@[ega "0 5.5.3" "more general", ega "II 4.6.13.1" "(ii)"]
theorem nonvanishingLocus_finiteTensorSection (n : ℕ) :
    ∀ (L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing X))
      (s : (i : Fin (n + 1)) → (L i).sections),
      nonvanishingLocus (finiteTensor n L) (finiteTensorSection n L s) =
        ⋂ i, nonvanishingLocus (L i) (s i) := by
  induction n with
  | zero =>
      intro L s
      ext x
      rw [Set.mem_iInter]
      exact ⟨fun h i => Fin.cases h (fun j => j.elim0) i, fun h => h 0⟩
  | succ n ih =>
      intro L s
      have h := ih (fun i => L i.succ) (fun i => s i.succ)
      show nonvanishingLocus
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (L 0)).obj
            (finiteTensor n fun i => L i.succ))
          (tensorSections (L 0) (finiteTensor n fun i => L i.succ) (s 0)
            (finiteTensorSection n (fun i => L i.succ) fun i => s i.succ)) = _
      rw [nonvanishingLocus_tensorSections, h]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_succ]

end FiniteTensor

/-- **Tag 01PV for a finite tensor product of sections.** An affine open meets the nonvanishing
locus of `s 0 ⊗ ⋯ ⊗ s n` in an affine open, by `n + 1` applications of Tag 01PV. -/
theorem isAffineOpen_inf_nonvanishingOpen_finiteTensor {X : Scheme.{u}} (n : ℕ) :
    ∀ (L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (hL : ∀ i, IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property (L i))
      (s : (i : Fin (n + 1)) → (L i).sections) (U : X.Opens), IsAffineOpen U →
      IsAffineOpen (U ⊓ @nonvanishingOpen X.toRingedSpace _ (finiteTensor n L)
        (isInvertible_finiteTensor n L hL) (finiteTensorSection n L s)) := by
  induction n with
  | zero =>
      intro L hL s U hU
      have := hL 0
      exact AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen (L 0) (s 0) U hU
  | succ n ih =>
      intro L hL s U hU
      have h0 := hL 0
      have hU' : IsAffineOpen (U ⊓ nonvanishingOpen (X := X.toRingedSpace) (L 0) (s 0)) :=
        AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen (L 0) (s 0) U hU
      have htail := ih (fun i => L i.succ) (fun i => hL i.succ) (fun i => s i.succ) _ hU'
      have hset : U ⊓ @nonvanishingOpen X.toRingedSpace _ (finiteTensor (n + 1) L)
            (isInvertible_finiteTensor (n + 1) L hL) (finiteTensorSection (n + 1) L s) =
          (U ⊓ nonvanishingOpen (X := X.toRingedSpace) (L 0) (s 0)) ⊓
            @nonvanishingOpen X.toRingedSpace _ (finiteTensor n (fun i => L i.succ))
              (isInvertible_finiteTensor n _ (fun i => hL i.succ))
              (finiteTensorSection n (fun i => L i.succ) (fun i => s i.succ)) := by
        refine TopologicalSpace.Opens.ext ?_
        show (U : Set X) ∩ nonvanishingLocus (finiteTensor (n + 1) L)
            (finiteTensorSection (n + 1) L s) = _
        rw [show nonvanishingLocus (X := X.toRingedSpace) (finiteTensor (n + 1) L)
              (finiteTensorSection (n + 1) L s) =
            nonvanishingLocus (L 0) (s 0) ∩ nonvanishingLocus
              (finiteTensor n (fun i => L i.succ))
              (finiteTensorSection n (fun i => L i.succ) (fun i => s i.succ)) from
          nonvanishingLocus_tensorSections _ _ _ _]
        exact (Set.inter_assoc _ _ _).symm
      rwa [hset]

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

/-- **Stacks Project, Tag 09NC.** A quasi-compact scheme every point of which lies in an affine
nonvanishing locus of a global section of some globally generated invertible sheaf carries an
ample invertible sheaf.

The proof is the Stacks Project's. Quasi-compactness gives finitely many pairs `(L i, t i)` with
`X = ⋃ X_{t i}` and each `X_{t i}` affine; put `B = L 0 ⊗ ⋯ ⊗ L n`. For a point `x`, pick an
index `j` with `x ∈ X_{t j}` and take `σ = s 0 ⊗ ⋯ ⊗ s n` where `s j = t j` and, for `i ≠ j`,
`s i` is a member of the generating family of `L i` not vanishing at `x`
(`Stacks.SheafOfModules.exists_generatingSection_nonvanishing`). Then `X_σ = ⋂ X_{s i}` contains
`x` and is contained in `X_{t j}`, so Tag 01PV applied `n + 1` times makes it affine. Ampleness
is read at exponent `1` through `Stacks.SheafOfModules.Invertible.tensorPowerOneIso`.

**Two invertibility predicates.** The hypothesis is spelled with
`Stacks.SheafOfModules.IsInvertible`, which is the one `Stacks.SheafOfModules.nonvanishingOpen`
is defined for, and the conclusion with `AlgebraicGeometry.SheafOfModules.IsInvertible`, which is
the one `AlgebraicGeometry.Scheme.Modules.IsAmple` is defined for. Both are `Prop`s, so the
choice of witness does not affect what either statement says, and
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` crosses between them. -/
@[stacks 09NC]
public theorem exists_isAmple_of_globallyGenerated_affine_nonvanishing (Y : Scheme.{u})
    (hcpt : CompactSpace Y)
    (hcover : ∀ y : Y, ∃ (M : Y.Modules)
      (hM : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.sheaf.obj
        (structureSheaf Y.toRingedSpace.sheaf).property M),
      Nonempty M.GeneratingSections ∧
        ∃ t : M.sections,
          y ∈ @Stacks.SheafOfModules.nonvanishingOpen
              Y.toLocallyRingedSpace.toRingedSpace _ M hM t ∧
            IsAffineOpen (@Stacks.SheafOfModules.nonvanishingOpen
              Y.toLocallyRingedSpace.toRingedSpace _ M hM t)) :
    ∃ (M : Y.Modules)
      (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
        (structureSheafRing Y.toRingedSpace).property M),
      @AlgebraicGeometry.Scheme.Modules.IsAmple Y M hM := by
  classical
  have _hcpt := hcpt
  by_cases hEmpty : IsEmpty Y
  · exact ⟨_root_.SheafOfModules.unit (structureSheafRing Y.toRingedSpace), inferInstance,
      ⟨hcpt, fun y => (hEmpty.false y).elim⟩⟩
  have hne : Nonempty Y := not_isEmpty_iff.mp hEmpty
  choose M hM hgen t hmem haff using hcover
  set V : Y → Y.Opens := fun y =>
    @nonvanishingOpen Y.toRingedSpace _ (M y) (hM y) (t y) with hVdef
  obtain ⟨S, hS⟩ := (isCompact_univ : IsCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun y : Y => ((V y : Y.Opens) : Set Y)) (fun y => (V y).2)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hmem y⟩)
  have hαne : Nonempty {y : Y // y ∈ S} := by
    obtain ⟨y, hyS, -⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (Classical.choice hne)))
    exact ⟨⟨y, hyS⟩⟩
  have hcard : Fintype.card {y : Y // y ∈ S} - 1 + 1 = Fintype.card {y : Y // y ∈ S} :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr hαne))
  set n : ℕ := Fintype.card {y : Y // y ∈ S} - 1 with hndef
  set e : Fin (n + 1) ≃ {y : Y // y ∈ S} :=
    (Fin.castOrderIso hcard).toEquiv.trans (Fintype.equivFin {y : Y // y ∈ S}).symm with hedef
  set L : Fin (n + 1) → _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
    fun i => M (e i).val with hLdef
  have hLinv : ∀ i, IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property (L i) := fun i => hM (e i).val
  refine ⟨finiteTensor n L,
    (isInvertible_iff_algebraicGeometry _ _ _).mp (isInvertible_finiteTensor n L hLinv),
    ⟨hcpt, fun x => ?_⟩⟩
  obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
  set j : Fin (n + 1) := e.symm ⟨y, hyS⟩ with hjdef
  have hjval : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyS⟩)
  set g : (i : Fin (n + 1)) → (L i).GeneratingSections :=
    fun i => (hgen (e i).val).some with hgdef
  have hk : ∀ i, ∃ k : (g i).I,
      x ∈ @nonvanishingOpen Y.toRingedSpace _ (L i) (hLinv i) ((g i).s k) := by
    intro i
    have := hLinv i
    exact exists_generatingSection_nonvanishing (L i) (g i) x
  choose k hkspec using hk
  set s : (i : Fin (n + 1)) → (L i).sections :=
    Function.update (fun i => (g i).s (k i)) j (t (e j).val) with hsdef
  have hsj : s j = t (e j).val := Function.update_self j (t (e j).val) (fun i => (g i).s (k i))
  have hjt : ∀ z, z ∈ nonvanishingLocus (X := Y.toRingedSpace) (L j) (s j) ↔ z ∈ V y := by
    intro z
    rw [hsj]
    change z ∈ nonvanishingLocus (X := Y.toRingedSpace) (M (e j).val) (t (e j).val) ↔ _
    rw [hjval]
    rfl
  have hxall : ∀ i, x ∈ nonvanishingLocus (X := Y.toRingedSpace) (L i) (s i) := by
    intro i
    by_cases hij : i = j
    · subst hij
      exact (hjt x).mpr hxy
    · rw [show s i = (g i).s (k i) from
        Function.update_of_ne hij (t (e j).val) (fun i => (g i).s (k i))]
      exact hkspec i
  have hlocus : nonvanishingLocus (X := Y.toRingedSpace) (finiteTensor n L)
      (finiteTensorSection n L s) = ⋂ i, nonvanishingLocus (L i) (s i) :=
    nonvanishingLocus_finiteTensorSection n L s
  have hxB : x ∈ nonvanishingLocus (X := Y.toRingedSpace) (finiteTensor n L)
      (finiteTensorSection n L s) := by
    rw [hlocus, Set.mem_iInter]
    exact hxall
  have hsub : nonvanishingLocus (X := Y.toRingedSpace) (finiteTensor n L)
      (finiteTensorSection n L s) ⊆ (V y : Set Y) := by
    intro z hz
    rw [hlocus, Set.mem_iInter] at hz
    exact (hjt z).mp (hz j)
  have hAff : IsAffineOpen (@nonvanishingOpen Y.toRingedSpace _ (finiteTensor n L)
      (isInvertible_finiteTensor n L hLinv) (finiteTensorSection n L s)) := by
    have hEq : V y ⊓ @nonvanishingOpen Y.toRingedSpace _ (finiteTensor n L)
        (isInvertible_finiteTensor n L hLinv) (finiteTensorSection n L s) =
        @nonvanishingOpen Y.toRingedSpace _ (finiteTensor n L)
          (isInvertible_finiteTensor n L hLinv) (finiteTensorSection n L s) :=
      TopologicalSpace.Opens.ext (Set.inter_eq_right.mpr hsub)
    rw [← hEq]
    exact isAffineOpen_inf_nonvanishingOpen_finiteTensor n L hLinv s (V y) (haff y)
  refine ⟨1, le_refl 1, ?_⟩
  have hBag := (isInvertible_iff_algebraicGeometry Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property (finiteTensor n L)).mp
      (isInvertible_finiteTensor n L hLinv)
  have eiso := Stacks.SheafOfModules.Invertible.tensorPowerOneIso Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property (finiteTensor n L)
  have hloc := nonvanishingLocus_sectionsMap Y.toRingedSpace eiso.symm
    (finiteTensorSection n L s)
  refine ⟨_root_.SheafOfModules.sectionsMap eiso.symm.hom (finiteTensorSection n L s),
    hloc.ge hxB, ?_⟩
  convert hAff using 1
  exact TopologicalSpace.Opens.ext hloc

/-- **Stacks Project, Tag 09ND.** A Noetherian integral separated scheme of topological Krull
dimension one has an ample invertible sheaf.

It is `Stacks.AlgebraicGeometry.AmpleDimensionOne.exists_ample_invertible_of_09NC` applied to
`exists_isAmple_of_globallyGenerated_affine_nonvanishing`. -/
@[stacks 09ND]
public theorem exists_isAmple_of_topologicalKrullDim_one (X : Scheme.{u})
    [IsNoetherian X] [IsIntegral X] [X.IsSeparated]
    (hdim : topologicalKrullDim X = 1) :
    ∃ (L : X.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L),
      @AlgebraicGeometry.Scheme.Modules.IsAmple X L hL :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.exists_ample_invertible_of_09NC
    (fun Y hY hcov => exists_isAmple_of_globallyGenerated_affine_nonvanishing Y hY hcov)
    X hdim

end AlgebraicGeometry.Scheme.Modules

end
