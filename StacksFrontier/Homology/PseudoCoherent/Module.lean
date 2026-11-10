module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.PseudoCoherent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherent modules and cohomological criteria

Let `R` be a ring. For an `R`-module `M`, pseudo-coherence in degrees `0` and `-1` is
respectively finite generation and finite presentation; pseudo-coherence from degree `-d` is
equivalent to admitting a finite free resolution through degree `d`, and pseudo-coherence is
equivalent to admitting a resolution by finite free modules. These module-level statements then
give cohomological criteria: a bounded-above complex whose degree-`i` term is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent, an object whose cohomology vanishes far enough
above `m` and is suitably finite in degrees `m` and `m + 1` is `m`-pseudo-coherent, and a
cohomologically bounded-above object whose degree-`i` cohomology is `(m - i)`-pseudo-coherent is
`m`-pseudo-coherent.

## Main definitions

* `StacksDraft.PseudoCoherence.HasFiniteFreeResolutionUpTo`: existence of an exact sequence
  `R^{a_n} → ⋯ → R^{a_0} → M → 0`.
* `StacksDraft.PseudoCoherence.HasFiniteFreeResolutionOfLength`: existence of a resolution whose
  terms through a prescribed degree are finite free.

## Main results

* `StacksDraft.PseudoCoherence.modulePseudoCoherent_iff_finiteness_and_resolutions`: the four
  characterizations of pseudo-coherent modules.
* `StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove`: the
  degreewise criterion for a bounded-above complex.
* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_vanishing_and_finite_homology`: the three
  criteria recognizing an `m`-pseudo-coherent object from its cohomology.
* `StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove_cohomology`:
  the criterion for a cohomologically bounded-above object.

## References

* [Stacks Project, Tag 064P](https://stacks.math.columbia.edu/tag/064P)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
* [Stacks Project, Tag 064W](https://stacks.math.columbia.edu/tag/064W)
* [Stacks Project, Tag 064Y](https://stacks.math.columbia.edu/tag/064Y)
* [Stacks Project, Tag 066B](https://stacks.math.columbia.edu/tag/066B)
-/

@[expose] public section

-- The syzygy construction and the truncation comparisons below elaborate deep instance
-- problems.
set_option maxRecDepth 8192
-- Needed so that the `singleFunctor`, mapping-cone and stupid-truncation normalisations below
-- close by `rfl`.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace StacksDraft.PseudoCoherence

universe u v

/-! ### Finite free resolutions of bounded length -/

/-- A module has a finite free resolution through degree `n` if there is an exact sequence
`R^{a_n} → ⋯ → R^{a_0} → M → 0`. Exactness is required at `M` and at every finite free term
except the leftmost one. -/
@[stacks 064P]
def HasFiniteFreeResolutionUpTo
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  match n with
  | 0 => ∃ a : ℕ, ∃ ε : (Fin a → R) →ₗ[R] M, Function.Surjective ε
  | n + 1 =>
      ∃ a : Fin (n + 2) → ℕ,
        ∃ d : ∀ i : Fin (n + 1),
            (Fin (a i.succ) → R) →ₗ[R] (Fin (a i.castSucc) → R),
          ∃ ε : (Fin (a 0) → R) →ₗ[R] M,
            Function.Surjective ε ∧ Function.Exact (d 0) ε ∧
              ∀ i : Fin n, Function.Exact (d i.succ) (d i.castSucc)

/-- An `R`-module admits a finite free resolution through degree `d` if it has an exact
resolution whose terms in degrees at most `d` are finite free. -/
def HasFiniteFreeResolutionOfLength {R : Type u} [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] (d : ℕ) : Prop :=
  ∃ F : ModuleResolution R M,
    ∀ n : ℕ, n ≤ d → Module.Finite R (F.complex.X n) ∧ Module.Free R (F.complex.X n)

/-! ### Pseudo-coherent modules -/

section Modules

variable {R : Type u} [Ring R]

/-- A finite free module placed in degree `0` is `m`-pseudo-coherent for every `m`. -/
private theorem modulePseudoCoherentFrom_of_finiteFree
    [HasDerivedCategory (ModuleCat.{v} R)] (N : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Free R N] (m : ℤ) :
    IsModulePseudoCoherentFrom (R := R) N m := by
  refine ⟨(CochainComplex.singleFunctor _ 0).obj N, isBoundedFiniteFree_single N 0,
    𝟙 _, ?_, ?_⟩
  · intro i hi
    change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (𝟙 _))
    infer_instance
  · change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map (𝟙 _))
    infer_instance

/-- The kernel inclusion of an epimorphism is the first map of a short exact sequence. -/
private theorem shortExact_kernel_ι {C : Type*} [Category* C] [Abelian C] {P N : C}
    (p : P ⟶ N) [Epi p] : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
  ⟨ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p)⟩

/-- A module which is `m`-pseudo-coherent for some `m ≤ 0` is finite. -/
private theorem finite_of_modulePseudoCoherentFrom
    [HasDerivedCategory (ModuleCat.{v} R)] (N : ModuleCat.{v} R)
    {m : ℤ} (hN : IsModulePseudoCoherentFrom (R := R) N m) (hm : m ≤ 0) :
    Module.Finite R N := by
  have h0 := IsPseudoCoherentFrom.mono hN hm
  have hfin := _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 0 h0
    (fun i hi => DerivedCategory.isZero_of_isLE _ 0 i hi)
  have : Module.Finite R
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj N) := hfin
  exact Module.Finite.equiv
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).app N).toLinearEquiv

/-- A `(-1)`-pseudo-coherent module is finitely presented. -/
@[sga "6 I 2.9" "(ii)⇒(i)"]
private theorem finitePresentation_of_modulePseudoCoherentFrom
    [HasDerivedCategory (ModuleCat.{v} R)] (N : ModuleCat.{v} R)
    (hN : IsModulePseudoCoherentFrom (R := R) N (-1)) :
    Module.FinitePresentation R N := by
  have hfin := _root_.PseudoCoherence.finitePresentation_homology_succ_of_isPseudoCoherentFrom
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-1) hN
    (fun i hi => DerivedCategory.isZero_of_isLE _ 0 i (by omega))
  have : Module.FinitePresentation R
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj N) := hfin
  exact Module.FinitePresentation.of_equiv
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0).app N).toLinearEquiv

/-- A finite module is `0`-pseudo-coherent: a finite free module surjects onto it. -/
private theorem modulePseudoCoherentFrom_zero_of_finite
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (N : ModuleCat.{v} R) [Module.Finite R N] :
    IsModulePseudoCoherentFrom (R := R) N 0 := by
  obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi N
  refine ⟨(CochainComplex.singleFunctor _ 0).obj P, isBoundedFiniteFree_single P 0,
    (DerivedCategory.singleFunctor _ 0).map p, ?_, ?_⟩
  · intro i hi
    exact (DerivedCategory.isZero_of_isLE _ 0 i hi).isIso
      (DerivedCategory.isZero_of_isLE _ 0 i hi) _
  · let e := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) 0
    have heq : (DerivedCategory.homologyFunctor _ 0).map
        ((DerivedCategory.singleFunctor _ 0).map p) =
        (e.app P).hom ≫ p ≫ (e.app N).inv := by
      simpa using (NatIso.naturality_2 e p).symm
    rw [heq]
    infer_instance

/-- The syzygy step: the kernel of a finite free cover of an `m`-pseudo-coherent module is
`(m + 1)`-pseudo-coherent. -/
private theorem kernel_modulePseudoCoherentFrom
    [HasDerivedCategory (ModuleCat.{v} R)] (P N : ModuleCat.{v} R) (p : P ⟶ N)
    [Epi p] [Module.Finite R P] [Module.Free R P] (m : ℤ)
    (hN : IsModulePseudoCoherentFrom (R := R) N m) :
    IsModulePseudoCoherentFrom (R := R) (kernel p : ModuleCat.{v} R) (m + 1) := by
  have hS := shortExact_kernel_ι p
  exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three m hS.singleTriangle
    hS.singleTriangle_distinguished (modulePseudoCoherentFrom_of_finiteFree P (m + 1)) hN

/-- Postcomposing the last map of a short complex with a monomorphism does not change
exactness. -/
private theorem exact_comp_mono_iff {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y : C} (i : S.X₃ ⟶ Y) [Mono i] :
    (ShortComplex.mk S.f (S.g ≫ i) (by rw [← Category.assoc, S.zero, zero_comp])).Exact ↔
      S.Exact := by
  let α : S ⟶ ShortComplex.mk S.f (S.g ≫ i)
      (by rw [← Category.assoc, S.zero, zero_comp]) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := i }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).symm

/-- An epimorphism onto the kernel of `f`, followed by the kernel inclusion, gives a short
complex exact at the middle term. -/
private theorem exact_epi_kernel {C : Type*} [Category* C] [Abelian C]
    {X Y P : C} (f : X ⟶ Y) (p : P ⟶ kernel f) [Epi p] :
    (ShortComplex.mk (p ≫ kernel.ι f) f (by simp)).Exact := by
  let α : ShortComplex.mk (p ≫ kernel.ι f) f (by simp) ⟶
      ShortComplex.mk (kernel.ι f) f (kernel.condition f) :=
    { τ₁ := p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mpr
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))

/-- A map from a chain complex to a module placed in degree `0` is a quasi-isomorphism exactly
when it is a resolution: exact at degree `0`, epi in degree `0`, and exact in every positive
degree. -/
private theorem quasiIso_toSingle_iff {C : Type*} [Category* C] [Abelian C]
    (F : ChainComplex C ℕ) (N : C) (π : F ⟶ (ChainComplex.single₀ C).obj N) :
    QuasiIso π ↔
      (ShortComplex.mk (F.d 1 0) (π.f 0) ((F.toSingle₀Equiv N) π).2).Exact ∧
        Epi (π.f 0) ∧ ∀ n : ℕ, F.ExactAt (n + 1) := by
  have h0 : QuasiIsoAt π 0 ↔
      (ShortComplex.mk (F.d 1 0) (π.f 0) ((F.toSingle₀Equiv N) π).2).Exact ∧
        Epi (π.f 0) := by
    rw [ChainComplex.quasiIsoAt₀_iff,
      ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)]
    rfl
  constructor
  · intro h
    have hzero := h0.mp (h.quasiIsoAt 0)
    exact ⟨hzero.1, hzero.2, fun n =>
      (exactAt_iff_of_quasiIsoAt π (n + 1)).mpr
        (ChainComplex.exactAt_succ_single_obj N n)⟩
  · rintro ⟨hex, hepi, hpos⟩
    refine ⟨fun n => ?_⟩
    cases n with
    | zero => exact h0.mpr ⟨hex, hepi⟩
    | succ n => exact (quasiIsoAt_iff_exactAt' π (n + 1)
        (ChainComplex.exactAt_succ_single_obj N n)).mpr (hpos n)

/-- A choice of epimorphism onto `N`, finite free whenever `N` is finite. -/
private structure PresentationCover (N : ModuleCat.{v} R) where
  /-- The covering module. -/
  source : ModuleCat.{v} R
  /-- The covering epimorphism. -/
  π : source ⟶ N
  /-- The covering map is an epimorphism. -/
  epi : Epi π
  /-- If `N` is finite, the covering module is finite free. -/
  finiteFree : Module.Finite R N → Module.Finite R source ∧ Module.Free R source

attribute [local instance] PresentationCover.epi

/-- A chosen presentation cover of `N`, finite free when `N` is finite. -/
private noncomputable def presentationCover [Small.{v} R] (N : ModuleCat.{v} R) :
    PresentationCover N := by
  classical
  apply Classical.choice
  by_cases hN : Module.Finite R N
  · obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi N
    exact ⟨⟨P, p, hp, fun _ => ⟨hfin, hfree⟩⟩⟩
  · exact ⟨⟨N, 𝟙 _, inferInstance, fun h => (hN h).elim⟩⟩

/-- The iterated syzygies of `N` obtained from the chosen presentation covers. -/
private noncomputable def syzygy [Small.{v} R] (N : ModuleCat.{v} R) : ℕ → ModuleCat.{v} R
  | 0 => N
  | n + 1 => kernel (presentationCover (syzygy N n)).π

/-- Each syzygy of an `m`-pseudo-coherent module is pseudo-coherent one degree further up, as
long as the degree has not passed `0`. -/
private theorem syzygy_pseudoCoherentFrom
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R] (N : ModuleCat.{v} R)
    (m : ℤ) (hN : IsModulePseudoCoherentFrom (R := R) N m) :
    ∀ n : ℕ, (n : ℤ) ≤ -m →
      IsModulePseudoCoherentFrom (R := R) (syzygy N n) (m + n) := by
  intro n
  induction n with
  | zero => simpa only [syzygy, Nat.cast_zero, add_zero] using fun _ : (0 : ℤ) ≤ -m => hN
  | succ n ih =>
    intro hn
    have hS := ih (by omega)
    have hfin := finite_of_modulePseudoCoherentFrom (syzygy N n) hS (by omega)
    obtain ⟨hP, hF⟩ := (presentationCover (syzygy N n)).finiteFree hfin
    simpa only [syzygy, Nat.cast_add, Nat.cast_one, ← add_assoc] using
      kernel_modulePseudoCoherentFrom _ _ (presentationCover (syzygy N n)).π (m + n) hS

/-- The differential of the syzygy resolution: cover the next syzygy and include it. -/
private noncomputable def resolutionDifferential [Small.{v} R]
    (N : ModuleCat.{v} R) (n : ℕ) :
    (presentationCover (syzygy N (n + 1))).source ⟶
      (presentationCover (syzygy N n)).source :=
  (presentationCover (syzygy N (n + 1))).π ≫ kernel.ι (presentationCover (syzygy N n)).π

/-- Consecutive differentials of the syzygy resolution compose to zero. -/
private theorem resolutionDifferential_comp [Small.{v} R] (N : ModuleCat.{v} R) (n : ℕ) :
    resolutionDifferential N (n + 1) ≫ resolutionDifferential N n = 0 := by
  simp [resolutionDifferential, Category.assoc]

/-- The syzygy resolution of `N` as a chain complex. -/
private noncomputable def resolutionComplex [Small.{v} R] (N : ModuleCat.{v} R) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n => (presentationCover (syzygy N n)).source)
    (resolutionDifferential N) (resolutionDifferential_comp N)

/-- The differentials of `resolutionComplex` are the syzygy differentials. -/
private theorem resolutionComplex_d [Small.{v} R] (N : ModuleCat.{v} R) (n : ℕ) :
    (resolutionComplex N).d (n + 1) n = resolutionDifferential N n := by
  simp [resolutionComplex]

/-- The syzygy resolution is exact in every positive degree. -/
private theorem resolutionComplex_exactAt [Small.{v} R] (N : ModuleCat.{v} R) (n : ℕ) :
    (resolutionComplex N).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  change (ShortComplex.mk ((resolutionComplex N).d (n + 2) (n + 1))
    ((resolutionComplex N).d (n + 1) n) _).Exact
  simp only [resolutionComplex_d]
  exact (exact_comp_mono_iff
    (ShortComplex.mk (resolutionDifferential N (n + 1))
      (presentationCover (syzygy N (n + 1))).π (by simp [resolutionDifferential]))
    (kernel.ι (presentationCover (syzygy N n)).π)).mpr
      (exact_epi_kernel _ _)

/-- The syzygy resolution, packaged as a `ModuleResolution`. -/
private noncomputable def chosenResolution [Small.{v} R] (N : ModuleCat.{v} R) :
    ModuleResolution R N where
  complex := resolutionComplex N
  hasHomology _ := inferInstance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(presentationCover N).π, by simp [resolutionComplex_d, resolutionDifferential, syzygy]⟩
  quasiIso := by
    rw [quasiIso_toSingle_iff]
    refine ⟨?_, ?_, resolutionComplex_exactAt N⟩
    · simpa only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero, resolutionComplex_d,
        resolutionDifferential, syzygy] using
        exact_epi_kernel (presentationCover N).π (presentationCover (syzygy N 1)).π
    · simpa using (presentationCover N).epi

/-- For an `m`-pseudo-coherent module, the terms of the syzygy resolution are finite free as
far down as the degree `m` allows. -/
private theorem chosenResolution_finiteFree
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R] (N : ModuleCat.{v} R)
    (m : ℤ) (hN : IsModulePseudoCoherentFrom (R := R) N m)
    (n : ℕ) (hn : (n : ℤ) ≤ -m) :
    Module.Finite R ((chosenResolution N).complex.X n) ∧
      Module.Free R ((chosenResolution N).complex.X n) :=
  (presentationCover (syzygy N n)).finiteFree
    (finite_of_modulePseudoCoherentFrom _ (syzygy_pseudoCoherentFrom N m hN n hn) (by omega))

/-- Conversely, if the kernel of a finite free cover of `N` is `(m + 1)`-pseudo-coherent then
`N` is `m`-pseudo-coherent. -/
private theorem modulePseudoCoherentFrom_of_kernel
    [HasDerivedCategory (ModuleCat.{v} R)] (P N : ModuleCat.{v} R) (p : P ⟶ N)
    [Epi p] [Module.Finite R P] [Module.Free R P] (m : ℤ)
    (hK : IsModulePseudoCoherentFrom (R := R) (kernel p : ModuleCat.{v} R) (m + 1)) :
    IsModulePseudoCoherentFrom (R := R) N m := by
  have hS := shortExact_kernel_ι p
  exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m hS.singleTriangle
    hS.singleTriangle_distinguished hK (modulePseudoCoherentFrom_of_finiteFree P m)

/-- A finitely presented module is `(-1)`-pseudo-coherent. -/
@[sga "6 I 2.9" "(i)⇒(ii)"]
private theorem modulePseudoCoherentFrom_neg_one_of_finitePresentation
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (N : ModuleCat.{v} R) [Module.FinitePresentation R N] :
    IsModulePseudoCoherentFrom (R := R) N (-1) := by
  obtain ⟨P, hfin, hfree, p, hp⟩ := exists_finite_free_epi N
  have : Module.Finite R (LinearMap.ker p.hom) := Module.Finite.iff_fg.mpr
    (Module.FinitePresentation.fg_ker p.hom ((ModuleCat.epi_iff_surjective p).mp hp))
  have : Module.Finite R (kernel p : ModuleCat.{v} R) :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer p).symm.toLinearEquiv
  apply modulePseudoCoherentFrom_of_kernel P N p (-1)
  simpa only [neg_add_cancel] using modulePseudoCoherentFrom_zero_of_finite (kernel p)

/-- Shifting a resolution one step to the left resolves the kernel of its degree-`0` map. -/
private theorem exists_kernel_resolution (N : ModuleCat.{v} R) (F : ModuleResolution R N) :
    ∃ G : ModuleResolution R (kernel (F.π.f 0) : ModuleCat.{v} R),
      ∀ n : ℕ, G.complex.X n = F.complex.X (n + 1) := by
  let p : F.complex.X 0 ⟶ N := F.π.f 0
  have hF := (quasiIso_toSingle_iff F.complex N F.π).mp F.quasiIso
  have hz : F.complex.d 1 0 ≫ p = 0 := ((F.complex.toSingle₀Equiv N) F.π).2
  let q : F.complex.X 1 ⟶ kernel p := kernel.lift p (F.complex.d 1 0) hz
  have hq : Epi q := hF.1.epi_kernelLift
  have hqz : F.complex.d 2 1 ≫ q = 0 := by
    rw [← cancel_mono (kernel.ι p), Category.assoc, kernel.lift_ι,
      HomologicalComplex.d_comp_d, zero_comp]
  let C : ChainComplex (ModuleCat.{v} R) ℕ :=
    ChainComplex.of (fun n => F.complex.X (n + 1))
      (fun n => F.complex.d (n + 1 + 1) (n + 1))
      (fun n => F.complex.d_comp_d _ _ _)
  have hC : ∀ n : ℕ, C.ExactAt (n + 1) := by
    intro n
    rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
    have h := (HomologicalComplex.exactAt_iff' F.complex
      (n + 2 + 1) (n + 1 + 1) (n + 1) (by simp) (by simp)).mp (hF.2.2 (n + 1))
    simpa [C, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      ChainComplex.of.d, Nat.add_assoc] using h
  have hz' : C.d 1 0 ≫ q = 0 := by simpa [C, ChainComplex.of.d] using hqz
  let π : C ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj (kernel p) :=
    (C.toSingle₀Equiv (kernel p)).symm ⟨q, hz'⟩
  have hπ : QuasiIso π := by
    rw [quasiIso_toSingle_iff]
    simp only [π, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    refine ⟨?_, hq, hC⟩
    have h := (HomologicalComplex.exactAt_iff' F.complex 2 1 0 (by simp) (by simp)).mp
      (hF.2.2 0)
    apply (exact_comp_mono_iff (ShortComplex.mk (C.d 1 0) q hz') (kernel.ι p)).mp
    simpa [q, C, ChainComplex.of.d,
      HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] using h
  exact ⟨⟨C, fun _ => inferInstance, π, hπ⟩, fun _ => rfl⟩

/-- A resolution whose first `d + 1` terms are finite free makes its module
`(-d)`-pseudo-coherent. -/
private theorem modulePseudoCoherentFrom_of_resolution
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R] (d : ℕ) :
    ∀ (N : ModuleCat.{v} R) (F : ModuleResolution R N),
      (∀ n : ℕ, n ≤ d → Module.Finite R (F.complex.X n) ∧ Module.Free R (F.complex.X n)) →
      IsModulePseudoCoherentFrom (R := R) N (-(d : ℤ)) := by
  induction d with
  | zero =>
    intro N F hF
    have hp := ((quasiIso_toSingle_iff F.complex N F.π).mp F.quasiIso).2.1
    have := (hF 0 le_rfl).1
    have : Module.Finite R N := Module.Finite.of_surjective (F.π.f 0).hom
      ((ModuleCat.epi_iff_surjective _).mp hp)
    simpa only [Nat.cast_zero, neg_zero] using modulePseudoCoherentFrom_zero_of_finite N
  | succ d ih =>
    intro N F hF
    have hp := ((quasiIso_toSingle_iff F.complex N F.π).mp F.quasiIso).2.1
    obtain ⟨hfin, hfree⟩ := hF 0 (Nat.zero_le _)
    obtain ⟨G, hG⟩ := exists_kernel_resolution N F
    have hK := ih (kernel (F.π.f 0)) G (fun n hn => by
      rw [hG n]
      exact hF (n + 1) (by omega))
    apply modulePseudoCoherentFrom_of_kernel (F.complex.X 0) N (F.π.f 0) (-(↑(d + 1)))
    simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev, neg_add_cancel_comm] using hK

/-- Finite generation, finite presentation, finite free resolutions of a fixed length, and
infinite finite free resolutions characterize the corresponding forms of pseudo-coherence for a
module in a universe containing `R`. -/
theorem modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    (IsModulePseudoCoherentFrom (R := R) M 0 ↔ Module.Finite R M) ∧
    (IsModulePseudoCoherentFrom (R := R) M (-1) ↔ Module.FinitePresentation R M) ∧
    (∀ d : ℕ, IsModulePseudoCoherentFrom (R := R) M (-(d : ℤ)) ↔
      HasFiniteFreeResolutionOfLength (R := R) M d) ∧
    (IsModulePseudoCoherent (R := R) M ↔
      Nonempty (FiniteFreeModuleResolution R M)) := by
  let N := ModuleCat.of R M
  refine ⟨⟨fun h => finite_of_modulePseudoCoherentFrom N h le_rfl,
    fun h => modulePseudoCoherentFrom_zero_of_finite N⟩,
    ⟨fun h => finitePresentation_of_modulePseudoCoherentFrom N h,
      fun h => modulePseudoCoherentFrom_neg_one_of_finitePresentation N⟩, ?_, ?_⟩
  · exact fun d => ⟨fun h => ⟨chosenResolution N, fun n hn =>
      chosenResolution_finiteFree N (-(d : ℤ)) h n (by omega)⟩,
      fun ⟨F, hF⟩ => modulePseudoCoherentFrom_of_resolution d N F hF⟩
  · have hU := pseudoCoherent_iff_all_of_small
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)
    constructor
    · intro h
      have hfin : ∀ n : ℕ, Module.Finite R ((chosenResolution N).complex.X n) ∧
          Module.Free R ((chosenResolution N).complex.X n) := fun n =>
        chosenResolution_finiteFree N (-(n : ℤ)) ((hU.mp h) (-(n : ℤ))) n (by omega)
      exact ⟨{
        toFreeModuleResolution := {
          toModuleResolution := chosenResolution N
          free := fun n => (hfin n).2 }
        finite := fun n => (hfin n).1 }⟩
    · rintro ⟨F⟩
      apply hU.mpr
      intro m
      have h := modulePseudoCoherentFrom_of_resolution (-m).toNat N
        F.toModuleResolution (fun n _ => ⟨F.finite n, F.free n⟩)
      exact IsPseudoCoherentFrom.mono h (by omega)

/-- Finite generation, finite presentation, finite free resolutions of a fixed length, and
infinite finite free resolutions characterize the corresponding forms of pseudo-coherence for a
module, represented in a universe containing both `R` and `M`. -/
@[stacks 064T, sga "6 I 2.9" "special case"]
theorem modulePseudoCoherent_iff_finiteness_and_resolutions
    [HasDerivedCategory (ModuleCat.{max v u} R)] (M : Type v) [AddCommGroup M] [Module R M] :
    (IsModulePseudoCoherentFrom (R := R) (ULift.{u} M) 0 ↔ Module.Finite R M) ∧
    (IsModulePseudoCoherentFrom (R := R) (ULift.{u} M) (-1) ↔ Module.FinitePresentation R M) ∧
    (∀ d : ℕ, IsModulePseudoCoherentFrom (R := R) (ULift.{u} M) (-(d : ℤ)) ↔
      HasFiniteFreeResolutionOfLength (R := R) (ULift.{u} M) d) ∧
    (IsModulePseudoCoherent (R := R) (ULift.{u} M) ↔
      Nonempty (FiniteFreeModuleResolution R (ULift.{u} M))) := by
  have h := modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    (R := R) (ULift.{u} M)
  refine ⟨h.1.trans ?_, h.2.1.trans ?_, h.2.2⟩
  · exact ⟨fun _ => Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M),
      fun _ => Module.Finite.equiv (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm⟩
  · exact ⟨fun _ => Module.FinitePresentation.of_equiv
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M),
      fun _ => Module.FinitePresentation.of_equiv
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm⟩

end Modules

/-! ### Bounded-above complexes with pseudo-coherent terms -/

/-- If `m`-pseudo-coherence of `K` follows from `(m - i)`-pseudo-coherence of the modules `M i`
for all `m`, then pseudo-coherence of every `M i` gives pseudo-coherence of `K`. -/
private lemma isPseudoCoherent_of_forall_isModulePseudoCoherentFrom {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : DerivedCategory (ModuleCat.{v} R))
    (M : ℤ → ModuleCat.{v} R)
    (first : ∀ m : ℤ, (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R) (M i) (m - i)) →
      IsPseudoCoherentFrom K m)
    (h : ∀ i : ℤ, IsModulePseudoCoherent (R := R) (M i)) : IsPseudoCoherent K :=
  (pseudoCoherent_iff_all K).mpr fun m => first m fun i =>
    (pseudoCoherent_iff_all ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (M i))).mp
      (h i) (m - i)

section BoundedAbove

variable {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]

/-- For a complex vanishing above `b`, there is a distinguished triangle relating its top term
placed in degree `b`, the complex itself, and its brutal truncation `σ_{≤ b-1}`. -/
private lemma exists_distinguished_single_stupidTrunc
    (L : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    ∃ (f : (DerivedCategory.singleFunctor (ModuleCat.{v} R) b).obj (L.X b) ⟶
        DerivedCategory.Q.obj L)
      (g : DerivedCategory.Q.obj L ⟶
        DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))))
      (h : DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) b).obj (L.X b))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  obtain ⟨ι, hιb⟩ := DerivedCategory.exists_hom_from_single_isIso_f L b
  obtain ⟨π, hπ⟩ := DerivedCategory.exists_hom_to_stupidTrunc_isIso_f L b
  have hMb : IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))).X b) :=
    DerivedCategory.isZero_stupidTrunc_X_of_lt L (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi
      exact hMb.eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  have hSE : (ShortComplex.mk ι π hcomp).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    by_cases hi : i = b
    · subst hi
      exact ShortComplex.shortExact_of_isIso_f_of_isZero_X₃ _ hιb hMb
    · exact ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) b (L.X b) i hi) (hπ i hi)
  exact ⟨_, _, _, Pretriangulated.mk_mem_distTriang_of_iso _
    (DerivedCategory.triangleOfSES_distinguished hSE)
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) b).app (L.X b))⟩

/-- A complex vanishing above some `b < m` whose degree-`m` term is `0`-pseudo-coherent is
`m`-pseudo-coherent. -/
private lemma zeroPseudoCoherentFrom_of_isStrictlyLE
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b m : ℤ) (hbm : b < m)
    (hK : K.IsStrictlyLE b)
    (hKm : IsModulePseudoCoherentFrom (R := R) (K.X m) 0) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  have : K.IsStrictlyLE b := hK
  obtain ⟨E, hE, α, hαiso, hαepi⟩ :=
    isPseudoCoherentFrom_single (K.X m) m m (by simpa using hKm)
  refine ⟨E, hE, 0, ?_, ?_⟩
  · intro i hi
    have htarget : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) m).obj (K.X m))) :=
      DerivedCategory.isZero_of_isLE _ m i hi
    have := hαiso i hi
    have hsource := htarget.of_iso (asIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α))
    exact hsource.isIso (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b i (by omega)) _
  · exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b m hbm).epi _

/-- A complex vanishing above `m - 1 + n` whose degree-`i` term is `(m - i)`-pseudo-coherent
is `m`-pseudo-coherent. -/
@[sga "6 I 2.11" "Part a), special case"]
private lemma pseudoCoherentFrom_of_bound (m : ℤ) :
    ∀ n : ℕ, (K : CochainComplex (ModuleCat.{v} R) ℤ) → K.IsStrictlyLE (m - 1 + n) →
      (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R) (K.X i) (m - i)) →
      IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  intro n
  induction n with
  | zero =>
      intro K hK hterms
      exact zeroPseudoCoherentFrom_of_isStrictlyLE K (m - 1) m (by omega) (by simpa using hK)
        (by simpa using hterms m)
  | succ n ih =>
      intro K hK hterms
      let b : ℤ := m - 1 + (n + 1 : ℕ)
      have : K.IsStrictlyLE b := by simpa [b] using hK
      obtain ⟨f, g, h, hT⟩ := exists_distinguished_single_stupidTrunc K b
      let L : CochainComplex (ModuleCat.{v} R) ℤ :=
        K.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))
      have hL : CochainComplex.IsStrictlyLE L (m - 1 + n) := by
        apply (CochainComplex.isStrictlyLE_iff L (m - 1 + n)).2
        intro i hi
        apply DerivedCategory.isZero_stupidTrunc_X_of_lt K
        dsimp [b]
        omega
      have hLterms : ∀ i : ℤ, IsModulePseudoCoherentFrom (R := R) (L.X i) (m - i) := by
        intro i
        by_cases hib : i ≤ b - 1
        · exact IsModulePseudoCoherentFrom.ofIso
            (K.stupidTruncXIso _
              (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hib)).symm _ (hterms i)
        · have hLi := DerivedCategory.isZero_stupidTrunc_X_of_lt K (show b - 1 < i by omega)
          by_cases hi : i = b
          · subst i
            have hKb1 : IsZero (K.X (b + 1)) := K.isZero_of_isStrictlyLE b (b + 1) (by omega)
            have hz : IsModulePseudoCoherentFrom (R := R) (K.X (b + 1)) (m - b) :=
              IsPseudoCoherentFrom.mono (hterms (b + 1)) (by omega)
            exact IsModulePseudoCoherentFrom.ofIso (hKb1.isoZero ≪≫ hLi.isoZero.symm) _ hz
          · have hKi : IsZero (K.X i) := K.isZero_of_isStrictlyLE b i (by omega)
            exact IsModulePseudoCoherentFrom.ofIso
              (hKi.isoZero ≪≫ hLi.isoZero.symm) _ (hterms i)
      have hsingle : IsPseudoCoherentFrom
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) b).obj (K.X b)) m :=
        isPseudoCoherentFrom_single _ b m (hterms b)
      have htrunc : IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m := ih L hL hLterms
      exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m
        (Triangle.mk f g h) hT hsingle (by simpa [L] using htrunc)

/-- A bounded-above complex with suitably pseudo-coherent terms is pseudo-coherent in the
corresponding degrees. In particular, pseudo-coherence of every term implies pseudo-coherence
of the complex. -/
@[stacks 064Y, sga "5 VIII 5.1" "'if' direction", sga "6 I 2.11" "Part a), special case"]
theorem pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (hK : ∃ b : ℤ, K.IsStrictlyLE b) :
    (∀ m : ℤ, (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R) (K.X i) (m - i)) →
      IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) ∧
    ((∀ i : ℤ, IsModulePseudoCoherent (R := R) (K.X i)) →
      IsPseudoCoherent (DerivedCategory.Q.obj K)) := by
  obtain ⟨b, hb⟩ := hK
  have first : ∀ m : ℤ,
      (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R) (K.X i) (m - i)) →
        IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
    intro m hterms
    let n : ℕ := (b - (m - 1)).toNat
    have hbound : b ≤ m - 1 + n := by
      dsimp [n]
      omega
    have hb' : K.IsStrictlyLE (m - 1 + n) := by
      apply (CochainComplex.isStrictlyLE_iff K (m - 1 + n)).2
      intro i hi
      exact K.isZero_of_isStrictlyLE b i (by omega)
    exact pseudoCoherentFrom_of_bound m n K hb' hterms
  exact ⟨first, isPseudoCoherent_of_forall_isModulePseudoCoherentFrom _ K.X first⟩

end BoundedAbove

/-! ### Recognizing pseudo-coherence from cohomology -/

/-- An object concentrated in degrees `≤ m` with finite top cohomology is
`m`-pseudo-coherent. -/
@[sga "6 I 2.10" "b), special case"]
private theorem isPseudoCoherentFrom_of_finite_top_homology
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)] :
    IsPseudoCoherentFrom K m := by
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eh : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K ≅ L.homology m :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) m).app L
  obtain ⟨P, hfin, hfree, f, hf⟩ := exists_finite_free_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_of_projective L m P (f ≫ eh.hom)
  refine ⟨_, isBoundedFiniteFree_single P m, DerivedCategory.Q.map φ ≫ e.hom, ?_, ?_⟩
  · intro i hi
    apply IsZero.isIso _ (hK i hi)
    exact DerivedCategory.isZero_of_isLE _ m i hi
  · rw [Functor.map_comp]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map
        (DerivedCategory.Q.map φ)) :=
      (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) m) φ).2 hφ
    infer_instance

/-- An object concentrated in the single degree `n`, with finitely presented cohomology there,
is `(n - 1)`-pseudo-coherent. -/
@[sga "6 I 2.9" "(i)⇒(ii)"]
private theorem isPseudoCoherentFrom_of_single_finitePresentation
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ) [K.IsGE n] [K.IsLE n]
    [Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)] :
    IsPseudoCoherentFrom K (n - 1) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K ≅ M :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) n).app M
  have : Module.FinitePresentation R M := Module.FinitePresentation.of_equiv eH.toLinearEquiv
  have hM := (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    (R := R) M).2.1.mpr this
  have hshift := IsPseudoCoherentFrom.shift hM (-n)
  have hsingle : IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) n).obj M) (n - 1) := by
    convert IsPseudoCoherentFrom.ofIso hshift
      (((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso (-n) n 0
        (by omega)).app M) using 1
    omega
  exact IsPseudoCoherentFrom.ofIso hsingle e.symm

/-- Vanishing above `m + 1`, with finitely presented cohomology in degree `m + 1` and finite
cohomology in degree `m`, implies `m`-pseudo-coherence. -/
private theorem isPseudoCoherentFrom_of_finitePresentation_next_homology
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : ∀ i : ℤ, m + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    [Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).obj K)]
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)] :
    IsPseudoCoherentFrom K m := by
  have : K.IsLE (m + 1) := (DerivedCategory.isLE_iff K (m + 1)).2 hK
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K (m + 1)
  let eH (i : ℤ) : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K ≅
      L.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app L
  have hlow : IsPseudoCoherentFrom (DerivedCategory.Q.obj (L.truncLE m)) m := by
    let eLow := eH m ≪≫ (asIso (HomologicalComplex.homologyMap (L.ιTruncLE m) m)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) m).symm.app (L.truncLE m)
    have : Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj
          (DerivedCategory.Q.obj (L.truncLE m))) := Module.Finite.equiv eLow.toLinearEquiv
    exact isPseudoCoherentFrom_of_finite_top_homology _ m
      (fun i hi ↦ DerivedCategory.isZero_of_isLE _ m i hi)
  have hhigh : IsPseudoCoherentFrom (DerivedCategory.Q.obj (L.truncGE (m + 1))) m := by
    let eHigh := eH (m + 1) ≪≫
      asIso (HomologicalComplex.homologyMap (L.πTruncGE (m + 1)) (m + 1)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) (m + 1)).symm.app
        (L.truncGE (m + 1))
    have : Module.FinitePresentation R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).obj
          (DerivedCategory.Q.obj (L.truncGE (m + 1)))) :=
      Module.FinitePresentation.of_equiv eHigh.toLinearEquiv
    simpa using isPseudoCoherentFrom_of_single_finitePresentation
      (DerivedCategory.Q.obj (L.truncGE (m + 1))) (m + 1)
  have hthird : IsPseudoCoherentFrom
      (DerivedCategory.Q.obj (L.shortComplexTruncLE m).X₃) m :=
    IsPseudoCoherentFrom.ofIso hhigh
      (asIso (DerivedCategory.Q.map (L.shortComplexTruncLEX₃ToTruncGE m (m + 1)))).symm
  have hmiddle := _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m
    (DerivedCategory.triangleOfSES (L.shortComplexTruncLE_shortExact m))
    (DerivedCategory.triangleOfSES_distinguished (L.shortComplexTruncLE_shortExact m))
    hlow hthird
  exact IsPseudoCoherentFrom.ofIso hmiddle e.symm

/-- Vanishing above degree `m`, with the appropriate finiteness assumptions on the cohomology
in degrees `m` and `m + 1`, implies `m`-pseudo-coherence. -/
@[stacks 064W, sga "6 I 2.11" "b), H^i=0 for i>m+1"]
theorem isPseudoCoherentFrom_of_vanishing_and_finite_homology
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) :
    ((∀ i : ℤ, m ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      IsPseudoCoherentFrom K m) ∧
    ((∀ i : ℤ, m < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K) →
      IsPseudoCoherentFrom K m) ∧
    ((∀ i : ℤ, m + 1 < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      Module.FinitePresentation R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).obj K) →
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K) →
      IsPseudoCoherentFrom K m) := by
  exact ⟨isPseudoCoherentFrom_of_homology_isZero K m,
    fun hK _ => isPseudoCoherentFrom_of_finite_top_homology K m hK,
    fun hK _ _ => isPseudoCoherentFrom_of_finitePresentation_next_homology K m hK⟩

/-! ### Pseudo-coherence from pseudo-coherent cohomology -/

section Cohomology

variable {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]

/-- An object concentrated in the single degree `d`, whose cohomology there is
`(m - d)`-pseudo-coherent, is `m`-pseudo-coherent. -/
private lemma pseudoCoherentFrom_of_isGE_of_isLE
    (X : DerivedCategory (ModuleCat.{v} R)) (d m : ℤ) [X.IsGE d] [X.IsLE d]
    (h : IsModulePseudoCoherentFrom (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).obj X) (m - d)) :
    IsPseudoCoherentFrom X m := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X d
  let q : ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).obj X) ≅ Y :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} R) d).app Y
  let e' : X ≅ (DerivedCategory.singleFunctor (ModuleCat.{v} R) d).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).obj X) :=
    e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{v} R) d).mapIso q.symm
  exact IsPseudoCoherentFrom.ofIso (isPseudoCoherentFrom_single _ d m h) e'.symm

/-- Below `d`, the canonical truncation `τ_{< d}` does not change cohomology. -/
private lemma isIso_homology_truncLT (d i : ℤ) (hi : i < d)
    (X : DerivedCategory (ModuleCat.{v} R)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((DerivedCategory.TStructure.t.truncLTι d).app X)) := by
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((DerivedCategory.TStructure.t.truncLTι d).app X)) := by
    change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((DerivedCategory.TStructure.t.triangleLTGE d).obj X).mor₁)
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff
      ((DerivedCategory.TStructure.t.triangleLTGE d).obj X)
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished d X) i]
    exact (DerivedCategory.isZero_of_isGE _ d i hi).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((DerivedCategory.TStructure.t.truncLTι d).app X)) := by
    change Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      ((DerivedCategory.TStructure.t.triangleLTGE d).obj X).mor₁)
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      ((DerivedCategory.TStructure.t.triangleLTGE d).obj X)
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished d X) (i - 1) i (by omega)]
    exact (DerivedCategory.isZero_of_isGE _ d (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- In degree `d`, the canonical truncation `τ_{≥ d}` does not change cohomology. -/
private lemma isIso_homology_truncGE (d : ℤ)
    (X : DerivedCategory (ModuleCat.{v} R)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app X)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE d).obj X
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d X
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT d (d + 1) rfl]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (d - 1) (d + 1) (by omega)).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT d]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (d - 1) d (by omega)).eq_of_src _ _
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).map T.mor₂)
  exact isIso_of_mono_of_epi _

/-- If `X` vanishes above `d` and its degree-`d` cohomology is `(m - d)`-pseudo-coherent, then
`τ_{≥ d} X` is `m`-pseudo-coherent. -/
private lemma pseudoCoherentFrom_truncGE (X : DerivedCategory (ModuleCat.{v} R)) (d m : ℤ)
    [X.IsLE d]
    (h : IsModulePseudoCoherentFrom (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).obj X) (m - d)) :
    IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncGE d).obj X) m := by
  apply pseudoCoherentFrom_of_isGE_of_isLE _ d m
  have := isIso_homology_truncGE d X
  exact IsModulePseudoCoherentFrom.ofIso
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) d).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app X))) _ h

/-- An object concentrated in degrees `≤ m + n` whose degree-`i` cohomology is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
private lemma pseudoCoherentFrom_boundedAbove_aux (m : ℤ) (n : ℕ)
    (X : DerivedCategory (ModuleCat.{v} R)) [hle : X.IsLE (m + n)]
    (h : ∀ i : ℤ, IsModulePseudoCoherentFrom (R := R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj X) (m - i)) :
    IsPseudoCoherentFrom X m := by
  induction n generalizing X with
  | zero =>
      let _ : X.IsLE m := by simpa using hle
      let T := (DerivedCategory.TStructure.t.triangleLTGE m).obj X
      have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished m X
      have h₁ : IsPseudoCoherentFrom T.obj₁ m :=
        isPseudoCoherentFrom_of_homology_isZero T.obj₁ m
          (fun i hi => DerivedCategory.isZero_of_isLE T.obj₁ (m - 1) i (by omega))
      exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT h₁
        (pseudoCoherentFrom_truncGE X m m (by simpa using h m))
  | succ n ih =>
      let d : ℤ := m + n + 1
      let T := (DerivedCategory.TStructure.t.triangleLTGE d).obj X
      have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished d X
      have h₁ : IsPseudoCoherentFrom T.obj₁ m := by
        let _ : T.obj₁.IsLE (m + n) := by
          apply DerivedCategory.TStructure.t.isLE_of_le _ (d - 1) (m + n) (by
            dsimp [d]
            omega)
        apply ih
        intro i
        by_cases hi : i < d
        · have := isIso_homology_truncLT d i hi X
          exact IsModulePseudoCoherentFrom.ofIso
            (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
              ((DerivedCategory.TStructure.t.truncLTι d).app X))).symm _ (h i)
        · exact isModulePseudoCoherentFrom_of_isZero _
            (DerivedCategory.isZero_of_isLE T.obj₁ (d - 1) i (by omega)) _
      let _ : X.IsLE d := by
        apply DerivedCategory.TStructure.t.isLE_of_le _ (m + (n + 1 : ℕ)) d (by
          dsimp [d]
          omega)
      exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT h₁
        (pseudoCoherentFrom_truncGE X d m (h d))

/-- A cohomologically bounded-above derived object whose cohomology modules are
pseudo-coherent in the corresponding degrees is pseudo-coherent. -/
@[stacks 066B]
theorem pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove_cohomology
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    (∀ m : ℤ,
      (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) (m - i)) →
      IsPseudoCoherentFrom K m) ∧
    ((∀ i : ℤ, IsModulePseudoCoherent (R := R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      IsPseudoCoherent K) := by
  obtain ⟨b, hb⟩ := hK
  have first : ∀ m : ℤ,
      (∀ i : ℤ, IsModulePseudoCoherentFrom (R := R)
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) (m - i)) →
      IsPseudoCoherentFrom K m := by
    intro m h
    let n : ℕ := (b - m).toNat
    let _ : K.IsLE (m + n) := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      apply hb i
      dsimp [n] at hi ⊢
      omega
    exact pseudoCoherentFrom_boundedAbove_aux m n K h
  exact ⟨first, isPseudoCoherent_of_forall_isModulePseudoCoherentFrom K
    (fun i => (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) first⟩

end Cohomology

end StacksDraft.PseudoCoherence
