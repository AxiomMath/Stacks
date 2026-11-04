module

public import StacksCore.Algebra.Homology.ExactSequence
public import StacksCore.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksCore.CategoryTheory.Filtration.Finite
public import StacksCore.CategoryTheory.Filtration.GradedExact
public import StacksCore.CategoryTheory.GradedObject.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Strictness and graded pieces

Let `f : A ⟶ B` be a morphism of filtered objects of an abelian category `𝒜`. When the filtration
of `A` has a top step and that of `B` has a zero step (in particular for finite filtrations), the
following are equivalent: (1) `f` is strict; (2) `Coim f → Im f` is an isomorphism; (3)
`gr(Coim f) → gr(Im f)` is an isomorphism; (4) `gr(Ker f) → gr(A) → gr(B)` is exact; (5)
`gr(A) → gr(B) → gr(Coker f)` is exact; (6) `0 → gr(Ker f) → gr(A) → gr(B) → gr(Coker f) → 0` is
exact. Here exactness of a sequence of graded objects means exactness on every `gr^p`, and the
sequences are `gr^p` applied to the canonical complexes of `f` in `Fil(𝒜)`.

## Main results

* `FilteredObject.isIso_of_forall_epi_gr`: a morphism over `ℤᵒᵖ` which is an isomorphism on the
  underlying objects and an epimorphism on every `gr^p` is an isomorphism, when the target has a
  zero step.
* `FilteredObject.isIso_of_forall_mono_gr`: the same with monomorphisms on every `gr^p`, when the
  source has a top step.
* `FilteredObject.exact_grMap_kernel_ι_cokernel_π_iff_isIso`: along any index arrow `φ`, the
  sequence `0 → gr_φ(Ker f) → gr_φ(A) → gr_φ(B) → gr_φ(Coker f) → 0` is exact iff
  `gr_φ(Coim f) → gr_φ(Im f)` is an isomorphism.
* `FilteredObject.preservesLimit_parallelPair_grMap_of_isStrict`,
  `FilteredObject.preservesColimit_parallelPair_grMap_of_isStrict`: `gr_φ` preserves the kernel
  and the cokernel of a strict morphism.
* `FilteredObject.isStrict_tfae`: the equivalence of (1)–(6).

## Implementation notes

Each direction is stated under its own hypotheses: (4) ⇒ (1) needs only a top step of `A`,
(5) ⇒ (1) only a zero step of `B`, (3) ⇒ (1) and (6) ⇒ (1) either one; a zero step of `A` and a
top step of `B` are never used. The implications (3) ⇒ (4), (5), (6) and (6) ⇔ (3) hold without
any bound, while (4) ⇒ (3) and (5) ⇒ (3) need one. The inductions on `p` use the four lemma on the
rows `0 → F^{p+1} → F^p → gr^p → 0` where Stacks invokes the five lemma.

## References

* [Stacks, Tag 0127](https://stacks.math.columbia.edu/tag/0127)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

open Filtration

section Steps

variable [Abelian C] {X Y : FilteredObject C I} (u : X ⟶ Y) {i j : I} (φ : i ⟶ j)

/-- The epimorphism half of the descending induction step of Stacks 0127, along any index arrow
`φ : i ⟶ j` (so `F^i ⊆ F^j`): if `u_i : F^iX ⟶ F^iY` and `gr_φ(u)` are epimorphisms, then so is
`u_j` (four lemma on the rows `0 → F^i → F^j → gr_φ → 0`). No hypothesis on `u.hom`. -/
lemma epi_natTrans_app_of_epi_grMap_map [Epi (u.natTrans.app i)] [Epi ((grMap φ).map u)] :
    Epi (u.natTrans.app j) :=
  ShortComplex.epi_of_epi_of_epi_of_epi (stepShortComplexMap φ u)
    (stepShortComplex_shortExact φ Y).exact (inferInstanceAs (Epi (grMapπ φ X))) ‹_› ‹_›

/-- The ascending induction step for quotients, along any index arrow `φ : i ⟶ j`: if `gr_φ(u)`
and `X/F^jX ⟶ Y/F^jY` are monomorphisms, then so is `X/F^iX ⟶ Y/F^iY` (four lemma on the rows
`0 → gr_φ → X/F^i → X/F^j → 0`). No hypothesis on `u.hom`. -/
lemma mono_quot_map_of_mono_grMap_map [Mono ((grMap φ).map u)] [Mono ((quot j).map u)] :
    Mono ((quot i).map u) :=
  ShortComplex.mono_of_mono_of_mono_of_mono (quotStepShortComplexMap φ u)
    (quotStepShortComplex_shortExact φ X).exact (inferInstanceAs (Mono (grMapι φ Y))) ‹_› ‹_›

/-- The descending induction step of Stacks 0127, along any index arrow `φ : i ⟶ j` (so
`F^i ⊆ F^j`): if `u` is a monomorphism, `u_i : F^iX ⟶ F^iY` is an isomorphism and `gr_φ(u)` is an
epimorphism, then `u_j` is an isomorphism (four lemma on the rows `0 → F^i → F^j → gr_φ → 0`). -/
lemma isIso_natTrans_app_of_epi_grMap_map [Mono u.hom] [IsIso (u.natTrans.app i)]
    [Epi ((grMap φ).map u)] : IsIso (u.natTrans.app j) :=
  have : Epi (u.natTrans.app j) := epi_natTrans_app_of_epi_grMap_map u φ
  have := mono_natTrans_app_of_mono_hom u j
  isIso_of_mono_of_epi _

/-- The ascending induction step of Stacks 0127, along any index arrow `φ : i ⟶ j`: if
`u_j : F^jX ⟶ F^jY` is an isomorphism and `gr_φ(u)` is a monomorphism, then `u_i` is an
isomorphism (four lemma on the rows `0 → F^i → F^j → gr_φ → 0`). -/
lemma isIso_natTrans_app_of_mono_grMap_map [IsIso (u.natTrans.app j)] [Mono ((grMap φ).map u)] :
    IsIso (u.natTrans.app i) :=
  Abelian.isIso_of_isIso_of_mono (ShortComplex.mapToComposableArrows (stepShortComplexMap φ u))
    (stepShortComplex_shortExact φ X).exact.exact_toComposableArrows
    (stepShortComplex_shortExact φ Y).exact.exact_toComposableArrows
    (inferInstanceAs (Mono (X.filtration.step φ))) (inferInstanceAs (Mono (Y.filtration.step φ)))
    ‹_› ‹_›

end Steps

section Descent

variable [Abelian C] {X Y : FilteredObject C ℤᵒᵖ} (u : X ⟶ Y)

/-- Ascending induction on `ℤ` from a base `n`, given the property for all `p ≤ n`. -/
private theorem forall_of_le_of_succ {P : ℤ → Prop} (n : ℤ) (below : ∀ p, p ≤ n → P p)
    (step : ∀ q, n ≤ q → P q → P (q + 1)) : ∀ p, P p := by
  have key : ∀ q, n ≤ q → P q := fun q hq => by
    induction q, hq using Int.leInduction with
    | base => exact below n le_rfl
    | succ q hq ih => exact step q hq ih
  exact fun p => (le_total p n).elim (below p) (key p)

/-- Descending induction on `ℤ` from a base `m`, given the property for all `p ≥ m`. -/
private theorem forall_of_ge_of_pred {P : ℤ → Prop} (m : ℤ) (above : ∀ p, m ≤ p → P p)
    (step : ∀ q, q ≤ m → P (q + 1) → P q) : ∀ p, P p := by
  have key : ∀ q, q ≤ m → P q := fun q hq => by
    induction q, hq using Int.leInductionDown with
    | base => exact above m le_rfl
    | pred q hq ih => exact step (q - 1) (by omega) (by rwa [Int.sub_add_cancel])
  exact fun p => (le_total m p).elim (above p) (key p)

/-- Descending induction, level-wise: a morphism of filtered objects over `ℤᵒᵖ` which is an
epimorphism on all graded pieces is an epimorphism on every step, `F^pX ↠ F^pY`, provided the
target filtration has a zero step (`F^mY = 0`). No hypothesis on `X` or on `u.hom`. -/
theorem epi_natTrans_app_of_forall_epi_gr (h : ∀ p, Epi ((gr p).map u))
    [HasBotStep Y.filtration] (p : ℤᵒᵖ) : Epi (u.natTrans.app p) := by
  obtain ⟨⟨m⟩, hm⟩ := HasBotStep.exists_isZero Y.filtration
  have above : ∀ p, m ≤ p → Epi (u.natTrans.app (op p)) := fun p hp => by
    have hY : IsZero (Y.filtration.obj (op p)) := Y.filtration.isZero_obj_of_le hp hm
    exact ⟨fun _ _ _ => hY.eq_of_src _ _⟩
  exact forall_of_ge_of_pred (P := fun q => Epi (u.natTrans.app (op q))) m above
    (fun q _ _ => have := h q; epi_natTrans_app_of_epi_grMap_map u (succHom q)) p.unop

/-- Descending induction, level-wise: a monomorphism of filtered objects over `ℤᵒᵖ` which is an
epimorphism on all graded pieces is an isomorphism on every step, `F^pX ≅ F^pY`, provided the
target filtration has a zero step (`F^mY = 0`). Only `Mono u.hom` is needed: `X` need not be
exhaustive, so `u` itself need not be an isomorphism. -/
theorem isIso_natTrans_app_of_forall_epi_gr [Mono u.hom] (h : ∀ p, Epi ((gr p).map u))
    [HasBotStep Y.filtration] (p : ℤᵒᵖ) : IsIso (u.natTrans.app p) :=
  have := epi_natTrans_app_of_forall_epi_gr u h p
  have := mono_natTrans_app_of_mono_hom u p
  isIso_of_mono_of_epi _

/-- Descending induction: a morphism of filtered objects over `ℤᵒᵖ` whose underlying morphism is an
isomorphism and which is an epimorphism on all graded pieces is an isomorphism, provided the
target filtration has a zero step (`F^mY = 0`). -/
theorem isIso_of_forall_epi_gr [IsIso u.hom] (h : ∀ p, Epi ((gr p).map u))
    [HasBotStep Y.filtration] : IsIso u :=
  (isIso_iff u).2 ⟨‹_›, isIso_natTrans_app_of_forall_epi_gr u h⟩

/-- Ascending induction: a morphism of filtered objects over `ℤᵒᵖ` whose underlying morphism is an
isomorphism and which is a monomorphism on all graded pieces is an isomorphism, provided the
source filtration has a top step (`F^nX = X`). -/
theorem isIso_of_forall_mono_gr [IsIso u.hom] (h : ∀ p, Mono ((gr p).map u))
    [HasTopStep X.filtration] : IsIso u := by
  obtain ⟨⟨n⟩, hn⟩ := HasTopStep.exists_isIso (F := X.filtration)
  have below : ∀ p, p ≤ n → IsIso (u.natTrans.app (op p)) := fun p hp => by
    have hX : IsIso (X.filtration.ι.app (op p)) := X.filtration.isIso_ι_app_of_le hp hn
    have h₁ : IsIso (u.natTrans.app (op p) ≫ Y.filtration.ι.app (op p)) := by
      rw [u.comm]; infer_instance
    have := epi_of_epi (u.natTrans.app (op p)) (Y.filtration.ι.app (op p))
    have := isIso_of_mono_of_epi (Y.filtration.ι.app (op p))
    exact IsIso.of_isIso_comp_right (u.natTrans.app (op p)) (Y.filtration.ι.app (op p))
  exact (isIso_iff u).2 ⟨‹_›, fun i =>
    forall_of_le_of_succ (P := fun q => IsIso (u.natTrans.app (op q))) n below
      (fun q _ _ => have := h q; isIso_natTrans_app_of_mono_grMap_map u (succHom q)) i.unop⟩

/-- Ascending induction, quotient-wise: a morphism of filtered objects over `ℤᵒᵖ` which is a
monomorphism on all graded pieces is a monomorphism on every quotient, `X/F^pX ↪ Y/F^pY`,
provided the source filtration has a top step (`F^nX = X`). No hypothesis on `Y` or on
`u.hom`. -/
theorem mono_quot_map_of_forall_mono_gr (h : ∀ p, Mono ((gr p).map u))
    [HasTopStep X.filtration] (p : ℤᵒᵖ) : Mono ((quot p).map u) := by
  obtain ⟨⟨n⟩, hn⟩ := HasTopStep.exists_isIso (F := X.filtration)
  have below : ∀ p, p ≤ n → Mono ((quot (op p)).map u) := fun p hp => by
    have := X.filtration.isIso_ι_app_of_le hp hn
    have hX := isZero_quot_obj_of_isIso_ι_app (op p) X
    exact ⟨fun _ _ _ => hX.eq_of_tgt _ _⟩
  exact forall_of_le_of_succ (P := fun q => Mono ((quot (op q)).map u)) n below
    (fun q _ _ => have := h q; mono_quot_map_of_mono_grMap_map u (succHom q)) p.unop

/-- A morphism of filtered objects over `ℤᵒᵖ` which is an epimorphism on all graded pieces is an
epimorphism on the underlying objects, provided the target filtration is finite. No hypothesis
on `X`. -/
theorem epi_hom_of_forall_epi_gr (h : ∀ p, Epi ((gr p).map u)) [HasTopStep Y.filtration]
    [HasBotStep Y.filtration] : Epi u.hom :=
  epi_hom_of_forall_epi_natTrans_app u (epi_natTrans_app_of_forall_epi_gr u h)

end Descent

section Comparison

variable [Abelian C] {A B : FilteredObject C I} (f : A ⟶ B)

/-- `Ker f ⊆ A` carries the induced filtration, so it inherits a top step from `A`. Since
`Abelian.image g = kernel (cokernel.π g)`, this also gives `Im g ⊆ B` a top step from `B`. -/
instance [HasTopStep A.filtration] : HasTopStep (kernel f).filtration :=
  hasTopStep_of_iso (kernelIsoKernelObj f).symm

/-- `Ker f ⊆ A` carries the induced filtration, so it inherits a zero step from `A`; likewise
`Im g ⊆ B` inherits one from `B`. -/
instance [HasBotStep A.filtration] : HasBotStep (kernel f).filtration :=
  hasBotStep_of_iso (kernelIsoKernelObj f).symm

/-- `Coker f` carries the quotient filtration, so it inherits a top step from `B`. Since
`Abelian.coimage g = cokernel (kernel.ι g)`, this also gives `Coim g` a top step from `A`. -/
instance [HasTopStep B.filtration] : HasTopStep (cokernel f).filtration :=
  hasTopStep_of_iso (cokernelIsoCokernelObj f).symm

/-- `Coker f` carries the quotient filtration, so it inherits a zero step from `B`; likewise
`Coim g` inherits one from `A`. -/
instance [HasBotStep B.filtration] : HasBotStep (cokernel f).filtration :=
  hasBotStep_of_iso (cokernelIsoCokernelObj f).symm

/-- The kernel of `f` has a finite filtration when `A` does. -/
instance [IsFinite A.filtration] : IsFinite (kernel f).filtration := {}

/-- The cokernel of `f` has a finite filtration when `B` does. -/
instance [IsFinite B.filtration] : IsFinite (cokernel f).filtration := {}

/-- Stacks 0127, (4) at one index arrow: `gr_φ(Ker f) → gr_φ(A) → gr_φ(B)` is exact iff
`gr_φ(Coim f) → gr_φ(Im f)` is a monomorphism. No finiteness needed. -/
theorem exact_grMap_kernel_ι_iff_mono {i j : I} (φ : i ⟶ j) :
    ((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map (grMap φ)).Exact ↔
      Mono ((grMap φ).map (Abelian.coimageImageComparison f)) := by
  have hT := shortExact_map_grMap_kernel_ι_coimage_π f φ
  exact (ShortComplex.exact_iff_mono_of_exact_of_epi hT.exact
    ((grMap φ).map (Abelian.coimageImageComparison f) ≫ (grMap φ).map (Abelian.image.ι f))
    (by rw [← Functor.map_comp, ← Functor.map_comp, Abelian.coimage_image_factorisation]) _).trans
    (mono_comp_iff_of_mono _ _)

/-- Stacks 0127, (5) at one index arrow: `gr_φ(A) → gr_φ(B) → gr_φ(Coker f)` is exact iff
`gr_φ(Coim f) → gr_φ(Im f)` is an epimorphism. No finiteness needed. -/
theorem exact_grMap_cokernel_π_iff_epi {i j : I} (φ : i ⟶ j) :
    ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map (grMap φ)).Exact ↔
      Epi ((grMap φ).map (Abelian.coimageImageComparison f)) := by
  have hT := shortExact_map_grMap_image_ι_cokernel_π f φ
  exact (ShortComplex.exact_iff_epi_of_exact_of_mono hT.exact
    ((grMap φ).map (Abelian.coimage.π f) ≫ (grMap φ).map (Abelian.coimageImageComparison f))
    (by
      dsimp only
      rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc,
        Abelian.coimage_image_factorisation]) _).trans
    (epi_comp_iff_of_epi _ _)

/-- Stacks 0127, (6) at one index arrow is (4) ∧ (5) there: the outer maps
`gr_φ(Ker f) → gr_φ(A)` and `gr_φ(B) → gr_φ(Coker f)` are always mono resp. epi (Stacks 05SP). -/
theorem exact_grMap_kernel_ι_cokernel_π_iff {i j : I} (φ : i ⟶ j) :
    ((ComposableArrows.mk₃ ((grMap φ).map (kernel.ι f)) ((grMap φ).map f)
        ((grMap φ).map (cokernel.π f))).Exact ∧ Mono ((grMap φ).map (kernel.ι f)) ∧
        Epi ((grMap φ).map (cokernel.π f))) ↔
      ((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map (grMap φ)).Exact ∧
        ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map (grMap φ)).Exact := by
  rw [ComposableArrows.exact_mk₃_iff _ _ _
    (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
    (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])]
  exact ⟨fun h => h.1, fun h => ⟨h, inferInstance, inferInstance⟩⟩

/-- Stacks 0127, (6) ⇔ (3) at one index arrow: `0 → gr_φ(Ker f) → gr_φ(A) → gr_φ(B) → gr_φ(Coker f)
→ 0` is exact iff `gr_φ(Coim f) → gr_φ(Im f)` is an isomorphism. No finiteness needed. -/
theorem exact_grMap_kernel_ι_cokernel_π_iff_isIso {i j : I} (φ : i ⟶ j) :
    ((ComposableArrows.mk₃ ((grMap φ).map (kernel.ι f)) ((grMap φ).map f)
        ((grMap φ).map (cokernel.π f))).Exact ∧ Mono ((grMap φ).map (kernel.ι f)) ∧
        Epi ((grMap φ).map (cokernel.π f))) ↔
      IsIso ((grMap φ).map (Abelian.coimageImageComparison f)) := by
  rw [exact_grMap_kernel_ι_cokernel_π_iff, exact_grMap_kernel_ι_iff_mono,
    exact_grMap_cokernel_π_iff_epi, isIso_iff_mono_and_epi]

end Comparison

section Preserves

variable [Abelian C] {A B : FilteredObject C I} (f : A ⟶ B) {i j : I} (φ : i ⟶ j)

/-- Stacks 0127, (1) ⇒ (4) in Mathlib's language: `gr_φ` preserves the kernel of a strict
morphism `f`, along any index arrow `φ`. By Stacks 05SI the comparison `Coim f ⟶ Im f` is an
isomorphism in `Fil(𝒜)`, so `gr_φ(Ker f) → gr_φ(A) → gr_φ(B)` is exact
(`exact_grMap_kernel_ι_iff_mono`) with `gr_φ(Ker f) → gr_φ(A)` a monomorphism (Stacks 05SP), i.e.
a kernel of `gr_φ(f)`. -/
instance preservesLimit_parallelPair_grMap_of_isStrict [IsStrict f] :
    PreservesLimit (parallelPair f 0) (grMap φ) :=
  have := (isStrict_iff_isIso_coimageImageComparison f).1 ‹_›
  have hex : (ShortComplex.mk ((grMap φ).map (kernel.ι f)) ((grMap φ).map f)
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])).Exact :=
    (exact_grMap_kernel_ι_iff_mono f φ).2 inferInstance
  preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    ((KernelFork.isLimitMapConeEquiv _ _).2 hex.fIsKernel)

/-- Stacks 0127, (1) ⇒ (5) in Mathlib's language: `gr_φ` preserves the cokernel of a strict
morphism `f`, along any index arrow `φ`. By Stacks 05SI the comparison `Coim f ⟶ Im f` is an
isomorphism in `Fil(𝒜)`, so `gr_φ(A) → gr_φ(B) → gr_φ(Coker f)` is exact
(`exact_grMap_cokernel_π_iff_epi`) with `gr_φ(B) → gr_φ(Coker f)` an epimorphism (Stacks 05SP),
i.e. a cokernel of `gr_φ(f)`. -/
instance preservesColimit_parallelPair_grMap_of_isStrict [IsStrict f] :
    PreservesColimit (parallelPair f 0) (grMap φ) :=
  have := (isStrict_iff_isIso_coimageImageComparison f).1 ‹_›
  have hex : (ShortComplex.mk ((grMap φ).map f) ((grMap φ).map (cokernel.π f))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])).Exact :=
    (exact_grMap_cokernel_π_iff_epi f φ).2 inferInstance
  preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).2 hex.gIsCokernel)

/-- For a strict `f`, `gr_φ(Ker f) ⟶ gr_φ(A)` is a kernel of `gr_φ(f)`, on the explicit model
`kernelObj f` (`Ker(f.hom)` with the induced filtration): `gr_φ` of the kernel fork
`kernelIsLimit f` (`preservesLimit_parallelPair_grMap_of_isStrict`). -/
noncomputable def grMapKernelιIsKernel [IsStrict f] :
    IsLimit (KernelFork.ofι ((grMap φ).map (kernelι f))
      (by rw [← Functor.map_comp, kernelι_comp, Functor.map_zero]) :
      KernelFork ((grMap φ).map f)) :=
  KernelFork.mapIsLimit _ (kernelIsLimit f) (grMap φ)

/-- For a strict `f`, `gr_φ(B) ⟶ gr_φ(Coker f)` is a cokernel of `gr_φ(f)`, on the explicit model
`cokernelObj f` (`Coker(f.hom)` with the quotient filtration): `gr_φ` of the cokernel cofork
`cokernelIsColimit f` (`preservesColimit_parallelPair_grMap_of_isStrict`). -/
noncomputable def grMapCokernelπIsCokernel [IsStrict f] :
    IsColimit (CokernelCofork.ofπ ((grMap φ).map (cokernelπ f))
      (by rw [← Functor.map_comp, comp_cokernelπ, Functor.map_zero]) :
      CokernelCofork ((grMap φ).map f)) :=
  CokernelCofork.mapIsColimit _ (cokernelIsColimit f) (grMap φ)

end Preserves

section Criteria

variable [Abelian C] {A B : FilteredObject C ℤᵒᵖ} (f : A ⟶ B)

/-- Stacks 0127, (1) ⇔ (4): `f` is strict iff `gr(Ker f) → gr(A) → gr(B)` is exact, when `A` has a
top step. -/
@[stacks 0127 "(1) ⇔ (4); needs only a top step of `A`"]
theorem isStrict_iff_forall_exact_gr_kernel_ι [HasTopStep A.filtration] :
    IsStrict f ↔ ∀ p, ((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map (gr p)).Exact := by
  rw [isStrict_iff_isIso_coimageImageComparison]
  refine ⟨fun h p => (exact_grMap_kernel_ι_iff_mono f _).2 inferInstance, fun h => ?_⟩
  exact isIso_of_forall_mono_gr _ fun p => (exact_grMap_kernel_ι_iff_mono f _).1 (h p)

/-- Stacks 0127, (1) ⇔ (5): `f` is strict iff `gr(A) → gr(B) → gr(Coker f)` is exact, when `B` has
a zero step. -/
@[stacks 0127 "(1) ⇔ (5); needs only a zero step of `B`"]
theorem isStrict_iff_forall_exact_gr_cokernel_π [HasBotStep B.filtration] :
    IsStrict f ↔
      ∀ p, ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map (gr p)).Exact := by
  rw [isStrict_iff_isIso_coimageImageComparison]
  refine ⟨fun h p => (exact_grMap_cokernel_π_iff_epi f _).2 inferInstance, fun h => ?_⟩
  exact isIso_of_forall_epi_gr _ fun p => (exact_grMap_cokernel_π_iff_epi f _).1 (h p)

/-- Stacks 0127, (1) ⇔ (3): `f` is strict iff `gr^p(Coim f) → gr^p(Im f)` is an isomorphism for all
`p`, when `A` has a top step. -/
@[stacks 0127 "(1) ⇔ (3), under a top step of `A`"]
theorem isStrict_iff_forall_isIso_gr_of_hasTopStep [HasTopStep A.filtration] :
    IsStrict f ↔ ∀ p, IsIso ((gr p).map (Abelian.coimageImageComparison f)) := by
  rw [isStrict_iff_isIso_coimageImageComparison]
  refine ⟨fun h p => inferInstance, fun h => ?_⟩
  exact isIso_of_forall_mono_gr _ fun p => have := h p; inferInstance

/-- Stacks 0127, (1) ⇔ (3): `f` is strict iff `gr^p(Coim f) → gr^p(Im f)` is an isomorphism for all
`p`, when `B` has a zero step. -/
@[stacks 0127 "(1) ⇔ (3), under a zero step of `B`"]
theorem isStrict_iff_forall_isIso_gr_of_hasBotStep [HasBotStep B.filtration] :
    IsStrict f ↔ ∀ p, IsIso ((gr p).map (Abelian.coimageImageComparison f)) := by
  rw [isStrict_iff_isIso_coimageImageComparison]
  refine ⟨fun h p => inferInstance, fun h => ?_⟩
  exact isIso_of_forall_epi_gr _ fun p => have := h p; inferInstance

/-- Stacks 0127, (1) ⇔ (6): `f` is strict iff `0 → gr(Ker f) → gr(A) → gr(B) → gr(Coker f) → 0` is
exact, when `A` has a top step. -/
@[stacks 0127 "(1) ⇔ (6), under a top step of `A`"]
theorem isStrict_iff_forall_exact_gr_kernel_ι_cokernel_π_of_hasTopStep [HasTopStep A.filtration] :
    IsStrict f ↔ ∀ p, (ComposableArrows.mk₃ ((gr p).map (kernel.ι f)) ((gr p).map f)
        ((gr p).map (cokernel.π f))).Exact ∧ Mono ((gr p).map (kernel.ι f)) ∧
        Epi ((gr p).map (cokernel.π f)) := by
  simp only [exact_grMap_kernel_ι_cokernel_π_iff_isIso]
  exact isStrict_iff_forall_isIso_gr_of_hasTopStep f

/-- Stacks 0127, (1) ⇔ (6): `f` is strict iff `0 → gr(Ker f) → gr(A) → gr(B) → gr(Coker f) → 0` is
exact, when `B` has a zero step. -/
@[stacks 0127 "(1) ⇔ (6), under a zero step of `B`"]
theorem isStrict_iff_forall_exact_gr_kernel_ι_cokernel_π_of_hasBotStep [HasBotStep B.filtration] :
    IsStrict f ↔ ∀ p, (ComposableArrows.mk₃ ((gr p).map (kernel.ι f)) ((gr p).map f)
        ((gr p).map (cokernel.π f))).Exact ∧ Mono ((gr p).map (kernel.ι f)) ∧
        Epi ((gr p).map (cokernel.π f)) := by
  simp only [exact_grMap_kernel_ι_cokernel_π_iff_isIso]
  exact isStrict_iff_forall_isIso_gr_of_hasBotStep f

/-- Stacks 0127: for `f : A ⟶ B` with `A` having a top step and `B` a zero step (in particular
for finite filtrations), the following are equivalent: (1) `f` is strict; (2) `Coim f → Im f` is an
isomorphism in `Fil(𝒜)`; (3) `gr(Coim f) → gr(Im f)` is an isomorphism; (4) `gr(Ker f) → gr(A) →
gr(B)` is exact; (5) `gr(A) → gr(B) → gr(Coker f)` is exact; (6) `0 → gr(Ker f) → gr(A) → gr(B) →
gr(Coker f) → 0` is exact. -/
@[stacks 0127 "for `A` with a top step and `B` with a zero step; in particular finite filtrations"]
theorem isStrict_tfae [HasTopStep A.filtration] [HasBotStep B.filtration] :
    [IsStrict f,
      IsIso (Abelian.coimageImageComparison f),
      ∀ p, IsIso ((gr p).map (Abelian.coimageImageComparison f)),
      ∀ p, ((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map (gr p)).Exact,
      ∀ p, ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map (gr p)).Exact,
      ∀ p, (ComposableArrows.mk₃ ((gr p).map (kernel.ι f)) ((gr p).map f)
        ((gr p).map (cokernel.π f))).Exact ∧ Mono ((gr p).map (kernel.ι f)) ∧
        Epi ((gr p).map (cokernel.π f))].TFAE := by
  tfae_have 1 ↔ 2 := isStrict_iff_isIso_coimageImageComparison f
  tfae_have 1 ↔ 3 := isStrict_iff_forall_isIso_gr_of_hasTopStep f
  tfae_have 1 ↔ 4 := isStrict_iff_forall_exact_gr_kernel_ι f
  tfae_have 1 ↔ 5 := isStrict_iff_forall_exact_gr_cokernel_π f
  tfae_have 1 ↔ 6 := isStrict_iff_forall_exact_gr_kernel_ι_cokernel_π_of_hasTopStep f
  tfae_finish

/-- Stacks 0127 (3) in `Gr(𝒜)`: `f` is strict iff the canonical `gr(Coim f) → gr(Im f)` is an
isomorphism, when `A` has a top step. -/
theorem isStrict_iff_isIso_grGraded_map_of_hasTopStep [HasTopStep A.filtration] :
    IsStrict f ↔ IsIso (grGraded.map (Abelian.coimageImageComparison f)) := by
  rw [isIso_grGraded_map_iff, isStrict_iff_forall_isIso_gr_of_hasTopStep]

/-- Stacks 0127 (3) in `Gr(𝒜)`: `f` is strict iff the canonical `gr(Coim f) → gr(Im f)` is an
isomorphism, when `B` has a zero step. -/
theorem isStrict_iff_isIso_grGraded_map_of_hasBotStep [HasBotStep B.filtration] :
    IsStrict f ↔ IsIso (grGraded.map (Abelian.coimageImageComparison f)) := by
  rw [isIso_grGraded_map_iff, isStrict_iff_forall_isIso_gr_of_hasBotStep]

end Criteria

section Gr

/-- Stacks: "this defines an additive functor `gr : Fil(𝒜) ⥤ Gr(𝒜)`". -/
instance [Preadditive C] [HasCokernels C] : (grGraded (C := C)).Additive where
  map_add := by intros; funext p; exact (gr p).map_add

variable [Abelian C]

/-- Exactness in `Gr(𝒜)` of `gr` applied to a short complex is exactness of every `gr^p`. -/
@[stacks 05QH "(1): exactness of `gr(A) → gr(B) → gr(C)` is exactness of every `gr^p`"]
lemma exact_map_grGraded_iff (S : ShortComplex (FilteredObject C ℤᵒᵖ)) :
    (S.map grGraded).Exact ↔ ∀ p, (S.map (gr p)).Exact := by
  rw [GradedObject.exact_iff_componentwise_exact]; rfl

/-- Short exactness in `Gr(𝒜)` of `gr` applied to a short complex is short exactness of every
`gr^p`. -/
lemma shortExact_map_grGraded_iff (S : ShortComplex (FilteredObject C ℤᵒᵖ)) :
    (S.map grGraded).ShortExact ↔ ∀ p, (S.map (gr p)).ShortExact := by
  rw [GradedObject.shortExact_iff_componentwise_shortExact]; rfl

end Gr

end FilteredObject

end CategoryTheory
