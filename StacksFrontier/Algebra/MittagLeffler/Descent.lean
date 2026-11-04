module


public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.Algebra.MittagLeffler.Criteria
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Faithfully flat descent of the Mittag-Leffler condition

Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module whose base change
`S ⊗[R] M` is a Mittag-Leffler `S`-module, in the intrinsic form 059E (1): every map from a
finitely presented module into it dominates and is dominated by a map into a finitely presented
module, domination being containment of the kernels of the maps `· ⊗ id_T`. Then `M` is a
Mittag-Leffler `R`-module (Stacks 05A5).

Writing `M = colim_{i ∈ I} M i` as a directed colimit of finitely presented `R`-modules, Stacks
059E turns the conclusion into its condition (2): for each `i` there is a `j ≥ i` such that
`M i → M j` dominates `M i → M`. Base change carries the system to a directed system of finitely
presented `S`-modules with colimit `S ⊗[R] M`, so the hypothesis and Stacks 059E over `S` supply a
`j ≥ i` for which `S ⊗[R] M i → S ⊗[R] M j` dominates `S ⊗[R] M i → S ⊗[R] M`, and faithful
flatness descends that containment of kernels to `R`.

## Main results

* `Stacks.MittagLeffler.FlatDescent.solution`: the statement of Stacks 05A5.

## Implementation notes

The source descends universal injectivity: it replaces the two maps out of `M i` by the pushout
`N` of `M j ← M i → M`, uses Lemma 0AUM to read the domination as universal injectivity of
`M j → N`, and descends *that* along `R → S`. The route here descends the containment of kernels
itself, which is what 059E's condition (2) asks for, so neither the pushout nor Lemma 0AUM is
needed: for an `R`-module `T` the comparison map
`N ⊗[R] T → (S ⊗[R] N) ⊗[S] (S ⊗[R] T)`, `x ↦ 1 ⊗ x` read through
`TensorProduct.AlgebraTensorModule.distribBaseChange`, is injective because `R → S` is faithfully
flat and natural in `N`, so a containment of kernels over `S` restricts to one over `R`
(`Stacks.MittagLeffler.FlatDescent.forall_ker_rTensor_le_of_baseChange`). This is the same use of
faithful flatness as the source's, one step earlier in the argument.

That every module is a directed colimit of finitely presented modules is Stacks 00HA; the form
needed here is a colimit cocone in `ModuleCat.{v} R` on a system indexed by a preorder in
`Type v`, with the legs available as named maps so that they can be base changed, which the
repository's `Module.exists_linearEquiv_directLimit_finitePresentation` (an existential without
named legs) does not provide. The system is therefore rebuilt here: the index is a finite
set `T ⊆ M` of generators together with a finite set of elements of the free module on `M` whose
members supported on `T` and killed by the evaluation map are the relations imposed, and the member
at that index is `R^T` modulo those relations. Scalars are transported into `Type v` by `Shrink`,
available because `R` is `v`-small, so that every module in the argument is an object of
`ModuleCat.{v} R` as 059E requires.

Base change preserves this colimit by hand rather than through `ModuleCat.extendScalars`, whose
`S`-module structure comes from `RingHom.toAlgebra` and so is not the one the statement's
`Algebra R S` provides. The colimit of the base changed system is computed as a direct limit: an
element of `S ⊗[R] M i` killed by `S ⊗[R] M i → S ⊗[R] M` comes, by flatness of `S`, from
`S ⊗[R] Ker(M i → M)`, and each generator `s ⊗ y` of the latter dies at the index obtained from
`i` by adjoining the relation `y`.

## References

* [StacksProject 05A5](https://stacks.math.columbia.edu/tag/05A5)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
* [StacksProject 00HA](https://stacks.math.columbia.edu/tag/00HA)
-/


open CategoryTheory Limits
open scoped TensorProduct

namespace Stacks.MittagLeffler.FlatDescent

open Stacks.MittagLeffler.PresentingSystem

-- The index set of the presenting system is a product of preorders; its category structure must
-- be the one coming from that preorder, not the product of the two categories.
attribute [-instance] CategoryTheory.uniformProd CategoryTheory.prod' CategoryTheory.prod

/-! ### Descending a containment of kernels along a faithfully flat ring map -/

section Descent

/-- The comparison map `N ⊗[R] T → (S ⊗[R] N) ⊗[S] (S ⊗[R] T)`, `x ↦ 1 ⊗ x` read through
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
private noncomputable def baseChangeComparison (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] (N T : Type v) [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T] :
    N ⊗[R] T →ₗ[R] (S ⊗[R] N) ⊗[S] (S ⊗[R] T) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R S N T).restrictScalars R ∘ₗ
    TensorProduct.mk R S (N ⊗[R] T) 1

private theorem baseChangeComparison_tmul (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] (N T : Type v) [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]
    (n : N) (t : T) :
    baseChangeComparison R S N T (n ⊗ₜ[R] t)
      = ((1 : S) ⊗ₜ[R] n) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] t) := by
  simp [baseChangeComparison, TensorProduct.AlgebraTensorModule.distribBaseChange]

private theorem baseChangeComparison_injective (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] (N T : Type v) [AddCommGroup N] [Module R N]
    [AddCommGroup T] [Module R T] : Function.Injective (baseChangeComparison R S N T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [baseChangeComparison, LinearMap.comp_apply] at hx
  have h1 : (1 : S) ⊗ₜ[R] x = 0 := by
    have := (LinearEquiv.map_eq_zero_iff
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R S N T).restrictScalars R)).mp hx
    simpa using this
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff R (N ⊗[R] T) x).mp h1

private theorem baseChangeComparison_naturality (R : Type u) [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] {N C T : Type v} [AddCommGroup N] [Module R N] [AddCommGroup C]
    [Module R C] [AddCommGroup T] [Module R T] (b : N →ₗ[R] C) (x : N ⊗[R] T) :
    (b.baseChange S).rTensor (S ⊗[R] T) (baseChangeComparison R S N T x)
      = baseChangeComparison R S C T (b.rTensor T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n t => simp [baseChangeComparison_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Domination descends along a faithfully flat ring map: if the base change of `a` to `S`
dominates the base change of `b`, then `a` dominates `b`. -/
private theorem forall_ker_rTensor_le_of_baseChange (R : Type u) [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] {A B C : Type v} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (a : A →ₗ[R] B)
    (b : A →ₗ[R] C)
    (h : ∀ (T' : Type v) [AddCommGroup T'] [Module S T'],
      LinearMap.ker ((a.baseChange S).rTensor T') ≤ LinearMap.ker ((b.baseChange S).rTensor T'))
    (T : Type v) [AddCommGroup T] [Module R T] :
    LinearMap.ker (a.rTensor T) ≤ LinearMap.ker (b.rTensor T) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hax : (a.baseChange S).rTensor (S ⊗[R] T) (baseChangeComparison R S A T x) = 0 := by
    rw [baseChangeComparison_naturality, hx, map_zero]
  have h2 := h (S ⊗[R] T) (LinearMap.mem_ker.mpr hax)
  rw [LinearMap.mem_ker, baseChangeComparison_naturality] at h2
  exact baseChangeComparison_injective R S C T (by rw [h2, map_zero])

end Descent

/-! ### A presenting system of finitely presented modules -/

section System

attribute [local simp] freeProj_single trans_mk toM_mk

variable (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]

private noncomputable instance : DecidableEq (Idx R M) := Classical.decEq _

private instance : IsDirectedOrder (Idx R M) := by
  classical
  exact ⟨fun a b ↦ ⟨(a.1 ∪ b.1, a.2 ∪ b.2),
    ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩⟩

private instance directedSystem_trans :
    DirectedSystem (sys R M) fun i j h ↦ (trans R M i j h : _ → _) where
  map_self i x := by
    obtain ⟨y, rfl⟩ := (rels R M i).mkQ_surjective x
    exact congrArg _ (Subtype.ext rfl)
  map_map {i j k} hij hjk x := by
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg _ (Subtype.ext rfl)

/-- Each member of the presenting system is a finitely presented `R`-module: the free module on
its finite set of generators, modulo the span of finitely many relations. -/
public instance finitePresentation_sys (i : Idx R M) :
    Module.FinitePresentation R (sys R M i) := by
  have := finitePresentation_freePart R M i.1
  refine Module.finitePresentation_of_surjective (rels R M i).mkQ
    (rels R M i).mkQ_surjective ?_
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_span
    (Set.Finite.subset (i.2.finite_toSet.preimage Subtype.coe_injective.injOn) fun _ hy ↦ hy.1)

/-- Every element of `M` is hit by one of the members of the presenting system. -/
private theorem exists_toM_eq (m : M) : ∃ (i : Idx R M) (x : sys R M i), toM R M i x = m := by
  refine ⟨({m}, ∅), Submodule.Quotient.mk
    ⟨Finsupp.single m ((Shrink.linearEquiv R R).symm 1),
      Finsupp.single_mem_supported R _ (by simp)⟩, ?_⟩
  rw [toM_mk]
  simp

/-- An element of a member of the presenting system which dies in `M` already dies at a later
index: adjoining it to the chosen relations produces such an index. -/
private theorem exists_trans_eq_zero (i : Idx R M) (x : sys R M i) (hx : toM R M i x = 0) :
    ∃ (j : Idx R M) (h : i ≤ j), trans R M i j h x = 0 := by
  classical
  obtain ⟨y, rfl⟩ := (rels R M i).mkQ_surjective x
  refine ⟨(i.1, insert (↑y : M →₀ Shrink.{v} R) i.2),
    ⟨le_rfl, Finset.subset_insert _ _⟩, ?_⟩
  rw [Submodule.mkQ_apply, trans_mk]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Submodule.subset_span ⟨Finset.mem_insert_self _ _, by simpa using hx⟩)

/-! #### The colimit over `R` -/

/-- A map out of a direct limit is injective if every element of a component killed by the
component map is killed by a later transition map. -/
private theorem lift_injective_of_exists_map_eq_zero {A ι : Type*} [Ring A] [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Module A (G i)] {f : ∀ i j, i ≤ j → G i →ₗ[A] G j} {P : Type*} [AddCommGroup P]
    [Module A P] (g : ∀ i, G i →ₗ[A] P) (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (h : ∀ i x, g i x = 0 → ∃ j hij, f i j hij x = 0) :
    Function.Injective (Module.DirectLimit.lift A ι G f g hg) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨i, w, rfl⟩ := Module.DirectLimit.exists_of z
  rw [Module.DirectLimit.lift_of] at hz
  obtain ⟨j, hij, hzero⟩ := h i w hz
  rw [← Module.DirectLimit.of_f (hij := hij), hzero, map_zero]

/-- The map from the direct limit of the presenting system to `M`. -/
private noncomputable def dlLift : Module.DirectLimit (sys R M) (trans R M) →ₗ[R] M :=
  Module.DirectLimit.lift R (Idx R M) (sys R M) (trans R M) (toM R M)
    fun i j h x ↦ toM_trans R M i j h x

@[local simp] private theorem dlLift_of (i : Idx R M) (x : sys R M i) :
    dlLift R M (Module.DirectLimit.of R _ _ _ i x) = toM R M i x :=
  Module.DirectLimit.lift_of _ _ _

private theorem dlLift_bijective : Function.Bijective (dlLift R M) := by
  refine ⟨lift_injective_of_exists_map_eq_zero _ _ (exists_trans_eq_zero R M), fun m ↦ ?_⟩
  obtain ⟨i, x, hx⟩ := exists_toM_eq R M m
  exact ⟨Module.DirectLimit.of R _ _ _ i x, by rw [dlLift_of, hx]⟩

/-- The direct limit of the presenting system is `M`. -/
private noncomputable def dlEquiv : Module.DirectLimit (sys R M) (trans R M) ≃ₗ[R] M :=
  LinearEquiv.ofBijective (dlLift R M) (dlLift_bijective R M)

@[local simp] private theorem dlEquiv_of (i : Idx R M) (x : sys R M i) :
    dlEquiv R M (Module.DirectLimit.of R _ _ _ i x) = toM R M i x := dlLift_of R M i x

/-- The presenting system as a functor to `ModuleCat R`. -/
private noncomputable abbrev diag : Idx R M ⥤ ModuleCat.{v} R :=
  ModuleCat.directLimitDiagram (sys R M) (trans R M)

/-- The colimit cocone on the presenting system, with vertex `M`. -/
private noncomputable def coc : Cocone (diag R M) :=
  Cocone.mk (ModuleCat.of R M)
    { app := fun i ↦ ModuleCat.ofHom (toM R M i)
      naturality := fun i j h ↦ by ext y; exact toM_trans R M i j h.le y }

private noncomputable def isColimitCoc : IsColimit (coc R M) :=
  IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit (sys R M) (trans R M))
    (Cocone.ext (LinearEquiv.toModuleIso (dlEquiv R M)) fun i ↦ by
      ext y; exact dlEquiv_of R M i y)

/-! #### The colimit over `S` -/

variable (S : Type v) [CommRing S] [Algebra R S]

/-- The base change of the presenting system to `S`. -/
private noncomputable abbrev sysBC (i : Idx R M) : Type v := S ⊗[R] sys R M i

/-- The transition maps of the base changed system. -/
private noncomputable def transBC (i j : Idx R M) (h : i ≤ j) :
    sysBC R M S i →ₗ[S] sysBC R M S j := (trans R M i j h).baseChange S

private instance directedSystem_transBC :
    DirectedSystem (sysBC R M S) fun i j h ↦ (transBC R M S i j h : _ → _) :=
  DirectedSystem.lTensor (R := R) (M := S) (directedSystem_trans R M)

/-- The base change of the canonical maps to `M`. -/
private noncomputable def toMBC (i : Idx R M) : sysBC R M S i →ₗ[S] S ⊗[R] M :=
  (toM R M i).baseChange S

private theorem toMBC_transBC (i j : Idx R M) (h : i ≤ j) (x : sysBC R M S i) :
    toMBC R M S j (transBC R M S i j h x) = toMBC R M S i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s y => simp [toMBC, transBC, LinearMap.baseChange_tmul, toM_trans]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The key step for the base changed colimit: an element of `S ⊗[R] M i` killed by the map to
`S ⊗[R] M` already dies at a later index. Flatness of `S` writes it as the image of an element of
`S ⊗[R] Ker(M i → M)`, and each pure tensor there dies by `exists_trans_eq_zero`. -/
private theorem exists_transBC_eq_zero [Module.Flat R S] (i : Idx R M) (x : sysBC R M S i)
    (hx : toMBC R M S i x = 0) :
    ∃ (j : Idx R M) (h : i ≤ j), transBC R M S i j h x = 0 := by
  have hex : Function.Exact ((LinearMap.ker (toM R M i)).subtype.lTensor S)
      ((toM R M i).lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map (toM R M i))
  obtain ⟨w, hw⟩ := (hex x).mp hx
  clear hx
  subst hw
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨i, le_rfl, by simp⟩
  | tmul s y =>
      obtain ⟨j, hij, hzero⟩ := exists_trans_eq_zero R M i (y : sys R M i) y.2
      refine ⟨j, hij, ?_⟩
      change (trans R M i j hij).baseChange S _ = 0
      simp only [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, Submodule.subtype_apply]
      rw [hzero, TensorProduct.tmul_zero]
  | add w₁ w₂ h₁ h₂ =>
      obtain ⟨j₁, hij₁, hz₁⟩ := h₁
      obtain ⟨j₂, hij₂, hz₂⟩ := h₂
      obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ · : Idx R M → Idx R M → Prop) j₁ j₂
      refine ⟨k, hij₁.trans hk₁, ?_⟩
      have later : ∀ {j'} (h₁ : i ≤ j') (h₂ : j' ≤ k) (y : sysBC R M S i),
          transBC R M S i j' h₁ y = 0 → transBC R M S i k (h₁.trans h₂) y = 0 := fun h₁ h₂ y hy ↦ by
        rw [← DirectedSystem.map_map (f := fun i j h ↦ (transBC R M S i j h : _ → _)) h₁ h₂,
          hy, map_zero]
      simp only [map_add, later hij₁ hk₁ _ hz₁, later hij₂ hk₂ _ hz₂, add_zero]

/-- The map from the direct limit of the base changed system to `S ⊗[R] M`. -/
private noncomputable def dlLiftBC : Module.DirectLimit (sysBC R M S) (transBC R M S) →ₗ[S]
    S ⊗[R] M :=
  Module.DirectLimit.lift S (Idx R M) (sysBC R M S) (transBC R M S) (toMBC R M S)
    fun i j h x ↦ toMBC_transBC R M S i j h x

@[local simp] private theorem dlLiftBC_of (i : Idx R M) (x : sysBC R M S i) :
    dlLiftBC R M S (Module.DirectLimit.of S _ _ _ i x) = toMBC R M S i x :=
  Module.DirectLimit.lift_of _ _ _

private theorem dlLiftBC_bijective [Module.Flat R S] : Function.Bijective (dlLiftBC R M S) := by
  refine ⟨lift_injective_of_exists_map_eq_zero _ _ (exists_transBC_eq_zero R M S), fun z ↦ ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s m =>
      obtain ⟨i, x, hx⟩ := exists_toM_eq R M m
      refine ⟨Module.DirectLimit.of S _ _ _ i (s ⊗ₜ[R] x), ?_⟩
      rw [dlLiftBC_of, toMBC, LinearMap.baseChange_tmul, hx]
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁⟩ := h₁
      obtain ⟨w₂, hw₂⟩ := h₂
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂]⟩

/-- The direct limit of the base changed system is `S ⊗[R] M`. -/
private noncomputable def dlEquivBC [Module.Flat R S] :
    Module.DirectLimit (sysBC R M S) (transBC R M S) ≃ₗ[S] S ⊗[R] M :=
  LinearEquiv.ofBijective (dlLiftBC R M S) (dlLiftBC_bijective R M S)

@[local simp] private theorem dlEquivBC_of [Module.Flat R S] (i : Idx R M) (x : sysBC R M S i) :
    dlEquivBC R M S (Module.DirectLimit.of S _ _ _ i x) = toMBC R M S i x :=
  dlLiftBC_of R M S i x

/-- The base changed system as a functor to `ModuleCat S`. -/
private noncomputable abbrev diagBC : Idx R M ⥤ ModuleCat.{v} S :=
  ModuleCat.directLimitDiagram (sysBC R M S) (transBC R M S)

/-- The colimit cocone on the base changed system, with vertex `S ⊗[R] M`. -/
private noncomputable def cocBC : Cocone (diagBC R M S) :=
  Cocone.mk (ModuleCat.of S (S ⊗[R] M))
    { app := fun i ↦ ModuleCat.ofHom (toMBC R M S i)
      naturality := fun i j h ↦ by ext y; exact toMBC_transBC R M S i j h.le y }

private noncomputable def isColimitCocBC [Module.Flat R S] : IsColimit (cocBC R M S) :=
  IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit (sysBC R M S) (transBC R M S))
    (Cocone.ext (LinearEquiv.toModuleIso (dlEquivBC R M S)) fun i ↦ by
      ext y; exact dlEquivBC_of R M S i y)

end System

/-- Stacks 05A5, with the Mittag-Leffler condition written out in the intrinsic form 059E (1):
if `R → S` is faithfully flat and `S ⊗[R] M` is a Mittag-Leffler `S`-module, then `M` is a
Mittag-Leffler `R`-module. -/
public theorem solution {R : Type u} [CommRing R]
    [Small.{v} R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] S ⊗[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module S T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T) := by
  have hfpR : ∀ i : Idx R M, Module.FinitePresentation R ((diag R M).obj i : Type v) :=
    fun i ↦ inferInstanceAs (Module.FinitePresentation R (sys R M i))
  have hfpS : ∀ i : Idx R M, Module.FinitePresentation S ((diagBC R M S).obj i : Type v) :=
    fun i ↦ inferInstanceAs (Module.FinitePresentation S (S ⊗[R] sys R M i))
  -- Condition (1) of 059E for the base change, transcribed from `hM`.
  have honeBC : ∀ (P : ModuleCat.{v} S) [Module.FinitePresentation S P]
      (f : P ⟶ (cocBC R M S).pt),
      ∃ (Q : ModuleCat.{v} S) (_ : Module.FinitePresentation S Q) (g : P ⟶ Q),
        ∀ T : ModuleCat.{v} S,
          LinearMap.ker (f.hom.rTensor T) = LinearMap.ker (g.hom.rTensor T) := by
    intro P _ f
    obtain ⟨Q, _, _, _, g, hg⟩ := hM P f.hom
    exact ⟨ModuleCat.of S Q, ‹_›, ModuleCat.ofHom g, fun T ↦ hg T⟩
  -- Condition (2) of 059E over `S`, for the base changed system.
  have htwoBC := (((diagBC R M S).tfae_isMittagLefflerSystem
    (isColimitCocBC R M S)).out 1 2).mp honeBC
  -- Condition (2) of 059E over `R`, by faithfully flat descent.
  have htwo : ∀ i : Idx R M, ∃ (j : Idx R M) (u : i ⟶ j), ∀ T : ModuleCat.{v} R,
      LinearMap.ker (((coc R M).ι.app i).hom.rTensor T)
        ≤ LinearMap.ker (((diag R M).map u).hom.rTensor T) := by
    intro i
    obtain ⟨j, u, hu⟩ := htwoBC i
    refine ⟨j, u, fun T ↦ ?_⟩
    exact forall_ker_rTensor_le_of_baseChange R S (toM R M i) (trans R M i j u.le)
      (fun T' _ _ ↦ hu (ModuleCat.of S T')) T
  -- Condition (1) of 059E over `R`.
  have hone := (((diag R M).tfae_isMittagLefflerSystem (isColimitCoc R M)).out 2 1).mp htwo
  intro P _ _ _ f
  obtain ⟨Q, _, g, hg⟩ := hone (ModuleCat.of R P) (ModuleCat.ofHom f)
  exact ⟨Q, inferInstance, inferInstance, ‹_›, g.hom, fun T _ _ ↦ hg (ModuleCat.of R T)⟩

end Stacks.MittagLeffler.FlatDescent

/-!
# Faithfully flat descent of the Mittag-Leffler condition

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) when the equivalent conditions of
Proposition 059E hold for it. Only one of those conditions is intrinsic to `M`, namely
condition (1), and it is the one used here: for every finitely presented `R`-module `P` and every
module map `f : P → M` there are a finitely presented `R`-module `Q` and a module map `g : P → Q`
which dominate each other, that is `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T`.

This file states Stacks 05A5: the Mittag-Leffler condition descends along a faithfully flat ring
map `R → S`, so that a module whose base change to `S` is Mittag-Leffler is already Mittag-Leffler.
The source's proof writes `M = colim_{i ∈ I} M i` as a directed colimit of finitely presented
`R`-modules and reads the conclusion in the form 059E (2): for each `i` there is a `j ≥ i` such
that `M i → M j` dominates `M i → M`. Forming the pushout `N` of `M j ← M i → M`, this asks
(Lemma 0AUM) for a `j` with `M j → N` universally injective. Tensoring with `S` again gives a
pushout square, and `M ⊗_R S = colim_i M i ⊗_R S` exhibits the base change as a directed colimit of
finitely presented `S`-modules, so the Mittag-Leffler hypothesis yields a `j ≥ i` for which
`M j ⊗_R S → N ⊗_R S` is universally injective; faithful flatness of `R → S` then descends
universal injectivity to `M j → N`.

## Main results

* `Module.mittagLeffler_of_mittagLeffler_tensorProduct`: for `R → S` faithfully flat, an
  `R`-module whose base change to `S` is a Mittag-Leffler `S`-module is a Mittag-Leffler
  `R`-module.

## Implementation notes

Mathlib has no predicate for a Mittag-Leffler module: its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
which is condition (4) of 059E rather than the condition on a module, and it presupposes the choice
of a directed system presenting the module. So the condition is spelled out inline on both sides of
the implication, in the intrinsic form 059E (1) — the one condition of that proposition which is
intrinsic to the module, needing no such choice — the two sides differing only in the ring and the
module, exactly as in the sibling results 05A3
(`Module.baseChange_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span_and_projective`,
the ascending direction), 05CN (`Module.mittagLeffler_tensorProduct`) and 05CQ
(`Module.mittagLeffler_trans`). Mutual domination is equality of the kernels of the tensored maps,
`f ⊗ id_T` being `f.rTensor T`, as in 059D
(`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`).

The source's base change is `M ⊗_R S`; the statement writes `S ⊗[R] M`, Mathlib's convention for a
base change (`Module.Flat.baseChange`, `Module.Flat.of_flat_tensorProduct`) and the only one of the
two orders carrying an `S`-module structure in Mathlib, as in 05A3. The two are identified by
`TensorProduct.comm`, and since the hypothesis is a statement about the `S`-action, having that
action be the pinned canonical one — the `S`-action on the left factor — is what makes it the
source's hypothesis rather than a statement about an unspecified action. The name mutates that of
the Mathlib sibling for the same descent, `Module.Flat.of_flat_tensorProduct`.

The faithfully flat ring map is `[Module.FaithfullyFlat R S]` for `[Algebra R S]`, Mathlib's
spelling. The module and the second ring share a universe, `S M : Type v`, so that `S ⊗[R] M` lies
in `Type v` and both occurrences of condition 059E (1) range over the same universe; `R : Type u`
is `v`-small, as in 059D, 05A3, 05CN and 05CQ, which is what makes the quantifier over
`P Q T : Type v` in the conclusion the source's quantifier over all finitely presented `R`-modules
and all test modules — for a `v`-small `R` every finitely presented `R`-module is isomorphic to one
in `Type v`, and the condition is invariant under isomorphism. On the hypothesis side `S` lies in
`Type v`, so the same holds there with no further assumption.

Faithfulness. (1) No hypothesis is dead: the Mittag-Leffler condition on `S ⊗[R] M` is the
antecedent of the conclusion, and faithful flatness cannot be weakened to flatness — for `R = ℤ`,
`S = ℚ` and `M = ℚ` the flat map `ℤ → ℚ` has `ℚ ⊗_ℤ ℚ ≅ ℚ` finitely presented over `ℚ`, hence
Mittag-Leffler, while `ℚ` is not a Mittag-Leffler `ℤ`-module (flat and countably generated but not
projective, Theorem 059Z); the one instance argument not used by the mathematics is `Small.{v} R`,
which calibrates the quantifiers of the conclusion. (2) The scalars and the base are the source's:
the hypothesis quantifies over `S`-modules and `S`-linear maps and tensors over `S`, the conclusion
over `R`-modules and `R`-linear maps and tensors over `R`, and the tensor product `S ⊗[R] M` is
over `R` along `algebraMap R S`. (3) Where the source names a canonical map the statement pins it:
the `S`-action on `S ⊗[R] M` is the canonical one on the left factor rather than an abstract module
structure making `S ⊗[R] M` a base change, and the maps whose kernels are compared are
`f.rTensor T` and `g.rTensor T` rather than arbitrary maps `P ⊗ T → M ⊗ T` and `P ⊗ T → Q ⊗ T`;
only `Q` and `g` are existentially quantified, as they are in 059E (1) itself. (4) The
instantiation is not degenerate: for `R = ℤ`, `S = ℤ[X]` (free, hence faithfully flat) and
`M = ⨁_{n : ℕ} ℤ` the hypothesis holds, `S ⊗_ℤ M` being a free `S`-module and so Mittag-Leffler by
Example 059R (2), and the conclusion says something non-vacuous about `M`; and the conclusion is
not satisfied by every module, `ℚ` not being a Mittag-Leffler `ℤ`-module, so the implication is not
vacuously true either.

## References

* [StacksProject 05A5](https://stacks.math.columbia.edu/tag/05A5)
-/

open scoped TensorProduct

/-- **Stacks 05A5.** Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module. If the
`S`-module `S ⊗_R M` is Mittag-Leffler, then `M` is Mittag-Leffler. The Mittag-Leffler condition is
spelled out in the intrinsic form 059E (1): every map `f` from a finitely presented module into the
module in question dominates and is dominated by a map `g` into a finitely presented module,
domination meaning equality of the kernels of the maps `· ⊗ id_T`. -/
@[stacks 05A5 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 05A3, 05CN and
  05CQ. The base change is written `S ⊗[R] M`, Mathlib's order, the source writing `M ⊗_R S`.",
  sga "3 VIB 11.8.2"]
public theorem Module.mittagLeffler_of_mittagLeffler_tensorProduct {R : Type u} [CommRing R]
    [Small.{v} R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] S ⊗[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module S T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T) :=
  Stacks.MittagLeffler.FlatDescent.solution hM

end
