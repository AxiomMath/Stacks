module

public import Mathlib.Algebra.Module.FinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Directed colimits of finitely presented modules

Every module is a directed colimit of finitely presented modules (Stacks tag 00HA).
We also define relations among finite families of module elements (Stacks tag 07N8).
-/

@[expose] public section

universe u v

variable (R : Type u) [Ring R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The free module on the elements of `M`. -/
private abbrev Fr : Type v := M →₀ Shrink.{v} R

/-- The canonical surjection from the free module on `M` to `M`. -/
private noncomputable def proj : Fr R M →ₗ[R] M := Finsupp.linearCombination R (id : M → M) ∘ₗ
  (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)).toLinearMap

private theorem proj_single (m : M) (r : Shrink.{v} R) :
    proj R M (Finsupp.single m r) = Shrink.linearEquiv R R r • m := by
  simp [proj]

/-- The kernel of `proj`, i.e. the relations. -/
private noncomputable abbrev relations : Submodule R (Fr R M) := LinearMap.ker (proj R M)

/-- The submodule of the free module supported on a finite set `S`. -/
private noncomputable abbrev supportedOn (S : Finset M) : Submodule R (Fr R M) :=
  Finsupp.supported (Shrink.{v} R) R (↑S : Set M)

/-- The index set: a finite set of generators `S` together with a finite set of
relations `T` (elements of the kernel) all supported on `S`. -/
private abbrev Idx : Type v :=
  { p : Finset M × Finset (relations R M) // ∀ t ∈ p.snd, ((t : Fr R M)).support ⊆ p.fst }

private noncomputable instance : DecidableEq (Idx R M) := Classical.decEq _

private instance : Nonempty (Idx R M) := ⟨⟨(∅, ∅), by simp⟩⟩

private instance : IsDirected (Idx R M) (· ≤ ·) := by
  classical
  constructor
  rintro ⟨⟨Sa, Ta⟩, ha⟩ ⟨⟨Sb, Tb⟩, hb⟩
  refine ⟨⟨(Sa ∪ Sb, Ta ∪ Tb), fun t ht => ?_⟩,
    ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩
  rcases Finset.mem_union.mp ht with h | h
  · exact (ha t h).trans Finset.subset_union_left
  · exact (hb t h).trans Finset.subset_union_right

/-- Each relation in `p.1.2` is supported on the generator set `p.1.1`. -/
private theorem coe_mem_supportedOn (p : Idx R M) (t : relations R M) (ht : t ∈ p.1.2) :
    (t : Fr R M) ∈ supportedOn R M p.1.1 := by
  rw [Finsupp.mem_supported]
  exact_mod_cast p.property t ht

/-- The submodule of `supportedOn S` spanned by the relations in `T`. -/
private noncomputable abbrev rho (p : Idx R M) : Submodule R (supportedOn R M p.1.1) :=
  Submodule.span R
    (Set.range (fun t : p.val.snd =>
      (⟨(t.val : Fr R M), coe_mem_supportedOn R M p t.val t.property⟩ :
        supportedOn R M p.val.fst)))

/-- The element of `rho p` given by a relation `t ∈ p.1.2`. -/
private theorem mk_mem_rho (p : Idx R M) (t : relations R M) (ht : t ∈ p.1.2) :
    (⟨t, coe_mem_supportedOn R M p t ht⟩ : supportedOn R M p.1.1) ∈ rho R M p :=
  Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩

/-- `rho p` lies in a submodule containing all the relations of `p`. -/
private theorem rho_le (p : Idx R M) (N : Submodule R (supportedOn R M p.1.1))
    (h : ∀ t (ht : t ∈ p.1.2), (⟨t, coe_mem_supportedOn R M p t ht⟩ : supportedOn R M p.1.1) ∈ N) :
    rho R M p ≤ N :=
  Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact h t t.2)

/-- The module at index `p`: `supportedOn S` modulo the relations. -/
private abbrev Gm (p : Idx R M) : Type v := (supportedOn R M p.val.fst) ⧸ (rho R M p)

private theorem finitePresentation_gm (p : Idx R M) : Module.FinitePresentation R (Gm R M p) := by
  have hfp : Module.FinitePresentation R (supportedOn R M p.val.fst) :=
    (LinearEquiv.finitePresentation_iff ((Finsupp.supportedEquivFinsupp (↑p.val.fst : Set M)).trans
      (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)))).mpr inferInstance
  apply Module.finitePresentation_of_surjective (rho R M p).mkQ (rho R M p).mkQ_surjective
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_span (Set.finite_range _)

/-- Inclusion of supported submodules for `p ≤ q`. -/
private theorem supportedOn_mono {p q : Idx R M} (h : p ≤ q) :
    supportedOn R M p.1.1 ≤ supportedOn R M q.1.1 :=
  Finsupp.supported_mono (by exact_mod_cast h.left)

/-- The transition map `Gm p → Gm q` for `p ≤ q`. -/
private noncomputable def transMap {p q : Idx R M} (h : p ≤ q) : Gm R M p →ₗ[R] Gm R M q :=
  Submodule.mapQ (rho R M p) (rho R M q) (Submodule.inclusion (supportedOn_mono R M h)) 
    (rho_le R M p _ fun t ht => mk_mem_rho R M q t (h.right ht))

private theorem transMap_mk {p q : Idx R M} (h : p ≤ q) (a : supportedOn R M p.1.1) :
    transMap R M h (Submodule.Quotient.mk a)
      = Submodule.Quotient.mk (Submodule.inclusion (supportedOn_mono R M h) a) := by
  rw [transMap, Submodule.mapQ_apply]

private theorem directedSystem_transMap :
    DirectedSystem (Gm R M) (fun _ _ h => transMap R M h) := by
  refine ⟨fun _ x => ?_, fun _ _ _ _ _ x => ?_⟩ <;>
    induction x using Submodule.Quotient.induction_on <;>
    simp only [transMap_mk] <;>
    exact congrArg Submodule.Quotient.mk (Subtype.ext (by simp))

/-- The restriction of `proj` to `supportedOn S`. -/
private noncomputable abbrev projS (p : Idx R M) : supportedOn R M p.1.1 →ₗ[R] M :=
  (proj R M).comp (supportedOn R M p.val.fst).subtype

/-- `rho p ≤ ker (projS p)`. -/
private theorem rho_le_ker (p : Idx R M) : rho R M p ≤ LinearMap.ker (projS R M p) :=
  rho_le R M p _ fun t _ => t.property

/-- The map `Gm p → M`. -/
private noncomputable def phi (p : Idx R M) : Gm R M p →ₗ[R] M :=
  Submodule.liftQ (rho R M p) (projS R M p) (rho_le_ker R M p)

private theorem phi_mk (p : Idx R M) (x : supportedOn R M p.1.1) :
    phi R M p (Submodule.Quotient.mk x) = proj R M (x : Fr R M) := by
  rw [phi, Submodule.liftQ_apply, projS, LinearMap.comp_apply, Submodule.subtype_apply]

/-- Compatibility of `phi` with transition maps. -/
private theorem phi_transMap {p q : Idx R M} (h : p ≤ q) (x : Gm R M p) :
    phi R M q (transMap R M h x) = phi R M p x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    rw [transMap_mk, phi_mk, phi_mk, Submodule.coe_inclusion]

/-- An element of `Gm p` killed by `phi p` becomes zero after a transition map. -/
private theorem exists_transMap_eq_zero (p : Idx R M) (a : supportedOn R M p.1.1)
    (ha : proj R M (a : Fr R M) = 0) :
    ∃ (q : Idx R M) (h : p ≤ q), transMap R M h (Submodule.Quotient.mk a) = 0 := by
  classical
  have hsupp : (a : Fr R M).support ⊆ p.val.fst := by
    exact_mod_cast (Finsupp.mem_supported _ _).mp a.property
  let arel : relations R M := ⟨(a : Fr R M), LinearMap.mem_ker.mpr ha⟩
  let q : Idx R M :=
    ⟨(p.val.fst, insert arel p.val.snd), Finset.forall_mem_insert _ _ _ |>.mpr ⟨hsupp, p.property⟩⟩
  refine ⟨q, ⟨subset_refl _, Finset.subset_insert _ _⟩, ?_⟩
  rw [transMap_mk, Submodule.Quotient.mk_eq_zero, Submodule.inclusion_apply]
  exact mk_mem_rho R M q arel (Finset.mem_insert_self _ _)

/-- Every element of `M` is in the image of some `phi p`. -/
private theorem exists_phi_eq (m : M) : ∃ p x, phi R M p x = m := by
  let p : Idx R M := ⟨(({m} : Finset M), ∅), by simp⟩
  refine ⟨p, Submodule.Quotient.mk
    ⟨Finsupp.single m ((Shrink.linearEquiv R R).symm 1),
      Finsupp.single_mem_supported _ _ (Finset.mem_singleton_self m)⟩, ?_⟩
  rw [phi_mk, proj_single, LinearEquiv.apply_symm_apply, one_smul]

/-- Every `R`-module `M` is the colimit of a directed system of finitely
presented `R`-modules in the universe of `M`, provided `R` is small in that universe. -/
@[stacks 00HA]
theorem Module.exists_linearEquiv_directLimit_finitePresentation
    (R : Type u) [Ring R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (ι : Type v) (_ : Preorder ι) (_ : IsDirectedOrder ι) (_ : Nonempty ι)
      (_ : DecidableEq ι)
      (G : ι → Type v) (_ : (i : ι) → AddCommGroup (G i))
      (_ : (i : ι) → Module R (G i))
      (f : (i j : ι) → i ≤ j → (G i →ₗ[R] G j))
      (_ : DirectedSystem G (fun i j h => f i j h)),
      -- each module in the system is finitely presented
      (∀ i, Module.FinitePresentation R (G i)) ∧
      -- and M is isomorphic to the colimit of the system
      Nonempty (M ≃ₗ[R] Module.DirectLimit G f) := by
  refine ⟨Idx R M, inferInstance, inferInstance, inferInstance, inferInstance,
    Gm R M, inferInstance, inferInstance, (fun i j h => transMap R M h),
    directedSystem_transMap R M, finitePresentation_gm R M, ?_⟩
  let g := Module.DirectLimit.lift R (Idx R M) (Gm R M) (fun i j h => transMap R M h) (phi R M)
    (fun i j hij x => phi_transMap R M hij x)
  refine ⟨(LinearEquiv.ofBijective g ⟨?_, fun m => ?_⟩).symm⟩
  · rw [← LinearMap.ker_eq_bot (M := Module.DirectLimit (Gm R M) fun i j h => transMap R M h),
      Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨p, x, rfl⟩ := Module.DirectLimit.exists_of z
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      rw [LinearMap.mem_ker, Module.DirectLimit.lift_of, phi_mk] at hz
      obtain ⟨q, hpq, hzero⟩ := exists_transMap_eq_zero R M p a hz
      rw [← Module.DirectLimit.of_f (hij := hpq), hzero, map_zero]
  · obtain ⟨p, x, rfl⟩ := exists_phi_eq R M m
    exact ⟨Module.DirectLimit.of R (Idx R M) (Gm R M) _ p x, Module.DirectLimit.lift_of ..⟩

/-- Every module is a directed colimit of finitely presented modules in the maximum of the
universes of the ring and the module. -/
@[stacks 00HA "no smallness assumption on the ring"]
theorem Module.exists_linearEquiv_directLimit_finitePresentation_max
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (ι : Type (max u v)) (_ : Preorder ι) (_ : IsDirectedOrder ι) (_ : Nonempty ι)
      (_ : DecidableEq ι)
      (G : ι → Type (max u v)) (_ : (i : ι) → AddCommGroup (G i))
      (_ : (i : ι) → Module R (G i))
      (f : (i j : ι) → i ≤ j → (G i →ₗ[R] G j))
      (_ : DirectedSystem G (fun i j h => f i j h)),
      (∀ i, Module.FinitePresentation R (G i)) ∧
      Nonempty (M ≃ₗ[R] Module.DirectLimit G f) := by
  obtain ⟨ι, _, _, _, _, G, _, _, f, hds, hfp, ⟨e⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation.{u, max u v} R (ULift.{u} M)
  exact ⟨ι, _, ‹_›, ‹_›, ‹_›, G, _, _, f, hds, hfp,
    ⟨(ULift.moduleEquiv.symm.trans e : M ≃ₗ[R] Module.DirectLimit G f)⟩⟩

namespace Module

/-- `IsRelation f x` says that the coefficients `f` give a relation among the elements
`x` of an `R`-module, i.e. `∑ i, f i • x i = 0`. -/
@[stacks 07N8]
def IsRelation {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} [Fintype ι] (f : ι → R) (x : ι → M) : Prop :=
  ∑ i, f i • x i = 0

/-- `IsRelation f x` unfolds to the vanishing of `∑ i, f i • x i`. -/
theorem isRelation_iff {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} [Fintype ι] (f : ι → R) (x : ι → M) :
    IsRelation f x ↔ ∑ i, f i • x i = 0 := Iff.rfl

end Module
