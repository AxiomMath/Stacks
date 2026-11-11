module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor

/-!
# Algebraizing a map to a completion on an algebraic space

Let `F` be an algebraic space over a scheme `S` whose étale charts are locally Noetherian and
let `𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals on its small étale site.  Stacks 08BB asserts
that a map `α : E ⟶ G^∧` from a coherent `𝓘`-adic system to the completion of a coherent module,
whose kernel and cokernel are annihilated by a power of `𝓘`, is the completion of a map
`a : M ⟶ G` of coherent modules with the same annihilation property, uniquely up to a unique
compatible isomorphism.  This file proves the **uniqueness** half, and the Hom-level
machinery it rests on.

## Main definitions

* `AlgebraicGeometry.Space.IsMapKernelCokernelAnnihilatedByPower` — a map of coherent modules
  whose kernel and cokernel are annihilated by a positive power of `𝓘`.
* `AlgebraicGeometry.Space.completionTermProjection` — the projection `M ⟶ M / 𝓘 ^ (n + 1) M` of a
  coherent module onto the `n`-th term of its completion.

## Main results

* `AlgebraicGeometry.Space.eq_of_completionFunctor_map_eq_of_annihilated` and
  `AlgebraicGeometry.Space.exists_completionFunctor_map_eq_of_annihilated` — the completion
  functor is **bijective on maps into a coherent module already annihilated by a power of
  `𝓘`**.  This is the engine of everything below: such a target has an invertible quotient
  projection at the level where it is annihilated, and all the transition maps of its
  completion above that level are invertible too, which lets a map of completions be read off
  at one level and reassembled at every other.
* `AlgebraicGeometry.Space.exists_section_of_completion_section` — a section of the completion
  of a map whose kernel and cokernel are annihilated by a power of `𝓘` is the completion of a
  section.
* `AlgebraicGeometry.Space.exists_lift_of_completion_lift` — a map between the completions of
  two coherent modules over a fixed one is the completion of a map over it.
* `AlgebraicGeometry.Space.existsUnique_iso_of_algebraization` — the uniqueness half of Stacks
  08BB with left exactness of completion as an instance argument: two algebraizations of the same
  `α` differ by a unique compatible isomorphism.  The whole of Stacks 08BB, over the source's own
  hypotheses, is `AlgebraicGeometry.Space.exists_algebraization_and_existsUnique_iso`.

## Implementation notes

The completion is `AlgebraicGeometry.Space.completionFunctor`, Stacks 08B4.  Its target is the
full subcategory `AlgebraicGeometry.Space.CoherentAdicSystems` of the inverse systems of
`𝒪_F`-modules, so a map of completions is a natural transformation subject to no condition
beyond naturality, and every statement below is proved by cancelling the quotient projections
`AlgebraicGeometry.Space.completionTermProjection`, which are epimorphisms.

Kernels and cokernels of maps of coherent modules are taken in the abelian category of coherent
modules.  Since the inclusion of the coherent modules into all `𝒪_F`-modules preserves finite
limits and colimits, this is the same as taking them in the ambient category.

### Two deviations from the source, and what is missing

The source assumes the algebraic space Noetherian.  Only local Noetherianity of its étale
charts is used, in the form of the `Fact` instance that
`AlgebraicGeometry.Space.completionFunctor` is stated with; this is strictly weaker, exactly as
for Stacks 08B4 itself.

**Left exactness of the completion functor is an instance argument** of the algebraization
results, `PreservesFiniteLimits (completionFunctor B S hS F hF 𝓘 hI)`.  It is Stacks 08B5, which
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact` supplies over a Noetherian
algebraic space.  It is used in one step of the proof, namely to recognize the completion of the
pullback `M ×_G N` as the pullback of the completions, and nowhere in the statement of what is
proved.

The existence of an algebraization is not proved in this file; it is
`AlgebraicGeometry.Space.C1573.exists_algebraization`, and the whole of Stacks 08BB is
`AlgebraicGeometry.Space.exists_algebraization_and_existsUnique_iso`.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 08B5](https://stacks.math.columbia.edu/tag/08B5)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Annihilation by a power of the ideal, as a calculus -/

/-- Annihilation of the sections of a module by `𝓘 ^ k` persists for higher powers. -/
theorem isPowAnnihilated_of_le {k l : ℕ} (h : k ≤ l) (M : Modules.{u, u} B S hS F hF)
    (hM : IsPowAnnihilated B S hS F hF 𝓘 k M) :
    IsPowAnnihilated B S hS F hF 𝓘 l M :=
  fun U r hr x => hM U r (Ideal.pow_le_pow_right h hr) x

/-- If `𝓘 ^ k M` vanishes then so does `𝓘 ^ l M` for every `l ≥ k`. -/
theorem idealPowerMultiple_eq_bot_of_le {k l : ℕ} (h : k ≤ l) (M : Modules.{u, u} B S hS F hF)
    (hM : idealPowerMultiple B S hS F hF 𝓘 k M = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 l M = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 l M).mpr
    (isPowAnnihilated_of_le B S hS F hF 𝓘 h M
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).mp hM))

/-- Annihilation of the sections by `𝓘 ^ k` transfers along an isomorphism of modules. -/
theorem isPowAnnihilated_of_iso {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N) (k : ℕ)
    (hM : IsPowAnnihilated B S hS F hF 𝓘 k M) :
    IsPowAnnihilated B S hS F hF 𝓘 k N := by
  intro U r hr x
  have hx : (e.hom.val.app (op U)).hom ((e.inv.val.app (op U)).hom x) = x :=
    congrArg (fun g : N ⟶ N => g.val.app (op U) x) e.inv_hom_id
  rw [← hx, ← map_smul, hM U r hr _, map_zero]

/-- If `𝓘 ^ k M` vanishes then so does `𝓘 ^ k N` for any module `N` isomorphic to `M`. -/
theorem idealPowerMultiple_eq_bot_of_iso {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N) (k : ℕ)
    (hM : idealPowerMultiple B S hS F hF 𝓘 k M = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 k N = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k N).mpr
    (isPowAnnihilated_of_iso B S hS F hF 𝓘 e k
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).mp hM))

/-- If `𝓘 ^ k N` vanishes and `M` injects into `N` then `𝓘 ^ k M` vanishes. -/
theorem idealPowerMultiple_eq_bot_of_mono {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) [Mono f]
    (k : ℕ) (hN : idealPowerMultiple B S hS F hF 𝓘 k N = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 k M = ⊥ :=
  (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).mpr
    (isPowAnnihilated_of_mono B S hS F hF 𝓘 k f
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k N).mp hN))

/-- **A map of coherent modules whose kernel and cokernel are annihilated by a power of `𝓘`.**

The kernel and the cokernel are taken in the abelian category of coherent modules; the
inclusion of the coherent modules into all `𝒪_F`-modules preserves both, so this is the same
condition as the one on the kernel and cokernel of the underlying map of modules. -/
def IsMapKernelCokernelAnnihilatedByPower {M N : CoherentModules.{u, u} B S hS F hF}
    (a : M ⟶ N) : Prop :=
  ∃ t : ℕ, 0 < t ∧ idealPowerMultiple B S hS F hF 𝓘 t (kernel a).obj = ⊥ ∧
    idealPowerMultiple B S hS F hF 𝓘 t (cokernel a).obj = ⊥

/-! ### The projection onto a term of the completion -/

/-- The projection `M ⟶ M / 𝓘 ^ k M` is an isomorphism as soon as `𝓘 ^ k M` vanishes. -/
theorem isIso_π_idealPowerMultiple_of_eq_bot (k : ℕ) (M : Modules.{u, u} B S hS F hF)
    (hM : idealPowerMultiple B S hS F hF 𝓘 k M = ⊥) :
    IsIso (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι) :=
  CokernelCofork.IsColimit.isIso_π
    (CokernelCofork.ofπ (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι)
      (cokernel.condition _))
    (cokernelIsCokernel _) (submodule_ι_eq_zero_of_eq_bot B S hS F hF hM)

/-! ### The projection onto a term of the completion -/

section Completion

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- The projection of a coherent module `M` onto the `n`-th term `M / 𝓘 ^ (n + 1) M` of its
completion. -/
def completionTermProjection (M : CoherentModules.{u, u} B S hS F hF) (n : ℕ) :
    M.obj ⟶ ((completionFunctor B S hS F hF 𝓘 hI).obj M).obj.obj (op n) :=
  cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M.obj).ι

/-- The projection onto a term of the completion is an epimorphism, being a quotient
projection. -/
instance epi_completionTermProjection (M : CoherentModules.{u, u} B S hS F hF) (n : ℕ) :
    Epi (completionTermProjection B S hS F hF 𝓘 hI M n) :=
  inferInstanceAs (Epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M.obj).ι))

/-- The projection onto a term of the completion is compatible with the maps induced on
completions by a morphism of coherent modules. -/
theorem completionTermProjection_naturality {M N : CoherentModules.{u, u} B S hS F hF} (g : M ⟶ N)
    (n : ℕ) :
    completionTermProjection B S hS F hF 𝓘 hI M n ≫
        ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op n) =
      g.hom ≫ completionTermProjection B S hS F hF 𝓘 hI N n :=
  π_comp_idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1) g.hom

/-- The projection onto a term of the completion is compatible with the transition maps of the
completion. -/
theorem completionTermProjection_transition (M : CoherentModules.{u, u} B S hS F hF) {j k : ℕ}
    (h : j ≤ k) :
    completionTermProjection B S hS F hF 𝓘 hI M k ≫
        ((completionFunctor B S hS F hF 𝓘 hI).obj M).obj.map (homOfLE h).op =
      completionTermProjection B S hS F hF 𝓘 hI M j :=
  π_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1) M.obj

/-- The projection onto the `n`-th term of the completion is an isomorphism as soon as
`𝓘 ^ (n + 1) M` vanishes. -/
theorem isIso_completionTermProjection_of_annihilated (M : CoherentModules.{u, u} B S hS F hF)
    (n : ℕ) (hM : idealPowerMultiple B S hS F hF 𝓘 (n + 1) M.obj = ⊥) :
    IsIso (completionTermProjection B S hS F hF 𝓘 hI M n) :=
  isIso_π_idealPowerMultiple_of_eq_bot B S hS F hF 𝓘 (n + 1) M.obj hM

/-- The transition maps of the completion of `M` above a level at which `M` is already
annihilated are isomorphisms. -/
theorem isIso_completion_map_of_annihilated (M : CoherentModules.{u, u} B S hS F hF) {j k : ℕ}
    (h : j ≤ k) (hM : idealPowerMultiple B S hS F hF 𝓘 (j + 1) M.obj = ⊥) :
    IsIso (((completionFunctor B S hS F hF 𝓘 hI).obj M).obj.map (homOfLE h).op) := by
  have := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI M j hM
  have := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI M k
    (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.add_le_add_right h 1) M.obj hM)
  have hfac : ((completionFunctor B S hS F hF 𝓘 hI).obj M).obj.map (homOfLE h).op =
      inv (completionTermProjection B S hS F hF 𝓘 hI M k) ≫
        completionTermProjection B S hS F hF 𝓘 hI M j := by
    rw [← completionTermProjection_transition B S hS F hF 𝓘 hI M h, IsIso.inv_hom_id_assoc]
  rw [hfac]
  infer_instance

/-- The completion functor preserves zero morphisms. -/
instance preservesZeroMorphisms_completionFunctor :
    (completionFunctor B S hS F hF 𝓘 hI).PreservesZeroMorphisms where
  map_zero M N := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext level
    obtain ⟨l⟩ := level
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI M l)).1 ?_
    rw [completionTermProjection_naturality]
    simp

/-! ### Maps into a coherent module annihilated by a power of the ideal -/

/-- A map of completions compatible with the quotient projections at one level at which the
target module is already annihilated is compatible with them at every level.

Both levels are compared with their maximum: the transition map of the completion of `N` from
the maximum down to `n` is an isomorphism, which identifies the two sides at the maximum with
their values at `n`, and the transition down to the other level then transports the identity
there. -/
theorem completionTermProjection_comp_app_eq_of_annihilated
    (M N : CoherentModules.{u, u} B S hS F hF) (n : ℕ)
    (hN : idealPowerMultiple B S hS F hF 𝓘 (n + 1) N.obj = ⊥)
    (φ : (completionFunctor B S hS F hF 𝓘 hI).obj M ⟶
      (completionFunctor B S hS F hF 𝓘 hI).obj N)
    (f : M.obj ⟶ N.obj)
    (hf : completionTermProjection B S hS F hF 𝓘 hI M n ≫ φ.hom.app (op n) =
      f ≫ completionTermProjection B S hS F hF 𝓘 hI N n)
    (l : ℕ) :
    completionTermProjection B S hS F hF 𝓘 hI M l ≫ φ.hom.app (op l) =
      f ≫ completionTermProjection B S hS F hF 𝓘 hI N l := by
  have hnm : n ≤ max n l := le_max_left _ _
  have hlm : l ≤ max n l := le_max_right _ _
  have hmid : completionTermProjection B S hS F hF 𝓘 hI M (max n l) ≫
      φ.hom.app (op (max n l)) =
        f ≫ completionTermProjection B S hS F hF 𝓘 hI N (max n l) := by
    have := isIso_completion_map_of_annihilated B S hS F hF 𝓘 hI N hnm hN
    refine (cancel_mono (((completionFunctor B S hS F hF 𝓘 hI).obj N).obj.map
      (homOfLE hnm).op)).1 ?_
    rw [Category.assoc, ← φ.hom.naturality (homOfLE hnm).op, ← Category.assoc,
      completionTermProjection_transition, Category.assoc, completionTermProjection_transition, hf]
  rw [← completionTermProjection_transition B S hS F hF 𝓘 hI M hlm, Category.assoc,
    φ.hom.naturality (homOfLE hlm).op, ← Category.assoc, hmid, Category.assoc,
    completionTermProjection_transition]

/-- **The completion functor is injective on maps into a coherent module already annihilated by
a power of the ideal.** -/
theorem eq_of_completionFunctor_map_eq_of_annihilated {M N : CoherentModules.{u, u} B S hS F hF}
    (n : ℕ) (hN : idealPowerMultiple B S hS F hF 𝓘 (n + 1) N.obj = ⊥) {f g : M ⟶ N}
    (hfg : (completionFunctor B S hS F hF 𝓘 hI).map f =
      (completionFunctor B S hS F hF 𝓘 hI).map g) :
    f = g := by
  have := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI N n hN
  have h : ((completionFunctor B S hS F hF 𝓘 hI).map f).hom.app (op n) =
      ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op n) :=
    congrArg (fun t => t.hom.app (op n)) hfg
  apply ObjectProperty.hom_ext
  refine (cancel_mono (completionTermProjection B S hS F hF 𝓘 hI N n)).1 ?_
  rw [← completionTermProjection_naturality B S hS F hF 𝓘 hI f n,
    ← completionTermProjection_naturality B S hS F hF 𝓘 hI g n, h]

/-- **The completion functor is surjective on maps into a coherent module already annihilated by
a power of the ideal.**

The algebraization of a map of completions is read off at a level at which the target is
annihilated, where the quotient projection of the target is invertible; it then induces the
given map at every level. -/
theorem exists_completionFunctor_map_eq_of_annihilated
    {M N : CoherentModules.{u, u} B S hS F hF} (n : ℕ)
    (hN : idealPowerMultiple B S hS F hF 𝓘 (n + 1) N.obj = ⊥)
    (φ : (completionFunctor B S hS F hF 𝓘 hI).obj M ⟶
      (completionFunctor B S hS F hF 𝓘 hI).obj N) :
    ∃ f : M ⟶ N, (completionFunctor B S hS F hF 𝓘 hI).map f = φ := by
  have := isIso_completionTermProjection_of_annihilated B S hS F hF 𝓘 hI N n hN
  have hf : completionTermProjection B S hS F hF 𝓘 hI M n ≫ φ.hom.app (op n) =
      (completionTermProjection B S hS F hF 𝓘 hI M n ≫ φ.hom.app (op n) ≫
          inv (completionTermProjection B S hS F hF 𝓘 hI N n)) ≫
        completionTermProjection B S hS F hF 𝓘 hI N n := by
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨ObjectProperty.homMk (completionTermProjection B S hS F hF 𝓘 hI M n ≫
    φ.hom.app (op n) ≫ inv (completionTermProjection B S hS F hF 𝓘 hI N n)), ?_⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext level
  obtain ⟨l⟩ := level
  refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI M l)).1 ?_
  rw [completionTermProjection_naturality]
  exact
    (completionTermProjection_comp_app_eq_of_annihilated B S hS F hF 𝓘 hI M N n hN φ _ hf l).symm

end Completion

/-! ### Algebraizing maps and isomorphisms -/

section Algebraization

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    [PreservesFiniteLimits (completionFunctor B S hS F hF 𝓘 hI)]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the binary products used by `Functor.additive_of_preserves_binary_products`
/-- The completion functor is additive, being left exact. -/
private instance additive_completionFunctor : (completionFunctor B S hS F hF 𝓘 hI).Additive :=
    Functor.additive_of_preserves_binary_products _

/-- Two maps of coherent modules which become equal after composing with a map whose kernel is
annihilated by a power of `𝓘`, and whose completions agree, are already equal.

Their difference factors through that kernel, and the completion functor is injective on maps
into it. -/
theorem eq_of_comp_eq_of_completionFunctor_map_eq
    {M N P : CoherentModules.{u, u} B S hS F hF} (b : N ⟶ P) (n : ℕ)
    (hker : idealPowerMultiple B S hS F hF 𝓘 (n + 1) (kernel b).obj = ⊥)
    {f g : M ⟶ N} (hcomp : f ≫ b = g ≫ b)
    (hmap : (completionFunctor B S hS F hF 𝓘 hI).map f =
      (completionFunctor B S hS F hF 𝓘 hI).map g) :
    f = g := by
  have hzero : (f - g) ≫ b = 0 := by rw [Preadditive.sub_comp, hcomp, sub_self]
  have hd : kernel.lift b (f - g) hzero ≫ kernel.ι b = f - g := kernel.lift_ι _ _ _
  have hdzero : (completionFunctor B S hS F hF 𝓘 hI).map (kernel.lift b (f - g) hzero) = 0 := by
    refine (cancel_mono ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι b))).1 ?_
    rw [← Functor.map_comp, hd, Functor.map_sub, hmap, sub_self, zero_comp]
  have hdz : kernel.lift b (f - g) hzero = 0 :=
    eq_of_completionFunctor_map_eq_of_annihilated B S hS F hF 𝓘 hI n hker
      (by rw [hdzero, Functor.map_zero])
  refine sub_eq_zero.mp ?_
  rw [← hd, hdz, zero_comp]

/-- **A section of the completion of a map of coherent modules whose kernel and cokernel are
annihilated by a power of `𝓘` is the completion of a section.**

The cokernel projection dies after completion, hence dies, so the map is an epimorphism.  The
retraction of its completion onto the kernel of the completion is, by left exactness, a map into
the completion of the kernel; the kernel being annihilated, that map is the completion of a
retraction `r` defined before completion.  Then `r` splits the kernel off, and the complementary
idempotent factors through the map itself, which is the asserted section. -/
theorem exists_section_of_completion_section
    {P M : CoherentModules.{u, u} B S hS F hF} (p : P ⟶ M) (n : ℕ)
    (hker : idealPowerMultiple B S hS F hF 𝓘 (n + 1) (kernel p).obj = ⊥)
    (hcoker : idealPowerMultiple B S hS F hF 𝓘 (n + 1) (cokernel p).obj = ⊥)
    (σ : (completionFunctor B S hS F hF 𝓘 hI).obj M ⟶
      (completionFunctor B S hS F hF 𝓘 hI).obj P)
    (hσ : σ ≫ (completionFunctor B S hS F hF 𝓘 hI).map p = 𝟙 _) :
    ∃ s : M ⟶ P, s ≫ p = 𝟙 _ ∧ (completionFunctor B S hS F hF 𝓘 hI).map s = σ := by
  have hcokmap : (completionFunctor B S hS F hF 𝓘 hI).map (cokernel.π p) = 0 := by
    calc (completionFunctor B S hS F hF 𝓘 hI).map (cokernel.π p)
        = (σ ≫ (completionFunctor B S hS F hF 𝓘 hI).map p) ≫
            (completionFunctor B S hS F hF 𝓘 hI).map (cokernel.π p) := by
          rw [hσ, Category.id_comp]
      _ = 0 := by
          rw [Category.assoc, ← Functor.map_comp, cokernel.condition, Functor.map_zero,
            comp_zero]
  have hcokzero : cokernel.π p = 0 :=
    eq_of_completionFunctor_map_eq_of_annihilated B S hS F hF 𝓘 hI n hcoker
      (by rw [hcokmap, Functor.map_zero])
  have : Epi p := by
    refine Preadditive.epi_of_cancel_zero p fun {Z} g hg => ?_
    rw [← cokernel.π_desc p g hg, hcokzero, zero_comp]
  have hlift : (𝟙 ((completionFunctor B S hS F hF 𝓘 hI).obj P) -
        (completionFunctor B S hS F hF 𝓘 hI).map p ≫ σ) ≫
      (completionFunctor B S hS F hF 𝓘 hI).map p = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hσ, Category.comp_id, sub_self]
  obtain ⟨r, hrmap⟩ := exists_completionFunctor_map_eq_of_annihilated B S hS F hF 𝓘 hI n hker
    (kernel.lift ((completionFunctor B S hS F hF 𝓘 hI).map p)
        (𝟙 ((completionFunctor B S hS F hF 𝓘 hI).obj P) -
          (completionFunctor B S hS F hF 𝓘 hI).map p ≫ σ) hlift ≫
      (PreservesKernel.iso (completionFunctor B S hS F hF 𝓘 hI) p).inv)
  have hsplit : IsSplitEpi ((completionFunctor B S hS F hF 𝓘 hI).map p) := ⟨⟨σ, hσ⟩⟩
  have hretreq : (completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι p ≫ r) =
      (completionFunctor B S hS F hF 𝓘 hI).map (𝟙 (kernel p)) := by
    rw [Functor.map_comp, hrmap, CategoryTheory.Functor.map_id]
    refine (cancel_mono ((completionFunctor B S hS F hF 𝓘 hI).map (kernel.ι p))).1 ?_
    rw [Category.assoc, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp, sub_zero, Category.id_comp]
  have hretr : kernel.ι p ≫ r = 𝟙 (kernel p) :=
    eq_of_completionFunctor_map_eq_of_annihilated B S hS F hF 𝓘 hI n hker hretreq
  have hkill : kernel.ι p ≫ (𝟙 P - r ≫ kernel.ι p) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hretr, Category.id_comp,
      sub_self]
  have nep : NormalEpi p := normalEpiOfEpi p
  have hnormal : nep.g ≫ (𝟙 P - r ≫ kernel.ι p) = 0 := by
    rw [← kernel.lift_ι p nep.g nep.w, Category.assoc, hkill, comp_zero]
  obtain ⟨s, hs⟩ := NormalEpi.desc' p (𝟙 P - r ≫ kernel.ι p) hnormal
  refine ⟨s, ?_, ?_⟩
  · refine (cancel_epi p).1 ?_
    rw [← Category.assoc, hs, Preadditive.sub_comp, Category.id_comp, Category.assoc,
      kernel.condition, comp_zero, sub_zero, Category.comp_id]
  · refine (cancel_epi ((completionFunctor B S hS F hF 𝓘 hI).map p)).1 ?_
    rw [← Functor.map_comp, hs, Functor.map_sub, CategoryTheory.Functor.map_id,
      Functor.map_comp, hrmap, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
    exact sub_sub_cancel _ _

/-- **A map between the completions of two coherent modules over a fixed one is the completion
of a map over it**, provided the kernel and cokernel of the target's structure map are
annihilated by a power of `𝓘`.

The pullback of the two structure maps has the same kernel and a submodule of the cokernel of
the target's structure map over the source, so its projection to the source again has kernel and
cokernel annihilated by a power of `𝓘`.  Left exactness makes the completed square a pullback
square, in which the identity and the given map produce a section of the completed projection;
that section algebraizes, and composing it with the other projection gives the asserted map. -/
theorem exists_lift_of_completion_lift
    {M N P : CoherentModules.{u, u} B S hS F hF} (a : M ⟶ P) (b : N ⟶ P)
    (hb : IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 b)
    (φ : (completionFunctor B S hS F hF 𝓘 hI).obj M ⟶
      (completionFunctor B S hS F hF 𝓘 hI).obj N)
    (hφ : φ ≫ (completionFunctor B S hS F hF 𝓘 hI).map b =
      (completionFunctor B S hS F hF 𝓘 hI).map a) :
    ∃ c : M ⟶ N, c ≫ b = a ∧ (completionFunctor B S hS F hF 𝓘 hI).map c = φ := by
  obtain ⟨t, ht, hkerb, hcokerb⟩ := hb
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have sq : IsPullback (pullback.fst a b) (pullback.snd a b) a b := IsPullback.of_hasPullback a b
  have : IsIso (kernel.map (pullback.fst a b) b (pullback.snd a b) a sq.w) :=
    isIso_kernel_map_of_isPullback sq
  have : Mono (cokernel.map (pullback.fst a b) b (pullback.snd a b) a sq.w) :=
    Abelian.mono_cokernel_map_of_isPullback sq
  have : Mono ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).map
      (cokernel.map (pullback.fst a b) b (pullback.snd a b) a sq.w)) :=
    Functor.map_mono _ _
  have hkerp : idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (kernel (pullback.fst a b)).obj = ⊥ :=
    idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).mapIso
        (asIso (kernel.map (pullback.fst a b) b (pullback.snd a b) a sq.w)).symm)
      (n + 1) hkerb
  have hcokerp : idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (cokernel (pullback.fst a b)).obj = ⊥ :=
    idealPowerMultiple_eq_bot_of_mono B S hS F hF 𝓘
      ((ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)).map
        (cokernel.map (pullback.fst a b) b (pullback.snd a b) a sq.w)) (n + 1) hcokerb
  have csq := sq.map (completionFunctor B S hS F hF 𝓘 hI)
  obtain ⟨s, hs, hsmap⟩ := exists_section_of_completion_section B S hS F hF 𝓘 hI
    (pullback.fst a b) n hkerp hcokerp
    (csq.lift (𝟙 _) φ (by rw [Category.id_comp, hφ]))
    (csq.lift_fst _ _ _)
  refine ⟨s ≫ pullback.snd a b, ?_, ?_⟩
  · rw [Category.assoc, ← sq.w, ← Category.assoc, hs, Category.id_comp]
  · rw [Functor.map_comp, hsmap]
    exact csq.lift_snd _ _ _

/-! ### Uniqueness of the algebraization -/

/-- **Stacks 08BB, uniqueness of the algebraization.**

Let `𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals on an algebraic space `F` with locally
Noetherian étale charts, let `G` be a coherent `𝒪_F`-module and let `E` be a coherent `𝓘`-adic
system with a map `α : E ⟶ G^∧`.  Given two algebraizations of `α` — coherent modules `M`, `N`
with maps `a : M ⟶ G`, `a' : N ⟶ G` whose kernels and cokernels are annihilated by a power of
`𝓘`, and isomorphisms `β : E ≅ M^∧`, `β' : E ≅ N^∧` with `α = β ≫ a^∧ = β' ≫ a'^∧` — there is a
*unique* isomorphism `e : M ≅ N` compatible with the maps to `G` and with the comparison
isomorphisms.

Left exactness of the completion functor is the instance argument
`PreservesFiniteLimits (completionFunctor B S hS F hF 𝓘 hI)`, which the source proves beforehand
as Stacks 08B5; it enters this proof only through the step that recognizes the completion of the
pullback `M ×_G N` as the pullback of the completions.
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` supplies it over a
Noetherian algebraic space, and
`AlgebraicGeometry.Space.exists_algebraization_and_existsUnique_iso` is the whole of Stacks 08BB. -/
theorem existsUnique_iso_of_algebraization {G M N : CoherentModules.{u, u} B S hS F hF}
    {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G) (a : M ⟶ G) (a' : N ⟶ G)
    (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M)
    (β' : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj N)
    (ha : IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a)
    (ha' : IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a')
    (hα : α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a)
    (hα' : α = β'.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a') :
    ∃! e : M ≅ N, e.hom ≫ a' = a ∧
      β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map e.hom = β'.hom := by
  have hβ : β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a =
      β'.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a' := hα ▸ hα'
  obtain ⟨t, ht, hkera, hcokera⟩ := id ha
  obtain ⟨t', ht', hkera', hcokera'⟩ := id ha'
  obtain ⟨u, hu, humap⟩ := exists_lift_of_completion_lift B S hS F hF 𝓘 hI a a' ha'
    (β.inv ≫ β'.hom) (by
      rw [Category.assoc, ← hβ, ← Category.assoc, β.inv_hom_id, Category.id_comp])
  obtain ⟨v, hv, hvmap⟩ := exists_lift_of_completion_lift B S hS F hF 𝓘 hI a' a ha
    (β'.inv ≫ β.hom) (by
      rw [Category.assoc, hβ, ← Category.assoc, β'.inv_hom_id, Category.id_comp])
  have huv : u ≫ v = 𝟙 M :=
    eq_of_comp_eq_of_completionFunctor_map_eq B S hS F hF 𝓘 hI a t
      (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.le_succ t) (kernel a).obj hkera)
      (by rw [Category.assoc, hv, hu, Category.id_comp])
      (by rw [Functor.map_comp, humap, hvmap, CategoryTheory.Functor.map_id]; simp)
  have hvu : v ≫ u = 𝟙 N :=
    eq_of_comp_eq_of_completionFunctor_map_eq B S hS F hF 𝓘 hI a' t'
      (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.le_succ t') (kernel a').obj hkera')
      (by rw [Category.assoc, hu, hv, Category.id_comp])
      (by rw [Functor.map_comp, hvmap, humap, CategoryTheory.Functor.map_id]; simp)
  refine ⟨⟨u, v, huv, hvu⟩, ⟨hu, ?_⟩, ?_⟩
  · change β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map u = β'.hom
    rw [humap, ← Category.assoc, β.hom_inv_id, Category.id_comp]
  · intro e he
    refine Iso.ext (eq_of_comp_eq_of_completionFunctor_map_eq B S hS F hF 𝓘 hI a' t'
      (idealPowerMultiple_eq_bot_of_le B S hS F hF 𝓘 (Nat.le_succ t') (kernel a').obj hkera')
      (he.1.trans hu.symm) ?_)
    refine (cancel_epi β.hom).1 ?_
    rw [he.2, humap, ← Category.assoc, β.hom_inv_id, Category.id_comp]

end Algebraization

end AlgebraicGeometry.Space

end
