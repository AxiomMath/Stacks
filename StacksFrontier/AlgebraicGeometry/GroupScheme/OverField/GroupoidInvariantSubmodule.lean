module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentAbelian

/-!
# Invariant submodules of a quasi-coherent module on a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` flat, and let `(F, α)` be a
quasi-coherent module on it, so `F` is a quasi-coherent `𝒪_U`-module and `α : t^*F ⟶ s^*F`
satisfies the cocycle and identity conditions.  A *submodule* of `(F, α)` is a quasi-coherent
`𝒢 ⊆ F` with `α(t^*𝒢) = s^*𝒢` inside `s^*F`; flatness of `s` and `t` makes the two pullbacks
exact, so they preserve subsheaves and the condition is meaningful.

This file produces such submodules.  A candidate subsheaf is described, as in Gabber's theorem
for a single scheme, by a compatible family of submodules `N V ⊆ Γ(F, V)` indexed by the affine
opens `V` of `U` (`Stacks.AlgebraicGeometry.GabberColimit.IsCompatible`), and the extra condition
imposed by `α` is `IsInvariant`: for affine opens `V`, `V'` of `U` and an affine open `W` of `R`
with `W ⊆ t⁻¹V` and `W ⊆ s⁻¹V'`, the descent morphism carries the pullbacks along `t` of the
sections in `N V` into the span of the pullbacks along `s` of the sections in `N V'`.  Over such a
triple `Γ(t^*F, W)` is `Γ(R, W) ⊗_{Γ(U, V)} Γ(F, V)` (Stacks 01I9), so this is the condition on
`N_i ⊗_{A_i, t} B_{ijk}` which the source writes down.

Two things are then proved.  *Invariance implies that `α` restricts*: the subsheaf cut out by an
invariant compatible family carries a descent morphism, satisfying the cocycle and identity
conditions, for which the inclusion is a morphism of quasi-coherent modules on the groupoid
scheme.  Only the inclusion `α(t^*𝒢) ⊆ s^*𝒢` is needed for this, the reverse inclusion being a
consequence of the cocycle condition through
`Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.alpha_isIso`.  And *invariant families exist
in abundance*: a bounded family of sections is contained in a bounded family whose spans are
compatible and invariant, by the source's closure construction run over the affine opens of `U`
together with the affine opens of `R`.

## Main definitions

* `IsInvariant`: the condition imposed on a family of submodules of the sections by the descent
  morphism.
* `invariantObject`: the quasi-coherent module on the groupoid scheme cut out by an invariant
  compatible family, and `invariantHom` its monomorphism into the ambient one.

## Main results

* `exists_bounded_closure`: a family of sets of size at most `κ` is contained in one of size at
  most `κ` which is closed under a family of at most `κ` enlargement operators at each index, each
  producing at most `κ` new elements from a single old one.  This is the cardinal arithmetic of
  the source's `𝒮 ↦ 𝒮'` iteration, in the form in which the compatibility and the invariance
  conditions are closed off simultaneously.
* `isBasis_affineOpens_over₂`: the affine opens of a scheme which lie over an affine open under
  each of two given morphisms form a basis of its topology.  This is what makes the invariance
  condition, imposed only on such triples, say something about all of `s^*F`.
* `invariantDescent_comp_ι`: the defining property of the restricted descent morphism.
* `IsTransitionInvariant` and `transition_comp_cokernelπ_eq_zero`: the invariance condition and
  the vanishing it implies, for an arbitrary pair of morphisms `t s : R ⟶ U` and an arbitrary
  morphism `α : t^*F ⟶ s^*F`, with no groupoid structure.
* `exists_bounded_invariant_compatible_family`: **the closure step**, producing the invariant
  compatible family of bounded spans.  It uses only `t`, `s` and `α`.
* `exists_transitionInvariant_mono_of_section`: for `κ` infinite dominating the numbers of affine
  opens of `U` and of `R` and `s` flat, every section of `F` over an open lies in a `κ`-generated
  quasi-coherent submodule to which `α` restricts.  No cocycle condition is used; this is the form
  in which the closure step is transported to a groupoid in algebraic spaces.
* `exists_invariantObject_of_section`: for `κ` infinite dominating the numbers of affine opens of
  `U` and of `R`, every section of `F` over an open is a section of a `κ`-generated submodule of
  `(F, α)`.

## Implementation notes

The descent morphism on the subsheaf is obtained from `CategoryTheory.Abelian.monoLift`: the
composite `t^*𝒢 → t^*F → s^*F → coker(s^*𝒢 → s^*F)` is zero, so the middle composite factors
through the monomorphism `s^*𝒢 → s^*F`.  No exactness of `s^*` is needed for the factorisation
itself — a monomorphism in an abelian category is the kernel of its cokernel — only the fact that
`s^*` carries the inclusion of the subsheaf to a monomorphism, which is where flatness of `s` is
used.  That the composite vanishes is checked on sections, over the affine opens of `R` lying over
affine opens of `U` along both `s` and `t`: there `Γ(t^*𝒢, W)` is spanned by the pullbacks of the
sections of `𝒢` over the affine open below (`AlgebraicGeometry.span_pullbackSection_eq_top`), so
the invariance condition is exactly what is needed, and such opens form a basis.

The cocycle and the identity conditions for the restricted descent morphism are deduced from those
of `α` by cancelling the monomorphism `(c ≫ s)^*𝒢 → (c ≫ s)^*F` resp. `𝒢 → F`, using the
naturality of `Stacks.Groupoids.reindexHom`,
`Stacks.Groupoids.GroupoidScheme.successiveDescent` and
`Stacks.Groupoids.GroupoidScheme.identityDescent` in the module.  Flatness of `c ≫ s` is the
instance `Stacks.Groupoids.GroupoidScheme.flat_comp_source`.

The three enlargement operators of the closure are collected into one sum type `InvArrow`, whose
summands are the restriction of a section to a smaller affine open, the finite set of sections
over a larger affine open generating a given section over a smaller one, and the finite set of
sections over `V'` whose pullbacks along `s` generate the image under `α` of the pullback along `t`
of a given section over `V`.  They are packaged as top-level definitions `invSrc` and `invGen`
rather than inlined, so that the dependent types of the closure lemma reduce by iota.

## References

* [Stacks Project, Tag 077U](https://stacks.math.columbia.edu/tag/077U)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Groupoids Stacks.Groupoids.GroupoidScheme
open Stacks.AlgebraicGeometry.CardinalGeneration
open Stacks.AlgebraicGeometry.GabberColimit

universe u

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat

namespace Stacks.AlgebraicGeometry.GroupoidCardinalGeneration

/-! ### Closing a bounded family of sets under bounded enlargements -/

private theorem mk_prod_le_of_le {A B : Type u} {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.mk A ≤ κ) (hB : Cardinal.mk B ≤ κ) : Cardinal.mk (A × B) ≤ κ := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (mul_le_mul' hA hB).trans_eq (Cardinal.mul_eq_self hκ)

private theorem mk_sum_le_of_le {A B : Type u} {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.mk A ≤ κ) (hB : Cardinal.mk B ≤ κ) : Cardinal.mk (A ⊕ B) ≤ κ := by
  rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ hA hB

/-- A subsingleton set has cardinality at most any infinite cardinal `κ`. -/
private theorem mk_le_of_subsingleton_of_aleph0_le {A : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) {s : Set A} (hs : s.Subsingleton) : Cardinal.mk s ≤ κ :=
  (Cardinal.mk_le_one_iff_set_subsingleton.mpr hs).trans (Cardinal.one_le_aleph0.trans hκ)

/-- **Closure of a bounded family of sets under bounded enlargements.**  Let `M i` be a family of
types, let `S₀ i ⊆ M i` be sets of size at most an infinite cardinal `κ`, and for every index `i`
let `ar i` be a type of at most `κ` enlargement operators at `i`, the operator `a` producing from
a single element of `M (src i a)` a set of at most `κ` elements of `M i`.  Then the family `S₀` is
contained in a family of sets of size at most `κ` which is closed under all the operators.

This is the cardinal arithmetic of the `𝒮 ↦ 𝒮'` iteration of Gabber's argument: the iteration runs
over `ℕ`, each stage stays bounded because `κ` is infinite, and the closure property is
elementwise, so an element of the union appears at some finite stage and the next stage already
contains what it requires. -/
theorem exists_bounded_closure {I : Type u} {M : I → Type u} {ar : I → Type u}
    (src : (i : I) → ar i → I) (g : (i : I) → (a : ar i) → M (src i a) → Set (M i))
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) (har : ∀ i, Cardinal.mk (ar i) ≤ κ)
    (hg : ∀ i a x, Cardinal.mk ↥(g i a x) ≤ κ)
    (S₀ : ∀ i, Set (M i)) (hS₀ : ∀ i, Cardinal.mk ↥(S₀ i) ≤ κ) :
    ∃ S : ∀ i, Set (M i), (∀ i, Cardinal.mk ↥(S i) ≤ κ) ∧ (∀ i, S₀ i ⊆ S i) ∧
      ∀ (i : I) (a : ar i) (x : M (src i a)), x ∈ S (src i a) → g i a x ⊆ S i := by
  classical
  let step : (∀ i, Set (M i)) → ∀ i, Set (M i) := fun A i ↦
    A i ∪ ⋃ p : Σ a : ar i, ↥(A (src i a)), g i p.1 p.2.1
  have hstep : ∀ A : ∀ i, Set (M i), (∀ i, Cardinal.mk ↥(A i) ≤ κ) →
      ∀ i, Cardinal.mk ↥(step A i) ≤ κ := by
    intro A hA i
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hκ (hA i)
      (mk_iUnion_le_of_forall_le hκ (mk_sigma_le hκ (har i) fun a ↦ hA (src i a))
        fun p ↦ hg i p.1 p.2.1))
  let stages : ℕ → ∀ i, Set (M i) := fun n ↦ Nat.rec S₀ (fun _ A ↦ step A) n
  have hstages : ∀ (n : ℕ) (i : I), Cardinal.mk ↥(stages n i) ≤ κ := by
    intro n
    induction n with
    | zero => exact hS₀
    | succ n ih => exact hstep (stages n) ih
  refine ⟨fun i ↦ ⋃ n : ULift.{u} ℕ, stages n.down i, fun i ↦ ?_, fun i x hx ↦ ?_, ?_⟩
  · exact mk_iUnion_le_of_forall_le hκ (by simpa using hκ) fun n ↦ hstages n.down i
  · exact Set.mem_iUnion.mpr ⟨⟨0⟩, hx⟩
  · intro i a x hx y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨n.down + 1⟩, Or.inr (Set.mem_iUnion.mpr ⟨⟨a, ⟨x, hn⟩⟩, hy⟩)⟩

/-- A map which is additive and semilinear along a ring homomorphism carries the span of a set
into any submodule containing the images of the elements of that set. -/
private theorem mem_of_mem_span_of_semilinear {R S A B : Type u} [CommRing R] [CommRing S]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module S B] (φ : R →+* S) (h : A → B)
    (hadd : ∀ x y, h (x + y) = h x + h y) (hzero : h 0 = 0)
    (hsmul : ∀ (r : R) (x : A), h (r • x) = φ r • h x) (P : Submodule S B) {s : Set A}
    (hs : ∀ x ∈ s, h x ∈ P) {x : A} (hx : x ∈ Submodule.span R s) : h x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => simp [hzero]
  | add y z _ _ hy hz => simpa [hadd] using P.add_mem hy hz
  | smul r y _ hy => simpa [hsmul] using P.smul_mem (φ r) hy

/-- A map which is additive and semilinear along a ring homomorphism, and which kills every
element of a set, kills the span of that set. -/
private theorem eq_zero_of_mem_span_of_semilinear {R S A B : Type u} [CommRing R] [CommRing S]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module S B] (φ : R →+* S) (h : A → B)
    (hadd : ∀ x y, h (x + y) = h x + h y) (hzero : h 0 = 0)
    (hsmul : ∀ (r : R) (x : A), h (r • x) = φ r • h x) {s : Set A} (hs : ∀ x ∈ s, h x = 0)
    {x : A} (hx : x ∈ Submodule.span R s) : h x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => exact hzero
  | add y z _ _ hy hz => rw [hadd, hy, hz, add_zero]
  | smul r y _ hy => rw [hsmul, hy, smul_zero]

/-! ### Opens lying over affine opens along two morphisms -/

/-- **The affine opens lying over affine opens along two morphisms form a basis.**  For morphisms
`f : Y ⟶ X` and `f' : Y ⟶ X'` of schemes, the affine opens `W` of `Y` for which there are affine
opens `V ⊆ X` and `V' ⊆ X'` with `W ⊆ f⁻¹V` and `W ⊆ f'⁻¹V'` form a basis of the topology of
`Y`. -/
theorem isBasis_affineOpens_over₂ {X X' Y : Scheme.{u}} (f : Y ⟶ X) (f' : Y ⟶ X') :
    Opens.IsBasis {W : Y.Opens | IsAffineOpen W ∧
      (∃ V : X.Opens, IsAffineOpen V ∧ W ≤ f ⁻¹ᵁ V) ∧
      ∃ V' : X'.Opens, IsAffineOpen V' ∧ W ≤ f' ⁻¹ᵁ V'} := by
  rw [Opens.isBasis_iff_nbhd]
  intro O y hy
  obtain ⟨-, ⟨V, hV, rfl⟩, hfy, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base y)) isOpen_univ
  obtain ⟨-, ⟨V', hV', rfl⟩, hfy', -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f'.base y)) isOpen_univ
  obtain ⟨-, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((f ⁻¹ᵁ V ⊓ (f' ⁻¹ᵁ V' ⊓ O) : Y.Opens) : Set Y) from ⟨hfy, hfy', hy⟩)
      (f ⁻¹ᵁ V ⊓ (f' ⁻¹ᵁ V' ⊓ O)).isOpen
  have hWle' : W ≤ f ⁻¹ᵁ V ⊓ (f' ⁻¹ᵁ V' ⊓ O) := hWle
  exact ⟨W, ⟨hW, ⟨V, hV, hWle'.trans inf_le_left⟩,
    ⟨V', hV', hWle'.trans (inf_le_right.trans inf_le_left)⟩⟩, hyW,
    hWle'.trans (inf_le_right.trans inf_le_right)⟩

/-! ### Sections of morphisms of modules -/

private theorem app_comp_apply {X : Scheme.{u}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (O : X.Opens) (y : Γ(A, O)) : (f ≫ g).app O y = g.app O (f.app O y) := by
  rw [Scheme.Modules.Hom.comp_app]
  rfl

private theorem app_zero_apply {X : Scheme.{u}} {A B : X.Modules} (O : X.Opens) (y : Γ(A, O)) :
    (0 : A ⟶ B).app O y = (0 : Γ(B, O)) := rfl

/-- Pulling a section back is natural in the module, read on `Scheme.Modules.Hom.app`. -/
private theorem pullbackSectionHom_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) {A B : X.Modules}
    (φ : A ⟶ B) (O : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ O) (a : Γ(A, O)) :
    ((Scheme.Modules.pullback f).map φ).app V (pullbackSectionHom f A O V h a) =
      pullbackSectionHom f B O V h (φ.app O a) :=
  Scheme.Modules.pullbackSection_naturality f φ O V h a

/-- Two sections of an `𝒪_X`-module which agree locally are equal. -/
theorem sections_eq_of_locally_eq {X : Scheme.{u}} (A : X.Modules) {O : X.Opens} (a b : Γ(A, O))
    (h : ∀ y ∈ O, ∃ (W : X.Opens) (hWO : W ≤ O), y ∈ W ∧
      A.presheaf.map (homOfLE hWO).op a = A.presheaf.map (homOfLE hWO).op b) : a = b := by
  classical
  choose W hWO hyW hab using fun y : O ↦ h y.1 y.2
  refine (CardinalGeneration.asSheaf A).eq_of_locally_eq' W O (fun y ↦ homOfLE (hWO y)) ?_ a b
    fun y ↦ hab y
  intro y hyO
  exact Opens.mem_iSup.mpr ⟨⟨y, hyO⟩, hyW ⟨y, hyO⟩⟩

/-- **Two morphisms of `𝒪_X`-modules agreeing on the sections over a basis are equal.** -/
theorem hom_ext_of_isBasis {X : Scheme.{u}} {A Z : X.Modules} (ψ χ : A ⟶ Z) {B : Set X.Opens}
    (hB : Opens.IsBasis B) (h : ∀ W ∈ B, ∀ z : Γ(A, W), ψ.app W z = χ.app W z) : ψ = χ := by
  refine Scheme.Modules.hom_ext ψ χ fun O ↦ ?_
  ext z
  refine sections_eq_of_locally_eq Z _ _ fun y hy ↦ ?_
  obtain ⟨W, hWB, hyW, hWO⟩ := (Opens.isBasis_iff_nbhd.mp hB) hy
  refine ⟨W, hWO, hyW, ?_⟩
  calc Z.presheaf.map (homOfLE hWO).op (ψ.app O z)
      = ψ.app W (A.presheaf.map (homOfLE hWO).op z) :=
        (CardinalGeneration.app_map ψ (homOfLE hWO) z).symm
    _ = χ.app W (A.presheaf.map (homOfLE hWO).op z) := h W hWB _
    _ = Z.presheaf.map (homOfLE hWO).op (χ.app O z) :=
        CardinalGeneration.app_map χ (homOfLE hWO) z

/-! ### Invariance along a pair of morphisms

The invariance condition, and the vanishing it implies, do not use the groupoid structure: they
make sense for any two morphisms `t s : R ⟶ U` of schemes and any morphism
`α : t^*F ⟶ s^*F`.  They are stated in that generality here, and specialised to a groupoid scheme
below. -/

section TransitionInvariant

variable {U R : Scheme.{u}} (t s : R ⟶ U) (F : U.Modules)
  (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)
  (N : ∀ V : U.affineOpens, Submodule Γ(U, V.1) Γ(F, V.1))

/-- **The condition imposed on a family of submodules of the sections by a morphism
`α : t^*F ⟶ s^*F`.**  For two morphisms `t s : R ⟶ U` of schemes, a family of submodules
`N V ⊆ Γ(F, V)` over the affine opens of `U` is *invariant* under `α` if, for all affine opens `V`,
`V'` of `U` and every affine open `W` of `R` with `W ⊆ t⁻¹V` and `W ⊆ s⁻¹V'`, `α` sends the
pullback along `t` of a section in `N V` into the `Γ(R, W)`-span of the pullbacks along `s` of the
sections in `N V'`. -/
abbrev IsTransitionInvariant : Prop :=
  ∀ (V V' : U.affineOpens) (W : R.affineOpens)
    (ht : W.1 ≤ t ⁻¹ᵁ V.1) (hs : W.1 ≤ s ⁻¹ᵁ V'.1)
    (n : Γ(F, V.1)), n ∈ N V →
      α.app W.1 (pullbackSectionHom t F V.1 W.1 ht n) ∈
        Submodule.span Γ(R, W.1)
          (pullbackSectionHom s F V'.1 W.1 hs '' (N V' : Set Γ(F, V'.1)))

variable [F.IsQuasicoherent] (hN : IsCompatible F N)

/-- The inclusion into `F` of the subsheaf cut out by a compatible family of submodules of its
sections. -/
def compatibleModuleι : compatibleModule F N hN ⟶ F := (sheafSubmodule F N hN).ι

/-- The inclusion of the subsheaf cut out by a compatible family is a monomorphism. -/
instance mono_compatibleModuleι : Mono (compatibleModuleι F N hN) :=
  (Scheme.Modules.toPresheafOfModules U).mono_of_mono_map
    (inferInstanceAs (Mono (sheafSubmodule F N hN).toSubmodule.ι))

include hN in
/-- The projection to the cokernel of `s^*𝒢 → s^*F` kills the pullback along `s` of a section of
`F` which lies in the family. -/
private theorem cokernelπ_pullbackSection_eq_zero (V' : U.Opens)
    (hV' : IsAffineOpen V') (W : R.Opens) (hs : W ≤ s ⁻¹ᵁ V')
    (n' : Γ(F, V')) (hn' : n' ∈ N ⟨V', hV'⟩) :
    (cokernel.π ((Scheme.Modules.pullback s).map (compatibleModuleι F N hN))).app W
        (pullbackSectionHom s F V' W hs n') = 0 := by
  have hmem : IsLocallyIn F N n' :=
    (isLocallyIn_iff_mem F N hN ⟨V', hV'⟩ n').mpr hn'
  have hz : pullbackSectionHom s F V' W hs n' =
      ((Scheme.Modules.pullback s).map (compatibleModuleι F N hN)).app W
        (pullbackSectionHom s (compatibleModule F N hN) V' W hs
          (mkSection F N hN n' hmem)) :=
    (pullbackSectionHom_naturality s (compatibleModuleι F N hN) V' W hs
      (mkSection F N hN n' hmem)).symm
  rw [hz, ← app_comp_apply, cokernel.condition, app_zero_apply]

include hN in
/-- The composite `t^*𝒢 → t^*F → s^*F → coker(s^*𝒢 → s^*F)` vanishes when the family is invariant.
It is enough to check this on the sections over the affine opens of the arrow scheme lying over
affine opens of the object scheme along both the source and the target: those sections are spanned
by the pullbacks along `t` of the sections of `𝒢`, the invariance condition puts the image of such
a pullback in the span of the pullbacks along `s` of sections of `𝒢`, and the projection to the
cokernel kills that span. -/
theorem transition_comp_cokernelπ_eq_zero (hinv : IsTransitionInvariant t s F α N) :
    (Scheme.Modules.pullback t).map (compatibleModuleι F N hN) ≫ α ≫
        cokernel.π ((Scheme.Modules.pullback s).map (compatibleModuleι F N hN)) = 0 := by
  classical
  have hq : (compatibleModule F N hN).IsQuasicoherent := isQuasicoherent_sheafSubmodule F N hN
  refine hom_ext_of_isBasis _ 0 (isBasis_affineOpens_over₂ t s) ?_
  rintro W ⟨hWaff, ⟨V, hV, ht⟩, ⟨V', hV', hs⟩⟩ z
  rw [app_zero_apply]
  have hspan := span_pullbackSection_eq_top t (compatibleModule F N hN) hV hWaff ht
  have hgen : ∀ y ∈ Set.range (fun a : Γ(compatibleModule F N hN, V) ↦
      pullbackSectionHom t (compatibleModule F N hN) V W ht a),
      ((Scheme.Modules.pullback t).map (compatibleModuleι F N hN) ≫ α ≫
          cokernel.π ((Scheme.Modules.pullback s).map
            (compatibleModuleι F N hN))).app W y = 0 := by
    rintro y ⟨a, rfl⟩
    rw [app_comp_apply, app_comp_apply,
      show ((Scheme.Modules.pullback t).map (compatibleModuleι F N hN)).app W
          (pullbackSectionHom t (compatibleModule F N hN) V W ht a) =
          pullbackSectionHom t F V W ht
            (valSection F N hN a) from
        pullbackSectionHom_naturality t (compatibleModuleι F N hN) V W ht a]
    refine eq_zero_of_mem_span_of_semilinear (RingHom.id Γ(R, W))
      (fun w ↦ (cokernel.π ((Scheme.Modules.pullback s).map
        (compatibleModuleι F N hN))).app W w)
      (fun x y ↦ by rw [map_add]) (by rw [map_zero])
      (fun r x ↦ Scheme.Modules.Hom.app_smul _ r x) ?_
      (hinv ⟨V, hV⟩ ⟨V', hV'⟩ ⟨W, hWaff⟩ ht hs _
        ((isLocallyIn_iff_mem F N hN ⟨V, hV⟩ _).mp (isLocallyIn_valSection F N hN a)))
    rintro w ⟨n'', hn'', rfl⟩
    exact cokernelπ_pullbackSection_eq_zero s F N hN V' hV' W hs n'' hn''
  exact eq_zero_of_mem_span_of_semilinear (RingHom.id Γ(R, W))
    (fun y ↦ ((Scheme.Modules.pullback t).map (compatibleModuleι F N hN) ≫ α ≫
      cokernel.π ((Scheme.Modules.pullback s).map (compatibleModuleι F N hN))).app W y)
    (fun x y ↦ by rw [map_add]) (by rw [map_zero])
    (fun r x ↦ Scheme.Modules.Hom.app_smul _ r x) hgen (hspan.ge Submodule.mem_top)

end TransitionInvariant

/-! ### Invariant families of submodules -/

section Invariant

variable {S : Scheme.{u}} {G : GroupoidScheme S} (M : QuasicoherentModule G)
  (N : ∀ V : G.objects.left.affineOpens,
    Submodule Γ(G.objects.left, V.1) Γ(M.module, V.1))

/-- **The condition imposed on a candidate submodule by the descent morphism.**  A family of
submodules `N V ⊆ Γ(F, V)` of the sections of a quasi-coherent module `(F, α)` on a groupoid
scheme over the affine opens of the object scheme is *invariant* if, for all affine opens `V`, `V'`
of the object scheme and every affine open `W` of the arrow scheme with `W ⊆ t⁻¹V` and `W ⊆ s⁻¹V'`,
the descent morphism sends the pullback along `t` of a section in `N V` into the `Γ(R, W)`-span of
the pullbacks along `s` of the sections in `N V'`.

Over such a triple `Γ(t^*F, W) = Γ(R, W) ⊗_{Γ(U, V)} Γ(F, V)` by Stacks 01I9, so this says that
`α` carries the base change of `N V` into the base change of `N V'`; since such `W` form a basis of
the arrow scheme, it says that `α(t^*𝒢) ⊆ s^*𝒢` for the subsheaf `𝒢` cut out by `N`. -/
abbrev IsInvariant : Prop :=
  IsTransitionInvariant G.target.left G.source.left M.module M.alpha N

variable (hN : IsCompatible M.module N)

/-- The subsheaf of `F` cut out by a compatible family of submodules of its sections, as an
`𝒪_U`-module. -/
abbrev invariantModule : G.objects.left.Modules := compatibleModule M.module N hN

/-- The inclusion of the subsheaf cut out by a compatible family into `F`. -/
def invariantι : invariantModule M N hN ⟶ M.module := compatibleModuleι M.module N hN

/-- The subsheaf cut out by a compatible family is quasi-coherent. -/
theorem isQuasicoherent_invariantModule : (invariantModule M N hN).IsQuasicoherent :=
  isQuasicoherent_sheafSubmodule M.module N hN

/-- The inclusion of the subsheaf cut out by a compatible family is a monomorphism. -/
instance mono_invariantι : Mono (invariantι M N hN) :=
  (Scheme.Modules.toPresheafOfModules G.objects.left).mono_of_mono_map
    (inferInstanceAs (Mono (sheafSubmodule M.module N hN).toSubmodule.ι))

include hN in
/-- Over an affine open, the sections of the subsheaf cut out by a compatible family are exactly
the members of the family. -/
theorem mem_of_section_invariantModule (V : G.objects.left.affineOpens)
    (z : Γ(invariantModule M N hN, V.1)) : valSection M.module N hN z ∈ N V :=
  (isLocallyIn_iff_mem M.module N hN V _).mp (isLocallyIn_valSection M.module N hN z)

section Flat

variable [Flat G.source.left] [Flat G.target.left]

/-- The pullback of the inclusion of the subsheaf along the source is a monomorphism, because
pullback along a flat morphism is left exact. -/
instance mono_pullback_invariantι :
    Mono ((Scheme.Modules.pullback G.source.left).map (invariantι M N hN)) :=
  Functor.map_mono _ _

omit [Flat G.source.left] [Flat G.target.left] in
include hN in
/-- The composite `t^*𝒢 → t^*F → s^*F → coker(s^*𝒢 → s^*F)` vanishes when the family is invariant.
This is `transition_comp_cokernelπ_eq_zero` for the target and the source of the groupoid
scheme. -/
theorem invariant_comp_cokernelπ_eq_zero (hinv : IsInvariant M N) :
    (Scheme.Modules.pullback G.target.left).map (invariantι M N hN) ≫ M.alpha ≫
        cokernel.π ((Scheme.Modules.pullback G.source.left).map (invariantι M N hN)) = 0 :=
  transition_comp_cokernelπ_eq_zero G.target.left G.source.left M.module M.alpha N hN hinv

include hN in
/-- The descent morphism of `(F, α)` restricted to the subsheaf cut out by an invariant compatible
family.  It exists because a monomorphism in an abelian category is the kernel of its cokernel,
and `invariant_comp_cokernelπ_eq_zero` says that the composite of `t^*𝒢 → t^*F → s^*F` with that
cokernel vanishes. -/
def invariantDescent (hinv : IsInvariant M N) :
    (Scheme.Modules.pullback G.target.left).obj (invariantModule M N hN) ⟶
      (Scheme.Modules.pullback G.source.left).obj (invariantModule M N hN) :=
  Abelian.monoLift ((Scheme.Modules.pullback G.source.left).map (invariantι M N hN))
    ((Scheme.Modules.pullback G.target.left).map (invariantι M N hN) ≫ M.alpha)
    (by rw [Category.assoc]; exact invariant_comp_cokernelπ_eq_zero M N hN hinv)

omit [Flat G.target.left] in
include hN in
/-- **The defining property of the restricted descent morphism**: it is compatible with `α` through
the inclusion of the subsheaf. -/
@[reassoc]
theorem invariantDescent_comp_ι (hinv : IsInvariant M N) :
    invariantDescent M N hN hinv ≫
        (Scheme.Modules.pullback G.source.left).map (invariantι M N hN) =
      (Scheme.Modules.pullback G.target.left).map (invariantι M N hN) ≫ M.alpha :=
  Abelian.monoLift_comp _ _ _

omit [Flat G.target.left] in
include hN in
/-- The restricted descent morphism satisfies the cocycle condition, by cancelling the monomorphism
obtained by pulling the inclusion of the subsheaf back along `c ≫ s`. -/
theorem successiveDescent_invariantDescent (hinv : IsInvariant M N) :
    successiveDescent G (invariantDescent M N hN hinv) =
      reindexHom G.comp.left (invariantDescent M N hN hinv) := by
  have hmono : Mono ((Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map
      (invariantι M N hN)) := Functor.map_mono _ _
  refine (cancel_mono ((Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map
    (invariantι M N hN))).1 ?_
  rw [_root_.AlgebraicGeometry.GroupoidScheme.successiveDescent_naturality G
      (invariantDescent M N hN hinv) M.alpha (invariantι M N hN)
      (invariantDescent_comp_ι M N hN hinv),
    reindexHom_naturality G.comp.left (invariantDescent M N hN hinv) M.alpha (invariantι M N hN)
      (invariantDescent_comp_ι M N hN hinv),
    M.cocycle]

omit [Flat G.target.left] in
include hN in
/-- The restricted descent morphism is the identity after pulling back along the identity section,
by cancelling the inclusion of the subsheaf. -/
theorem identityDescent_invariantDescent (hinv : IsInvariant M N) :
    identityDescent G (invariantDescent M N hN hinv) = 𝟙 (invariantModule M N hN) := by
  refine (cancel_mono (invariantι M N hN)).1 ?_
  rw [_root_.AlgebraicGeometry.GroupoidScheme.identityDescent_naturality G
      (invariantDescent M N hN hinv) M.alpha (invariantι M N hN)
      (invariantDescent_comp_ι M N hN hinv), M.identity, Category.comp_id, Category.id_comp]

/-- **The submodule of `(F, α)` cut out by an invariant compatible family**, as a quasi-coherent
module on the groupoid scheme. -/
def invariantObject (hinv : IsInvariant M N) : QuasicoherentModule G where
  module := invariantModule M N hN
  isQuasicoherent := isQuasicoherent_invariantModule M N hN
  alpha := invariantDescent M N hN hinv
  cocycle := successiveDescent_invariantDescent M N hN hinv
  identity := identityDescent_invariantDescent M N hN hinv

omit [Flat G.target.left] in
/-- The underlying module of `invariantObject M N hN hinv` is `invariantModule M N hN`. -/
@[simp]
theorem invariantObject_module (hinv : IsInvariant M N) :
    (invariantObject M N hN hinv).module = invariantModule M N hN := rfl

/-- The inclusion of the submodule cut out by an invariant compatible family into `(F, α)`. -/
def invariantHom (hinv : IsInvariant M N) : invariantObject M N hN hinv ⟶ M where
  hom := invariantι M N hN
  comm := invariantDescent_comp_ι M N hN hinv

end Flat

end Invariant

/-- The forgetful functor to modules on the object scheme is faithful: a morphism of quasi-coherent
modules on a groupoid scheme carries no data beyond the underlying morphism of modules. -/
instance {S : Scheme.{u}} {G : GroupoidScheme S} : (QuasicoherentModule.forget G).Faithful where
  map_injective h := QuasicoherentModule.Hom.ext h

section MonoHom

variable {S : Scheme.{u}} {G : GroupoidScheme S} [Flat G.source.left] [Flat G.target.left]
  (M : QuasicoherentModule G)
  (N : ∀ V : G.objects.left.affineOpens,
    Submodule Γ(G.objects.left, V.1) Γ(M.module, V.1))
  (hN : IsCompatible M.module N)

/-- The inclusion of the submodule cut out by an invariant compatible family is a
monomorphism. -/
instance mono_invariantHom (hinv : IsInvariant M N) : Mono (invariantHom M N hN hinv) :=
  (QuasicoherentModule.forget G).mono_of_mono_map
    (show Mono (invariantι M N hN) from inferInstance)

end MonoHom

/-! ### Existence of bounded invariant compatible families -/

section Existence

variable {U R : Scheme.{u}} (t s : R ⟶ U) (F : U.Modules) [F.IsQuasicoherent]
  (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F)

/-- **A finite set of sections expressing the image of a pullback under a transition morphism.**
For morphisms `t s : R ⟶ U`, a morphism `α : t^*F ⟶ s^*F`, affine opens `V`, `V'` of `U`, an
affine open `W` of `R` and a
section `n` of `F` over `V`, there are finitely many sections of `F` over `V'` whose pullbacks
along `s` span an element containing the image under `α` of the pullback of `n` along `t`.  The
statement is phrased so as to hold vacuously unless `W` lies over `V` along `t` and over `V'` along
`s`, which makes the resulting choice function total. -/
theorem exists_finite_subset_span_alpha (V V' : U.affineOpens)
    (W : R.affineOpens) (n : Γ(F, V.1)) :
    ∃ e : Set Γ(F, V'.1), e.Finite ∧
      ∀ (ht : W.1 ≤ t ⁻¹ᵁ V.1) (hs : W.1 ≤ s ⁻¹ᵁ V'.1),
        α.app W.1 (pullbackSectionHom t F V.1 W.1 ht n) ∈
          Submodule.span Γ(R, W.1)
            (pullbackSectionHom s F V'.1 W.1 hs '' e) := by
  classical
  by_cases h : W.1 ≤ t ⁻¹ᵁ V.1 ∧ W.1 ≤ s ⁻¹ᵁ V'.1
  · obtain ⟨ht, hs⟩ := h
    have hspan := span_pullbackSection_eq_top s F V'.2 W.2 hs
    have hmem : α.app W.1
        (pullbackSectionHom t F V.1 W.1 ht n) ∈
        Submodule.span Γ(R, W.1) (Set.range fun a : Γ(F, V'.1) ↦
          pullbackSectionHom s F V'.1 W.1 hs a) :=
      hspan.ge Submodule.mem_top
    obtain ⟨k, c, y, hy⟩ := Submodule.mem_span_set'.mp hmem
    refine ⟨Set.range fun i : Fin k ↦ (y i).2.choose, Set.finite_range _, fun ht' hs' ↦ ?_⟩
    show α.app W.1
        (pullbackSectionHom t F V.1 W.1 ht n) ∈
      Submodule.span Γ(R, W.1)
        (pullbackSectionHom s F V'.1 W.1 hs ''
          Set.range fun i : Fin k ↦ (y i).2.choose)
    rw [← hy]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨(y i).2.choose, Set.mem_range_self i, (y i).2.choose_spec⟩
  · exact ⟨∅, Set.finite_empty, fun ht' hs' ↦ absurd ⟨ht', hs'⟩ h⟩

variable (U R) in
/-- The three kinds of enlargement used to close off a family of sets of sections of `F` over the
affine opens of `U`: restriction of a section to a smaller affine open, generation of
a section over a smaller affine open from sections over a larger one, and generation of the image
under `α` of the pullback of a section from pullbacks of sections over a second affine open. -/
abbrev InvArrow : Type u :=
  U.affineOpens ⊕ U.affineOpens ⊕
    U.affineOpens × R.affineOpens

variable (U R) in
/-- The affine open over which the input of an enlargement operator lives. -/
def invSrc (a : InvArrow U R) : U.affineOpens :=
  match a with
  | .inl V₀ => V₀
  | .inr (.inl V₀) => V₀
  | .inr (.inr p) => p.1

/-- The set of sections over `V` added by an enlargement operator applied to a single section. -/
def invGen
    (gres : ∀ V V₀ : U.affineOpens, Γ(F, V₀.1) → Set Γ(F, V.1))
    (gα : ∀ V V' : U.affineOpens,
      R.affineOpens → Γ(F, V.1) → Set Γ(F, V'.1))
    (V : U.affineOpens) (a : InvArrow U R) :
    Γ(F, (invSrc U R a).1) → Set Γ(F, V.1) :=
  match a with
  | .inl V₀ => fun x ↦ {y | ∃ h : V.1 ≤ V₀.1, F.presheaf.map (homOfLE h).op x = y}
  | .inr (.inl V₀) => fun y ↦ gres V V₀ y
  | .inr (.inr p) => fun n ↦ gα p.1 V p.2 n

/-- **The closure step producing an invariant compatible family.**  Let `t s : R ⟶ U` be morphisms
of schemes, `F` a quasi-coherent `𝒪_U`-module and `α : t^*F ⟶ s^*F` a morphism, and let `κ` be an
infinite cardinal bounding the numbers of affine opens of `U` and of `R`.  Then every family of at
most `κ` sections of `F` over each affine open of `U` is contained in such a family whose spans
form a compatible family of submodules invariant under `α`, i.e. the sections of a candidate
`κ`-generated submodule of `(F, α)`. -/
theorem exists_bounded_invariant_compatible_family {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hU : Cardinal.mk U.affineOpens ≤ κ)
    (hR : Cardinal.mk R.affineOpens ≤ κ)
    (S₀ : ∀ V : U.affineOpens, Set Γ(F, V.1))
    (h₀ : ∀ V, Cardinal.mk ↥(S₀ V) ≤ κ) :
    ∃ T : ∀ V : U.affineOpens, Set Γ(F, V.1),
      (∀ V, S₀ V ⊆ T V) ∧ (∀ V, Cardinal.mk ↥(T V) ≤ κ) ∧
      IsCompatible F (fun V ↦ Submodule.span Γ(U, V.1) (T V)) ∧
      IsTransitionInvariant t s F α (fun V ↦ Submodule.span Γ(U, V.1) (T V)) := by
  classical
  choose gres hgresfin hgresspan using exists_finite_subset_span F
  choose gα hgαfin hgαspan using exists_finite_subset_span_alpha t s F α
  have hgbd : ∀ (V : U.affineOpens) (a : InvArrow U R)
      (x : Γ(F, (invSrc U R a).1)), Cardinal.mk ↥(invGen F gres gα V a x) ≤ κ := by
    intro V a
    obtain V₀ | V₀ | p := a
    · exact fun x ↦ mk_le_of_subsingleton_of_aleph0_le hκ (by rintro y ⟨h1, rfl⟩ z ⟨h2, rfl⟩; rfl)
    · exact fun y ↦ ((hgresfin V V₀ y).lt_aleph0.le).trans hκ
    · exact fun n ↦ ((hgαfin p.1 V p.2 n).lt_aleph0.le).trans hκ
  obtain ⟨T, hTb, hT₀, hTcl⟩ :=
    exists_bounded_closure (fun _ : U.affineOpens ↦ invSrc U R)
      (invGen F gres gα) hκ
      (fun _ ↦ mk_sum_le_of_le hκ hU (mk_sum_le_of_le hκ hU (mk_prod_le_of_le hκ hU hR)))
      hgbd S₀ h₀
  · have hres : ∀ (V V₀ : U.affineOpens) (h : V.1 ≤ V₀.1) (x : Γ(F, V₀.1)),
        x ∈ T V₀ → F.presheaf.map (homOfLE h).op x ∈ T V :=
      fun V V₀ h x hx ↦ hTcl V (.inl V₀) x hx ⟨h, rfl⟩
    have hgenres : ∀ (V V₀ : U.affineOpens) (y : Γ(F, V₀.1)),
        y ∈ T V₀ → gres V V₀ y ⊆ T V := fun V V₀ y hy ↦ hTcl V (.inr (.inl V₀)) y hy
    have hgenα : ∀ (V V' : U.affineOpens) (W : R.affineOpens)
        (n : Γ(F, V.1)), n ∈ T V → gα V V' W n ⊆ T V' :=
      fun V V' W n hn ↦ hTcl V' (.inr (.inr (V, W))) n hn
    refine ⟨T, hT₀, hTb, ?_, ?_⟩
    · refine isCompatible_span F T fun V V' h ↦ le_antisymm ?_ ?_
      · refine Submodule.span_le.mpr fun y hy ↦ ?_
        exact Submodule.span_mono (Set.image_mono (hgenres V V' y hy)) (hgresspan V V' y h)
      · refine Submodule.span_le.mpr ?_
        rintro z ⟨x, hx, rfl⟩
        exact Submodule.subset_span (hres V' V h x hx)
    · intro V V' W ht hs n hn
      refine mem_of_mem_span_of_semilinear (t.appLE V.1 W.1 ht).hom
        (fun m ↦ α.app W.1
          (pullbackSectionHom t F V.1 W.1 ht m))
        (fun x y ↦ by rw [map_add, map_add]) (by rw [map_zero, map_zero])
        (fun r x ↦ ?_) _ (fun m hm ↦ ?_) hn
      · rw [show pullbackSectionHom t F V.1 W.1 ht (r • x) =
              t.appLE V.1 W.1 ht r •
                pullbackSectionHom t F V.1 W.1 ht x from
            pullbackSectionHom_smul t F V.1 W.1 ht r x,
          Scheme.Modules.Hom.app_smul]
      · refine Submodule.span_mono (Set.image_mono ?_) (hgαspan V V' W m ht hs)
        exact fun z hz ↦ Submodule.subset_span (hgenα V V' W m hm hz)

/-- **A section of `F` lies in a bounded invariant compatible family.**  This is the common first
step of the existence results below: the family of spans of the sets `T V` is compatible and
invariant, the sets are bounded by `κ`, and the given section is locally in the family. -/
private theorem exists_invariant_compatible_family_of_section {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hU : Cardinal.mk U.affineOpens ≤ κ)
    (hR : Cardinal.mk R.affineOpens ≤ κ) (O : U.Opens) (x : Γ(F, O)) :
    ∃ T : ∀ V : U.affineOpens, Set Γ(F, V.1), (∀ V, Cardinal.mk ↥(T V) ≤ κ) ∧
      ∃ _ : IsCompatible F (fun V ↦ Submodule.span Γ(U, V.1) (T V)),
        IsTransitionInvariant t s F α (fun V ↦ Submodule.span Γ(U, V.1) (T V)) ∧
          IsLocallyIn F (fun V ↦ Submodule.span Γ(U, V.1) (T V)) x := by
  obtain ⟨T, hT₀, hTb, hN, hinv⟩ := exists_bounded_invariant_compatible_family t s F α hκ hU hR
    (fun V ↦ {y | ∃ h : V.1 ≤ O, y = F.presheaf.map (homOfLE h).op x})
    fun V ↦ mk_le_of_subsingleton_of_aleph0_le hκ (by rintro a ⟨ha, rfl⟩ b ⟨hb, rfl⟩; rfl)
  exact ⟨T, hTb, hN, hinv, fun V h ↦ Submodule.subset_span (hT₀ V ⟨h, rfl⟩)⟩

/-- **Every section of `F` lies in a bounded submodule invariant under `α`.**  Let `t s : R ⟶ U`
be morphisms of schemes with `s` flat, let `F` be a quasi-coherent `𝒪_U`-module and
`α : t^*F ⟶ s^*F` a morphism, and let `κ` be an infinite cardinal dominating the numbers of affine
opens of `U` and of `R`.  Then every section of `F` over an open of `U` is a section of a
quasi-coherent, `κ`-generated submodule `ι : 𝒢 ⟶ F` such that `α` restricts along `ι` to a
morphism `β : t^*𝒢 ⟶ s^*𝒢`.

No cocycle condition is asked of `α`; this is the closure step of the source's proof of
Stacks 077U, which uses only `α`. -/
theorem exists_transitionInvariant_mono_of_section [Flat s] {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hU : Cardinal.mk U.affineOpens ≤ κ)
    (hR : Cardinal.mk R.affineOpens ≤ κ) (O : U.Opens) (x : Γ(F, O)) :
    ∃ (Y : U.Modules) (ι : Y ⟶ F)
      (β : (Scheme.Modules.pullback t).obj Y ⟶ (Scheme.Modules.pullback s).obj Y),
      Mono ι ∧ Y.IsQuasicoherent ∧ CardinalGeneration.IsCardinalGenerated Y κ ∧
        β ≫ (Scheme.Modules.pullback s).map ι = (Scheme.Modules.pullback t).map ι ≫ α ∧
        x ∈ Set.range (ι.app O) := by
  obtain ⟨T, hTb, hN, hinv, hloc⟩ :=
    exists_invariant_compatible_family_of_section t s F α hκ hU hR O x
  let ι := compatibleModuleι F _ hN
  have hmono : Mono ι := mono_compatibleModuleι F _ hN
  have hmono' : Mono ((Scheme.Modules.pullback s).map ι) := Functor.map_mono _ _
  refine ⟨compatibleModule F _ hN, ι,
    Abelian.monoLift ((Scheme.Modules.pullback s).map ι)
      ((Scheme.Modules.pullback t).map ι ≫ α)
      (by rw [Category.assoc]; exact transition_comp_cokernelπ_eq_zero t s F α _ hN hinv),
    hmono, isQuasicoherent_sheafSubmodule F _ hN,
    CardinalGeneration.isCardinalGenerated_sheafSubmodule F κ T hTb hN,
    Abelian.monoLift_comp _ _ _, ⟨mkSection F _ hN x hloc, rfl⟩⟩

end Existence

section ExistenceGroupoid

variable {S : Scheme.{u}} {G : GroupoidScheme S} (M : QuasicoherentModule G)
  [Flat G.source.left] [Flat G.target.left]

omit [Flat G.target.left] in
/-- **Every section of `F` lies in a bounded submodule of `(F, α)`.**  For `κ` infinite dominating
the numbers of affine opens of the object scheme and of the arrow scheme, every section of `F` over
an open of the object scheme is a section of a `κ`-generated quasi-coherent submodule of `(F, α)`,
that is, of a quasi-coherent module on the groupoid scheme mapping monomorphically to `(F, α)`. -/
theorem exists_invariantObject_of_section {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hU : Cardinal.mk G.objects.left.affineOpens ≤ κ)
    (hR : Cardinal.mk G.arrows.left.affineOpens ≤ κ)
    (O : G.objects.left.Opens) (x : Γ(M.module, O)) :
    ∃ (P : QuasicoherentModule G) (j : P ⟶ M), Mono j ∧
      CardinalGeneration.IsCardinalGenerated P.module κ ∧ x ∈ Set.range (j.hom.app O) := by
  obtain ⟨T, hTb, hN, hinv, hloc⟩ := exists_invariant_compatible_family_of_section
    G.target.left G.source.left M.module M.alpha hκ hU hR O x
  refine ⟨invariantObject M _ hN hinv, invariantHom M _ hN hinv, inferInstance, ?_,
    ⟨mkSection M.module _ hN x hloc, rfl⟩⟩
  exact CardinalGeneration.isCardinalGenerated_sheafSubmodule M.module κ T hTb hN

end ExistenceGroupoid

end Stacks.AlgebraicGeometry.GroupoidCardinalGeneration

end
