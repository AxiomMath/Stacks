module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import StacksFrontier.RingTheory.Flat.ZeroFunctorLimit

/-!
# Vanishing of a base-changed module map descends along a filtered colimit of algebras

Let `A` be a commutative ring, `B` an `A`-algebra, and `u : M ⟶ N` a homomorphism of `B`-modules
whose source is a finite `B`-module.  For an `A`-algebra `T` write `u_T` for the base change
`T ⊗_A M ⟶ T ⊗_A N` of `u`, which is `LinearMap.lTensor T (u.restrictScalars A)`.

`StacksFrontier/RingTheory/Flat/ZeroFunctorLimit.lean` proves that `u_T = 0` descends to a finitely
generated `A`-subalgebra of `T`, and hence
(`Stacks.Flattening.exists_lTensor_eq_zero_of_directed`) to a member of any directed family of
`A`-*subalgebras* of `T` whose union is `T`.  That form is not the one the geometry of
[Stacks, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ) produces.  There the algebras are
the rings of sections `Γ(T_i, ⊤)` of an inverse system of affine schemes over the base, and `T`
is the ring of sections at the limit; the structure maps `Γ(T_i, ⊤) ⟶ T` are *not* injective, so
no `C i` is a subalgebra of `T` and
`Stacks.Flattening.exists_lTensor_eq_zero_of_directed` does not apply.  For a two-element
example inside that class, take `A` any ring, `C 0 = A[X]`, `C 1 = A` and the transition map
`X ↦ 0`; the colimit is `A`, and `A[X]` is not a subalgebra of it.

This file proves the descent for an arbitrary filtered colimit, which covers that case:
`Stacks.Flattening.exists_lTensor_eq_zero_of_colimit`.  The colimit is described by the two
element-level conditions `hsurj` and `hker` below — every element of `T` comes from a stage, and
an element of a stage killed in `T` is killed by some transition map.  These are exactly the
statement that `T` is the filtered colimit of the `C i`, they mention only the system of
algebras (not `u`, `M` or `N`), and for a colimit cocone in `CommRingCat` over a directed
preorder they are discharged by
`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'` together with
`CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`, the forgetful functor out of
`CommRingCat` preserving filtered colimits.

## Main results

* `Stacks.Flattening.exists_rTensor_eq_zero_of_directLimit`: an element of `G i ⊗_A P` that dies
  in `(lim G) ⊗_A P` already dies in `G j ⊗_A P` for some `j ≥ i`.  This is Mathlib's
  `TensorProduct.directLimitLeft` — tensoring commutes with a direct limit — combined with
  `Module.DirectLimit.of.zero_exact`.
* `Stacks.Flattening.tmul_one_eq_zero_of_map`: the vanishing of `1 ⊗ n` persists along a
  transition map of the system, the analogue for a colimit of
  `Stacks.Flattening.tmul_one_eq_zero_of_le`.
* `Stacks.Flattening.exists_lTensor_eq_zero_of_colimit`: the descent itself.

## Implementation notes

The proof is the one the subalgebra version cannot run.  It does not use
`Stacks.Flattening.exists_adjoin_lTensor_eq_zero`: that lemma produces a finitely generated
`A`-subalgebra of `T` over which `u` already vanishes, and when the structure maps are not
injective the vanishing cannot be lifted back from a subalgebra of `T` to a stage — the map
`C i ⊗_A N ⟶ (image of C i) ⊗_A N` is surjective, not injective, so it carries vanishing the
wrong way.  What replaces it is the colimit property, used through
`Stacks.Flattening.exists_rTensor_eq_zero_of_directLimit`.

`hsurj` and `hker` are converted into a single `LinearEquiv` from `Module.DirectLimit` onto `T`
rather than used directly, because that is the form in which Mathlib's
`TensorProduct.directLimitLeft` is available; surjectivity of the comparison map is `hsurj` and
its injectivity is `hker`.  `Module.DirectLimit` needs `DecidableEq` on the index, which is why
`Stacks.Flattening.exists_rTensor_eq_zero_of_directLimit` carries that hypothesis while
`Stacks.Flattening.exists_lTensor_eq_zero_of_colimit`, whose statement does not mention a direct
limit, opens with `classical`.

`Stacks.Flattening.directedSystem_toLinearMap` transfers a `DirectedSystem` along
`AlgHom.toLinearMap`.  It is needed because the system is given by `AlgHom`s — the base change
is an `A`-algebra and `1 : C i` has to be carried to `1 : C j` — while `Module.DirectLimit`
indexes its systems by `LinearMap`s.  The two underlying functions are the same, so the transfer
is the two structure fields applied to the `AlgHom` instance.

Nothing here carries Tag 05MJ.  The tag is a statement about a subterminal functor on schemes
over a base being limit preserving; this is one of its algebraic inputs, the one that the
reduction in `StacksFrontier/AlgebraicGeometry/Flatness/ZeroFunctorLimitPreserving.lean` leaves
open as the hypothesis `hdesc` of
`Stacks.Flatness.ModuleMapBaseChangeSituation.zeroFunctor_preservesColimit_of_isAffine`.  What
still stands between the two is geometric and is not addressed here: the identification of the
sections of a pulled-back quasi-coherent module with a base change
(`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`), the passage from
`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` — which needs a *small* index category,
`I : Type u` with `Category.{u} I`, whereas Tag 05MJ is stated for `I : Type v` with
`Category.{w} I` — to a directed preorder, and the reduction of the vanishing of a homomorphism
of quasi-coherent modules on `X ×_S T` to a finite affine cover.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

section DirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} [Preorder ι]

/-- A directed system of `A`-algebras is a directed system of `A`-modules.  The two underlying
families of functions are the same; only the bundling differs. -/
theorem directedSystem_toLinearMap {C : ι → Type*} [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (φ : ∀ i j, i ≤ j → C i →ₐ[A] C j)
    [DirectedSystem C fun i j h ↦ (φ i j h : C i → C j)] :
    DirectedSystem (fun i ↦ C i) fun i j h ↦ ((φ i j h).toLinearMap : C i →ₗ[A] C j) := by
  constructor
  · intro i x
    exact DirectedSystem.map_self (F := C) (f := fun _ _ h ↦ (φ _ _ h : _ → _)) x
  · intro k j i hij hjk x
    exact DirectedSystem.map_map (F := C) (f := fun _ _ h ↦ (φ _ _ h : _ → _)) hij hjk x

/-- An element of `G i ⊗_A P` that dies in `(lim G) ⊗_A P` already dies in `G j ⊗_A P` for some
`j ≥ i`.

This is Mathlib's `TensorProduct.directLimitLeft`, that tensoring commutes with a direct limit,
followed by `Module.DirectLimit.of.zero_exact`. -/
theorem exists_rTensor_eq_zero_of_directLimit [DecidableEq ι] [IsDirectedOrder ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module A (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[A] G j) [DirectedSystem G (f · · ·)]
    (P : Type*) [AddCommGroup P] [Module A P] (i : ι) (x : G i ⊗[A] P)
    (hx : LinearMap.rTensor P (Module.DirectLimit.of A ι G f i) x = 0) :
    ∃ j, ∃ h : i ≤ j, LinearMap.rTensor P (f i j h) x = 0 := by
  have h1 := TensorProduct.directLimitLeft_rTensor_of f P x
  rw [hx, map_zero] at h1
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h1.symm
  exact ⟨j, hij, hj⟩

/-- Vanishing of `1 ⊗ n` persists along a transition map of a system of `A`-algebras.  This is
the colimit analogue of `Stacks.Flattening.tmul_one_eq_zero_of_le`. -/
theorem tmul_one_eq_zero_of_map {C : ι → Type*} [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (φ : ∀ i j, i ≤ j → C i →ₐ[A] C j) {P : Type*} [AddCommGroup P] [Module A P] {i j : ι}
    (h : i ≤ j) {n : P} (hn : (1 : C i) ⊗ₜ[A] n = 0) : (1 : C j) ⊗ₜ[A] n = 0 := by
  have := congrArg (LinearMap.rTensor P ((φ i j h).toLinearMap : C i →ₗ[A] C j)) hn
  rwa [map_zero, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at this

end DirectLimit

section Colimit

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  {C : ι → Type*} [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
  {T : Type*} [CommRing T] [Algebra A T]

/-- **The "zero" clause of Stacks 05MJ in filtered-colimit form.**  Let `(C i)` be a directed
system of `A`-algebras exhibiting the `A`-algebra `T` as its colimit, in the sense that every
element of `T` comes from some stage (`hsurj`) and an element of a stage that dies in `T` is
killed by some transition map (`hker`).  If the base change of `u : M →ₗ[B] N` to `T` is zero and
`M` is a finite `B`-module, then its base change to some `C i` is already zero.

Unlike `Stacks.Flattening.exists_lTensor_eq_zero_of_directed` this does not require the `C i` to
be subalgebras of `T`, so it applies to the colimit of the rings of sections of an inverse system
of affine schemes, whose structure maps to the limit need not be injective. -/
theorem exists_lTensor_eq_zero_of_colimit
    (φ : ∀ i j, i ≤ j → C i →ₐ[A] C j)
    [DirectedSystem C fun i j h ↦ (φ i j h : C i → C j)]
    (ψ : ∀ i, C i →ₐ[A] T)
    (hψ : ∀ i j (h : i ≤ j) (c : C i), ψ j (φ i j h c) = ψ i c)
    (hsurj : ∀ t : T, ∃ i, ∃ c : C i, ψ i c = t)
    (hker : ∀ (i : ι) (c : C i), ψ i c = 0 → ∃ j, ∃ h : i ≤ j, φ i j h c = 0)
    (u : M →ₗ[B] N) [Module.Finite B M]
    (h : LinearMap.lTensor T (u.restrictScalars A) = 0) :
    ∃ i, LinearMap.lTensor (C i) (u.restrictScalars A) = 0 := by
  classical
  obtain ⟨i₀, -, -⟩ := hsurj 0
  have hne : Nonempty ι := ⟨i₀⟩
  have hDS := directedSystem_toLinearMap φ
  set f : ∀ i j, i ≤ j → C i →ₗ[A] C j := fun i j h ↦ (φ i j h).toLinearMap with hf
  set l : Module.DirectLimit (fun i ↦ C i) f →ₗ[A] T :=
    Module.DirectLimit.lift A ι _ f (fun i ↦ (ψ i).toLinearMap) (fun i j h c ↦ hψ i j h c) with hl
  have hl_of : ∀ (i : ι) (c : C i), l (Module.DirectLimit.of A ι _ f i c) = ψ i c := fun i c ↦
    Module.DirectLimit.lift_of _ _ _
  -- `hsurj` is the surjectivity of the comparison map and `hker` its injectivity.
  have hbij : Function.Bijective l := by
    refine ⟨(injective_iff_map_eq_zero l).2 fun z hz ↦ ?_, fun t ↦ ?_⟩
    · obtain ⟨i, c, rfl⟩ := Module.DirectLimit.exists_of z
      rw [hl_of] at hz
      obtain ⟨j, hij, hj⟩ := hker i c hz
      rw [← Module.DirectLimit.of_f (f := f) (hij := hij) (x := c)]
      simp only [hf, AlgHom.toLinearMap_apply, hj, map_zero]
    · obtain ⟨i, c, rfl⟩ := hsurj t
      exact ⟨Module.DirectLimit.of A ι _ f i c, hl_of i c⟩
  set e := LinearEquiv.ofBijective l hbij with he
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule B M).FG)
  have hspan : Submodule.span B (s : Set M) = ⊤ := hs
  have hzero : ∀ m ∈ (s : Set M), (1 : T) ⊗ₜ[A] u m = 0 :=
    (lTensor_eq_zero_iff_of_span T u hspan).1 h
  -- One element at a time: transport the vanishing across `e` and detect it at a stage.
  have key : ∀ m : M, (1 : T) ⊗ₜ[A] u m = 0 → ∃ j, (1 : C j) ⊗ₜ[A] u m = 0 := by
    intro m hm
    have h1 : e (Module.DirectLimit.of A ι _ f i₀ 1) = (1 : T) := by
      rw [he, LinearEquiv.ofBijective_apply, hl_of]
      exact map_one (ψ i₀)
    have h3 : Module.DirectLimit.of A ι _ f i₀ (1 : C i₀) ⊗ₜ[A] u m = 0 := by
      apply (TensorProduct.congr e (LinearEquiv.refl A N)).injective
      rw [map_zero, TensorProduct.congr_tmul, LinearEquiv.refl_apply, h1, hm]
    obtain ⟨j, hij, hj⟩ := exists_rTensor_eq_zero_of_directLimit f N i₀ _
      (by rw [LinearMap.rTensor_tmul]; exact h3)
    rw [LinearMap.rTensor_tmul] at hj
    exact ⟨j, by simpa only [hf, AlgHom.toLinearMap_apply, map_one] using hj⟩
  -- Finitely many generators, so the finitely many stages have a common upper bound.
  choose jj hjj using fun (m : {x // x ∈ s}) ↦ key m.1 (hzero m.1 m.2)
  obtain ⟨k, hk⟩ := Finset.exists_le (s.attach.image jj)
  refine ⟨k, (lTensor_eq_zero_iff_of_span _ u hspan).2 fun m hm ↦ ?_⟩
  exact tmul_one_eq_zero_of_map φ
    (hk (jj ⟨m, hm⟩) (Finset.mem_image_of_mem jj (Finset.mem_attach _ _))) (hjj ⟨m, hm⟩)

end Colimit

end Stacks.Flattening

end
