module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.Topology.Connected.ContractedLocus

/-!
# Quasi-finiteness at a point, read off the set-theoretic fibre

For a morphism `f : X ⟶ Y` locally of finite type, Mathlib characterizes quasi-finiteness of `f`
at `x` as isolation of `x` in the scheme-theoretic fibre `f.fiber (f x)`. This file restates that
in terms of the set-theoretic fibre `f ⁻¹' {f x}` as a subspace of `X`, which is the form in which
it transports along embeddings, and records two consequences.

* A point whose set-theoretic fibre is finite is a quasi-finite point.
* If `f` is constant and quasi-finite at `x`, then `{x}` is clopen in `X`.

Finally, a purely topological input: a continuous closed map out of a Noetherian `T₀` space of
dimension at most one has finite fibres over the non-closed points of the target, since such a
fibre consists of generic points of irreducible components.

## Main results

* `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_exists_isOpen`.
* `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_finite_preimage_singleton`.
* `AlgebraicGeometry.Scheme.Hom.isClopen_singleton_of_quasiFiniteAt_of_forall_eq`.
* `finite_preimage_singleton_of_not_isClosed_singleton`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Fibres of a closed map over non-closed points.** Let `X` be a Noetherian `T₀` space of
dimension at most one and `g : X → Y` a closed map. If `{y}` is not closed, the fibre `g ⁻¹' {y}`
is finite: a closed point of `X` maps to a closed point, so every point of the fibre is the generic
point of an irreducible component of `X`, and there are finitely many of those. -/
theorem finite_preimage_singleton_of_not_isClosed_singleton [NoetherianSpace X] [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1) {g : X → Y} (hcl : IsClosedMap g) {y : Y}
    (hy : ¬ IsClosed ({y} : Set Y)) : (g ⁻¹' {y}).Finite := by
  have hsub : g ⁻¹' {y} ⊆ (fun x : X ↦ closure ({x} : Set X)) ⁻¹' irreducibleComponents X := by
    intro x hx
    refine (isClosed_singleton_or_closure_mem_irreducibleComponents hdim x).resolve_left ?_
    intro hxc
    refine hy ?_
    have := hcl _ hxc
    rwa [Set.image_singleton, show g x = y from hx] at this
  refine Set.Finite.subset (Set.Finite.preimage ?_
    (NoetherianSpace.finite_irreducibleComponents (α := X))) hsub
  intro a _ b _ hab
  exact (inseparable_iff_closure_eq.mpr hab).eq

end Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **Quasi-finiteness at a point is isolation in the set-theoretic fibre.** For `f` locally of
finite type, `f` is quasi-finite at `x` exactly when some open `U ∋ x` of `X` meets `f ⁻¹' {f x}`
only in `x`. -/
theorem Scheme.Hom.quasiFiniteAt_iff_exists_isOpen [LocallyOfFiniteType f] {x : X} :
    f.QuasiFiniteAt x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x → x' = x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (f.fiberHomeo (f x)).isOpen_image,
    Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply, isOpen_induced_iff]
  constructor
  · rintro ⟨U, hU, hpre⟩
    refine ⟨U, hU, ?_, fun x' hx' hfx ↦ ?_⟩
    · change (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' U
      rw [hpre]; rfl
    · have : (⟨x', hfx⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' U := hx'
      rw [hpre] at this
      exact congrArg Subtype.val this
  · rintro ⟨U, hU, hxU, h⟩
    refine ⟨U, hU, ?_⟩
    ext ⟨x', hx'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h' ↦ Subtype.ext (h x' h' hx'), fun h' ↦ ?_⟩
    rw [show x' = x from congrArg Subtype.val h']
    exact hxU

/-- **A point with finite fibre is a quasi-finite point.** The scheme-theoretic fibre is then a
finite Jacobson space, hence discrete. -/
theorem Scheme.Hom.quasiFiniteAt_of_finite_preimage_singleton [LocallyOfFiniteType f] {x : X}
    (h : (f ⁻¹' {f x}).Finite) : f.QuasiFiniteAt x := by
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr h
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- **A constant morphism quasi-finite at a point isolates that point.** If `f` maps every point
to `f x` and is quasi-finite at `x`, then `{x}` is clopen in `X`: the fibre over `f x` is all of
`X`, and `x` is clopen in its fibre. -/
theorem Scheme.Hom.isClopen_singleton_of_quasiFiniteAt_of_forall_eq [LocallyOfFiniteType f]
    {x : X} (hx : f.QuasiFiniteAt x) (hf : ∀ x', f x' = f x) : IsClopen ({x} : Set X) := by
  have hc := hx.isClopen_singleton_asFiber
  have huniv : f ⁻¹' {f x} = Set.univ := Set.eq_univ_of_forall hf
  let e : f.fiber (f x) ≃ₜ X :=
    (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr huniv).trans (Homeomorph.Set.univ X))
  have he : e '' {f.asFiber x} = {x} := by
    rw [Set.image_singleton]
    simp [e, Scheme.Hom.asFiber]
    rfl
  rw [← he]
  exact ⟨e.isClosed_image.mpr hc.1, e.isOpen_image.mpr hc.2⟩

end AlgebraicGeometry

end
