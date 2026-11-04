module

public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian

/-!
# Sections of a cokernel of sheaves of modules on a space, locally

Let `φ : N ⟶ M` be a morphism of sheaves of modules on a topological space and
`π : M ⟶ coker φ` its cokernel. Sections of `coker φ` are local images of sections of `M`, and a
section of `M` killed by `π` is locally in the image of `φ`.

## Main results

* `Stacks.SheafOfModules.exists_cokernel_π_eq`: local lifts along `π`.
* `Stacks.SheafOfModules.exists_eq_of_cokernel_π_eq_zero`: the kernel of `π` is, locally, the
  image of `φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- **Local lifts along a cokernel.** Every section of the cokernel of a morphism of sheaves of
modules is, near each point of its domain, the image of a section of the target. -/
theorem exists_cokernel_π_eq {N M : _root_.SheafOfModules.{u} R} (φ : N ⟶ M) {V : Opens X}
    (s : (cokernel φ).val.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (h : W ≤ V) (t : M.val.obj (op W)), x ∈ W ∧
      (cokernel.π φ).val.app (op W) t = (cokernel φ).val.map (homOfLE h).op s := by
  obtain ⟨S, hS, hlift⟩ := EpiMono.exists_covering_of_epi (cokernel.π φ) s
  obtain ⟨W, g, hg, hxW⟩ := hS x hx
  obtain ⟨t, ht⟩ := hlift g hg
  exact ⟨W, leOfHom g, t, hxW, ht⟩

/-- **The kernel of a cokernel map is locally the image.** A section of the target of `φ` killed
by the cokernel map is, near each point of its domain, the image of a section of the source. -/
theorem exists_eq_of_cokernel_π_eq_zero {N M : _root_.SheafOfModules.{u} R} (φ : N ⟶ M)
    {V : Opens X} (t : M.val.obj (op V)) (ht : (cokernel.π φ).val.app (op V) t = 0) {x : X}
    (hx : x ∈ V) :
    ∃ (W : Opens X) (h : W ≤ V) (r : N.val.obj (op W)), x ∈ W ∧
      φ.val.app (op W) r = M.val.map (homOfLE h).op t := by
  let S := (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).map
    (_root_.SheafOfModules.toSheaf.{u} R)
  have hS : S.Exact := (exact_iff_toSheaf_exact R _).mpr (ShortComplex.exact_cokernel φ)
  obtain ⟨W, g, ⟨r, hr⟩, hxW⟩ := AbelianSheaves.imageSieve_mem_of_exact S hS V t ht x hx
  exact ⟨W, leOfHom g, r, hxW, hr⟩

end Stacks.SheafOfModules
