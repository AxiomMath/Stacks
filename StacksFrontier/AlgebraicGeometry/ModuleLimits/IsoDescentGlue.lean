module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentGlue
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso

/-!
# Zariski glueing of an isomorphism of sheaves of modules out of isomorphisms of restrictions

`Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_inf` glues a
*morphism* of sheaves of modules out of morphisms of the restrictions to the members of an open
covering which agree on the pairwise intersections.  A local-to-global argument whose local data
are *isomorphisms* wants the glued morphism to be an isomorphism as well, and that is not part of
the glueing: the statement that the glued morphism inherits invertibility from its restrictions is
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map`, proved on the stalks.

This file puts the two together.  Nothing else is used: the glued morphism restricts to the given
isomorphism on each member of the covering by the defining property of the glueing, so it is
invertible there, hence invertible.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf`: **two sheaves of modules
  identified over the members of an open covering, compatibly on the pairwise intersections, are
  isomorphic.**

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **Two sheaves of modules identified over the members of an open covering, compatibly on the
pairwise intersections, are isomorphic.**

The underlying morphism is glued by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_inf`; it
restricts to `χ a` on the `a`-th member of the covering, so it is invertible there, and
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map` makes it invertible. -/
theorem nonempty_iso_of_cover_of_inf {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (χ : ∀ a, Scheme.Modules.restrict M (W a).ι ≅ Scheme.Modules.restrict N (W a).ι)
    (hagree : ∀ a b, restrictHomOfLE (inf_le_left : W a ⊓ W b ≤ W a) (χ a).hom =
      restrictHomOfLE (inf_le_right : W a ⊓ W b ≤ W b) (χ b).hom) :
    Nonempty (M ≅ N) := by
  obtain ⟨φ, hφ⟩ :=
    exists_restrictFunctor_map_eq_of_cover_of_inf W hW (fun a => (χ a).hom) hagree
  have hiso : IsIso φ :=
    Scheme.Modules.isIso_of_isIso_restrictFunctor_map φ (fun a => (W a).ι)
      (fun x => by
        obtain ⟨a, ha⟩ := hW x
        exact ⟨a, ⟨x, ha⟩, rfl⟩)
      (fun a => by rw [hφ a]; infer_instance)
  exact ⟨asIso φ⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
