module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FiniteLocallyFreeNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatFromFreeNeighbourhood

/-!
# Freeness near the generic points of the fibres

Let `g : B ⟶ T` be a morphism of schemes and `G` an `𝒪_B`-module. This file isolates the
condition that `G` be free of finite rank on a neighbourhood of every point of `B` whose closure
contains its whole fibre — the generic point of that fibre — and records the two conclusions of
[Stacks, Tag 0811] that follow from it when the fibres of `g` are geometrically integral.

That condition is what the affine engine [Stacks, Tag 0810] delivers: for each prime `p'` of the
blowup chart it produces an element `g` outside the extended prime `p'S'` after inverting which
the strict transform is free of rank `r`, and `p'S'` is exactly the generic point of the fibre
over `p'`. It is also what the conclusion of [Stacks, Tag 0811] needs, and it is strictly
stronger than flatness over the base at those points.

## Main definitions

* `AlgebraicGeometry.FreeNearFibreGeneric`: the condition above.

## Main results

* `AlgebraicGeometry.FreeNearFibreGeneric.isFlatOverAt`: it implies flatness over the base at
  every generic point of a fibre, for a flat `g`.
* `AlgebraicGeometry.exists_opens_isFiniteLocallyFree_surjective_of_freeNearFibreGeneric`: the
  conclusion of [Stacks, Tag 0811] — an open `V` on which `G` is finitely locally free and which
  surjects onto `T`.
* `AlgebraicGeometry.exists_opens_forall_free_surjective_of_freeNearFibreGeneric`: the same with
  the freeness spelled out pointwise.

## Implementation notes

"Generic point of the fibre" is written in the purely topological form
`g⁻¹(g b) ⊆ closure {b}`, as everywhere else in this development; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibresFlattening.lean`. Only the
proof that such a point exists over every point of `T`
(`AlgebraicGeometry.exists_fibre_dense_preimage`) uses geometric integrality of the fibres, which
is why the definition itself asks for nothing.

Flatness over the base at the points in question is
`AlgebraicGeometry.isFlatOverAt_of_over_iso_free`, which needs `g` flat and `G` quasi-coherent;
neither is needed for the open subscheme of the conclusion, so the two results below carry
different hypotheses.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Freeness near the generic points of the fibres.** An `𝒪_B`-module `G` satisfies this for
`g : B ⟶ T` when every point `b` of `B` whose closure contains the whole fibre through it has an
open neighbourhood on which `G` is isomorphic to a finite free module. -/
def FreeNearFibreGeneric {B T : Scheme.{u}} (g : B ⟶ T) (G : B.Modules) : Prop :=
  ∀ b : B, g.base ⁻¹' {g.base b} ⊆ closure {b} →
    ∃ (W : B.Opens) (n : ℕ), b ∈ W ∧
      Nonempty (G.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))

/-- A module free of finite rank near the generic points of the fibres of a flat morphism is
flat over the base at those points, by
`AlgebraicGeometry.isFlatOverAt_of_over_iso_free`. -/
theorem FreeNearFibreGeneric.isFlatOverAt {B T : Scheme.{u}} (g : B ⟶ T) [Flat g]
    (G : B.Modules) [G.IsQuasicoherent] (h : FreeNearFibreGeneric g G) (b : B)
    (hb : g.base ⁻¹' {g.base b} ⊆ closure {b}) :
    IsFlatOverAt g.toLRSHom.toShHom G b := by
  obtain ⟨W, n, hbW, ⟨eW⟩⟩ := h b hb
  exact isFlatOverAt_of_over_iso_free g G hbW n eW

/-- Free neighbourhoods of generic points of fibres, one over each point of `T`, whose union
surjects onto `T`. -/
private theorem exists_family_free_surjective_of_freeNearFibreGeneric {B T : Scheme.{u}}
    (g : B ⟶ T) [GeometricallyIntegral g] (G : B.Modules) (h : FreeNearFibreGeneric g G) :
    ∃ (W : T → B.Opens) (n : T → ℕ),
      (∀ t, Nonempty (G.over (W t) ≅ SheafOfModules.free (ULift.{u} (Fin (n t))))) ∧
      Function.Surjective ((⨆ t : T, W t).ι ≫ g).base := by
  classical
  have hstep : ∀ t : T, ∃ (b : B) (W : B.Opens) (n : ℕ), g.base b = t ∧ b ∈ W ∧
      Nonempty (G.over W ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
    intro t
    obtain ⟨b, hbt, hbcl⟩ := exists_fibre_dense_preimage g t
    obtain ⟨W, n, hbW, hfree⟩ := h b (by rw [hbt]; exact hbcl)
    exact ⟨b, W, n, hbt, hbW, hfree⟩
  choose b W n hbt hbW hfree using hstep
  refine ⟨W, n, hfree, fun t ↦ ⟨⟨b t, Opens.mem_iSup.mpr ⟨t, hbW t⟩⟩, ?_⟩⟩
  change g.base ((⨆ t : T, W t).ι.base ⟨b t, _⟩) = t
  exact hbt t

/-- **The open subscheme of the conclusion of [Stacks, Tag 0811].** If the fibres of `g` are
geometrically integral and `G` is free of finite rank near the generic point of every fibre, the
union of those neighbourhoods is an open `V` which surjects onto `T` and on which `G` is free of
finite rank near every point. -/
theorem exists_opens_forall_free_surjective_of_freeNearFibreGeneric {B T : Scheme.{u}}
    (g : B ⟶ T) [GeometricallyIntegral g] (G : B.Modules) (h : FreeNearFibreGeneric g G) :
    ∃ V : B.Opens,
      (∀ b : B, b ∈ V → ∃ (W : B.Opens) (n : ℕ), b ∈ W ∧ W ≤ V ∧
        Nonempty (G.over W ≅ SheafOfModules.free (ULift.{u} (Fin n)))) ∧
      Function.Surjective (V.ι ≫ g).base := by
  obtain ⟨W, n, hfree, hsurj⟩ := exists_family_free_surjective_of_freeNearFibreGeneric g G h
  refine ⟨⨆ t : T, W t, fun x hx ↦ ?_, hsurj⟩
  obtain ⟨t, hxt⟩ := Opens.mem_iSup.mp hx
  exact ⟨W t, n t, hxt, le_iSup W t, hfree t⟩

/-- **The open subscheme of the conclusion of [Stacks, Tag 0811]**, with the freeness in the form
the source states it: `G` restricts to a finitely locally free module on `V`. -/
theorem exists_opens_isFiniteLocallyFree_surjective_of_freeNearFibreGeneric {B T : Scheme.{u}}
    (g : B ⟶ T) [GeometricallyIntegral g] (G : B.Modules) (h : FreeNearFibreGeneric g G) :
    ∃ V : B.Opens, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (G.over V) ∧
      Function.Surjective (V.ι ≫ g).base := by
  obtain ⟨W, n, hfree, hsurj⟩ := exists_family_free_surjective_of_freeNearFibreGeneric g G h
  exact ⟨⨆ t : T, W t,
    SheafOfModules.isFiniteLocallyFree_over_iSup G W (fun t ↦ ⟨n t, hfree t⟩), hsurj⟩

end AlgebraicGeometry

end
