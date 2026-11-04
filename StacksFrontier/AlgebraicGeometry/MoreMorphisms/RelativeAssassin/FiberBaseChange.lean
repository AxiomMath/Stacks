module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated

/-!
# Associated points in a fibre after base change

For a locally finite type morphism `f : X ⟶ S` and a finite type quasi-coherent module `F` on `X`,
containment of the associated points of a fibre in an open subscheme `U` of `X` is invariant under
arbitrary extension of the base point: for `g : S' ⟶ S` and `s' : S'`, the associated points of
the restriction of `F` to the fibre of `f` over `g s'` lie in `U` exactly when the associated
points of the restriction of the pulled-back module to the fibre of `pullback.snd f g` over `s'`
lie in the preimage of `U`.

## Main results

* `Stacks.RelativeAssassin.associatedPoints_fiber_subset_preimage_iff_baseChange`

## Implementation notes

Both directions pass through the relative assassin: membership of a point of a fibre in the
associated points of the restricted module is membership of its image in the relative assassin,
and the base-change criterion for the relative assassin is
`AlgebraicGeometry.mem_relativeAssassin_pullback_iff` (Stacks Project, Tag 05DC). The backward
direction has to produce a point of the base-changed fibre above a given point of the original
fibre; it takes the generic point of an irreducible component of the spectrum of the
residue-field tensor product attached to that point by
`AlgebraicGeometry.Scheme.Pullback.carrierEquiv`, which is exactly the extra condition in the
criterion.

## References

* [Stacks Project, Tag 05KQ](https://stacks.math.columbia.edu/tag/05KQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeAssassin

/-- A point of the fibre of `f` over `y` lies over `y`. -/
private alias fiber_apply_fiberι := AlgebraicGeometry.Scheme.Hom.apply_fiberι

/-- A point of the relative assassin of `φ` lying over `s` comes from an associated point of the
restriction of the module to the fibre over `s`. -/
lemma exists_mem_associatedPoints_fiber_of_mem_relativeAssassin {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (G : X.Modules) {s : Y} {z : X} (hz : φ z = s)
    (hA : z ∈ Stacks.Divisors.relativeAssassin φ G) :
    ∃ y ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (φ.fiberι s)).obj G),
      φ.fiberι s y = z := by
  have hy : φ.fiberι s ((φ.fiberHomeo s).symm ⟨z, hz⟩) = z := by simp
  exact ⟨(φ.fiberHomeo s).symm ⟨z, hz⟩,
    (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin φ G s _).mpr
      (hy.symm ▸ hA), hy⟩

/-- **Stacks Project, Tag 05KQ.** After arbitrary base change, the associated points of the
pullback module on a fibre lie in the pulled-back open exactly when they did so on the original
fibre. -/
@[stacks 05KQ]
theorem associatedPoints_fiber_subset_preimage_iff_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.Opens) (g : S' ⟶ S) (s' : S') :
    Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F) ⊆
        (f.fiberι (g s')) ⁻¹' (U : Set X) ↔
      Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback ((pullback.snd f g).fiberι s')).obj
              ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ⊆
          ((pullback.snd f g).fiberι s') ⁻¹'
            ((pullback.fst f g) ⁻¹' (U : Set X)) := by
  refine ⟨fun h x' hx' => ?_, fun h x hx => ?_⟩
  · let z := (pullback.snd f g).fiberι s' x'
    have hfg : f (pullback.fst f g z) = g s' := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
        fiber_apply_fiberι (pullback.snd f g) s' x']
    obtain ⟨y, hy, hyι⟩ := exists_mem_associatedPoints_fiber_of_mem_relativeAssassin f F hfg
      ((mem_relativeAssassin_pullback_iff f g F z).mp
        ((Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
          (pullback.snd f g) _ s' x').mp hx')).1
    simpa [z, hyι] using h hy
  · let T : Scheme.Pullback.Triplet f g :=
      Scheme.Pullback.Triplet.mk' (f.fiberι (g s') x) s' (fiber_apply_fiberι f (g s') x)
    obtain ⟨p, Z, hZ, hp⟩ :=
      AlgebraicGeometry.exists_isGenericPoint_mem_irreducibleComponents T.tensor
    let z : (pullback f g : Scheme) := T.SpecTensorTo p
    have hzx : pullback.fst f g z = f.fiberι (g s') x := by
      simpa [z, T] using T.fst_SpecTensorTo_apply p
    have hz : z ∈ Stacks.Divisors.relativeAssassin (pullback.snd f g)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F) := by
      rw [mem_relativeAssassin_pullback_iff]
      refine ⟨hzx ▸ (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
        f F (g s') x).mp hx, ?_⟩
      have he : (⟨Scheme.Pullback.Triplet.ofPoint z,
          Scheme.Pullback.SpecOfPoint z⟩ :
            Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) = ⟨T, p⟩ :=
        (Scheme.Pullback.carrierEquiv (f := f) (g := g)).apply_symm_apply ⟨T, p⟩
      let P : (Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) → Prop := fun q ↦
        ∃ Z ∈ irreducibleComponents (Spec q.1.tensor), IsGenericPoint q.2 Z
      change P ⟨Scheme.Pullback.Triplet.ofPoint z, Scheme.Pullback.SpecOfPoint z⟩
      exact he.symm ▸ (show P ⟨T, p⟩ from ⟨Z, hZ, hp⟩)
    have hzs : pullback.snd f g z = s' := by
      simpa [z, T] using T.snd_SpecTensorTo_apply p
    obtain ⟨y, hy, hyι⟩ :=
      exists_mem_associatedPoints_fiber_of_mem_relativeAssassin (pullback.snd f g) _ hzs hz
    simpa [hyι, hzx] using h hy

end Stacks.RelativeAssassin

end
