module

public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.RingTheory.Depth.AssociatedPrime

/-!
# Coherent extensions without associated points outside the open

Let `X` be a Noetherian scheme and `W ⊆ X` an open subscheme. Every coherent module `F` on `W`
extends to a coherent module `F'` on `X` all of whose associated points lie in `W`.

## Main results

* `AlgebraicGeometry.exists_isCoherent_extension_associatedPoints_subset`: the statement above.

## Implementation notes

First `F` is extended to some coherent `F₀` on `X`
(`AlgebraicGeometry.exists_isCoherent_restrict_iso`, the extension assertion of Stacks 0BK0;
`W` is quasi-compact because `X` is Noetherian). Then `F₀` is replaced by its depth-one quotient
along the closed, hence specialization-stable, complement `T = X ∖ W`
(`AlgebraicGeometry.depthOneQuotient`, Stacks 0DX3). The quotient map is an isomorphism on stalks
off `T`, so its restriction to `W` is an isomorphism (restriction to an open commutes with
stalks, and isomorphisms of sheaves of modules are detected on stalks). The quotient has depth at
least one at every point of `T`, which excludes the maximal ideal of the local ring from the
associated primes of the stalk there; so no point of `T` is associated.

No `@[stacks]` attribute: this is a step of a proof, not a numbered statement of the source.

## References

* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Coherent extension with associated points in the open.** On a Noetherian scheme `X`, a
coherent module `F` on an open `W` is the restriction of a coherent module `F'` on `X` whose
associated points all lie in `W`. -/
theorem exists_isCoherent_extension_associatedPoints_subset {X : Scheme.{u}} [IsNoetherian X]
    (W : X.Opens) (F : W.toScheme.Modules) [F.IsCoherent] :
    ∃ (F' : X.Modules) (_ : F'.IsCoherent), Nonempty (F'.restrict W.ι ≅ F) ∧
      Stacks.Divisors.associatedPoints F' ⊆ (W : Set X) := by
  obtain ⟨F₀, _, ⟨e⟩⟩ := exists_isCoherent_restrict_iso W
    (NoetherianSpace.isCompact (W : Set X)) F
  let T : Set X := (W : Set X)ᶜ
  have hT : StableUnderSpecialization T := W.isOpen.isClosed_compl.stableUnderSpecialization
  have hspec := depthOneQuotient_spec X T hT F₀
  let G := depthOneQuotient X T hT F₀
  let g : F₀ ⟶ G := toDepthOneQuotient X T hT F₀
  have hGc : G.IsCoherent := hspec.1
  refine ⟨G, hGc, ⟨?_⟩, ?_⟩
  · have : IsIso ((Scheme.Modules.restrictFunctor W.ι).map g) := by
      refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun w => ?_
      exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso W.ι w) g).mpr
        (hspec.2.2.1 (W.ι w) fun hw => hw w.2)
    exact (asIso ((Scheme.Modules.restrictFunctor W.ι).map g)).symm ≪≫ e
  · intro x hx
    by_contra hxW
    rw [Stacks.Divisors.mem_associatedPoints_iff] at hx
    let _ : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    have : Module.Finite (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      Scheme.Modules.finite_stalk_of_isCoherent G x
    exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth (hspec.2.2.2 x hxW) hx

end AlgebraicGeometry

end
