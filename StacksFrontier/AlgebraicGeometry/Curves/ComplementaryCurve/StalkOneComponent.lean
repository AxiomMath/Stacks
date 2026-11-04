module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The closure of a complement, at a point lying on only one of its components

Let `X` be a reduced Noetherian curve and `I ⊆ X` a closed subscheme. The scheme-theoretic
closure `X'` of the complement of `I` is the reduced union of the irreducible components of `X`
not contained in `I`. At a point `x` through which exactly one of those components passes, say
`D`, the ideal sheaf of `X'` and the vanishing ideal of `D` agree on a neighbourhood of `x` — an
affine open avoiding the other components — hence have the same stalk at `x`.

## Main results

* `Stacks.Curves.stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal` — the stalk of the ideal
  sheaf of the closure of the complement is the stalk of the vanishing ideal of the unique
  component of that closure through the point.

## Implementation notes

The stalk of an ideal sheaf is computed on a single affine open neighbourhood by
`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`, and the sections of a vanishing ideal on
an affine open are the vanishing ideal of the preimage of the closed set under
`IsAffineOpen.fromSpec` (`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_ideal`). So it
is enough to find one affine open `V` containing `x` on which the support of the closure and the
component `D` have the same intersection; the range of `fromSpec` being `V`, the two preimages
then coincide and the two ideals of sections are literally equal.

Such a `V` exists because the union of the *other* components of the closure is a finite union
of closed sets — the ambient space is Noetherian — and misses `x` by hypothesis, so its
complement is an open neighbourhood of `x` and contains an affine open around `x`.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- **At a point lying on exactly one irreducible component not contained in a closed subscheme,
the ideal sheaf of the scheme-theoretic closure of the complement has the same stalk as the
vanishing ideal of that component.** The two ideal sheaves agree already on an affine open
neighbourhood of the point avoiding the other components. -/
theorem stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hnodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) {x : X} (D : Closeds X)
    (hD : (D : Set X) ∈ irreducibleComponents X)
    (hDI : ¬ (D : Set X) ⊆ (I.support : Set X)) (_hxD : x ∈ (D : Set X))
    (huniq : ∀ E ∈ irreducibleComponents X, x ∈ E → ¬ E ⊆ (I.support : Set X) →
      E = (D : Set X)) :
    IdealSheafData.stalk (complementaryCurveIdeal I) x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D) x := by
  classical
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hCS : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hN : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hNS : NoetherianSpace X := inferInstance
  set Zcomps := {E : Set X // E ∈ irreducibleComponents X ∧ ¬ E ⊆ (I.support : Set X)}
    with hZcompsDef
  set Zc : Closeds X := ⨆ E : Zcomps, Closeds.closure E.1 with hZcDef
  have hcomponents : LocallyFinite (fun E : irreducibleComponents X => (E : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hUnionClosed : IsClosed (⋃ E : Zcomps, (E.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents _).isClosed_iUnion fun E =>
      isClosed_of_mem_irreducibleComponents E.1 E.2.1
  have hZcCoe : (Zc : Set X) = ⋃ E : Zcomps, (E.1 : Set X) :=
    coe_iSup_closure_eq_iUnion_of_isClosed (fun E : Zcomps => E.1)
      (fun E => isClosed_of_mem_irreducibleComponents E.1 E.2.1) hUnionClosed
  have hcompl : complementaryCurveIdeal I = Scheme.IdealSheafData.vanishingIdeal Zc :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hnodal I
  -- the union of the other components of the closure is closed and misses `x`
  set Bad : Set X := ⋃₀ {E : Set X | E ∈ irreducibleComponents X ∧
    ¬ E ⊆ (I.support : Set X) ∧ E ≠ (D : Set X)} with hBadDef
  have hBadFin : {E : Set X | E ∈ irreducibleComponents X ∧
      ¬ E ⊆ (I.support : Set X) ∧ E ≠ (D : Set X)}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun E hE => hE.1
  have hBadClosed : IsClosed Bad :=
    hBadFin.isClosed_sUnion fun E hE => isClosed_of_mem_irreducibleComponents E hE.1
  have hxBad : x ∉ Bad := by
    rintro ⟨E, ⟨hE, hEI, hED⟩, hxE⟩
    exact hED (huniq E hE hxE hEI)
  -- an affine open neighbourhood of `x` inside the complement of that union
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVBad⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxBad hBadClosed.isOpen_compl
  -- on that neighbourhood the closure and the component have the same points
  have hpre : hV.fromSpec ⁻¹' (Zc : Set X) = hV.fromSpec ⁻¹' (D : Set X) := by
    apply Set.eq_of_subset_of_subset
    · intro z hz
      rw [Set.mem_preimage, hZcCoe] at hz
      obtain ⟨E, hzE⟩ := Set.mem_iUnion.mp hz
      have hzV : hV.fromSpec z ∈ (V : Set X) := by
        rw [← IsAffineOpen.range_fromSpec hV]; exact ⟨z, rfl⟩
      have hED : E.1 = D := by
        by_contra hne
        exact hVBad hzV ⟨E.1, ⟨E.2.1, E.2.2, hne⟩, hzE⟩
      exact hED ▸ hzE
    · intro z hz
      rw [Set.mem_preimage, hZcCoe]
      exact Set.mem_iUnion.mpr ⟨⟨(D : Set X), hD, hDI⟩, hz⟩
  have hideal : (Scheme.IdealSheafData.vanishingIdeal Zc).ideal ⟨V, hV⟩ =
      (Scheme.IdealSheafData.vanishingIdeal D).ideal ⟨V, hV⟩ := by
    simp only [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact congrArg PrimeSpectrum.vanishingIdeal hpre
  rw [hcompl, IdealSheafData.stalk_eq_map_germ _ x ⟨V, hV⟩ hxV,
    IdealSheafData.stalk_eq_map_germ _ x ⟨V, hV⟩ hxV, hideal]

end Stacks.Curves

end
