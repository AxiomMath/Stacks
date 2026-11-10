module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingAssembly
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.IntegralSource

/-!
# Steps D, E and F of Stacks Tag 0559, assembled over a domain base

Let `A` be a domain, let `X` be an integral scheme of finite type over `Spec A` whose generic
point lies over the generic point of `Spec A`, and let `S` be a domain with an injective ring
homomorphism `A ⟶ S` such that `Spec S` is geometrically irreducible of finite type over
`Spec A` and such that the residue field of `X` at its generic point is a field of fractions of
`S`, compatibly with the structure morphism of `X`. If the fibre of `X` over the generic point
of `Spec A` is geometrically irreducible, then `X` has geometrically irreducible fibres over a
nonempty open subscheme of `Spec A`.

This is the join of Step D with Steps E and F. Step D
(`AlgebraicGeometry.exists_nonempty_open_iso_spec_of_isFractionRing`, which is Tag 0552)
produces opens `U ⊆ X` and `V ⊆ Spec S` isomorphic over `Spec A`; Steps E and F
(`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_denseOpenIso`) carry geometric
irreducibility from `Spec S` to `X` over a nonempty open of the base, given that `U` and `V` are
dense in the fibres over the generic point.

That density is what this module supplies, and it is where the two irreducibility hypotheses are
used. The generic fibre of `X` is irreducible because it is geometrically irreducible over a
one-point base, and it meets `U`: the generic point of `X` lies in every nonempty open of the
integral scheme `X`, and it lies in the generic fibre by hypothesis. A nonempty open subset of an
irreducible space is dense, which gives the density of `U`. The same argument applies to
`Spec S`, whose generic fibre is irreducible because `Spec S` is geometrically irreducible over
`Spec A`, and whose generic point lies over the generic point of `Spec A` because `A ⟶ S` is
injective (`AlgebraicGeometry.map_genericPoint_Spec_map`).

## Main results

* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_specModel`: **Steps D, E and F of
  Stacks Tag 0559 over a domain base.**

## Implementation notes

The model is an argument rather than the hypersurface
`MvPolynomial (Fin n) A ⧸ (P)` of the source: nothing in this join uses its shape, only that it
is an affine, geometrically irreducible, finite type model of the same function field. What the
source's hypersurface contributes — geometric irreducibility of all of its fibres — is Step F,
and it enters here as the instance argument `GeometricallyIrreducible (Spec.map φ)`.

No Stacks tag is attached: Steps D, E and F are not themselves tags of the source, and Tag 0552
is carried by the source of
`AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso`.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Steps D, E and F of the
  first proof
* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A nonempty open subscheme of an integral scheme contains the generic point, so its trace on
an irreducible fibre through the generic point is dense in that fibre. -/
private theorem dense_fiber_preimage_of_nonempty {Y : Scheme.{u}} {Z : Scheme.{u}}
    (h : Z ⟶ Y) [IrreducibleSpace Z] (y : Y)
    [GeometricallyIrreducible (h.fiberToSpecResidueField y)] (W : Z.Opens)
    (hW : (W : Set Z).Nonempty) (hy : h (genericPoint Z) = y) :
    Dense ((h.fiberι y ⁻¹ᵁ W : (h.fiber y).Opens) : Set ↥(h.fiber y)) := by
  have := GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := h.fiberToSpecResidueField y)
  have hgen : IsGenericPoint (genericPoint Z) (Set.univ : Set Z) := by
    simpa using genericPoint_spec Z
  obtain ⟨z, hz⟩ : ∃ z : h.fiber y, h.fiberι y z = genericPoint Z := by
    rw [← Set.mem_range, h.range_fiberι y]
    exact hy
  refine (preirreducibleSpace_iff_open_dense ↥(h.fiber y)).mp inferInstance
    ((h.fiberι y ⁻¹ᵁ W).isOpen) ⟨z, ?_⟩
  change h.fiberι y z ∈ W
  rw [hz]
  exact mem_of_isGenericPoint_univ hgen W.isOpen hW

/-- **Steps D, E and F of Stacks Tag 0559 over a domain base.** Let `A` and `S` be domains with
an injective ring homomorphism `φ : A ⟶ S`, and let `X` be an integral scheme of finite type
over `Spec A` whose generic point lies over the generic point of `Spec A` and whose fibre there
is geometrically irreducible. If `Spec S` is geometrically irreducible of finite type over
`Spec A` and the residue field of `X` at its generic point is a field of fractions of `S`,
compatibly with the structure morphism of `X`, then `X` has geometrically irreducible fibres
over a nonempty open subscheme of `Spec A`. -/
theorem exists_open_geometricallyIrreducible_of_specModel {A S : CommRingCat.{u}} [IsDomain A]
    [IsDomain S] (φ : A ⟶ S) (hφ : Function.Injective φ.hom) {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec A) [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Spec.map φ)] [GeometricallyIrreducible (Spec.map φ)]
    (hgen : g (genericPoint X) = genericPoint (Spec A))
    [Algebra S (X.residueField (genericPoint X))]
    (hfrac : IsFractionRing S (X.residueField (genericPoint X)))
    (hcompat : φ ≫ CommRingCat.ofHom (algebraMap S (X.residueField (genericPoint X))) =
      (Scheme.ΓSpecIso A).inv ≫ g.appTop ≫ X.Γevaluation (genericPoint X))
    (hfib : GeometricallyIrreducible (g.fiberToSpecResidueField (genericPoint (Spec A)))) :
    ∃ V : (Spec A).Opens, Nonempty V ∧ GeometricallyIrreducible (g ∣_ V) := by
  obtain ⟨U, V, hUne, hVne, e, he⟩ :=
    exists_nonempty_open_iso_spec_of_isFractionRing φ hφ g hgen hfrac hcompat
  have hη : IsGenericPoint (genericPoint (Spec A)) (Set.univ : Set (Spec A)) := by
    simpa using genericPoint_spec (Spec A)
  have hU := dense_fiber_preimage_of_nonempty g (genericPoint (Spec A)) U hUne hgen
  have : GeometricallyIrreducible
      ((Spec.map φ).fiberToSpecResidueField (genericPoint (Spec A))) :=
    (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber (Spec.map φ)).mp ‹_› _
  have hV := dense_fiber_preimage_of_nonempty (Spec.map φ) (genericPoint (Spec A)) V hVne
    (map_genericPoint_Spec_map φ hφ)
  exact exists_open_geometricallyIrreducible_of_denseOpenIso g (Spec.map φ) U V e he
    (genericPoint (Spec A)) hη hU hV

end AlgebraicGeometry

end
