module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ResidueFieldSquare
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FractionFieldModel

/-!
# Comparing an integral scheme with the spectrum of a model of its function field

Step D of the proof of Stacks Tag 0559, assembled. Let `X` be an integral scheme of finite type
over `Spec R` whose generic point lies over the generic point of `Spec R`, and let `S` be a
domain with an injective map `R ⟶ S` such that the residue field of `X` at its generic point is
a field of fractions of `S`, compatibly with the structure morphism of `X`. Then `X` and
`Spec S` have isomorphic nonempty open subschemes over `Spec R`.

In the application `R` is the residue field `K` of the base at its generic point, `X` is the
generic fibre and `S` is the standard model `K[x₁, …, x_{r+1}] ⧸ (q)` of Steps B, C and D(i).

## Main results

* `AlgebraicGeometry.exists_nonempty_open_iso_spec_of_isFractionRing`: **Step D of Stacks
  Tag 0559.**

## Implementation notes

The hypothesis that the generic point of `Spec S` lies over the generic point of `Spec R` is
not an argument: it is `AlgebraicGeometry.map_genericPoint_Spec_map` applied to the injectivity
of `R ⟶ S`. The residue field isomorphism and its global-sections equation come from
`AlgebraicGeometry.exists_residueFieldIso_appTop_of_isFractionRing`, so no transport along an
equality of points is performed anywhere in the composition.

No Stacks tag is attached: Step D is not itself a tag of the source, and Tag 0552 is already
carried by
`AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso_of_appTop`'s own source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step D of the first
  proof
* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Step D of Stacks Tag 0559.** Let `R` and `S` be domains with an injective ring
homomorphism `R ⟶ S`, and let `X` be an integral scheme locally of finite type over `Spec R`
whose generic point lies over the generic point of `Spec R`. If the residue field of `X` at its
generic point is a field of fractions of `S`, compatibly with the structure morphism of `X`,
then `X` and `Spec S` have isomorphic nonempty open subschemes over `Spec R`. -/
theorem exists_nonempty_open_iso_spec_of_isFractionRing {R S : CommRingCat.{u}} [IsDomain R]
    [IsDomain S] (f : R ⟶ S) (hf : Function.Injective f.hom) {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec R) [LocallyOfFiniteType sX] [LocallyOfFiniteType (Spec.map f)]
    (hX : sX (genericPoint X) = genericPoint (Spec R))
    [Algebra S (X.residueField (genericPoint X))]
    (hfrac : IsFractionRing S (X.residueField (genericPoint X)))
    (hcompat : f ≫ CommRingCat.ofHom (algebraMap S (X.residueField (genericPoint X))) =
      (Scheme.ΓSpecIso R).inv ≫ sX.appTop ≫ X.Γevaluation (genericPoint X)) :
    ∃ (U : X.Opens) (V : (Spec S).Opens), (U : Set X).Nonempty ∧
      (V : Set (Spec S)).Nonempty ∧
      ∃ e' : U.toScheme ≅ V.toScheme, e'.hom ≫ V.ι ≫ Spec.map f = U.ι ≫ sX := by
  obtain ⟨e, he⟩ := exists_residueFieldIso_appTop_of_isFractionRing f sX hfrac hcompat
  exact exists_nonempty_open_iso_of_residueFieldIso_of_appTop sX (Spec.map f) hX
    (map_genericPoint_Spec_map f hf) e he

end AlgebraicGeometry

end
