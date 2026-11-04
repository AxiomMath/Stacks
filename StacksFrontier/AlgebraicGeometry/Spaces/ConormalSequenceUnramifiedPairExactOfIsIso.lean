module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramifiedExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPair

/-!
# The conormal sequence of a pair of formally unramified morphisms, without the clauses of 05ZA

This file proves the epimorphism clause and the exactness of the sequence
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0` of Stacks 06BE with no hypothesis about the clauses of
Stacks 05ZA for `Z ⊂ Z'` over `Y`.  Both statements take the isomorphism `he` of Stacks 060E
and formal unramifiedness of `j`; the exactness statement also takes `hzero067` and `h067V`,
the clauses of Stacks 067V.  They rest on the form
`AlgebraicGeometry.Space.thickeningConormalSequence_exact_of_isIso` of Stacks 060F.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `epi_thickeningConormalFirstMap_of_isIso_of_formallyUnramified`: the second arrow
  `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}` of the sequence of Stacks 06BE is an epimorphism.
* `thickeningConormalPairSequence_exact_of_isIso_of_formallyUnramified`: the sequence of
  Stacks 06BE is exact and its second arrow is an epimorphism.

## References

* [Stacks Project, Tag 06BE](https://stacks.math.columbia.edu/tag/06BE)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 067V](https://stacks.math.columbia.edu/tag/067V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' W' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {W : Subfunctor W'.obj}
    {p : Z' ⟶ X} {q : W' ⟶ Y}

/-- **The `⟶ 0` at the right-hand end of the sequence of Stacks 06BE, with nothing of
Stacks 05ZA assumed.**  The hypotheses are the isomorphism `he` of Stacks 060E and formal
unramifiedness of `j`. -/
theorem epi_thickeningConormalFirstMap_of_isIso_of_formallyUnramified (g : X ⟶ Y)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g))
    (hj : FormallyUnramified (universalThickeningInclusion B S hS hZ ≫ p ≫ g).hom) :
    Epi (thickeningConormalFirstMap B S hS hZ g he) := by
  obtain ⟨hc, hex⟩ := thickeningConormalSequence_exact_of_isIso B S hS hZ g he
  have hΩ : IsZero (sheafOfDifferentials B S hS
      (universalThickeningInclusion B S hS hZ ≫ p ≫ g)) :=
    isZero_sheafOfDifferentials_of_formallyUnramified B S hS _ hj
  exact (ShortComplex.exact_iff_epi _ (hΩ.eq_of_tgt _ _)).mp hex

/-- **The sequence of Stacks 06BE, with nothing of Stacks 05ZA assumed.**  The hypotheses are the
isomorphism `he` of Stacks 060E, formal unramifiedness of `j`, and the clauses `hzero067` and
`h067V` of Stacks 067V. -/
theorem thickeningConormalPairSequence_exact_of_isIso_of_formallyUnramified (g : X ⟶ Y)
    (f : Z.toFunctor ⟶ W.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p)
    (hW : IsUniversalFirstOrderThickening B S hS W q)
    (hsq : Z.ι ≫ p.hom ≫ g.hom = f ≫ W.ι ≫ q.hom)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g))
    (hj : FormallyUnramified (universalThickeningInclusion B S hS hZ ≫ p ≫ g).hom)
    (hzero067 : universalThickeningConormalMap B S hS g f hZ hW hsq ≫
      conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (p ≫ g) = 0)
    (h067V : (ShortComplex.mk _ _ hzero067).Exact) :
    ∃ hc : universalThickeningConormalMap B S hS g f hZ hW hsq ≫
        thickeningConormalFirstMap B S hS hZ g he = 0,
      (ShortComplex.mk _ _ hc).Exact ∧ Epi (thickeningConormalFirstMap B S hS hZ g he) := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ g) := he
  have key := thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ g he
  have hc : universalThickeningConormalMap B S hS g f hZ hW hsq ≫
      thickeningConormalFirstMap B S hS hZ g he = 0 := by
    refine (cancel_mono (thickeningSheafOfDifferentialsMap B S hS hZ g)).mp ?_
    rw [Category.assoc, key, hzero067, zero_comp]
  refine ⟨hc, ?_,
    epi_thickeningConormalFirstMap_of_isIso_of_formallyUnramified B S hS g hZ he hj⟩
  have hsc : ShortComplex.mk _ _ hc ≅ ShortComplex.mk _ _ hzero067 :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (asIso (thickeningSheafOfDifferentialsMap B S hS hZ g)) (by simp) (by simpa using key.symm)
  exact (ShortComplex.exact_iff_of_iso hsc).mpr h067V

end AlgebraicGeometry.Space

end
