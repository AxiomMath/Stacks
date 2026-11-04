module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Homology.DoubleHomology

/-!
# The degree zero cohomology sheaf of the naive cotangent complex

For a morphism `a : A ⟶ B` of sheaves of commutative rings on a site, the naive cotangent
complex `NL_{B/A}` is the two-term complex

`I/I² ⟶ B ⊗[A[B]] Ω[A[B]/A]`

attached to the conormal sequence of the canonical polynomial presentation `A[B] ⟶ B`. Its
degree `0` cohomology sheaf is therefore the cokernel of the conormal map, and the conormal
sequence identifies that cokernel with the sheaf of relative differentials `Ω_{B/A}`.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIsoCokernel`: the degree `0`
  cohomology sheaf is the cokernel of the conormal map.
* `Stacks.SheafOfModules.cokernelCanonicalConormalSequenceIso`: that cokernel is the
  right-hand term of the conormal sequence.
* `Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso`: the canonical isomorphism
  `H⁰(NL_{B/A}) ≅ Ω_{B/A}`.

## Implementation notes

The complex is built with `HomologicalComplex.double`, so its degree `0` cohomology sheaf is
the cokernel of the only nonzero differential by
`HomologicalComplex.doubleHomologyIsoCokernel`. That cokernel is the right-hand term of the
conormal sequence because the sequence is exact at its middle term with epimorphic right-hand
map (`Stacks.Sites.Conormal.conormalSequence_exact`, whose `gIsCokernel` is used here), and
that term is `Ω_{B/A}` by `Stacks.Sites.Conormal.imageDifferentialsIso`. The last comparison
produces the differentials of `A[B] ⟶ A[B] ⟶ B`, which is `a` by
`Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap`; that equation of
morphisms is transported with `eqToIso`.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- The degree `0` cohomology sheaf of `NL_{B/A}` is the cokernel of the conormal map: the
complex is a `HomologicalComplex.double`, which has nothing in degree `1`. -/
noncomputable def naiveCotangentComplexHomologyZeroIsoCokernel :
    (naiveCotangentComplex.{v, u, w, z} J A B a).homology 0 ≅
      cokernel (canonicalConormalSequence.{v, u, w, z} J A B a).f := by
  change (HomologicalComplex.double
    (canonicalConormalSequence.{v, u, w, z} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).homology 0 ≅ _
  exact HomologicalComplex.doubleHomologyIsoCokernel _ _ (by decide)

/-- The conormal sequence of the canonical polynomial presentation is exact at its middle
term and its right-hand map is an epimorphism, so its right-hand term is the cokernel of the
conormal map. -/
noncomputable def cokernelCanonicalConormalSequenceIso :
    cokernel (canonicalConormalSequence.{v, u, w, z} J A B a).f ≅
      (canonicalConormalSequence.{v, u, w, z} J A B a).X₃ :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (Stacks.Sites.Conormal.conormalSequence_exact.{v, u, w, z} J A
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)) B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)).gIsCokernel

/-- **Stacks 08TY in degree `0`.** The degree `0` cohomology sheaf of the naive cotangent
complex `NL_{B/A}` of a morphism of sheaves of commutative rings is the sheaf of relative
differentials `Ω_{B/A}`. -/
noncomputable def naiveCotangentComplexHomologyZeroIso :
    (naiveCotangentComplex.{v, u, w, z} J A B a).homology 0 ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  naiveCotangentComplexHomologyZeroIsoCokernel.{v, u, w, z} J A B a ≪≫
    cokernelCanonicalConormalSequenceIso.{v, u, w, z} J A B a ≪≫
    Stacks.Sites.Conormal.imageDifferentialsIso.{v, u, w, z} J A
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)) B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a) ≪≫
    eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B a))

end Stacks.SheafOfModules

end
