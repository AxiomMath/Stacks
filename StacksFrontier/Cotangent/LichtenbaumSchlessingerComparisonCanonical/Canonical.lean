module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical.HomologyZeroNegOne

/-!
# The canonical comparison

This file packages the comparison map of complexes `Algebra.Presentation.lsChainMap` and its
isomorphisms on `H⁰`, `H^{-1}` and `H^{-2}` into the chain-level comparison
`Algebra.Presentation.LichtenbaumSchlessingerComparison.canonical`, and deduces the canonical
map `L_{B/A} → L` in `D(B)` and the isomorphism `τ_{≥ -2} L_{B/A} ≅ L` it induces
([Stacks, Tag 09CG]).

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Algebra.Presentation

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
  {X T : Type w} (P : Algebra.Presentation A B X T)

/-- The chain-level comparison of a presentation constructed in the source: the map of complexes
`Algebra.Presentation.lsChainMap`, which is `dψ ⊗ 1`, `λ̄` and `q` in degrees `0`, `-1` and `-2`,
together with its isomorphisms on `H⁰`, `H^{-1}` and `H^{-2}`. -/
@[stacks 09CG "the map of complexes L_{B/A} → L built from the choices ψ and λ of the source,
with its isomorphisms on H^0 (Remark 08UP, Lemma 08RB), H^{-1} (idem) and H^{-2} (Remark 09D6)"]
public def LichtenbaumSchlessingerComparison.canonical : LichtenbaumSchlessingerComparison P where
  hom := P.lsChainMap
  isIso_homologyMap_zero := P.isIso_homologyMap_lsChainMap_zero
  isIso_homologyMap_neg_one := P.isIso_homologyMap_lsChainMap_negOne
  isIso_homologyMap_neg_two := P.isIso_homologyMap_lsChainMap_negTwo

/-- The comparison map of complexes is an isomorphism on cohomology in every degree `≥ -2`. -/
public theorem isIso_homologyMap_lsChainMap (i : ℤ) (hi : -2 ≤ i) :
    IsIso (HomologicalComplex.homologyMap P.lsChainMap i) :=
  (LichtenbaumSchlessingerComparison.canonical P).isIso_homologyMap i hi

/-- The canonical map `L_{B/A} → L` in `D(B)`: the image under the localization functor of the
map of complexes `Algebra.Presentation.lsChainMap`. It does not depend on the choices `ψ` and
`λ`: `Algebra.Presentation.Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger`. -/
@[stacks 09CG "the canonical map L_{B/A} → L in D(B), the class of the map of complexes
dψ ⊗ 1, λ̄, q built from the choices ψ : P₀ → P and the biderivation λ of the source"]
public def canonicalCotangentToLichtenbaumSchlessinger :
    DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B) ⟶
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  DerivedCategory.Q.map P.lsChainMap

/-- The canonical map is an isomorphism on the cohomology of the derived category in every
degree `≥ -2`. -/
public theorem isIso_homologyFunctor_map_canonicalCotangentToLichtenbaumSchlessinger
    (i : ℤ) (hi : -2 ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
      (canonicalCotangentToLichtenbaumSchlessinger P)) :=
  isIso_homologyFunctor_map_cotangentToLichtenbaumSchlessinger
    (LichtenbaumSchlessingerComparison.canonical P) i hi

/-- The canonical map `L_{B/A} → L` factors through the truncation `τ_{≥ -2} L_{B/A}`, and the
factorization is an isomorphism. -/
@[stacks 09CG "the canonical map L_{B/A} → L induces an isomorphism τ_{≥ -2} L_{B/A} → L in
D(B)"]
public theorem isIso_descTruncGE_canonicalCotangentToLichtenbaumSchlessinger :
    IsIso (DerivedCategory.TStructure.t.descTruncGE
      (canonicalCotangentToLichtenbaumSchlessinger P) (-2)) :=
  isIso_descTruncGE_cotangentToLichtenbaumSchlessinger
    (LichtenbaumSchlessingerComparison.canonical P)

/-- The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` induced by the canonical map. -/
@[stacks 09CG "the induced map τ_{≥ -2} L_{B/A} → L is an isomorphism in D(B)"]
public def canonicalTruncGECotangentIsoLichtenbaumSchlessinger :
    (DerivedCategory.TStructure.t.truncGE (-2)).obj
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≅
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  haveI := isIso_descTruncGE_canonicalCotangentToLichtenbaumSchlessinger P
  asIso (DerivedCategory.TStructure.t.descTruncGE
    (canonicalCotangentToLichtenbaumSchlessinger P) (-2))

/-- The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` is the one induced by the canonical map
`L_{B/A} → L`: composing it with the projection to the truncation returns that map. -/
@[stacks 09CG "the isomorphism τ_{≥ -2} L_{B/A} → L is induced by the canonical map L_{B/A} → L"]
public theorem canonicalTruncGECotangentIsoLichtenbaumSchlessinger_fac :
    (DerivedCategory.TStructure.t.truncGEπ (-2)).app
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≫
      (canonicalTruncGECotangentIsoLichtenbaumSchlessinger P).hom =
        canonicalCotangentToLichtenbaumSchlessinger P :=
  DerivedCategory.TStructure.t.π_descTruncGE _ _

end Algebra.Presentation

end
