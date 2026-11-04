module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentablePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings

/-!
# Compactness of constructible étale sheaves of sets

Let `X` be a quasi-compact quasi-separated scheme. Morphisms out of a constructible sheaf of sets
on `X_étale` commute with filtered colimits: for a filtered colimit `G = colim G_i` of sheaves of
sets, `Mor(F, G) = colim Mor(F, G_i)`. This is the sheaves-of-sets case of Stacks 09Z4.

Stacks 09Y9 presents such a sheaf as a coequalizer of two maps between finite coproducts of
sheaves represented by quasi-compact quasi-separated étale objects, which is the predicate
`AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation`. For a sheaf presented that
way compactness needs only one statement about the geometry of the small étale site, namely that a
quasi-compact quasi-separated étale object has a cofinal system of finite coverings with
quasi-compact pairwise fibre products
(`CategoryTheory.GrothendieckTopology.HasFiniteQuasiCompactCoverings`, the hypothesis of part (4)
of Stacks 0738); that statement is
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`. Everything else — Yoneda's lemma for
sheaves of sets, part (4) of Stacks 0738 itself, and the closure of finite presentability under
finite coproducts and coequalizers — is supplied by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactRepresentables`.

The presentation itself is not available in the library, so Stacks 09Y9 is carried as the named
hypothesis `h09Y9`.

## Main results

* `AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation` —
  a sheaf of sets with a finite coequalizer presentation by quasi-compact quasi-separated
  representables is finitely presentable, given the cofinality hypothesis on those
  representables.
* `AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleSetSheaf` — **the sheaves-of-sets
  case of Stacks 09Z4**, with Stacks 09Y9 as a hypothesis.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A sheaf of sets on the small étale site of `X` presented as a coequalizer of two maps between
finite coproducts of sheaves represented by quasi-compact quasi-separated étale objects is
finitely presentable, provided every such object has a cofinal system of finite coverings with
quasi-compact pairwise fibre products.

Composed with Stacks 09Y9, which produces such a presentation for every constructible sheaf of
sets on a quasi-compact quasi-separated scheme, this is the sheaves-of-sets case of
Stacks 09Z4. -/
public theorem isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))}
    (hqc : ∀ W : SmallEtale B X.1 X.property,
      CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) →
      QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W) →
      (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings W)
    (hF : HasFiniteQCSRepresentableCoequalizerPresentation B X F) :
    IsFinitelyPresentable.{u + 1} F := by
  let : HasFiniteColimits
      (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  obtain ⟨n, m, U, V, hU, hV, f, g, ⟨e⟩⟩ := hF
  have (k : ℕ) : HasColimitsOfShape (Discrete (Fin k))
      (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :=
    HasFiniteColimits.out _
  have : IsFinitelyPresentable.{u + 1} (coequalizer f g) :=
    Sheaf.isFinitelyPresentable_coequalizer_sigmaSheafifiedYoneda _ U V
      (fun i ↦ hqc (U i) (hU i).1 (hU i).2) (fun j ↦ hqc (V j) (hV j).1 (hV j).2) f g
  exact isCardinalPresentable_of_iso e _

/-- **The sheaves-of-sets case of Stacks 09Z4.** Let `X` be a quasi-compact quasi-separated scheme
and let `F` be a constructible sheaf of sets on `X_étale`. Then morphisms out of `F` commute with
filtered colimits of sheaves of sets: `Mor(F, colim G_i) = colim Mor(F, G_i)`.

Stacks 09Y9 — the presentation of a constructible sheaf of sets as a coequalizer of two maps
between finite coproducts of sheaves represented by quasi-compact quasi-separated étale objects —
is carried as the hypothesis `h09Y9`. It is a special case of
`AlgebraicGeometry.IsConstructibleSetSheaf.isFinitelyPresentable`, which proves Stacks 09Y9. -/
public theorem isFinitelyPresentable_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (h09Y9 : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X G → HasFiniteQCSRepresentableCoequalizerPresentation B X G)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_hasFiniteQCSRepresentableCoequalizerPresentation B X
    (fun W hc hqs ↦ SmallEtale.hasFiniteQuasiCompactCoverings B X W hc hqs) (h09Y9 F hF)

end AlgebraicGeometry

end
