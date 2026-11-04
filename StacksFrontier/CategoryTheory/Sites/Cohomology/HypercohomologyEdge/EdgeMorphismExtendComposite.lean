module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExtend
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The comparison of the two indexings of homology, read at a complex

`Stacks.DerivedIndexing.extendMapHomologyIso` compares the degree-`i` homology of `G` applied
termwise to a cochain complex `N` indexed by `ℕ`, read in the homotopy category of `ℕ`-indexed
complexes, with the degree-`i` homology of `G` applied termwise to the extension by zero of `N`
to a complex indexed by `ℤ`. Both of those homology objects are computed in a homotopy category,
and the consumer of the comparison — the `Gamma(V, -)`-exactness mirror of
`Stacks.Cohomology.AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`
for [Stacks, Tag 01XK] rather than [Stacks, Tag 089W] — needs the comparison read on homology of
*complexes*, where `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomologyIso_comp_homologyComparison` applies.

That reading is what this file supplies: `extendMapHomologyIso`, followed by the factorisation
of the degree-`i` cohomology functor of the `ℤ`-indexing through the homotopy category, is the
factorisation of the degree-`i` cohomology functor of the `ℕ`-indexing, followed by
`HomologicalComplex.extendHomologyIso` inverted and by the homology of
`Stacks.DerivedIndexing.mapExtendIso`.

## Main results

* `Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp_homologyFunctorFactors`: **the two
  indexings of homology, compared on homology objects of complexes.**

## Implementation notes

This file exists because the statement names both `Stacks.DerivedIndexing.extendMapHomologyIso`,
declared in `Homology/DerivedIndexing/Composite.lean`, and
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomotopyHomologyNatIso_hom_app_quotient`, declared in `EdgeMorphismExtend.lean`; neither
of those two modules imports the other.

*Everything is reconciled in argument position.* The homotopy-category image of the extension of
`(G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N` admits two spellings — one through
`CategoryTheory.Functor.mapHomotopyCategory` and `ComplexShape.Embedding.extendHomotopyFunctor`,
one through the quotient functor applied to the extension of complexes — and the comparisons
identifying them, `ComplexShape.Embedding.extendHomotopyFunctorFactors` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, are `CategoryTheory.Iso.refl`. Substituting
an identity for one factor of a composite does not change the object the composite records
between its two factors, so `Category.id_comp` stops matching and no rewrite can remove such a
factor. Every step below is therefore a term applied to its hypotheses — `congrArg`,
`Category.assoc`, and the single private cancellation `inv_comp_eq_of_hom_eq`, which is stated at
variables of an abstract category — so that the elaborator checks the two spellings against one
another at default transparency, where they are one object.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits ComplexShape
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.DerivedIndexing

universe v v' u u'

/-- **An isomorphism's inverse against a composite computing its forward morphism.** If
`fh` and `fi` are mutually inverse, `gh` and `gi` are mutually inverse, `ni` and `nh` are
mutually inverse, and `fh = z ≫ gh ≫ ni`, then `fi ≫ z = nh ≫ gi`.

Stated at variables of an abstract category, with each invertibility given as a hypothesis on
plain morphisms rather than as an `CategoryTheory.Iso`: the morphisms it is applied to are
components of natural isomorphisms, so a hypothesis phrased with `CategoryTheory.Iso.inv` would
have to be matched against `CategoryTheory.NatTrans.app` of an inverse, and at variables the
unifier instead meets each morphism directly and reconciles the objects — two of which have two
definitionally equal spellings — in argument position. -/
private theorem inv_comp_eq_of_hom_eq {C : Type*} [Category* C] {P Q R S : C}
    {fh : P ⟶ Q} {fi : Q ⟶ P} (hfi : fi ≫ fh = 𝟙 Q)
    {gh : R ⟶ S} {gi : S ⟶ R} (hgh : gh ≫ gi = 𝟙 R)
    {nh : Q ⟶ S} {ni : S ⟶ Q} (hni : ni ≫ nh = 𝟙 S)
    {z : P ⟶ R} (hf : fh = z ≫ gh ≫ ni) : fi ≫ z = nh ≫ gi := by
  have hz : fh ≫ nh ≫ gi = z := by
    rw [hf]
    simp only [Category.assoc]
    rw [← Category.assoc ni nh gi, hni, Category.id_comp, hgh, Category.comp_id]
  rw [← hz, ← Category.assoc, hfi, Category.id_comp]

section

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  (G : A ⥤ B) [G.Additive] (N : CochainComplex A ℕ) (i : ℕ)

/-- **The two indexings of the homology of `G` applied termwise to `N`, compared on homology
objects of complexes.** The comparison `Stacks.DerivedIndexing.extendMapHomologyIso`, followed by
the factorisation of the degree-`i` cohomology functor of the `ℤ`-indexing through the homotopy
category at `G` applied termwise to the extension of `N`, equals the factorisation of the
degree-`i` cohomology functor of the `ℕ`-indexing at `G` applied termwise to `N`, followed by
`HomologicalComplex.extendHomologyIso` inverted and by the degree-`i` homology of
`Stacks.DerivedIndexing.mapExtendIso`.

So an identity about `extendMapHomologyIso` — in particular
`Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq`, which reads the comparison of the two
indexings of the right derived functors at the chosen injective resolution — becomes an identity
between maps of homology objects of complexes, which is where
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomologyIso_comp_homologyComparison` applies.

The first half is `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomotopyHomologyNatIso_hom_app_quotient`, whose leading factor — the degree-`i`
cohomology of `ComplexShape.Embedding.extendHomotopyFunctorFactors` — is an identity and is
absorbed here; the second half is `Stacks.DerivedIndexing.mapExtendHomotopyNatIso_hom_app`, which
is the class of `mapExtendIso` and is what the naturality of
`HomotopyCategory.homologyFunctorFactors` is applied to. -/
public theorem extendMapHomologyIso_hom_comp_homologyFunctorFactors :
    (extendMapHomologyIso G N i).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (N.extend embeddingUpNat)) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N) ≫
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
            embeddingUpNat (rfl : embeddingUpNat.f i = (i : ℤ))).inv ≫
          HomologicalComplex.homologyMap (mapExtendIso G embeddingUpNat N).hom (i : ℤ) := by
  have hfac : (embeddingUpNat.extendHomotopyFunctorFactors B).hom.app
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N) = 𝟙 _ := rfl
  have hidm : (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map
        ((embeddingUpNat.extendHomotopyFunctorFactors B).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N)) = 𝟙 _ :=
    (congrArg (fun g => (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map g)
      hfac).trans ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map_id _)
  have hez : (extendHomotopyHomologyNatIso (A := B) embeddingUpNat
        (rfl : embeddingUpNat.f i = (i : ℤ))).hom.app
        ((G.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj N)) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extend embeddingUpNat) ≫
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
            embeddingUpNat (rfl : embeddingUpNat.f i = (i : ℤ))).hom ≫
          (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N) :=
    (extendHomotopyHomologyNatIso_hom_app_quotient embeddingUpNat
        (rfl : embeddingUpNat.f i = (i : ℤ))
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N)).trans
      ((congrArg (fun g => g ≫
          (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
              (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extend embeddingUpNat) ≫
            (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
                embeddingUpNat (rfl : embeddingUpNat.f i = (i : ℤ))).hom ≫
              (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).inv.app
                ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N)) hidm).trans
        (Category.id_comp _))
  have hstepB : (extendHomotopyHomologyNatIso (A := B) embeddingUpNat
          (rfl : embeddingUpNat.f i = (i : ℤ))).inv.app
        ((G.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj N)) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extend embeddingUpNat) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N) ≫
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
          embeddingUpNat (rfl : embeddingUpNat.f i = (i : ℤ))).inv :=
    inv_comp_eq_of_hom_eq
      (Iso.inv_hom_id_app (extendHomotopyHomologyNatIso (A := B) embeddingUpNat
          (rfl : embeddingUpNat.f i = (i : ℤ)))
        ((G.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj N)))
      (Iso.hom_inv_id (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
        embeddingUpNat (rfl : embeddingUpNat.f i = (i : ℤ))))
      (Iso.inv_hom_id_app (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) i)
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N))
      hez
  have hstepA : (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (i : ℤ)).map
          ((mapExtendHomotopyNatIso G embeddingUpNat).hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj N)) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (N.extend embeddingUpNat)) =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.app
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extend embeddingUpNat) ≫
        HomologicalComplex.homologyMap (mapExtendIso G embeddingUpNat N).hom (i : ℤ) :=
    (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (i : ℤ)).hom.naturality
      (mapExtendIso G embeddingUpNat N).hom
  rw [extendMapHomologyIso_hom]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun w => (extendHomotopyHomologyNatIso (A := B) embeddingUpNat
      (rfl : embeddingUpNat.f i = (i : ℤ))).inv.app
    ((G.mapHomotopyCategory (ComplexShape.up ℕ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj N)) ≫ w) hstepA) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ HomologicalComplex.homologyMap
    (mapExtendIso G embeddingUpNat N).hom (i : ℤ)) hstepB) ?_
  exact Category.assoc _ _ _

end

end Stacks.DerivedIndexing

end
