module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.MapHomologyCycles

/-!
# Cohomology read through a representative, and independence of the representative

An object `K` of a derived category is not a complex, so a statement about `Hⁱ(K)` has to be read
through a **representative**: a cochain complex `P` together with an identification
`e : Qh(P) ≅ K`. This file sets up the two comparisons such a representative supplies and proves
the one structural fact about them that makes statements of that shape tractable:

> an identity between maps out of `G(Hᵈ P)` holds for **every** representative as soon as it holds
> for **one** that receives a quasi-isomorphism.

Nothing here is about geometry; the file is stated for an arbitrary additive functor `G` of
abelian categories, an arbitrary functor `L` of the derived categories, and an arbitrary
comparison `L(Qh P) ⟶ Qh(G P)` satisfying one naturality square.

## Main definitions

* `Stacks.RepresentativeHomology.classOfRepresentative`: the identification
  `Hᵃ(P) ⟶ Hᵃ(K)` induced by `e`, through the two factorizations of the cohomology functor.
* `Stacks.RepresentativeHomology.comparisonOfRepresentative`: the comparison
  `Hᵃ(L K) ⟶ Hᵃ(G P)` obtained by transporting `K` back to `Qh(P)` along `e` and applying the
  comparison `L(Qh P) ⟶ Qh(G P)`.

## Main results

* `Stacks.RepresentativeHomology.classOfRepresentative_naturality` and
  `Stacks.RepresentativeHomology.comparisonOfRepresentative_naturality`: both comparisons are
  natural in the representative, in the sense made precise by a map `ψ : P₁ ⟶ P` of
  representatives of the *same* `K`.
* `Stacks.RepresentativeHomology.eq_mapHomology_of_quasiIso`: **the reduction.** If
  `ψ : P₁ ⟶ P` is a quasi-isomorphism and
  `G(class) ≫ γ ≫ comparison = Stacks.MapHomologyCycles.mapHomology` holds at `P₁`, then it
  holds at `P`. The morphism `γ` is arbitrary: the reduction uses nothing about it, which is why
  it applies to a comparison that is still being constructed.

## Implementation notes

*The comparison is taken as a family of morphisms together with one naturality square, not as a
natural transformation.* A natural transformation `Qh ⋙ L ⟶ G.mapHomotopyCategory _ ⋙ Qh` has
components whose declared target is `(G.mapHomotopyCategory _ ⋙ Qh).obj (Qh-quotient of P)`,
which is only `rfl`-equal — not interchangeable at the `implicit` transparency level — to
`Qh.obj (quotient of G P)`. A goal mixing the two is not type-correct at that level, so `rw`,
`simp only` and even `Category.assoc` refuse it; taking the family and the square in the second
spelling removes the mismatch from every statement in this file. Consumers supply the components
of their natural transformation and its naturality in **argument** position, where the `rfl` is
discharged at default transparency.

*The remaining mismatch is confined to one `have`.* `HomologicalComplex.homologyMap φ a` has
source `P.homology a` while the factorization isomorphism has target
`(HomologicalComplex.homologyFunctor _ _ a).obj P`, and the two are again only `rfl`-equal, so
the last composite of `comparisonOfRepresentative_naturality` is assembled in **term mode** with
`congrArg` and `Category.assoc` rather than by rewriting.

*No bound on the complexes is needed.* Both comparisons exist in every degree for every complex;
it is only their invertibility that needs a bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.RepresentativeHomology

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]

/-- **The cohomology class of a representative.** For a cochain complex `P` with an
identification `e` of its class in the derived category with `K`, this is the induced
identification of `Hᵃ(P)` with `Hᵃ(K)`, through the two factorizations of the cohomology
functor — first through the homotopy category, then through the derived category. -/
def classOfRepresentative (P : CochainComplex C ℤ) {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) (a : ℤ) :
    P.homology a ⟶ (homologyFunctor C a).obj K :=
  (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) a).inv.app P ≫
    (homologyFunctorFactorsh C a).inv.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≫
    (homologyFunctor C a).map e.hom

section Class

variable {P₁ P : CochainComplex C ℤ} (ψ : P₁ ⟶ P) {K : DerivedCategory C}
  (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K)
  (e₁ : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P₁) ≅ K)
  (he : e₁.hom =
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ) ≫ e.hom) (a : ℤ)

include he in
/-- **`classOfRepresentative` is natural in the representative.** If `ψ : P₁ ⟶ P` is a map of
representatives of the same object — the identification of `P₁` being the one `ψ` induces from
that of `P` — then the class of `P₁` is the class of `P` precomposed with `Hᵃ(ψ)`. -/
theorem classOfRepresentative_naturality :
    classOfRepresentative P₁ e₁ a =
      HomologicalComplex.homologyMap ψ a ≫ classOfRepresentative P e a := by
  have h2 := (homologyFunctorFactorsh C a).inv.naturality
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ)
  have h1 := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) a).inv.naturality ψ
  simp only [classOfRepresentative, he, Functor.map_comp]
  exact (congrArg (fun t => _ ≫ t) ((reassoc_of% h2.symm) _)).trans ((reassoc_of% h1.symm) _)

end Class

section Comparison

variable (G : C ⥤ D) [G.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
  (cmp : ∀ P : CochainComplex C ℤ,
    L.obj (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ⟶
      Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))

/-- **A comparison `L(Qh P) ⟶ Qh(G P)`, read through a representative.** The object `K` is
transported back to the class of `P` along `e`, compared with the class of `G P`, and the result
read on cohomology through the two factorizations. -/
def comparisonOfRepresentative (P : CochainComplex C ℤ) {K : DerivedCategory C}
    (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) (a : ℤ) :
    (homologyFunctor D a).obj (L.obj K) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology a :=
  (homologyFunctor D a).map (L.map e.inv ≫ cmp P) ≫
    (homologyFunctorFactorsh D a).hom.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) a).hom.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

variable {P₁ P : CochainComplex C ℤ} (ψ : P₁ ⟶ P)
  (hcmp : L.map (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ)) ≫ cmp P =
    cmp P₁ ≫ Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)))
  {K : DerivedCategory C}
  (e : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K)
  (e₁ : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P₁) ≅ K)
  (he : e₁.hom =
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ) ≫ e.hom) (a : ℤ)

include he hcmp in
/-- **`comparisonOfRepresentative` is natural in the representative.** The comparison at `P₁`,
followed by `Hᵃ(G ψ)`, is the comparison at `P`. Note the direction: it is `G ψ` that appears,
and no invertibility of it is needed — only the naturality square of `cmp` and `he`. -/
theorem comparisonOfRepresentative_naturality :
    comparisonOfRepresentative G L cmp P₁ e₁ a ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) a =
      comparisonOfRepresentative G L cmp P e a := by
  have h4 : e₁.inv ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ψ) =
      e.inv := by
    rw [Iso.inv_comp_eq, he, assoc, e.hom_inv_id, comp_id]
  have h5 : (L.map e₁.inv ≫ cmp P₁) ≫
      Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)) =
      L.map e.inv ≫ cmp P := by
    rw [assoc, ← hcmp, ← assoc, ← Functor.map_comp, h4]
  have h1 := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) a).hom.naturality
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)
  have h2 := (homologyFunctorFactorsh D a).hom.naturality
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ))
  simp only [Functor.comp_obj, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] at h1 h2
  have hA := congrArg (homologyFunctor D a).map h5
  rw [Functor.map_comp] at hA
  simp only [comparisonOfRepresentative, ← hA, assoc]
  exact congrArg _ ((assoc _ _ _).trans ((congrArg _ h1.symm).trans ((reassoc_of% h2.symm) _)))

include he hcmp in
/-- **A cycle-free identity at one representative gives it at every representative.** Suppose
`G` is right exact, so that `Stacks.MapHomologyCycles.mapHomology` exists, and suppose that
for a quasi-isomorphism `ψ : P₁ ⟶ P` of representatives of the same `K` the identity

> `G(class of P₁) ≫ γ ≫ (comparison at P₁) = mapHomology G P₁`

holds. Then the same identity holds at `P`.

The morphism `γ` is **arbitrary**: no property of it is used. So the quantifier over
representatives in a statement of this shape can be discharged against a single convenient one —
in the intended application, a K-flat complex with no terms above the top degree — before the
comparison `γ` it is about has been identified at all.

The proof is the two naturality statements above together with
`Stacks.MapHomologyCycles.mapHomology_naturality`, cancelled against the epimorphism
`G(Hᵃ(ψ))`, which is one because `ψ` is a quasi-isomorphism. -/
theorem eq_mapHomology_of_quasiIso [PreservesFiniteColimits G] (hψ : QuasiIso ψ)
    (γ : G.obj ((homologyFunctor C a).obj K) ⟶ (homologyFunctor D a).obj (L.obj K))
    (h₁ : G.map (classOfRepresentative P₁ e₁ a) ≫ γ ≫
        comparisonOfRepresentative G L cmp P₁ e₁ a =
      Stacks.MapHomologyCycles.mapHomology G P₁ a) :
    G.map (classOfRepresentative P e a) ≫ γ ≫ comparisonOfRepresentative G L cmp P e a =
      Stacks.MapHomologyCycles.mapHomology G P a := by
  rw [← cancel_epi (G.map (HomologicalComplex.homologyMap ψ a)),
    Stacks.MapHomologyCycles.mapHomology_naturality, ← h₁,
    classOfRepresentative_naturality ψ e e₁ he a, G.map_comp]
  simp only [assoc]
  rw [comparisonOfRepresentative_naturality G L cmp ψ hcmp e e₁ he a]

end Comparison

end Stacks.RepresentativeHomology

end
