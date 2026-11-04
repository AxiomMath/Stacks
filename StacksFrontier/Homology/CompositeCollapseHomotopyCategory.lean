module

public import StacksFrontier.Homology.CompositeCollapse

/-!
# Collapse of a composite derived functor at the level of complexes

Let `G : C ⥤ D` be an additive, left exact functor between abelian categories which preserves
injective objects, `T : D ⥤ E` an additive functor, and `T' : C ⥤ E` a functor isomorphic to
`G ⋙ T`. If `A : C` is `G`-acyclic, then `G` carries an injective resolution of `A` to an
injective resolution of `G A` (`Stacks.RightDerivedComp.mapOfAcyclic`), so the complex
`R T'(A)`, the image of an injective resolution of `A` under `T'`, is isomorphic in the homotopy
category to the complex `R T(G A)`. Taking cohomology recovers the degreewise collapse
`Stacks.RightDerivedComp.objIso`.

## Main definitions

* `Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIso`: the collapse `R T'(A) ≅ R T(G A)` in
  the homotopy category of `E`, for `T' ≅ G ⋙ T`.
* `Stacks.RightDerivedComp.objIsoOfIso`: the collapse `R ⁿ T'(A) ≅ R ⁿ T(G A)` in each degree.
* `Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIsoComp` and
  `Stacks.RightDerivedComp.objIsoOfIsoComp`: the same for a functor `P ≅ G ⋙ T ⋙ L` with `L`
  additive, respectively exact: `R P(A) ≅ L(R T(G A))` and `R ⁿ P(A) ≅ L(R ⁿ T(G A))`. This is the
  shape of a comparison of higher direct images for two topologies, `L` being sheafification
  for the finer one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
  (T : D ⥤ E) [T.Additive] {T' : C ⥤ E} [T'.Additive] (e : T' ≅ G ⋙ T)
  {A : C} (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))

/-- **The derived functor of a composite at a `G`-acyclic object, as a complex.** For
`T' ≅ G ⋙ T` with `G` additive, left exact and preserving injectives, and `A` acyclic for `G`,
the complex `R T'(A)` computed from an injective resolution of `A` is isomorphic in the homotopy
category to `R T(G A)`. -/
def homotopyCategoryObjIsoOfIso :
    T'.rightDerivedToHomotopyCategory.obj A ≅ T.rightDerivedToHomotopyCategory.obj (G.obj A) :=
  (injectiveResolution A).isoRightDerivedToHomotopyCategoryObj T' ≪≫
    (HomotopyCategory.quotient E (ComplexShape.up ℕ)).mapIso
      (((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℕ)).app
        (injectiveResolution A).cocomplex).symm) ≪≫
    ((mapOfAcyclic G (injectiveResolution A) hA).isoRightDerivedToHomotopyCategoryObj T).symm

/-- **The derived functors of a composite at a `G`-acyclic object.** For `T' ≅ G ⋙ T` with `G`
additive, left exact and preserving injectives, and `A` acyclic for `G`,
`R ⁿ T'(A) ≅ R ⁿ T(G A)` for every `n`. -/
def objIsoOfIso (n : ℕ) : (T'.rightDerived n).obj A ≅ (T.rightDerived n).obj (G.obj A) :=
  (injectiveResolution A).isoRightDerivedObj T' n ≪≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).mapIso
      (((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℕ)).app
        (injectiveResolution A).cocomplex).symm) ≪≫
    ((mapOfAcyclic G (injectiveResolution A) hA).isoRightDerivedObj T n).symm

section ThroughAnExactFunctor

variable {E' : Type*} [Category* E'] [Abelian E'] (L : E ⥤ E') [L.Additive]
  {P : C ⥤ E'} [P.Additive] (e' : P ≅ G ⋙ T ⋙ L)

/-- **The derived functor of `P ≅ G ⋙ T ⋙ L` at a `G`-acyclic object, as a complex.** For `G`
additive, left exact and preserving injectives, `A` acyclic for `G`, and `L` additive, the
complex `R P(A)` is isomorphic in the homotopy category to `L` applied to `R T(G A)`. -/
def homotopyCategoryObjIsoOfIsoComp :
    P.rightDerivedToHomotopyCategory.obj A ≅
      (L.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        (T.rightDerivedToHomotopyCategory.obj (G.obj A)) :=
  (injectiveResolution A).isoRightDerivedToHomotopyCategoryObj P ≪≫
    (HomotopyCategory.quotient E' (ComplexShape.up ℕ)).mapIso
      ((NatIso.mapHomologicalComplex e' (ComplexShape.up ℕ)).app
        (injectiveResolution A).cocomplex) ≪≫
    ((L.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).app
      (mapCocomplex T (mapOfAcyclic G (injectiveResolution A) hA))).symm ≪≫
    (L.mapHomotopyCategory (ComplexShape.up ℕ)).mapIso
      ((mapOfAcyclic G (injectiveResolution A) hA).isoRightDerivedToHomotopyCategoryObj T).symm

/-- **The derived functors of `P ≅ G ⋙ T ⋙ L` at a `G`-acyclic object, for `L` exact.** For `G`
additive, left exact and preserving injectives, `A` acyclic for `G`, and `L` preserving homology,
`R ⁿ P(A) ≅ L(R ⁿ T(G A))` for every `n`. -/
def objIsoOfIsoComp [L.PreservesHomology] (n : ℕ) :
    (P.rightDerived n).obj A ≅ L.obj ((T.rightDerived n).obj (G.obj A)) :=
  (injectiveResolution A).isoRightDerivedObj P n ≪≫
    (HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex e' (ComplexShape.up ℕ)).app
        (injectiveResolution A).cocomplex) ≪≫
    ((mapCocomplex T (mapOfAcyclic G (injectiveResolution A) hA)).sc n).mapHomologyIso L ≪≫
    L.mapIso ((mapOfAcyclic G (injectiveResolution A) hA).isoRightDerivedObj T n).symm

end ThroughAnExactFunctor

end Stacks.RightDerivedComp
