module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# The diagram of two composable exact functors of Galois categories

Two composable exact functors `H : C ⥤ C'` and `H' : C' ⥤ C''` between Galois categories give a
2-commutative diagram whose top row is `H` followed by `H'`, whose bottom row is restriction along
the induced continuous homomorphisms `h : Aut F' → Aut F` and `h' : Aut F'' → Aut F'`, and whose
vertical arrows are the identifications of each Galois category with the finite continuous actions
of the automorphism group of its fibre functor.

## Main definitions

* `CategoryTheory.TranslationDiagram` packages the two fibre-functor isomorphisms together with
  the two induced continuous homomorphisms and the two 2-commutative squares.

## Main results

* `CategoryTheory.nonempty_translationDiagram` produces the diagram from exactness of the two
  functors.
* `CategoryTheory.TranslationDiagram.outerIso` pastes the two squares into the outer rectangle.

## Implementation notes

The bottom row is the pair of restriction functors `ContAction.res` along `h` and `h'` separately,
as displayed in the source, rather than the restriction along the composite homomorphism.

## References

* [Stacks Project, Tag 0BTR](https://stacks.math.columbia.edu/tag/0BTR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete CategoryTheory.PreGaloisCategory

universe u v u' v' u'' v'' w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']

/-- The diagram attached to two composable exact functors of Galois categories: an isomorphism of
fibre functors for each functor, together with the continuous homomorphism of automorphism groups
and the 2-commutative square that each such isomorphism determines. -/
public structure TranslationDiagram (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (F'' : C'' ⥤ FintypeCat.{w}) (H : C ⥤ C') (H' : C' ⥤ C'') where
  /-- The isomorphism of fibre functors for `H`. -/
  fiberIso : H ⋙ F' ≅ F
  /-- The isomorphism of fibre functors for `H'`. -/
  fiberIso' : H' ⋙ F'' ≅ F'
  /-- The homomorphism `h` and the left-hand square. -/
  left : GaloisFunctorData F F' H fiberIso
  /-- The homomorphism `h'` and the right-hand square. -/
  right : GaloisFunctorData F' F'' H' fiberIso'

namespace TranslationDiagram

variable {F : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}} {F'' : C'' ⥤ FintypeCat.{w}}
  {H : C ⥤ C'} {H' : C' ⥤ C''}

/-- The outer rectangle of the diagram 2-commutes: restricting first along `h` and then along `h'`
agrees with the composite functor `H ⋙ H'`. -/
@[stacks 0BTR "the outer rectangle"]
public def outerIso (D : TranslationDiagram F F' F'' H H') :
    (PreGaloisCategory.functorToContAction F ⋙ ContAction.res FintypeCat D.left.hom) ⋙
        ContAction.res FintypeCat D.right.hom ≅
      H ⋙ H' ⋙ PreGaloisCategory.functorToContAction F'' :=
  Functor.isoWhiskerRight D.left.actionIso (ContAction.res FintypeCat D.right.hom) ≪≫
    Functor.isoWhiskerLeft H D.right.actionIso

end TranslationDiagram

/-- Two composable exact functors between Galois categories admit fibre-functor isomorphisms whose
induced continuous homomorphisms fit into a 2-commutative diagram over the categories of finite
continuous actions. -/
@[stacks 0BTR "the two 2-commutative squares"]
public theorem nonempty_translationDiagram
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (hH : exactFunctor C C' H) (hH' : exactFunctor C' C'' H') :
    Nonempty (TranslationDiagram F F' F'' H H') := by
  obtain ⟨t⟩ := nonempty_fiberIso_of_exact F F' H hH
  obtain ⟨t'⟩ := nonempty_fiberIso_of_exact F' F'' H' hH'
  obtain ⟨d⟩ := nonempty_galoisFunctorData_of_fiberIso F F' H t
  obtain ⟨d'⟩ := nonempty_galoisFunctorData_of_fiberIso F' F'' H' t'
  exact ⟨⟨t, t', d, d'⟩⟩

end CategoryTheory
