module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.TrivialComposite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Triviality of the composite of induced homomorphisms

Let `H : C ⥤ C'` and `H' : C' ⥤ C''` be functors between Galois categories with fibre functors
`F`, `F'`, `F''`, and let `t : H ⋙ F' ≅ F` and `t' : H' ⋙ F'' ≅ F'` be isomorphisms of fibre
functors (for exact functors these exist by `CategoryTheory.nonempty_fiberIso_of_exact`). The
homomorphisms `h = inducedHom F F' H t : Aut F' →* Aut F` and
`h' = inducedHom F' F'' H' t' : Aut F'' →* Aut F'` are those of the source. Their composite
`h ∘ h'` is trivial exactly when every object `H' (H X)` is a finite coproduct of terminal objects.

## Main results

* `CategoryTheory.inducedHom_comp_eq_one_iff_forall_isFiniteCoproductOfTerminal`: the composite
  `h ∘ h'` is trivial if and only if the composite functor takes every object to a finite
  coproduct of terminal objects.

## Implementation notes

The continuity of `h`, `h'` and the 2-commutative squares relating `H`, `H'` with restriction of
finite continuous actions are constructed from `t` and `t'` by
`CategoryTheory.galoisFunctorDataOfFiberIso`, so they are not assumed. The statement holds for
every choice of `t` and `t'`, hence for the homomorphisms of the source whatever choices are made.

## References

* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' u'' v'' w

namespace CategoryTheory

/-- **Stacks Project, Tag 0BS8.** Let `H : C ⥤ C'` and `H' : C' ⥤ C''` be functors between
Galois categories with fibre functors `F`, `F'`, `F''`, and let `t : H ⋙ F' ≅ F` and
`t' : H' ⋙ F'' ≅ F'` be isomorphisms of fibre functors, with induced homomorphisms
`h : Aut F' →* Aut F` and `h' : Aut F'' →* Aut F'`. Then `h ∘ h'` is trivial if and only if every
object in the image of `H ⋙ H'` is a finite coproduct of terminal objects. -/
@[stacks 0BS8 "for every choice of fibre-functor isomorphisms; continuity of the induced
homomorphisms and the 2-commutative squares are constructed, not assumed",
  sga "1 V 6.5" "more general"]
public theorem inducedHom_comp_eq_one_iff_forall_isFiniteCoproductOfTerminal
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C'']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'') (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F') :
    (inducedHom F F' H t).comp (inducedHom F' F'' H' t') = 1 ↔
      ∀ X : C, IsFiniteCoproductOfTerminal ((H ⋙ H').obj X) := by
  let d := galoisFunctorDataOfFiberIso F F' H t
  let d' := galoisFunctorDataOfFiberIso F' F'' H' t'
  rw [← d.hom_toMonoidHom, ← d'.hom_toMonoidHom]
  exact comp_hom_eq_one_iff_forall_isFiniteCoproductOfTerminal F F' F'' H H' t t' d d'

end CategoryTheory
