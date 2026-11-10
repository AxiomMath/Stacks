module

public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Homology.Injectives.Sheaf.SheafificationTowerFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial injective embeddings for abelian presheaves

Abelian-group-valued presheaves on a category `C` admit injective embeddings functorially, in
any target universe containing the object and morphism universes of `C`. This is Tag 01DK.

## Main results

* `Stacks.Injectives.presheaf_hasFunctorialInjectiveEmbeddings`: the category of abelian
  presheaves on `C` has functorial injective embeddings.

## Implementation notes

The target universe is written `max u v t` with `t` free, so the result applies to
`AddCommGrpCat`-valued presheaves in any universe at least as large as those of `C`.

## References

* [Stacks Project, Tag 01DK](https://stacks.math.columbia.edu/tag/01DK)
-/

@[expose] public section

open CategoryTheory
open Stacks.Injectives.SheafificationTowerFactorization

universe u v t

namespace Stacks.Injectives

/-- The category of abelian presheaves on a category has functorial injective embeddings. -/
@[stacks 01DK]
theorem presheaf_hasFunctorialInjectiveEmbeddings (C : Type u) [Category.{v} C] :
    HasFunctorialInjectiveEmbeddings (Cᵒᵖ ⥤ AddCommGrpCat.{max u v t}) := by
  let e : Cᵒᵖ ≌ (AsSmall.{max u v t} C)ᵒᵖ := (AsSmall.equiv (C := C)).op
  let P := Equivalence.congrLeft e (E := AddCommGrpCat.{max u v t})
  let A := (AsSmall.{max u v t} C)ᵒᵖ ⥤ AddCommGrpCat.{max u v t}
  have hA : HasFunctorialInjectiveEmbeddings A := by
    obtain ⟨E⟩ := exists_functorialInjectiveEmbedding_presheaf (C := AsSmall.{max u v t} C)
    exact ⟨{ obj X := Arrow.mk (E.emb.app X)
             map f := Arrow.homMk f (E.func.map f) (E.emb.naturality f) },
      rfl, E.mono_emb, E.injective_obj⟩
  have : P.inverse.Additive := by
    change ((Functor.whiskeringLeft _ _ _).obj e.functor).Additive; infer_instance
  have : P.functor.Additive := by
    change ((Functor.whiskeringLeft _ _ _).obj e.inverse).Additive; infer_instance
  have : EnoughInjectives A := enoughInjectives_of_hasFunctorialInjectiveEmbeddings (𝒜 := A) hA
  exact hasFunctorialInjectiveEmbeddings_of_adjunction
    (A := A) (B := Cᵒᵖ ⥤ AddCommGrpCat.{max u v t}) P.inverse P.functor P.toAdjunction
    (by intro X Y f hf; dsimp only [P]; infer_instance)
    (by intro X hX; exact (Functor.map_isZero P.inverse hX).of_iso (P.unitIso.app X)) hA

end Stacks.Injectives
