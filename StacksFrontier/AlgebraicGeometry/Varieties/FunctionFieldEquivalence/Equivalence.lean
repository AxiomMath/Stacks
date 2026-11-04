module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.AffineModel
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.FieldHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Varieties and finitely generated field extensions

Over a field `k`, passing from a variety to its function field identifies dominant rational
maps of varieties over `k` with `k`-algebra maps of function fields in the opposite direction, and
every finitely generated field extension of `k` arises as a function field. So the category of
varieties over `k` and dominant rational maps is anti-equivalent to the category of finitely
generated field extensions of `k`.

## Main results

* `AlgebraicGeometry.functionFieldFunctor` — the contravariant function-field functor.
* `AlgebraicGeometry.varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite` — the
  anti-equivalence between the two categories.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The contravariant functor sending a variety over `k` to its function field and a dominant
rational map to the induced map of function fields. -/
noncomputable def functionFieldFunctor (k : Type u) [Field k] :
    Variety k ⥤ (FinitelyGeneratedFieldExtension k)ᵒᵖ where
  obj X := Opposite.op (functionFieldObject X)
  map {X Y} f := (ObjectProperty.homMk
    (CommAlgCat.ofHom (fieldHomOfRationalMap X Y f))).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact fieldHomOfRationalMap_id X
  map_comp {X Y Z} f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact fieldHomOfRationalMap_comp X Y Z f g

/-- The function-field functor is faithful: a dominant rational map is determined by the induced
map of function fields. -/
instance functionFieldFunctor_faithful (k : Type u) [Field k] :
    (functionFieldFunctor k).Faithful where
  map_injective {X Y} _ _ h :=
    fieldHomOfRationalMap_injective X Y (congrArg (fun t ↦ t.unop.hom.hom) h)

/-- The function-field functor is full: every `k`-algebra map of function fields comes from a
dominant rational map. -/
instance functionFieldFunctor_full (k : Type u) [Field k] :
    (functionFieldFunctor k).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := fieldHomOfRationalMap_surjective X Y f.unop.hom.hom
    refine ⟨g, Quiver.Hom.unop_inj ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact hg

/-- The function-field functor is essentially surjective: every finitely generated field extension
of `k` is the function field of its affine model. -/
instance functionFieldFunctor_essSurj (k : Type u) [Field k] :
    (functionFieldFunctor k).EssSurj where
  mem_essImage K := ⟨affineModelOfFieldExtension K.unop,
    ⟨(affineModelFunctionFieldObjectIso K.unop).op.symm⟩⟩

/-- The function-field functor is an equivalence of categories. -/
instance functionFieldFunctor_isEquivalence (k : Type u) [Field k] :
    (functionFieldFunctor k).IsEquivalence where

/-- **Stacks Project, Tag 0BXN.** Varieties and dominant rational maps over a field are
contravariantly equivalent to finitely generated field extensions of that field. -/
@[stacks 0BXN]
noncomputable def varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite
    (k : Type u) [Field k] :
    Variety k ≌ (FinitelyGeneratedFieldExtension k)ᵒᵖ :=
  (functionFieldFunctor k).asEquivalence

/-- The equivalence of Stacks 0BXN is given by the function-field functor. -/
@[simp]
lemma varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite_functor (k : Type u) [Field k] :
    (varietyEquivalenceFinitelyGeneratedFieldExtensionOpposite k).functor =
      functionFieldFunctor k :=
  rfl

end AlgebraicGeometry

end
