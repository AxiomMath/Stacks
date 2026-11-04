module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Category
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# The function field of a variety

The function field of a variety `X` over `k` is a field extension of `k`, through the stalk
map of the structure morphism at the generic point, and it is finitely generated as such. This
makes the function field an object of the category of finitely generated field extensions of `k`.

## Main definitions

* `AlgebraicGeometry.functionFieldAlgebraMap` — the structure map `k → k(X)`.
* `AlgebraicGeometry.varietyFunctionFieldAlgebra` — the resulting `k`-algebra structure.
* `AlgebraicGeometry.functionFieldObject` — `k(X)` as a finitely generated field extension of `k`.
* `AlgebraicGeometry.functionFieldAlgebraMap_eq_germToFunctionField` — the same structure map
  described through global sections.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The structure map `k → k(X)` of a variety over `k`, obtained from the stalk map of the
structure morphism at the generic point and the canonical map from `k` to the stalk of
`Spec k` at the image point. -/
noncomputable def functionFieldAlgebraMap {k : Type u} [Field k]
    (X : Variety k) : k →+* X.toScheme.functionField := by
  let η := genericPoint X.toScheme
  let R := (Spec (.of k)).presheaf.stalk (X.structureMap η)
  letI : Algebra k R := StructureSheaf.stalkAlgebra k (X.structureMap η)
  exact (X.structureMap.stalkMap η).hom.comp (algebraMap k R)

/-- The function field of a variety over `k` is a `k`-algebra, through
`AlgebraicGeometry.functionFieldAlgebraMap`. -/
noncomputable instance varietyFunctionFieldAlgebra {k : Type u} [Field k]
    (X : Variety k) : Algebra k X.toScheme.functionField :=
  (functionFieldAlgebraMap X).toAlgebra

/-- The function field of a variety over `k` is essentially of finite type over `k`, that is,
finitely generated as a field extension of `k`. Indeed it is essentially of finite type over
the stalk of `Spec k` at the image of the generic point, and that stalk is a quotient of `k`. -/
lemma varietyFunctionField_essFiniteType {k : Type u} [Field k]
    (X : Variety k) : Algebra.EssFiniteType k X.toScheme.functionField := by
  let η := genericPoint X.toScheme
  let R := (Spec (.of k)).presheaf.stalk (X.structureMap η)
  let K := X.toScheme.functionField
  let : Algebra k R := StructureSheaf.stalkAlgebra k (X.structureMap η)
  let : Algebra R K := (X.structureMap.stalkMap η).hom.toAlgebra
  let : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType R K := LocallyOfFiniteType.stalkMap X.structureMap η
  have hsurj : Function.Surjective (algebraMap k R) := by
    show Function.Surjective (StructureSheaf.toStalk k (X.structureMap η)).hom
    exact fieldBaseStalkAlgebraMap_surjective (Subsingleton.elim _ _)
  have : Algebra.EssFiniteType k R :=
    RingHom.essFiniteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  exact Algebra.EssFiniteType.comp k R K

/-- The `k`-algebra structure map of the function field of a variety, described through global
sections instead of stalks: it is the inverse of `AlgebraicGeometry.Scheme.ΓSpecIso` followed by
the global-sections map of the structure morphism and the germ at the generic point. -/
lemma functionFieldAlgebraMap_eq_germToFunctionField {k : Type u} [Field k] (X : Variety k) :
    letI : Nonempty (⊤ : X.toScheme.Opens) := ⟨⟨genericPoint X.toScheme, trivial⟩⟩
    functionFieldAlgebraMap X =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
        X.toScheme.germToFunctionField ⊤).hom := by
  let : Nonempty (⊤ : X.toScheme.Opens) := ⟨⟨genericPoint X.toScheme, trivial⟩⟩
  have h : StructureSheaf.toStalk k (X.structureMap (genericPoint X.toScheme)) ≫
        X.structureMap.stalkMap (genericPoint X.toScheme) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
        X.toScheme.germToFunctionField ⊤ := by
    refine (Category.assoc (Scheme.ΓSpecIso (.of k)).inv
      ((Spec (.of k)).presheaf.germ ⊤ (X.structureMap (genericPoint X.toScheme)) trivial)
      _).trans ?_
    exact congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·)
      (Scheme.Hom.germ_stalkMap X.structureMap ⊤ (genericPoint X.toScheme) trivial)
  exact congrArg CommRingCat.Hom.hom h

/-- The `k`-algebra structure on the function field of a variety agrees with the one built from
global sections. This is the form in which the algebra is named by consumers of Stacks 0BXN, such
as Stacks 0BY1. -/
lemma varietyFunctionFieldAlgebra_eq_germToFunctionField {k : Type u} [Field k]
    (X : Variety k) :
    letI : Nonempty (⊤ : X.toScheme.Opens) := ⟨⟨genericPoint X.toScheme, trivial⟩⟩
    varietyFunctionFieldAlgebra X =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop ≫
        X.toScheme.germToFunctionField ⊤).hom.toAlgebra :=
  congrArg RingHom.toAlgebra (functionFieldAlgebraMap_eq_germToFunctionField X)

/-- The structure morphism of a variety over a field is locally of finite presentation: it is of
finite type and the spectrum of a field is locally Noetherian. -/
lemma varietyStructureMap_locallyOfFinitePresentation {k : Type u} [Field k]
    (Y : Variety k) : LocallyOfFinitePresentation Y.structureMap :=
  (finitePresentation_of_finiteType Y.structureMap).locallyOfFinitePresentation

/-- The finitely generated field extension of `k` underlying a variety over `k`, namely its
function field. -/
noncomputable def functionFieldObject {k : Type u} [Field k] (X : Variety k) :
    FinitelyGeneratedFieldExtension k :=
  ⟨CommAlgCat.of k X.toScheme.functionField,
    ⟨Field.toIsField _, varietyFunctionField_essFiniteType X⟩⟩

end AlgebraicGeometry

end
