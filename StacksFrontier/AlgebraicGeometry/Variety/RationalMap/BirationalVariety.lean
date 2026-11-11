module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.FunctionField
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Equivalence

/-!
# Birational varieties

Two varieties over a field `k` are birational, that is isomorphic in the category of varieties
over `k` and dominant rational maps, exactly when their function fields are isomorphic as
extensions of `k`, exactly when they have isomorphic nonempty open subvarieties, and exactly when
some nonempty open subvariety of one admits a birational morphism to the other.

## Main results

* `AlgebraicGeometry.Variety.nonempty_iso_tfae`: the four equivalent characterizations of
  birational varieties of Stacks 0BXP.
* `AlgebraicGeometry.Variety.nonempty_iso_iff_birationalOver`: two varieties are isomorphic in
  the category `AlgebraicGeometry.Variety k` of varieties and dominant rational maps exactly when
  they are birational over `k` in the sense of Mathlib's `AlgebraicGeometry.Scheme.BirationalOver`,
  that is, when they have isomorphic dense open subschemes over `Spec k`.

## Implementation notes

The four entries of `AlgebraicGeometry.Variety.nonempty_iso_tfae` follow the order of the source.
Being birational varieties is, by the source, being `Spec k`-birational, which Stacks 0A20 (2)
defines as being isomorphic in the category of irreducible schemes over `Spec k` and dominant
`Spec k`-rational maps; for varieties this is the category `AlgebraicGeometry.Variety k` of
Stacks 0BXN. The function field is `AlgebraicGeometry.Scheme.functionField`, the stalk at the
generic point, with the `k`-algebra structure `AlgebraicGeometry.varietyFunctionFieldAlgebra`
of Stacks 0BXN. Isomorphisms and morphisms of open subvarieties are required explicitly to commute
with the structure morphisms to `Spec k`.

The first entry is compared with the second by the anti-equivalence of Stacks 0BXN, which is
fully faithful and so reflects isomorphisms. The second is compared with the others through
`AlgebraicGeometry.birationalOver_tfae_functionField`, after the ring of rational functions
`Stacks.Chow.rationalFunctions` is identified with the function field as a `k`-algebra by
`AlgebraicGeometry.Variety.rationalFunctionsAlgEquivFunctionField`.

## References

* [Stacks Project, Tag 0BXP](https://stacks.math.columbia.edu/tag/0BXP)
* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The ring of rational functions of a variety over `k` is its function field, as a `k`-algebra.
The `k`-algebra structure on the rational functions is induced by the global sections of the
structure morphism, and the one on the function field is
`AlgebraicGeometry.varietyFunctionFieldAlgebra`. -/
noncomputable def Variety.rationalFunctionsAlgEquivFunctionField (X : Variety k) :
    letI : Algebra k (Stacks.Chow.rationalFunctions X.toScheme) :=
      ((Stacks.Chow.ofSectionRingHom X.toScheme ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop).hom).toAlgebra
    Stacks.Chow.rationalFunctions X.toScheme ≃ₐ[k] X.toScheme.functionField := by
  letI : Algebra k (Stacks.Chow.rationalFunctions X.toScheme) :=
    ((Stacks.Chow.ofSectionRingHom X.toScheme ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop).hom).toAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := (Stacks.Chow.rationalFunctionsEquivFunctionField X.toScheme).val) ?_
  intro a
  change (Stacks.Chow.rationalFunctionsEquivFunctionField X.toScheme).val
      (((Stacks.Chow.ofSectionRingHom X.toScheme ⟨⊤, dense_univ⟩).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop).hom) a) =
    functionFieldAlgebraMap X a
  rw [RingHom.comp_apply, Stacks.Chow.ofSectionRingHom_apply,
    (Stacks.Chow.rationalFunctionsEquivFunctionField X.toScheme).property ⟨⊤, dense_univ⟩ _
      trivial, functionFieldAlgebraMap_eq_germToFunctionField]
  rfl

/-- Two varieties over `k` are isomorphic in the category `AlgebraicGeometry.Variety k` of
varieties and dominant rational maps exactly when their function fields are isomorphic as
extensions of `k`. This is the function-field functor of Stacks 0BXN reflecting isomorphisms. -/
theorem Variety.nonempty_iso_iff_nonempty_algEquiv_functionField (X Y : Variety k) :
    Nonempty (X ≅ Y) ↔
      Nonempty (X.toScheme.functionField ≃ₐ[k] Y.toScheme.functionField) := by
  constructor
  · rintro ⟨e⟩
    let e' : functionFieldObject Y ≅ functionFieldObject X :=
      ((functionFieldFunctor k).mapIso e).unop
    exact ⟨(CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso e')).symm⟩
  · rintro ⟨e⟩
    let e' : functionFieldObject Y ≅ functionFieldObject X :=
      ObjectProperty.isoMk _ (CommAlgCat.isoMk e.symm)
    exact ⟨(functionFieldFunctor k).preimageIso (X := X) (Y := Y) e'.op⟩

/-- The function fields of two varieties over `k` are isomorphic as extensions of `k` exactly
when the varieties are birational over `k` in the sense of
`AlgebraicGeometry.Scheme.BirationalOver`. -/
theorem Variety.nonempty_algEquiv_functionField_iff_birationalOver (X Y : Variety k) :
    Nonempty (X.toScheme.functionField ≃ₐ[k] Y.toScheme.functionField) ↔
      Scheme.BirationalOver X.structureMap Y.structureMap := by
  let : Algebra k (Stacks.Chow.rationalFunctions X.toScheme) :=
    ((Stacks.Chow.ofSectionRingHom X.toScheme ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.structureMap.appTop).hom).toAlgebra
  let : Algebra k (Stacks.Chow.rationalFunctions Y.toScheme) :=
    ((Stacks.Chow.ofSectionRingHom Y.toScheme ⟨⊤, dense_univ⟩).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.structureMap.appTop).hom).toAlgebra
  refine Iff.trans ?_
    ((birationalOver_tfae_functionField k X.structureMap Y.structureMap).out 2 1)
  exact ⟨fun ⟨e⟩ => ⟨(rationalFunctionsAlgEquivFunctionField X).trans
      (e.trans (rationalFunctionsAlgEquivFunctionField Y).symm)⟩,
    fun ⟨e⟩ => ⟨((rationalFunctionsAlgEquivFunctionField X).symm.trans e).trans
      (rationalFunctionsAlgEquivFunctionField Y)⟩⟩

/-- Two varieties over `k` are isomorphic in the category `AlgebraicGeometry.Variety k` of
varieties and dominant rational maps, that is, they are birational in the sense of
Stacks 0A20 (2), exactly when they are birational over `k` in the sense of Mathlib's
`AlgebraicGeometry.Scheme.BirationalOver`: they have isomorphic dense open subschemes over
`Spec k`. -/
theorem Variety.nonempty_iso_iff_birationalOver (X Y : Variety k) :
    Nonempty (X ≅ Y) ↔ Scheme.BirationalOver X.structureMap Y.structureMap :=
  (nonempty_iso_iff_nonempty_algEquiv_functionField X Y).trans
    (nonempty_algEquiv_functionField_iff_birationalOver X Y)

/-- **Stacks Project, Tag 0BXP.** Let `X` and `Y` be varieties over a field `k`. The following
are equivalent:
1. `X` and `Y` are birational varieties, that is, isomorphic in the category of varieties over
   `k` and dominant rational maps;
2. the function fields `k(X)` and `k(Y)` are isomorphic as extensions of `k`;
3. there exist nonempty opens of `X` and `Y` which are isomorphic as varieties over `k`;
4. there exist an open `U ⊆ X` and a birational morphism `U → Y` of varieties over `k`. -/
@[stacks 0BXP "Item (1), birationality of varieties, which the source defines as \
Spec(k)-birationality in the sense of Tag 0A20, is isomorphism in `AlgebraicGeometry.Variety k`, \
the category of varieties over `k` and dominant rational maps of Tag 0BXN. The function field in \
item (2) is the stalk at the generic point with its `k`-algebra structure from Tag 0BXN. The \
opens in items (3) and (4) are nonempty, as varieties are, and the isomorphism and the morphism \
commute with the structure morphisms to `Spec k`."]
theorem Variety.nonempty_iso_tfae (X Y : Variety k) :
    List.TFAE [
      Nonempty (X ≅ Y),
      Nonempty (X.toScheme.functionField ≃ₐ[k] Y.toScheme.functionField),
      ∃ (U : X.toScheme.Opens) (V : Y.toScheme.Opens),
        (U : Set X.toScheme).Nonempty ∧ (V : Set Y.toScheme).Nonempty ∧
          ∃ e : U.toScheme ≅ V.toScheme,
            e.hom ≫ V.ι ≫ Y.structureMap = U.ι ≫ X.structureMap,
      ∃ (U : X.toScheme.Opens), (U : Set X.toScheme).Nonempty ∧
        ∃ f : U.toScheme ⟶ Y.toScheme,
          IsBirational f ∧ f ≫ Y.structureMap = U.ι ≫ X.structureMap] := by
  have h := birationalOver_tfae_functionField k X.structureMap Y.structureMap
  tfae_have 1 ↔ 2 := nonempty_iso_iff_nonempty_algEquiv_functionField X Y
  tfae_have 2 ↔ 3 := (nonempty_algEquiv_functionField_iff_birationalOver X Y).trans (h.out 1 3)
  tfae_have 3 ↔ 4 := h.out 3 4
  tfae_finish

end AlgebraicGeometry

end
