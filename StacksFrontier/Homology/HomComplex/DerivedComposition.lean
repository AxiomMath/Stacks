module

public import StacksFrontier.Homology.HomComplex.DerivedInternalHom

/-!
# Composition for derived internal Hom

Let `R` be a commutative ring. Composition of morphisms induces a canonical morphism
`RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` in the derived category `D(R)`, for all objects `K`,
`L`, `M`. This file records the functoriality of that composition morphism: it is
contravariantly natural in the source `K`, covariantly natural in the target `M`, and dinatural
in the middle object `L`.

## Main results

* `StacksDraft.DerivedHom.derivedInternalHomComposition_natural` ([stacks 0A8J]): the three
  functoriality laws for the canonical composition of derived internal Homs.

## Implementation notes

The composition morphism is the one fixed by the K-flat/K-injective model construction of the
derived tensor--Hom adjunction, namely `DerivedInternalHom.Model.composition`, defined from
evaluation and the canonical currying isomorphism of that adjunction; it is therefore honest
data rather than an existential statement, and no separate uniqueness clause is needed.

The middle object `L` occurs covariantly in `RHom(K, L)` and contravariantly in `RHom(L, M)`,
so functoriality in `L` cannot be an ordinary naturality square and is stated as a dinaturality
equation. The explicit type ascriptions in that clause pin down the morphism of the product
category whose image under the derived tensor bifunctor is intended.

## References

* [Stacks Project, Tag 0A8J](https://stacks.math.columbia.edu/tag/0A8J)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace StacksDraft.DerivedHom

/-- **Stacks 0A8J.** The canonical composition morphisms
`RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` in `D(R)` are contravariantly natural in
`K`, dinatural in `L`, and covariantly natural in `M`. -/
@[stacks 0A8J]
theorem derivedInternalHomComposition_natural
    (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat R)] :
    (∀ {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K),
      (DerivedInternalHom.Model.tensor R).map
            (𝟙 ((DerivedInternalHom.Model.hom R).obj (Opposite.op L, M)),
              (DerivedInternalHom.Model.hom R).map (f.op, 𝟙 L)) ≫
          DerivedInternalHom.Model.composition K' L M =
        DerivedInternalHom.Model.composition K L M ≫
          (DerivedInternalHom.Model.hom R).map (f.op, 𝟙 M)) ∧
    (∀ {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L),
      (DerivedInternalHom.Model.tensor R).map
            ((DerivedInternalHom.Model.hom R).map (f.op, 𝟙 M),
              𝟙 ((DerivedInternalHom.Model.hom R).obj (Opposite.op K, L'))) ≫
          DerivedInternalHom.Model.composition K L' M =
        (DerivedInternalHom.Model.tensor R).map
            ((𝟙 ((DerivedInternalHom.Model.hom R).obj (Opposite.op L, M)),
              ((DerivedInternalHom.Model.hom R).map (𝟙 (Opposite.op K), f) :
                (DerivedInternalHom.Model.hom R).obj (Opposite.op K, L') ⟶
                  (DerivedInternalHom.Model.hom R).obj (Opposite.op K, L))) :
              ((DerivedInternalHom.Model.hom R).obj (Opposite.op L, M),
                (DerivedInternalHom.Model.hom R).obj (Opposite.op K, L')) ⟶
              ((DerivedInternalHom.Model.hom R).obj (Opposite.op L, M),
                (DerivedInternalHom.Model.hom R).obj (Opposite.op K, L))) ≫
          DerivedInternalHom.Model.composition K L M) ∧
    (∀ {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M'),
      (DerivedInternalHom.Model.tensor R).map
            ((DerivedInternalHom.Model.hom R).map (𝟙 (Opposite.op L), f),
              𝟙 ((DerivedInternalHom.Model.hom R).obj (Opposite.op K, L))) ≫
          DerivedInternalHom.Model.composition K L M' =
        DerivedInternalHom.Model.composition K L M ≫
          (DerivedInternalHom.Model.hom R).map (𝟙 (Opposite.op K), f)) :=
  ⟨(DerivedInternalHom.Model.canonicalMapLaws R).composition_naturality_source,
    (DerivedInternalHom.Model.canonicalMapLaws R).composition_dinaturality,
    (DerivedInternalHom.Model.canonicalMapLaws R).composition_naturality_target⟩

end StacksDraft.DerivedHom

end
