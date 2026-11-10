module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBifunctorIsoGeneral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor–hom bijection over a ring, in monoidal form

For a commutative ring `A`, the monoidal tensor product of `D(A)`, given by
`CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure`, is identified as a bifunctor
with the tensor half of the tensor–hom bundle `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`
of [Stacks, Tag 0A63]. Through this identification the evaluation morphism
`R𝐻om_A(K, M) ⊗ K ⟶ M` exhibits `R𝐻om_A(K, M)` as an internal hom: for every `Z` the map
`a ↦ a ▷ K ≫ evaluationTensorMap K M` from `Z ⟶ R𝐻om_A(K, M)` to `Z ⊗ K ⟶ M` is a bijection.
Over a Noetherian ring, the evaluation morphism of one dualizing complex against another is an
isomorphism.

## Main definitions

* `Dualizing.monoidalTensorNatIso`: the isomorphism of bifunctors `D(A) × D(A) ⥤ D(A)` between
  the monoidal tensor product and the tensor of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`.
* `Dualizing.monoidalTensorObjIso`: its component at a pair.
* `Dualizing.evaluationTensorMap`: the evaluation morphism `DerivedHomAdjunction.evaluation`,
  as a morphism `R𝐻om_A(K, M) ⊗ K ⟶ M` of the monoidal category.
* `Dualizing.canonicalDerivedSymmetric`: the symmetric structure on
  `CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure`, the symmetry of
  [Stacks, Tag 0FNQ] transported along the scalar equivalence.

## Main results

* `Dualizing.whiskerRight_monoidalTensorObjIso`: the identification is natural in the first
  variable, with whiskering on the monoidal side.
* `Dualizing.tensorHomBijective_evaluationTensorMap`: for all `K`, `M` and `Z` in `D(A)`, the map
  `a ↦ a ▷ K ≫ evaluationTensorMap K M` from `Z ⟶ R𝐻om_A(K, M)` is a bijection.
* `Dualizing.isIso_evaluationTensorMap_iff`: the monoidal evaluation morphism is invertible
  exactly when the adjunction's evaluation morphism is.
* `Dualizing.isIso_evaluationTensorMap_self_of_isDualizingComplex`: for a dualizing complex `ω`
  over a Noetherian ring, `R𝐻om_A(ω, ω) ⊗ ω ⟶ ω` is an isomorphism.
* `Dualizing.isIso_evaluationTensorMap_iff_of_isInvertible`: for an invertible `L` and
  `M ⊗ L ≅ M'`, the evaluation morphisms at `(K, M)` and at `(K, M')` are invertible together.
* `Dualizing.isIso_evaluationTensorMap_of_isDualizingComplex`: for dualizing complexes `K` and
  `K'` over a Noetherian ring, `R𝐻om_A(K, K') ⊗ K ⟶ K'` is an isomorphism.

## Implementation notes

`Dualizing.monoidalTensorIso` chooses a K-flat resolution of each argument and carries no
naturality statement, so the identification is built from the bifunctorial comparison
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` instead. The two agree on pairs of K-flat
complexes, by `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped MonoidalCategory
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable (A : Type u) [CommRing A]

/-- **The monoidal tensor product of `D(A)` and the tensor half of [Stacks, Tag 0A63] agree, as
bifunctors**: the composite of `CochainComplex.DerivedTensor.canonicalDerivedMonoidalTensorIso`,
which identifies the curried monoidal tensor product with the derived tensor product datum of
[Stacks, Tag 068I], and `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`, which identifies
that datum with the tensor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`. -/
def monoidalTensorNatIso :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    Functor.uncurry.obj (curriedTensor (DerivedCategory (ModuleCat.{max u v} A))) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  exact Functor.uncurry.mapIso (canonicalDerivedMonoidalTensorIso.{u, v} A) ≪≫
    derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A

variable {A}

/-- The component of `Dualizing.monoidalTensorNatIso` at a pair: `P ⊗ Q` is the derived tensor
product of the tensor–hom bundle. -/
def monoidalTensorObjIso (P Q : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    P ⊗ Q ≅
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
        (P, Q) :=
  (monoidalTensorNatIso.{u, v} A).app (P, Q)

/-- **The identification is natural in the first variable**, with whiskering on the monoidal
side and `DerivedHomAdjunction.tensor.map (a, 𝟙 Q)` on the adjunction side. -/
theorem whiskerRight_monoidalTensorObjIso
    {P Z : DerivedCategory (ModuleCat.{max u v} A)} (a : Z ⟶ P)
    (Q : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    a ▷ Q ≫ (monoidalTensorObjIso.{u, v} P Q).hom =
      (monoidalTensorObjIso.{u, v} Z Q).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (show ((Z, Q) : DerivedCategory (ModuleCat.{max u v} A) ×
            DerivedCategory (ModuleCat.{max u v} A)) ⟶ (P, Q) from (a, 𝟙 Q)) := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  simpa [monoidalTensorObjIso] using (monoidalTensorNatIso.{u, v} A).hom.naturality
    (show ((Z, Q) : DerivedCategory (ModuleCat.{max u v} A) ×
      DerivedCategory (ModuleCat.{max u v} A)) ⟶ (P, Q) from (a, 𝟙 Q))

/-- The evaluation morphism of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, read as a
morphism `R𝐻om_A(K, M) ⊗ K ⟶ M` of the monoidal category `D(A)`. -/
@[sga "5 IIIB 5.0" "special case"]
def evaluationTensorMap (K M : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
        (op K, M) ⊗ K ⟶ M :=
  let := canonicalDerivedMonoidalStructure.{u, v} A
  (monoidalTensorObjIso.{u, v} _ K).hom ≫
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).evaluation K M

/-- **The tensor–hom bijection of [Stacks, Tag 0A63], in the shape the monoidal criterion asks
for.** For all `K`, `M` and `Z` in `D(A)` the map

`a ↦ a ▷ K ≫ evaluationTensorMap K M`

from `Z ⟶ R𝐻om_A(K, M)` to `Z ⊗ K ⟶ M` is a bijection. -/
theorem tensorHomBijective_evaluationTensorMap
    (K M Z : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    Function.Bijective fun a : Z ⟶
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
          (op K, M) =>
      a ▷ K ≫ evaluationTensorMap.{u, v} K M := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  set d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A
  convert ((d.homEquiv Z K M).toEquiv.trans
    (monoidalTensorObjIso.{u, v} Z K).symm.homFromEquiv).bijective using 1
  funext a
  have hnat := d.homEquiv_naturality_left (K := d.hom.obj (op K, M)) (K' := Z) (L := K) (M := M)
    a (𝟙 _)
  rw [Category.comp_id] at hnat
  change a ▷ K ≫ (monoidalTensorObjIso.{u, v} _ K).hom ≫ d.evaluation K M = _
  rw [← Category.assoc, whiskerRight_monoidalTensorObjIso a K, Category.assoc]
  exact congrArg ((monoidalTensorObjIso.{u, v} Z K).hom ≫ ·) hnat.symm

/-- The monoidal reading of the evaluation morphism is invertible exactly when the adjunction's
own evaluation morphism is. -/
theorem isIso_evaluationTensorMap_iff (K M : DerivedCategory (ModuleCat.{max u v} A)) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    IsIso (evaluationTensorMap.{u, v} K M) ↔
      IsIso ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).evaluation
        K M) := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  exact isIso_comp_left_iff (monoidalTensorObjIso.{u, v} _ K).hom _

/-- **The evaluation morphism of a dualizing complex against itself, in the monoidal
vocabulary.** For a Noetherian ring `A` and a dualizing complex `ω` over `A`, the morphism

`R𝐻om_A(ω, ω) ⊗ ω ⟶ ω`

of the monoidal category `D(A)` is an isomorphism. -/
theorem isIso_evaluationTensorMap_self_of_isDualizingComplex
    [IsNoetherianRing A] (ω : DerivedCategory (ModuleCat.{max u v} A))
    (hω : IsDualizingComplex ω) :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    IsIso (evaluationTensorMap.{u, v} ω ω) :=
  (isIso_evaluationTensorMap_iff.{u, v} ω ω).2
    (isIso_evaluation_self_overRing_of_isDualizingComplex.{u, v} A ω hω)

/-! ### The symmetric structure, and the step from `(K, K)` to `(K, K')` -/

/-- **The monoidal structure on `D(A)` in an independent module universe is symmetric**: the
symmetry of [Stacks, Tag 0FNQ] over `ULift.{v} A`, transported along the scalar equivalence as
the monoidal structure `CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure` is. -/
@[instance_reducible]
def canonicalDerivedSymmetric (A : Type u) [CommRing A] :
    @SymmetricCategory (DerivedCategory (ModuleCat.{max u v} A)) _
      (canonicalDerivedMonoidalStructure.{u, v} A) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} A)).choose_spec.choose
  exact CategoryTheory.Monoidal.Transported.instSymmetricCategory
    (StacksDraft.DerivedHom.derivedScalarEquivalence.{u, v, max u v + 1} A)

/-- **The evaluation morphisms at `(K, M)` and at `(K, M')` are invertible together**, for an
invertible `L` and an isomorphism `M ⊗ L ≅ M'`. -/
theorem isIso_evaluationTensorMap_iff_of_isInvertible
    (K M M' L : DerivedCategory (ModuleCat.{max u v} A))
    (hL : letI := canonicalDerivedMonoidalStructure.{u, v} A
      MonoidalCategory.IsInvertible L)
    (u : letI := canonicalDerivedMonoidalStructure.{u, v} A; M ⊗ L ≅ M') :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    IsIso (evaluationTensorMap.{u, v} K M') ↔ IsIso (evaluationTensorMap.{u, v} K M) := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  let := canonicalDerivedSymmetric.{u, v} A
  exact MonoidalCategory.isIso_iff_of_tensorHomBijective_of_isInvertible
    (evaluationTensorMap.{u, v} K M) (evaluationTensorMap.{u, v} K M')
    (tensorHomBijective_evaluationTensorMap.{u, v} K M)
    (tensorHomBijective_evaluationTensorMap.{u, v} K M') hL u

/-- **The evaluation morphism of one dualizing complex against another is an isomorphism**: for
dualizing complexes `K` and `K'` over a Noetherian ring `A`, the morphism
`R𝐻om_A(K, K') ⊗ K ⟶ K'` of the monoidal category `D(A)` is an isomorphism. -/
theorem isIso_evaluationTensorMap_of_isDualizingComplex
    [IsNoetherianRing A] (K K' : DerivedCategory (ModuleCat.{max u v} A))
    (hK : IsDualizingComplex K) (hK' : IsDualizingComplex K') :
    letI := canonicalDerivedMonoidalStructure.{u, v} A
    IsIso (evaluationTensorMap.{u, v} K K') := by
  let := canonicalDerivedMonoidalStructure.{u, v} A
  set d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A
  have u : K ⊗ d.hom.obj (op K, K') ≅ K' :=
    monoidalTensorIso.{u, v} A K (d.hom.obj (op K, K')) ≪≫
      (dualizingIsoTensorDerivedHom.{u, v} A hK hK').symm
  exact (isIso_evaluationTensorMap_iff_of_isInvertible.{u, v} K K K'
      (d.hom.obj (op K, K')) (isInvertible_derivedHom.{u, v} A hK hK') u).2
    (isIso_evaluationTensorMap_self_of_isDualizingComplex.{u, v} K hK)

end Dualizing

end
