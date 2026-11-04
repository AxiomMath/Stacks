module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Local properties of continuous ring maps

A property of continuous homomorphisms of countably indexed weakly admissible topological rings
is *local* when it can be checked after localization, descends along faithfully flat maps, and
is stable under finite products.  This file packages that bundle of axioms, together with the
parallel bundles for stability under base change, stability under composition, the Noetherian
variants, and the cancellation property.

## References

* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0GBC](https://stacks.math.columbia.edu/tag/0GBC)
* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBF](https://stacks.math.columbia.edu/tag/0GBF)
* [Stacks Project, Tag 0GBG](https://stacks.math.columbia.edu/tag/0GBG)
* [Stacks Project, Tag 0GBH](https://stacks.math.columbia.edu/tag/0GBH)
* [Stacks Project, Tag 0GBJ](https://stacks.math.columbia.edu/tag/0GBJ)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GBL](https://stacks.math.columbia.edu/tag/0GBL)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
-/

@[expose] public section

namespace TopologicalRing

section

open TopologicalRing
open Filter

universe u

/-- A commutative localization diagram of countably indexed weakly admissible rings, with
étale horizontal maps and continuous vertical maps. -/
@[stacks 0CBA "localization diagram"]
public structure LocalizationDiagram
    (A B A' B' : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B'] where
  /-- The étale map from `A` to `A'`. -/
  toA' : A →+* A'
  /-- The étale map from `B` to `B'`. -/
  toB' : B →+* B'
  /-- The continuous map from `B` to `A`. -/
  map : B →+* A
  /-- The continuous map between the completions of `B'` over `B` and of `A'` over `A`. -/
  completedMap : CompletionOver toB' →+* CompletionOver toA'
  /-- `A` is weakly admissible. -/
  weaklyAdmissibleA : TopologicalRing.IsWeaklyAdmissible A
  /-- `B` is weakly admissible. -/
  weaklyAdmissibleB : TopologicalRing.IsWeaklyAdmissible B
  /-- `A` is countably indexed. -/
  countableA : (nhds (0 : A)).IsCountablyGenerated
  /-- `B` is countably indexed. -/
  countableB : (nhds (0 : B)).IsCountablyGenerated
  /-- `A → A'` is étale. -/
  etaleA : toA'.Etale
  /-- `B → B'` is étale. -/
  etaleB : toB'.Etale
  /-- `B → A` is continuous. -/
  continuousMap : Continuous map
  /-- The map between the completions is continuous. -/
  continuousCompletedMap : Continuous completedMap
  /-- The square formed by the four maps commutes. -/
  commutes :
    (CompletionOver.canonicalMap toA').comp map =
      completedMap.comp (CompletionOver.canonicalMap toB')

/-- Membership in the category of countably indexed weakly admissible topological rings. -/
public abbrev IsCountablyWeaklyAdmissible
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : Prop :=
  TopologicalRing.IsWeaklyAdmissible R ∧ (nhds (0 : R)).IsCountablyGenerated

/-- The ascent axiom for a property of morphisms in a subclass of countably indexed
weakly admissible rings. Both original and completed rings must lie in the subclass. -/
public abbrev LocalizationPreserves
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B'),
      C A → C B → C (CompletionOver D.toA') → C (CompletionOver D.toB') →
        P D.map → P D.completedMap

/-- The faithfully flat descent axiom for a subclass of weakly admissible rings. -/
public abbrev FaithfullyFlatDescent
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
    ∀ {A B A' B' : Type u}
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B'),
      C A → C B → C (CompletionOver D.toA') → C (CompletionOver D.toB') →
        D.toA'.FaithfullyFlat → P D.completedMap → P D.map

/-- The finite-product axiom for a subclass of weakly admissible rings. -/
public abbrev FiniteProductPreserves
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
    ∀ {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [IsLinearTopology B B] (_hB : TopologicalRing.IsWeaklyAdmissible B)
      (_hBcount : (nhds (0 : B)).IsCountablyGenerated)
      {ι : Type u} [Fintype ι] (A : ι → Type u)
      [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsTopologicalRing (A i)] [∀ i, IsLinearTopology (A i) (A i)]
      (_hA : ∀ i, TopologicalRing.IsWeaklyAdmissible (A i))
      (_hAcount : ∀ i, (nhds (0 : A i)).IsCountablyGenerated)
      (f : ∀ i, B →+* A i) (_hf : ∀ i, Continuous (f i)),
      C B → (∀ i, C (A i)) →
        (∀ i, P (f i)) → P (RingHom.pi f)

/-- A property of morphisms of countably indexed weakly admissible rings is local if it
ascends along completed étale localization diagrams, descends along faithfully flat ones,
and is preserved by finite products of targets. The optional subclass parameter restricts
all four corners of each diagram and every ring in the finite-product family. -/
@[stacks 0CBA "local property"]
public structure PropertyIsLocal
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop := IsCountablyWeaklyAdmissible) : Prop where
  localizationPreserves : LocalizationPreserves C P
  faithfullyFlatDescent : FaithfullyFlatDescent C P
  finiteProduct : FiniteProductPreserves C P

/-- The three axioms characterize a local morphism property. -/
@[simp] public theorem propertyIsLocal_iff
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop := IsCountablyWeaklyAdmissible) :
    PropertyIsLocal P C ↔
      LocalizationPreserves C P ∧ FaithfullyFlatDescent C P ∧
        FiniteProductPreserves C P := ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩⟩

end

section

universe u

/-- A property of morphisms of weakly admissible adic-star rings is local when it satisfies
the three locality axioms of `TopologicalRing.PropertyIsLocal` within that subcategory: the
rings tested are those whose topology is the `I`-adic topology of a finitely generated ideal
`I`. -/
@[stacks 0ANH "adic_star_local_property"]
public abbrev AdicStarPropertyIsLocal (P : ∀ {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  TopologicalRing.PropertyIsLocal P (fun R => ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I)

end

section

universe u

/-- A property of morphisms of `WAdm^{adic*}` is *local* when the three locality axioms of
`TopologicalRing.PropertyIsLocal` hold for morphisms of that subcategory.

`WAdm^{adic*}` is the full subcategory of `WAdm` whose objects are the adic topological rings
possessing a finitely generated ideal of definition. Its objects are complete and separated:
`TopologicalRing.IsAdic` is pre-adicness together with `TopologicalRing.IsComplete`, which is
completeness for the canonical uniformity together with the Hausdorff condition.

This agrees with `TopologicalRing.AdicStarPropertyIsLocal`, by
`TopologicalRing.adicStarPropertyIsLocal_iff_propertyIsLocalAdicStar`. -/
@[stacks 0ANH "the first half, the definition, at the source's class of rings: the adic \
topological rings -- hence complete and separated -- possessing a finitely generated ideal of \
definition"]
public abbrev PropertyIsLocalAdicStar (P : ∀ {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  TopologicalRing.PropertyIsLocal P
    (fun R => TopologicalRing.IsAdic R ∧
      ∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)

end

section

universe u

/-- A morphism property of Noetherian adic topological rings is local if it ascends along
completed étale localization diagrams, descends along faithfully flat ones, and is preserved
by finite products of targets. -/
@[stacks 0ANI "local_property_noetherian"]
public abbrev PropertyIsLocalNoetherian
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
  TopologicalRing.PropertyIsLocal P
    (fun R => TopologicalRing.IsAdic R ∧ IsNoetherianRing R)

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property of morphisms of countably indexed weakly admissible rings
that is preserved by completed tensor-product base change. -/
@[stacks 0GBC]
public structure IsStableUnderBaseChange
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocal P
  baseChange : ∀ {B A C : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [Algebra B A] [Algebra B C],
      TopologicalRing.IsCountablyWeaklyAdmissible B →
      TopologicalRing.IsCountablyWeaklyAdmissible A →
      TopologicalRing.IsCountablyWeaklyAdmissible C →
      Continuous (algebraMap B A) → Continuous (algebraMap B C) →
      P (algebraMap B A) →
        P (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property of morphisms of weakly admissible adic-star rings that is
preserved by completed tensor-product base change. -/
@[stacks 0GBE "adic_star_base_change_stability"]
public structure AdicStarPropertyIsStableUnderBaseChange
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.AdicStarPropertyIsLocal P
  baseChange : ∀ {B A C : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [Algebra B A] [Algebra B C],
      TopologicalRing.IsWeaklyAdmissible B →
      (∃ I : Ideal B, I.FG ∧ _root_.IsAdic I) →
      TopologicalRing.IsWeaklyAdmissible A →
      (∃ I : Ideal A, I.FG ∧ _root_.IsAdic I) →
      TopologicalRing.IsWeaklyAdmissible C →
      (∃ I : Ideal C, I.FG ∧ _root_.IsAdic I) →
      Continuous (algebraMap B A) → Continuous (algebraMap B C) →
      P (algebraMap B A) →
        P (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))

end

section

add_to_stacks 0GBE "completed_tensor_adic_star"
    TopologicalRing.completedTensorProduct_isWeaklyAdmissible
add_to_stacks 0GBE "completed_tensor_adic_star" TopologicalRing.completedTensorProduct_isAdic
add_to_stacks 0GBE "completed_tensor_adic_star" TopologicalRing.exists_fg_ideal_of_definition

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property `P` of morphisms of `WAdm^{adic*}` is *stable under base change* when,
for every pair of morphisms `B → A` and `B → C` of `WAdm^{adic*}`, `P (B → A)` implies
`P (C → A ⊗̂_B C)`.

`WAdm^{adic*}` is the full subcategory of `WAdm` whose objects are the adic, hence complete and
separated, topological rings possessing a finitely generated ideal of definition, and the
locality of `P` is `TopologicalRing.PropertyIsLocalAdicStar`, read in the same subcategory. That
`A ⊗̂_B C` lies in `WAdm^{adic*}` is `TopologicalRing.isAdicStar_completedTensorProduct`.

This agrees with `TopologicalRing.AdicStarPropertyIsStableUnderBaseChange`, by
`TopologicalRing.adicStarPropertyIsStableUnderBaseChange_iff`. -/
@[stacks 0GBE "the first half, the definition of stability under base change, at the source's \
class of rings: the morphisms range over WAdm^{adic*}, the adic topological rings -- hence \
complete and separated -- possessing a finitely generated ideal of definition, and the \
locality of P is read in the same subcategory by TopologicalRing.PropertyIsLocalAdicStar. The \
well definedness the remark cites, that the completed tensor product is again an object of \
WAdm^{adic*} by Lemma 87.4.12, is TopologicalRing.isAdicStar_completedTensorProduct"]
public structure PropertyIsStableUnderBaseChangeAdicStar
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocalAdicStar P
  baseChange : ∀ {B A C : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      [Algebra B A] [Algebra B C],
      TopologicalRing.IsWeaklyAdmissible B →
      (TopologicalRing.IsAdic B ∧
        ∃ I : Ideal B, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) →
      TopologicalRing.IsWeaklyAdmissible A →
      (TopologicalRing.IsAdic A ∧
        ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) →
      TopologicalRing.IsWeaklyAdmissible C →
      (TopologicalRing.IsAdic C ∧
        ∃ I : Ideal C, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) →
      Continuous (algebraMap B A) → Continuous (algebraMap B C) →
      P (algebraMap B A) →
        P (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property `P` of morphisms of Noetherian adic topological rings is *stable under
base change* when, for every pair of continuous homomorphisms `B →+* A` and `B →+* C` of such
rings, `P (B →+* A)` forces the completed tensor product `A ⊗̂_B C` to be adic Noetherian again
and `P` to hold for `C →+* A ⊗̂_B C`. No condition is imposed on `B →+* C`. -/
@[stacks 0GBF "the definition of stability under base change; not the 0GBD variant for spaces"]
public structure IsStableUnderBaseChangeNoetherian
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocalNoetherian P
  baseChange : ∀ {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
      [IsLinearTopology C C] [Algebra B A] [Algebra B C] [IsNoetherianRing B]
      [IsNoetherianRing A] [IsNoetherianRing C], TopologicalRing.IsAdic B →
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      Continuous (algebraMap B A) → Continuous (algebraMap B C) →
      P (algebraMap B A) →
      (TopologicalRing.IsAdic (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      IsNoetherianRing (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      P (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))))

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local morphism property of Noetherian adic rings is stable under completed
tensor-product base change along morphisms satisfying another local property. -/
@[stacks 0GBG "stable_under_base_change_by_noetherian"]
public structure IsStableUnderBaseChangeBy (P Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
    (B →+* A) → Prop) : Prop where
  isLocalP : TopologicalRing.PropertyIsLocalNoetherian P
  isLocalQ : TopologicalRing.PropertyIsLocalNoetherian Q
  baseChange : ∀ {B A C : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [IsLinearTopology B B] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
      [IsLinearTopology C C] [Algebra B A] [Algebra B C] [IsNoetherianRing B]
      [IsNoetherianRing A] [IsNoetherianRing C], TopologicalRing.IsAdic B →
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      Continuous (algebraMap B A) → Continuous (algebraMap B C) →
      P (algebraMap B A) → Q (algebraMap B C) →
      (TopologicalRing.IsAdic (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      IsNoetherianRing (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) ∧
      P (algebraMap C (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))))

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Stability under base change is stability under base change by every local property: the
hypothesis on the morphism being based along is not used. -/
public theorem IsStableUnderBaseChangeNoetherian.isStableUnderBaseChangeBy
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    (hP : TopologicalRing.IsStableUnderBaseChangeNoetherian P)
    (Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop)
    (hQ : TopologicalRing.PropertyIsLocalNoetherian Q) :
    TopologicalRing.IsStableUnderBaseChangeBy P Q :=
  ⟨hP.isLocal, hQ, fun hB hA hC hcB hcC hp _ => hP.baseChange hB hA hC hcB hcC hp⟩

end

section

universe u

/-- The property of morphisms of Noetherian adic topological rings that holds of every
morphism is local: the conclusion of each of the three locality axioms is `True`. -/
public theorem propertyIsLocalNoetherian_true :
    TopologicalRing.PropertyIsLocalNoetherian.{u} (P := fun _ ↦ True) :=
  ⟨fun _ _ _ _ _ _ ↦ trivial, fun _ _ _ _ _ _ _ ↦ trivial,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ trivial⟩

end

section

universe u

/-- A local property of morphisms of countably indexed weakly admissible rings is
stable under composition when two composable morphisms with the property have a
composite with the property. -/
@[stacks 0GBH]
public structure PropertyIsStableUnderComposition
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocal P
  comp : ∀ {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] (_hA : TopologicalRing.IsCountablyWeaklyAdmissible A)
    (_hB : TopologicalRing.IsCountablyWeaklyAdmissible B)
    (_hC : TopologicalRing.IsCountablyWeaklyAdmissible C) (f : B →+* A) (g : C →+* B), Continuous f
    → Continuous g → P f → P g → P (f.comp g)

end

section

universe u

/-- A local property of morphisms of weakly admissible adic-star rings is stable
under composition if it is preserved by composition of continuous maps between
such rings. -/
@[stacks 0GBJ "stable_under_composition_for_adic_ring_map_properties"]
public structure AdicStarPropertyIsStableUnderComposition
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
      [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.AdicStarPropertyIsLocal P
  comp : ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (_hA : TopologicalRing.IsCountablyWeaklyAdmissible A)
      (_hB : TopologicalRing.IsCountablyWeaklyAdmissible B)
      (_hC : TopologicalRing.IsCountablyWeaklyAdmissible C)
    (_hAadic : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I)
      (_hBadic : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I)
      (_hCadic : ∃ I : Ideal C, I.FG ∧ _root_.IsAdic I)
    (f : B →+* A) (g : C →+* B), Continuous f → Continuous g → P f → P g → P (f.comp g)

end

section

universe u

/-- A local property `P` of morphisms of `WAdm^{adic*}` is *stable under composition* when,
for morphisms `B → A` and `C → B` of `WAdm^{adic*}`, `P (B → A)` and `P (C → B)` imply
`P (C → A)`.

`WAdm^{adic*}` is the full subcategory of `WAdm` whose objects are the adic, hence complete and
separated, topological rings possessing a finitely generated ideal of definition, and the
locality of `P` is `TopologicalRing.PropertyIsLocalAdicStar`, read in the same subcategory.

This agrees with `TopologicalRing.AdicStarPropertyIsStableUnderComposition`, by
`TopologicalRing.adicStarPropertyIsStableUnderComposition_iff`. -/
@[stacks 0GBJ "the definition of stability under composition, at the source's class of rings: \
the morphisms range over WAdm^{adic*}, the adic topological rings -- hence complete and \
separated -- possessing a finitely generated ideal of definition, and the locality of P is \
read in the same subcategory by TopologicalRing.PropertyIsLocalAdicStar"]
public structure PropertyIsStableUnderCompositionAdicStar
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
      [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocalAdicStar P
  comp : ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (_hA : TopologicalRing.IsCountablyWeaklyAdmissible A)
      (_hB : TopologicalRing.IsCountablyWeaklyAdmissible B)
      (_hC : TopologicalRing.IsCountablyWeaklyAdmissible C)
    (_hAadic : TopologicalRing.IsAdic A ∧
        ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
      (_hBadic : TopologicalRing.IsAdic B ∧
        ∃ I : Ideal B, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
      (_hCadic : TopologicalRing.IsAdic C ∧
        ∃ I : Ideal C, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (f : B →+* A) (g : C →+* B), Continuous f → Continuous g → P f → P g → P (f.comp g)

end

section

universe u

/-- A local property of morphisms of Noetherian adic rings is stable under composition
when it holds for the composite of two continuous morphisms having the property. -/
@[stacks 0GBK "stable_under_composition_noetherian"]
public structure PropertyIsStableUnderCompositionNoetherian
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocalNoetherian P
  comp : ∀ {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] (_hA : TopologicalRing.IsAdic A ∧ IsNoetherianRing A)
    (_hB : TopologicalRing.IsAdic B ∧ IsNoetherianRing B)
    (_hC : TopologicalRing.IsAdic C ∧ IsNoetherianRing C) (f : B →+* A) (g : C →+* B), Continuous f
    → Continuous g → P f → P g → P (f.comp g)

end

section

universe u

/-- A local property of morphisms of countably indexed weakly admissible rings with
the cancellation property for composable morphisms. -/
@[stacks 0GBL]
public structure PropertyIsLocalWithCancellation
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  isLocal : TopologicalRing.PropertyIsLocal P
  cancellation : ∀ {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] (f : B →+* A) (g : C →+* B), TopologicalRing.IsCountablyWeaklyAdmissible
    A → TopologicalRing.IsCountablyWeaklyAdmissible B → TopologicalRing.IsCountablyWeaklyAdmissible
    C → Continuous f → Continuous g → ((P g ∧ P (f.comp g)) → P f)

end

section

universe u

/-- Cancellation for a morphism property on Noetherian adic topological rings. -/
@[stacks 0GBP "noetherian_cancellation_property"]
public abbrev HasNoetherianCancellationProperty
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop := ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] (f : B →+* A) (g : C →+* B),
    (TopologicalRing.IsAdic A ∧ IsNoetherianRing A) →
    (TopologicalRing.IsAdic B ∧ IsNoetherianRing B) →
    (TopologicalRing.IsAdic C ∧ IsNoetherianRing C) → Continuous f → Continuous g →
    ((P g ∧ P (f.comp g)) → P f)

end

end TopologicalRing

end
