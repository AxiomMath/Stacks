module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRingsRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Local properties of continuous ring maps: the refined forms

A property of continuous ring maps between linearly topologized rings of a given class is local
if it is independent of the presentations of source and target, ascends along completed étale
localization diagrams, descends along faithfully flat ones, and is preserved by finite products
of targets. This file states that notion, and the notions of stability under completed
tensor-product base change and under composition built on it, for countably indexed weakly
admissible rings, weakly admissible adic-star rings, and Noetherian adic rings.

## Main definitions

* `TopologicalRing.IsomorphismInvariant`: a property of arrows is independent of the chosen
  presentations of source and target up to bicontinuous ring isomorphism.
* `TopologicalRing.PropertyIsLocal'`: a local property of morphisms of rings of a given class.
* `TopologicalRing.AdicStarPropertyIsLocal'`: a local property of morphisms of weakly admissible
  adic-star rings.
* `TopologicalRing.PropertyIsLocalNoetherian'`: a local property of morphisms of Noetherian adic
  rings.
* `TopologicalRing.IsStableUnderBaseChange'`,
  `TopologicalRing.AdicStarPropertyIsStableUnderBaseChange'`,
  `TopologicalRing.IsStableUnderBaseChangeNoetherian'`: a local property preserved by completed
  tensor-product base change.
* `TopologicalRing.IsStableUnderBaseChangeBy'`: a local property of morphisms of Noetherian adic
  rings preserved by completed tensor-product base change along morphisms with a second local
  property.
* `TopologicalRing.PropertyIsStableUnderComposition'`,
  `TopologicalRing.AdicStarPropertyIsStableUnderComposition'`,
  `TopologicalRing.PropertyIsStableUnderCompositionNoetherian'`: a local property preserved by
  composition.
* `TopologicalRing.PropertyIsLocalWithCancellation'`: a local property with the cancellation
  property for composable morphisms.

## Main results

* `TopologicalRing.propertyIsLocal_iff'`: `PropertyIsLocal' P C` is the conjunction of its four
  axioms.
* `TopologicalRing.PropertyIsLocal'.toPropertyIsLocal`: a local property in this sense is local
  in the sense of `TopologicalRing.PropertyIsLocal`.
* `TopologicalRing.IsStableUnderBaseChangeNoetherian'.isStableUnderBaseChangeBy`: stability
  under base change implies stability under base change by every local property.
* `TopologicalRing.propertyIsLocalNoetherian_true'`: the property holding of every morphism of
  Noetherian adic rings is local.
-/

@[expose] public section

namespace TopologicalRing

section

open TopologicalRing
open Filter

universe u

/-- A property of arrows of `WAdmᶜᵒᵘⁿᵗ` is independent of the chosen presentations of its
source and target: for bicontinuous ring isomorphisms `eB : B ≃+* B'` and `eA : A ≃+* A'` of
rings of the class `C`, a continuous `f : B →+* A` has `P` if and only if `eA ∘ f ∘ eB⁻¹` does. -/
public abbrev IsomorphismInvariant
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) : Prop :=
  ∀ {B A B' A' : Type u}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    (eB : B ≃+* B') (eA : A ≃+* A')
    (_heB : Continuous eB) (_heB' : Continuous eB.symm)
    (_heA : Continuous eA) (_heA' : Continuous eA.symm)
    (f : B →+* A) (_hf : Continuous f)
    (_hB : C B) (_hA : C A) (_hB' : C B') (_hA' : C A'),
    P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)

namespace IsomorphismInvariant

/-- Conjunction of presentation-independent properties is presentation-independent. -/
public theorem and
    {P Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop}
    (hP : IsomorphismInvariant P C) (hQ : IsomorphismInvariant Q C) :
    IsomorphismInvariant (fun f => P f ∧ Q f) C := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro eB eA heB heB' heA heA' f hf hB hA hB' hA'
  exact and_congr (hP eB eA heB heB' heA heA' f hf hB hA hB' hA')
    (hQ eB eA heB heB' heA heA' f hf hB hA hB' hA')

/-- A property stable under composition and holding for every bicontinuous ring isomorphism of
rings of the class is presentation-independent. -/
public theorem of_comp_of_ringEquiv
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop}
    (hcomp : ∀ {X Y Z : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y]
      [IsLinearTopology Y Y] [CommRing Z] [TopologicalSpace Z] [IsTopologicalRing Z]
      [IsLinearTopology Z Z], C X → C Y → C Z → ∀ (f : Y →+* X) (g : Z →+* Y),
      Continuous f → Continuous g → P f → P g → P (f.comp g))
    (hiso : ∀ {X Y : Type u} [CommRing X] [TopologicalSpace X] [IsTopologicalRing X]
      [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsTopologicalRing Y]
      [IsLinearTopology Y Y] (e : X ≃+* Y), C X → C Y → Continuous e → Continuous e.symm →
      P e.toRingHom) :
    IsomorphismInvariant P C := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro eB eA heB heBs heA heAs f hf hB hA hB' hA'
  refine ⟨fun h ↦ hcomp hA' hB hB' (eA.toRingHom.comp f) eB.symm.toRingHom (heA.comp hf) heBs
    (hcomp hA' hA hB eA.toRingHom f heA hf (hiso eA hA hA' heA heAs) h)
    (hiso eB.symm hB' hB heBs heB), fun h ↦ ?_⟩
  have hg : Continuous ((eA.toRingHom.comp f).comp eB.symm.toRingHom) :=
    (heA.comp hf).comp heBs
  have hQ := hcomp hA hB' hB
    (eA.symm.toRingHom.comp ((eA.toRingHom.comp f).comp eB.symm.toRingHom)) eB.toRingHom
    (heAs.comp hg) heB
    (hcomp hA hA' hB' eA.symm.toRingHom ((eA.toRingHom.comp f).comp eB.symm.toRingHom)
      heAs hg (hiso eA.symm hA' hA heAs heA) h)
    (hiso eB hB hB' heB heBs)
  rwa [show (eA.symm.toRingHom.comp
    ((eA.toRingHom.comp f).comp eB.symm.toRingHom)).comp eB.toRingHom = f by ext; simp] at hQ

end IsomorphismInvariant

/-- A property of morphisms of countably indexed weakly admissible rings is local if it is
independent of the presentations of the arrows and ascends along completed étale localization
diagrams, descends along faithfully flat ones, and is preserved by finite products of targets.
The optional subclass parameter restricts all four corners of each diagram and every ring in
the finite-product family. -/
public structure PropertyIsLocal'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop := IsCountablyWeaklyAdmissible) : Prop where
  /-- `P` is independent of the presentations of source and target. -/
  isomorphismInvariant : IsomorphismInvariant P C
  /-- `P` ascends along completed étale localization diagrams. -/
  localizationPreserves : LocalizationPreserves C P
  /-- `P` descends along faithfully flat diagrams. -/
  faithfullyFlatDescent : FaithfullyFlatDescent C P
  /-- `P` is preserved by finite products of targets. -/
  finiteProduct : FiniteProductPreserves C P

/-- Presentation independence and the three axioms characterize a local morphism property. -/
@[simp] public theorem propertyIsLocal_iff'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop)
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop := IsCountablyWeaklyAdmissible) :
    PropertyIsLocal' P C ↔
      IsomorphismInvariant P C ∧ LocalizationPreserves C P ∧
        FaithfullyFlatDescent C P ∧ FiniteProductPreserves C P :=
  ⟨fun ⟨a, b, c, d⟩ ↦ ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ ↦ ⟨a, b, c, d⟩⟩

/-- A local property in the sense of `TopologicalRing.PropertyIsLocal'` is local in the sense of
`TopologicalRing.PropertyIsLocal`. -/
public theorem PropertyIsLocal'.toPropertyIsLocal
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop}
    {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop} (h : PropertyIsLocal' P C) : PropertyIsLocal P C :=
  ⟨h.localizationPreserves, h.faithfullyFlatDescent, h.finiteProduct⟩

end

section

universe u

/-- A property of morphisms of weakly admissible adic-star rings is local when it is local in the
sense of `TopologicalRing.PropertyIsLocal'` for the class of rings admitting a finitely generated
ideal of definition. -/
public abbrev AdicStarPropertyIsLocal' (P : ∀ {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  TopologicalRing.PropertyIsLocal' P (fun R => ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I)

end

section

universe u

/-- A morphism property of Noetherian adic topological rings is local if it is independent of
presentations, ascends along completed étale localization diagrams, descends along faithfully
flat ones, and is preserved by finite products of targets. -/
public abbrev PropertyIsLocalNoetherian'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A],
      (B →+* A) → Prop) : Prop :=
  TopologicalRing.PropertyIsLocal' P
    (fun R => TopologicalRing.IsAdic R ∧ IsNoetherianRing R)

end

section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A local property of morphisms of countably indexed weakly admissible rings
that is preserved by completed tensor-product base change. -/
public structure IsStableUnderBaseChange'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.PropertyIsLocal' P
  /-- If `B →+* A` has `P`, then so does `C →+* A ⊗̂_B C`. -/
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
public structure AdicStarPropertyIsStableUnderBaseChange'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.AdicStarPropertyIsLocal' P
  /-- If `B →+* A` has `P`, then so does `C →+* A ⊗̂_B C`. -/
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

/-- A local property `P` of morphisms of Noetherian adic topological rings is *stable under
base change* when, for every pair of continuous homomorphisms `B →+* A` and `B →+* C` of such
rings, `P (B →+* A)` forces the completed tensor product `A ⊗̂_B C` to be adic Noetherian again
and `P` to hold for `C →+* A ⊗̂_B C`. -/
public structure IsStableUnderBaseChangeNoetherian'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.PropertyIsLocalNoetherian' P
  /-- If `B →+* A` has `P`, then `A ⊗̂_B C` is adic Noetherian and `C →+* A ⊗̂_B C` has `P`. -/
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
public structure IsStableUnderBaseChangeBy'
    (P Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocalP : TopologicalRing.PropertyIsLocalNoetherian' P
  /-- `Q` is local. -/
  isLocalQ : TopologicalRing.PropertyIsLocalNoetherian' Q
  /-- If `B →+* A` has `P` and `B →+* C` has `Q`, then `A ⊗̂_B C` is adic Noetherian and
  `C →+* A ⊗̂_B C` has `P`. -/
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

/-- A local property of morphisms of Noetherian adic rings that is stable under base change is
stable under base change by every local property `Q`. -/
public theorem IsStableUnderBaseChangeNoetherian'.isStableUnderBaseChangeBy
    {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
    (hP : TopologicalRing.IsStableUnderBaseChangeNoetherian' P)
    (Q : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop)
    (hQ : TopologicalRing.PropertyIsLocalNoetherian' Q) :
    TopologicalRing.IsStableUnderBaseChangeBy' P Q :=
  ⟨hP.isLocal, hQ, fun hB hA hC hcB hcC hp _ => hP.baseChange hB hA hC hcB hcC hp⟩

end

section

universe u

/-- The property of morphisms of Noetherian adic topological rings that holds of every
morphism is local. -/
public theorem propertyIsLocalNoetherian_true' :
    TopologicalRing.PropertyIsLocalNoetherian'.{u} (P := fun _ ↦ True) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ ↦ Iff.rfl, fun _ _ _ _ _ _ ↦ trivial,
    fun _ _ _ _ _ _ _ ↦ trivial,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ trivial⟩

end

section

universe u

/-- A local property of morphisms of countably indexed weakly admissible rings is
stable under composition when two composable morphisms with the property have a
composite with the property. -/
public structure PropertyIsStableUnderComposition'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.PropertyIsLocal' P
  /-- The composite of two continuous morphisms with `P` has `P`. -/
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
public structure AdicStarPropertyIsStableUnderComposition'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
      [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.AdicStarPropertyIsLocal' P
  /-- The composite of two continuous morphisms with `P` has `P`. -/
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

/-- A local property of morphisms of Noetherian adic rings is stable under composition
when it holds for the composite of two continuous morphisms having the property. -/
public structure PropertyIsStableUnderCompositionNoetherian'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.PropertyIsLocalNoetherian' P
  /-- The composite of two continuous morphisms with `P` has `P`. -/
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
public structure PropertyIsLocalWithCancellation'
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop where
  /-- `P` is local. -/
  isLocal : TopologicalRing.PropertyIsLocal' P
  /-- For continuous `f : B →+* A` and `g : C →+* B`, if `g` and `f ∘ g` have `P`, so does `f`. -/
  cancellation : ∀ {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] (f : B →+* A) (g : C →+* B), TopologicalRing.IsCountablyWeaklyAdmissible
    A → TopologicalRing.IsCountablyWeaklyAdmissible B → TopologicalRing.IsCountablyWeaklyAdmissible
    C → Continuous f → Continuous g → ((P g ∧ P (f.comp g)) → P f)

end

end TopologicalRing

end
