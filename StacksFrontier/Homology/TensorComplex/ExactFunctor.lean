module

public import StacksFrontier.Homology.TensorComplex.ExactFunctor.Descent
public import StacksFrontier.Homology.TensorComplex.ExactFunctor.LeftMappingCone
public import StacksFrontier.Homology.TensorComplex.ExactFunctor.RightMappingCone
public import StacksFrontier.Homology.TensorComplex.ExactFunctor.IsTriangulated

/-!
# Tensoring with a fixed complex is an exact functor of triangulated categories

This module is the tree's single provider of Stacks tag 06Y8 and of the `Tleft` / `Tright`
exact-functor API on the homotopy category of cochain complexes.

## Ownership

Tag 06Y8 belongs to Chapter 20 by subject matter — it is Lemma 20.26.1, on flat resolutions in
Cohomology of Sheaves — but it is owned and maintained here, as support, by the cluster
responsible for Chapter 15 sections 57-64. The transfer is deliberate and was made because this
tag is *only* consumed as infrastructure: `Tleft` and `Tright` are what Chapter 15's tags 064J,
06Y0, 06Y2 and 06Y4 are stated in terms of, and tag 064J is nothing but the pair of aliases
`main_left` / `main_right` declared below. Keeping the tag in a per-tag chapter path meant every
consumer imported a legacy path, which is the arrangement this file exists to end.

Two consequences that matter for anyone editing this file. The `@[stacks 06Y8]` registrations on
`main_left` and `main_right` are the covering set for the tag and there must be no other
registration of 06Y8 anywhere in the tree — the two statements are genuinely distinct, differing
by the commutativity isomorphism and its Koszul sign, so neither alone covers it. And the
declaration names below are a published API consumed across chapters, so they are not free to be
renamed for local convenience: `Tleft`, `TleftCochain`, `Tright`, `TrightCochain`,
`TrightCochain_mappingCone_iso`, `TrightCochain_preservesHomotopyRel`, `descendF_comp_quotient`,
`TleftCommShift`, `TrightCommShift`, `main_left`, `main_right`.

Stacks Project Lemma 20.26.1 (Tag 06Y8) is stated for a ringed space.  Let `(X, O_X)` be a
ringed space and `Mod(O_X)` the abelian category of sheaves of `O_X`-modules.  Fix a complex
`G^*` of `O_X`-modules.  Then the two "tensor with `G`, then take the total complex" functors

  `F^* ↦ Tot(G^* ⊗ F^*)`     (left)
  `F^* ↦ Tot(F^* ⊗ G^*)`     (right)

descend to additive endofunctors of the homotopy category `K(Mod(O_X))` and are *exact
functors of triangulated categories* (a.k.a. triangulated functors): each comes equipped
with a functorial comparison isomorphism `ξ` commuting with the shift `[1]`, such that
distinguished triangles are carried to distinguished triangles.

The Stacks proof reads: "This follows from Derived Categories, Remark 13.10.9."  That remark
establishes the *general* fact: for a fixed complex in an additive (here: preadditive
monoidal) category equipped with a tensor bifunctor, the total-complex-of-tensor functors
are exact functors of the triangulated homotopy category.  We therefore formalize this
general content.  Specializing `C := Mod(O_X)` (the abelian, hence preadditive, category of
sheaves of `O_X`-modules) with its tensor product `⊗_{O_X}` recovers the statement for a
ringed space.

We work in the homotopy category `K(C) = HomotopyCategory C (ComplexShape.up ℤ)` of cochain
complexes, which Mathlib equips with a shift by `ℤ` and a `Pretriangulated` structure
(distinguished triangles coming from mapping cones), exactly as in Stacks Tags 013T / 05RU,
0118, 014P.

## Background and context

- `C` plays the role of `Mod(O_X)`.  We only use that it is preadditive, monoidal (the
  tensor product `⊗_{O_X}`), has a zero object and binary biproducts, and that its tensor
  bifunctor is additive in each variable.  The category `Mod(O_X)` is abelian, hence
  satisfies all of these.

- The tensor-product double complex and its total complex `Tot(A^* ⊗ B^*)` (Stacks Tag
  0FNG / Homology 12.18.3) are realized in Mathlib by `Functor.map₂CochainComplex` applied
  to the curried tensor bifunctor `curriedTensor C`; the underlying total complex of the
  double complex is `HomologicalComplex.mapBifunctor`.  The Leibniz sign rule for the
  differential and the Stacks sign conventions for the shift and the comparison isomorphism
  are the ones built into these Mathlib constructions.

- "Exact functor of triangulated categories" (Stacks Tag 014V / Definition 13.3.3) is
  `CategoryTheory.Functor.IsTriangulated`: an additive functor `F`
  together with a `CommShift` datum (the natural isomorphism `ξ : F(-[1]) ≅ F(-)[1]`
  satisfying the coherence with `0` and `+`), such that the image of every distinguished
  triangle is distinguished.  The comparison isomorphism `ξ` is exactly the canonical
  isomorphism `Tot(M^* ⊗ N^*)[a] ≅ Tot(M^*[a] ⊗ N^*)` of Stacks Tag 0FNG, available in
  Mathlib as the `CommShift` of `map₂CochainComplex` (with the appropriate sign).

- The descent to the homotopy category ("homotopic morphisms are sent to homotopic
  morphisms") is **part of the asserted content** of the lemma, not a hypothesis: we prove
  `PreservesHomotopyRel (TleftCochain G)` / `PreservesHomotopyRel (TrightCochain G)` as
  lemmas (they follow from additivity of the tensor bifunctor), and use them to build the
  descended functors `Tleft G`, `Tright G` on `K(C)` unconditionally.

The parts are `Descent`, `LeftMappingCone`, `RightMappingCone` and `IsTriangulated`.
-/
