module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomotopy

/-!
# Homology of the product of a simplicial set with a simplicial object

Let `A` be a category with coproducts, let `P` be a simplicial object of `A` and let `S` be a
simplicial set. The product `S × P` of [Stacks, Tag 017C] is the copower
`Functor.copower P S : n ↦ ∐_{s ∈ S_n} P_n` of
`StacksFrontier/AlgebraicTopology/SimplicialObject/Copower.lean`. Multiplying by `P` is homotopy
invariant in `S`: a homotopy equivalence of simplicial sets induces a homotopy equivalence of
the products, which is
`CategoryTheory.SimplicialObject.homotopyEquivalences_copowerMap_id` of
`StacksFrontier/AlgebraicTopology/SimplicialObject/CopowerHomotopy.lean`. This file draws the
consequences for any functor on simplicial objects which inverts homotopy equivalences, and in
particular for the homology of the Moore complex.

The consequence this file is written for is the following. Let `F` be a functor on simplicial
objects of `A` which inverts homotopy equivalences, let `a : P ⟶ P'` be a morphism of simplicial
objects with `F(a)` invertible, and let `S` be a simplicial set homotopy equivalent to a
singleton. Then `F` also inverts `S × a : S × P ⟶ S × P'`. The projections `S × P ⟶ P` and
`S × P' ⟶ P'` of [Stacks, Tag 017E] (2) are what make this work: they are compatible with `a`,
and `F` inverts them because `S` is contractible — the projection out of `S × P` factors as the
morphism of products induced by a homotopy equivalence `S ⟶ ∗` followed by the projection out of
`∗ × P`, which is already an isomorphism (`CategoryTheory.Functor.copowerConstPUnitIso`). At
`F = s(-)` followed by degree `n` homology this is the statement that the Moore complex of
`S × a` is a homology isomorphism, which is the form used in the homology of a category.

## Main results

* `CategoryTheory.Functor.comp_copower`, `CategoryTheory.Functor.whiskerLeft_copowerMap` and
  `CategoryTheory.Functor.whiskerLeft_copowerProj`: precomposition with a functor commutes with
  the copower, with its morphisms and with its projection, on the nose.
* `CategoryTheory.SimplicialObject.isIso_map_copowerProj`: a functor inverting homotopy
  equivalences inverts the projection `S × P ⟶ P` whenever `S` is homotopy equivalent to a
  singleton.
* `CategoryTheory.SimplicialObject.isIso_map_copowerMap`: such a functor inverts `S × a` as soon
  as it inverts `a`.
* `CategoryTheory.SimplicialObject.isInvertedBy_homologyFunctor_alternatingFaceMapComplex`:
  degree `n` homology of the Moore complex inverts homotopy equivalences of simplicial objects.
* `CategoryTheory.SimplicialObject.isIso_homologyMap_copowerProj` and
  `CategoryTheory.SimplicialObject.isIso_homologyMap_copowerMap`: the two statements above for
  the functor "degree `n` homology of the Moore complex".

## Implementation notes

The three compatibilities with precomposition hold by `rfl`: the copower is defined objectwise by
a coproduct and its structure maps are `Limits.Sigma.map'`, so precomposing the index category
changes neither. They are what lets a statement about the simplicial object `U_• ↦ ℱ(U_•)` be
read off from a statement about the presheaf `ℱ`.

That the homology of the Moore complex inverts homotopy equivalences is
`AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map` ([Stacks, Tag 019T]),
which turns a simplicial homotopy equivalence into a homotopy equivalence of chain complexes,
followed by `homotopyEquivalences_le_quasiIso`.

## References

* [Stacks, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
* [Stacks, Tag 017E](https://stacks.math.columbia.edu/tag/017E)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Stacks, Tag 019T](https://stacks.math.columbia.edu/tag/019T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w v u

namespace CategoryTheory.Functor

section Whisker

variable {K : Type*} [Category* K] {J : Type*} [Category* J] {A : Type u} [Category.{v} A]
  [HasCoproducts.{w} A]

/-- **Precomposition commutes with the copower.** For `G : K ⥤ J`, a diagram `V : J ⥤ A` and a
diagram of types `S : J ⥤ Type w`, the copower of the restrictions along `G` is the restriction
along `G` of the copower: both send `k` to `∐_{s ∈ S(G k)} V(G k)`, with the same structure
maps. -/
lemma comp_copower (G : K ⥤ J) (V : J ⥤ A) (S : J ⥤ Type w) :
    G ⋙ V.copower S = (G ⋙ V).copower (G ⋙ S) :=
  rfl

/-- **Precomposition commutes with the morphisms of copowers.** -/
lemma whiskerLeft_copowerMap (G : K ⥤ J) {V V' : J ⥤ A} {S S' : J ⥤ Type w} (b : V ⟶ V')
    (a : S ⟶ S') :
    Functor.whiskerLeft G (copowerMap b a) =
      copowerMap (Functor.whiskerLeft G b) (Functor.whiskerLeft G a) :=
  rfl

/-- **Precomposition commutes with the projection out of a copower.** -/
lemma whiskerLeft_copowerProj (G : K ⥤ J) (V : J ⥤ A) (S : J ⥤ Type w) :
    Functor.whiskerLeft G (V.copowerProj S) = (G ⋙ V).copowerProj (G ⋙ S) :=
  rfl

end Whisker

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A]

/-- **A functor inverting homotopy equivalences inverts the projection `S × P ⟶ P`** whenever the
simplicial set `S` is homotopy equivalent to a singleton: the projection factors as the morphism
of products induced by a homotopy equivalence `S ⟶ ∗`, which `F` inverts, followed by the
projection out of the product with `∗`, which is already an isomorphism. -/
theorem isIso_map_copowerProj {D : Type*} [Category* D] (F : SimplicialObject A ⥤ D)
    (hF : (homotopyEquivalences A).IsInvertedBy F) (P : SimplicialObject A)
    (S : SimplicialObject (Type w))
    (hS : ∃ f : S ⟶ (Functor.const _).obj PUnit.{w + 1}, homotopyEquivalences (Type w) f) :
    IsIso (F.map (P.copowerProj S)) := by
  obtain ⟨f, hf⟩ := hS
  have := hF _ (homotopyEquivalences_copowerMap_id P hf)
  have : IsIso (P.copowerProj ((Functor.const _).obj PUnit.{w + 1})) := inferInstance
  have he : Functor.copowerMap (𝟙 P) f ≫ P.copowerProj ((Functor.const _).obj PUnit.{w + 1}) =
      P.copowerProj S := by
    simpa only [Category.comp_id] using Functor.copowerMap_comp_copowerProj (𝟙 P) f
  rw [← he, F.map_comp]
  infer_instance

/-- **A functor inverting homotopy equivalences inverts `S × a` as soon as it inverts `a`**, for
every simplicial set `S` homotopy equivalent to a singleton. The two projections are compatible
with `a`, and the functor inverts both of them. -/
theorem isIso_map_copowerMap {D : Type*} [Category* D] (F : SimplicialObject A ⥤ D)
    (hF : (homotopyEquivalences A).IsInvertedBy F) {P P' : SimplicialObject A} (a : P ⟶ P')
    (ha : IsIso (F.map a)) (S : SimplicialObject (Type w))
    (hS : ∃ f : S ⟶ (Functor.const _).obj PUnit.{w + 1}, homotopyEquivalences (Type w) f) :
    IsIso (F.map (Functor.copowerMap a (𝟙 S))) := by
  have := ha
  have := isIso_map_copowerProj F hF P S hS
  have := isIso_map_copowerProj F hF P' S hS
  rw [← isIso_comp_right_iff _ (F.map (P'.copowerProj S)), ← F.map_comp,
    Functor.copowerMap_comp_copowerProj, F.map_comp]
  infer_instance

omit [HasCoproducts.{w} A] in
/-- **Degree `n` homology of the Moore complex inverts homotopy equivalences of simplicial
objects**: the Moore complex of a homotopy equivalence is a homotopy equivalence of chain
complexes ([Stacks, Tag 019T]), hence a quasi-isomorphism. -/
theorem isInvertedBy_homologyFunctor_alternatingFaceMapComplex [Abelian A] (n : ℕ) :
    (homotopyEquivalences A).IsInvertedBy (alternatingFaceMapComplex A ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n) := by
  intro V W b hb
  have hq : QuasiIso ((alternatingFaceMapComplex A).map b) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (homotopyEquivalences_alternatingFaceMapComplex_map hb)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq.quasiIsoAt n)

/-- **The Moore complex of the projection `S × P ⟶ P` is a homology isomorphism** for every
simplicial set `S` homotopy equivalent to a singleton. This is the step of [Stacks, Tag 08RX]
which identifies the homology of the simplicial abelian group `n ↦ ⊕_{s ∈ S_n} P_n` with that of
`P`. -/
theorem isIso_homologyMap_copowerProj [Abelian A] (P : SimplicialObject A) (n : ℕ)
    (S : SimplicialObject (Type w))
    (hS : ∃ f : S ⟶ (Functor.const _).obj PUnit.{w + 1}, homotopyEquivalences (Type w) f) :
    IsIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex A).map (P.copowerProj S)) n) :=
  isIso_map_copowerProj _ (isInvertedBy_homologyFunctor_alternatingFaceMapComplex n) P S hS

/-- **The Moore complex of `S × a` is a homology isomorphism in degree `n` as soon as that of `a`
is**, for every simplicial set `S` homotopy equivalent to a singleton. This is the step of
[Stacks, Tag 08RX] which compares the two simplicial abelian groups `n ↦ ⊕_{s ∈ S_n} P_n` and
`n ↦ ⊕_{s ∈ S_n} P'_n`. -/
theorem isIso_homologyMap_copowerMap [Abelian A] {P P' : SimplicialObject A} (a : P ⟶ P')
    (n : ℕ) (ha : IsIso (HomologicalComplex.homologyMap ((alternatingFaceMapComplex A).map a) n))
    (S : SimplicialObject (Type w))
    (hS : ∃ f : S ⟶ (Functor.const _).obj PUnit.{w + 1}, homotopyEquivalences (Type w) f) :
    IsIso (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex A).map (Functor.copowerMap a (𝟙 S))) n) :=
  isIso_map_copowerMap _ (isInvertedBy_homologyFunctor_alternatingFaceMapComplex n) a ha S hS

end CategoryTheory.SimplicialObject

end
