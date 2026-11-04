module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over

/-!
# The inverse image of the structure sheaf along an open immersion is the structure sheaf

Let `j : U ⟶ T` be an open immersion of schemes.  The structural map
`AlgebraicGeometry.inverseImageStructureMap j : j⁻¹𝒪_T ⟶ 𝒪_U` is the adjunct of the comorphism
`j.c` under the pullback--pushforward adjunction for sheaves of commutative rings.  This file
proves that it is an isomorphism, which is the statement that the inverse image of a sheaf of
rings along an open immersion is its restriction.

The difficulty is that `TopCat.Sheaf.pullback` is defined as the left adjoint of the direct
image, hence as a sheafified left Kan extension, with no description of its sections.  It is
avoided entirely: the inverse image along an *open embedding* has a second, naive description as
precomposition with the functor `W ↦ j(W)` on opens, and that description is also a left adjoint
of the direct image, by `CategoryTheory.Adjunction.sheafPushforwardContinuous` applied to the
adjunction `IsOpenMap.adjunction`.  Uniqueness of left adjoints then transports the question to
the naive inverse image, where every map in sight is computed on sections.

## Main definitions

* `AlgebraicGeometry.naiveInverseImageAdjunction` is the adjunction between the naive inverse
  image `Topology.IsOpenEmbedding.sheafPullback` along an open immersion and the direct image of
  sheaves of commutative rings.
* `AlgebraicGeometry.naiveInverseImageStructureMap` is the naive counterpart of
  `AlgebraicGeometry.inverseImageStructureMap`, namely the adjunct of `j.c` for that adjunction.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_eq_leftAdjointUniq_comp`: for two adjunctions with
  the same right adjoint, the two adjuncts of a morphism differ by the canonical isomorphism of
  the left adjoints.
* `AlgebraicGeometry.naiveInverseImageStructureMap_app`: the naive structural map is, on sections
  over an open `W` of `U`, the isomorphism `Γ(T, j(W)) ≅ Γ(U, W)` of
  `AlgebraicGeometry.Scheme.Hom.appIso`.
* `AlgebraicGeometry.isIso_inverseImageStructureMap_of_isOpenImmersion`: **the structural map
  `j⁻¹𝒪_T ⟶ 𝒪_U` of an open immersion is an isomorphism.**

## Implementation notes

The counit of `naiveInverseImageAdjunction` is, on sections over `W`, the action of the sheaf on
the unit `W ⟶ j⁻¹(j(W))` of `IsOpenMap.adjunction`; that unit is an isomorphism because the two
opens are equal, and in a partially ordered set every morphism between equal objects is
invertible.  This is the whole content of the counit being an isomorphism, and it is why the
naive inverse image is the one to compute with.

The three general lemmas about adjunctions are stated for an arbitrary pair of categories rather
than specialized to sheaves on a space.  This is not only for generality: `TopCat.Sheaf
CommRingCat X` is a category of sheaves on an `InducedCategory`, and the anonymous constructor
`⟨j.c⟩` for a morphism of such sheaves is not type-correct at instance transparency, so a `rw`
whose motive mentions it fails even though the statement elaborates.  Performing the rewrites in
the general setting and then instantiating avoids the problem.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]

/-- **Two adjuncts of the same morphism differ by the canonical isomorphism of left adjoints.**
If `F` and `F'` are both left adjoint to `G`, then the adjunct `F x ⟶ y` of `k : x ⟶ G y` for the
first adjunction is the canonical isomorphism `F x ≅ F' x` followed by the adjunct for the
second. -/
public theorem homEquiv_symm_eq_leftAdjointUniq_comp {F F' : C ⥤ D} {G : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {x : C} {y : D} (k : x ⟶ G.obj y) :
    (adj1.homEquiv x y).symm k =
      (leftAdjointUniq adj1 adj2).hom.app x ≫ (adj2.homEquiv x y).symm k := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    ← leftAdjointUniq_hom_app_counit adj1 adj2, ← Category.assoc,
    (leftAdjointUniq adj1 adj2).hom.naturality k, Category.assoc]

/-- The adjunct of `k : x ⟶ G y` is an isomorphism as soon as `F k` and the counit at `y` are. -/
public theorem isIso_homEquiv_symm_of_isIso_map {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {x : C} {y : D} (k : x ⟶ G.obj y) [IsIso (F.map k)] [IsIso (adj.counit.app y)] :
    IsIso ((adj.homEquiv x y).symm k) := by
  rw [Adjunction.homEquiv_counit]; infer_instance

/-- Whether the adjunct of a morphism is an isomorphism does not depend on which left adjoint of
`G` is used to form it. -/
public theorem isIso_homEquiv_symm_of_isIso {F F' : C ⥤ D} {G : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G) {x : C} {y : D} (k : x ⟶ G.obj y)
    [IsIso ((adj2.homEquiv x y).symm k)] : IsIso ((adj1.homEquiv x y).symm k) := by
  rw [homEquiv_symm_eq_leftAdjointUniq_comp adj1 adj2 k]; infer_instance

end CategoryTheory.Adjunction

namespace TopCat.Sheaf

/-- A morphism of sheaves of commutative rings on a topological space which is an isomorphism on
sections over every open is an isomorphism. -/
public theorem isIso_of_isIso_app {X : TopCat.{u}} {F G : TopCat.Sheaf CommRingCat.{u} X}
    (φ : F ⟶ G) (h : ∀ W : Opens X, IsIso (φ.hom.app (op W))) : IsIso φ :=
  have _hall : ∀ W : (Opens X)ᵒᵖ, IsIso (φ.hom.app W) := fun W ↦ W.rec fun W ↦ h W
  have _hval : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map φ) :=
    NatIso.isIso_of_isIso_app φ.hom
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}).isIso_of_isIso_map φ

end TopCat.Sheaf

namespace Topology.IsOpenEmbedding

/-- For an open embedding `f`, the unit `W ⟶ f⁻¹(f(W))` of the adjunction between the image and
the preimage functors on opens is an isomorphism: the two opens are equal, and the morphisms of a
partially ordered set are invertible as soon as source and target agree. -/
public theorem isIso_isOpenMap_adjunction_unit_app {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsOpenEmbedding f) (W : Opens X) :
    IsIso (hf.isOpenMap.adjunction.unit.app W) :=
  have h : (Opens.map f).obj (hf.isOpenMap.functor.obj W) = W :=
    Opens.ext (by simpa using Set.preimage_image_eq (W : Set X) hf.injective)
  ⟨homOfLE h.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end Topology.IsOpenEmbedding

namespace AlgebraicGeometry

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- **The naive inverse image along an open immersion is left adjoint to the direct image.** The
naive inverse image `Topology.IsOpenEmbedding.sheafPullback` is precomposition with the functor
`W ↦ j(W)` on opens; it is adjoint to the direct image because that functor is left adjoint to
`Opens.map j.base`. -/
public noncomputable def naiveInverseImageAdjunction :
    j.isOpenEmbedding.sheafPullback CommRingCat.{u} ⊣
      TopCat.Sheaf.pushforward CommRingCat.{u} j.base :=
  have := j.isOpenEmbedding.functor_isContinuous
  Adjunction.sheafPushforwardContinuous (E := CommRingCat.{u})
    j.isOpenEmbedding.isOpenMap.adjunction (Opens.grothendieckTopology U)
    (Opens.grothendieckTopology T)

/-- The counit of `AlgebraicGeometry.naiveInverseImageAdjunction` is, on sections over an open
`W`, the action of the sheaf on the unit `W ⟶ j⁻¹(j(W))`. -/
public theorem naiveInverseImageAdjunction_counit_app_hom_app
    (P : TopCat.Sheaf CommRingCat.{u} U) (W : U.Opens) :
    ((naiveInverseImageAdjunction j).counit.app P).hom.app (op W) =
      P.obj.map (j.isOpenEmbedding.isOpenMap.adjunction.unit.app W).op :=
  rfl

/-- The counit of `AlgebraicGeometry.naiveInverseImageAdjunction` is an isomorphism: the naive
inverse image of the direct image of a sheaf is that sheaf. -/
public instance isIso_naiveInverseImageAdjunction_counit_app
    (P : TopCat.Sheaf CommRingCat.{u} U) :
    IsIso ((naiveInverseImageAdjunction j).counit.app P) := by
  refine TopCat.Sheaf.isIso_of_isIso_app _ fun W ↦ ?_
  have _h := j.isOpenEmbedding.isIso_isOpenMap_adjunction_unit_app W
  exact (inferInstance :
    IsIso (P.obj.map (j.isOpenEmbedding.isOpenMap.adjunction.unit.app W).op))

/-- The comorphism of an open immersion, as a morphism of sheaves of commutative rings from the
structure sheaf of the target to the direct image of the structure sheaf of the source. -/
public noncomputable abbrev comorphismSheafHom :
    T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj U.sheaf :=
  ⟨j.c⟩

/-- The naive inverse image of the comorphism of an open immersion is, on sections over an open
`W` of the source, the comorphism at the open `j(W)`. -/
public theorem sheafPullback_map_comorphismSheafHom_app (W : U.Opens) :
    ((j.isOpenEmbedding.sheafPullback CommRingCat.{u}).map
      (comorphismSheafHom j)).hom.app (op W) = j.c.app (op (j ''ᵁ W)) :=
  rfl

/-- The naive inverse image of the comorphism of an open immersion is an isomorphism: on sections
over `W` it is the comorphism at `j(W)`, which is invertible because `j(W)` lies in the range of
`j`. -/
public instance isIso_sheafPullback_map_comorphismSheafHom :
    IsIso ((j.isOpenEmbedding.sheafPullback CommRingCat.{u}).map (comorphismSheafHom j)) := by
  refine TopCat.Sheaf.isIso_of_isIso_app _ fun W ↦ ?_
  exact (inferInstance : IsIso (j.c.app (op (j ''ᵁ W))))

/-- The naive counterpart of `AlgebraicGeometry.inverseImageStructureMap` for an open immersion:
the adjunct of the comorphism for the adjunction
`AlgebraicGeometry.naiveInverseImageAdjunction`. -/
public noncomputable def naiveInverseImageStructureMap :
    (j.isOpenEmbedding.sheafPullback CommRingCat.{u}).obj T.sheaf ⟶ U.sheaf :=
  ((naiveInverseImageAdjunction j).homEquiv T.sheaf U.sheaf).symm (comorphismSheafHom j)

/-- The naive structural map is an isomorphism, being the composite of two isomorphisms. -/
public instance isIso_naiveInverseImageStructureMap :
    IsIso (naiveInverseImageStructureMap j) :=
  Adjunction.isIso_homEquiv_symm_of_isIso_map (naiveInverseImageAdjunction j) _

/-- **On sections over an open `W`, the naive structural map is the canonical isomorphism
`Γ(T, j(W)) ≅ Γ(U, W)`** of `AlgebraicGeometry.Scheme.Hom.appIso`. -/
public theorem naiveInverseImageStructureMap_app (W : U.Opens) :
    (naiveInverseImageStructureMap j).hom.app (op W) = (j.appIso W).hom := by
  have h1 : (naiveInverseImageStructureMap j).hom.app (op W) =
      j.c.app (op (j ''ᵁ W)) ≫
        U.presheaf.map (j.isOpenEmbedding.isOpenMap.adjunction.unit.app W).op := by
    refine Eq.trans (congrArg (fun k : (j.isOpenEmbedding.sheafPullback CommRingCat.{u}).obj
        T.sheaf ⟶ U.sheaf ↦ k.hom.app (op W))
      (Adjunction.homEquiv_counit (naiveInverseImageAdjunction j) T.sheaf U.sheaf
        (comorphismSheafHom j))) ?_
    exact congrArg (fun k ↦ j.c.app (op (j ''ᵁ W)) ≫ k)
      (naiveInverseImageAdjunction_counit_app_hom_app j U.sheaf W)
  have h2 : (j.appIso W).hom = j.c.app (op (j ''ᵁ W)) ≫
      U.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op := j.appIso_hom W
  rw [h1, h2]
  exact congrArg (fun i : W ⟶ j ⁻¹ᵁ (j ''ᵁ W) ↦
    j.c.app (op (j ''ᵁ W)) ≫ U.presheaf.map i.op) (Subsingleton.elim _ _)

/-- Composing the inverse of `AlgebraicGeometry.Scheme.Hom.appIso` with the naive structural map
gives the identity of the structure sheaf of `U`. -/
public theorem appIso_inv_comp_naiveInverseImageStructureMap_app (W : U.Opens) :
    (j.appIso W).inv ≫ (naiveInverseImageStructureMap j).hom.app (op W) = 𝟙 Γ(U, W) :=
  Eq.trans (congrArg (fun k ↦ (j.appIso W).inv ≫ k)
    (naiveInverseImageStructureMap_app j W)) (j.appIso W).inv_hom_id

/-- **The structural map `j⁻¹𝒪_T ⟶ 𝒪_U` of an open immersion is an isomorphism.** Equivalently,
the inverse image of the structure sheaf along an open immersion is the structure sheaf of the
source: this is the statement that the inverse image of a sheaf of rings along an open immersion
is its restriction, in the only case in which it is needed. -/
public instance isIso_inverseImageStructureMap_of_isOpenImmersion :
    IsIso (inverseImageStructureMap j) :=
  have _h : IsIso (((naiveInverseImageAdjunction j).homEquiv T.sheaf U.sheaf).symm
      (comorphismSheafHom j)) := isIso_naiveInverseImageStructureMap j
  Adjunction.isIso_homEquiv_symm_of_isIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base)
    (naiveInverseImageAdjunction j) _

end AlgebraicGeometry

end
