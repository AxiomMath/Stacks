module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleKaroubiColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The quotient of a morphism of systems of abelian étale sheaves

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes and let `φ_i : F_i ⟶ G_i` be a morphism of
systems of abelian sheaves on the small étale sites of the levels, in the sense of
[Stacks, Tag 0EZL] — that is, a family of maps commuting with the transitions. This file forms the
**levelwise cokernel** and shows that it is again a system.

The transition map is the only thing to construct. The inverse image
`Stacks.EtaleCohomology.systemPullback` along a transition is a left adjoint, so it preserves
cokernels; hence `f_a^{-1}(G_j/F_j)` is the cokernel of `f_a^{-1}F_j ⟶ f_a^{-1}G_j`, and the
composite `f_a^{-1}G_j ⟶ G_i ⟶ G_i/F_i` kills `f_a^{-1}F_j` because `φ` commutes with the
transitions. The cocycle condition then follows by cancelling the epimorphism
`f_a^{-1}G_k ⟶ f_a^{-1}(G_k/F_k)` against the cocycle condition of `G`.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.quotientSystemMap` — the transition map of the
  quotient.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.quotientSystem` — the quotient system.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.π_comp_quotientSystemMap` — the defining
  property of the transition map: the projections `G_i ⟶ G_i/F_i` form a morphism of systems from
  `G` to the quotient.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_naturality_of_map` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_quotientSystem` — the two
  morphism-of-systems statements read through
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`, that is in the
  vocabulary of `Stacks.EtaleCohomology.systemTransitionMap`, which is what the dévissage datum of
  [Stacks, Tag 09YQ] asks for.

## Implementation notes

**Two inverse images, again.** A system carries its transitions along
`Stacks.EtaleCohomology.systemPullback`, the abstract left adjoint; the dévissage datum states its
compatibilities along `Stacks.EtaleCohomology.etaleAbelianInverseImage`, the constructed one. The
construction here is done in the first vocabulary, where the adjunction and hence the preservation
of cokernels is available, and the two statements above carry it into the second. This is the
pattern of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_eq`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}} (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
  (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (systemPullback D AddCommGrpCat.{u + 1} a).map (φ j) ≫ G.map a = F.map a ≫ φ i)

/-- **The transition map of the levelwise quotient.** Through the comparison identifying
`f_a^{-1}(G_j/F_j)` with the cokernel of `f_a^{-1}φ_j`, it is the map induced by
`f_a^{-1}G_j ⟶ G_i ⟶ G_i/F_i`, which kills `f_a^{-1}F_j` because `φ` commutes with the
transitions. -/
def quotientSystemMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D AddCommGrpCat.{u + 1} a).obj (cokernel (φ j)) ⟶ cokernel (φ i) :=
  (PreservesCokernel.iso (systemPullback D AddCommGrpCat.{u + 1} a) (φ j)).hom ≫
    cokernel.desc _ (G.map a ≫ cokernel.π (φ i)) (by
      rw [← Category.assoc, hφ a, Category.assoc, cokernel.condition, comp_zero])

/-- **The defining property of the quotient transition map**: the levelwise projections form a
morphism of systems from `G` to the quotient. -/
theorem π_comp_quotientSystemMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D AddCommGrpCat.{u + 1} a).map (cokernel.π (φ j)) ≫
        quotientSystemMap φ hφ a =
      G.map a ≫ cokernel.π (φ i) := by
  rw [quotientSystemMap, ← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- **The cocycle condition of the quotient system.** Both sides agree after composition with the
epimorphism `f_{a ≫ b}^{-1}G_k ⟶ f_{a ≫ b}^{-1}(G_k/F_k)`, where they become the cocycle
condition of `G`. -/
theorem quotientSystemMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp D AddCommGrpCat.{u + 1} a b).inv.app (cokernel (φ k)) ≫
        (systemPullback D AddCommGrpCat.{u + 1} a).map (quotientSystemMap φ hφ b) ≫
          quotientSystemMap φ hφ a =
      quotientSystemMap φ hφ (a ≫ b) := by
  refine (cancel_epi ((systemPullback D AddCommGrpCat.{u + 1} (a ≫ b)).map
    (cokernel.π (φ k)))).mp ?_
  rw [π_comp_quotientSystemMap,
    (systemPullbackComp D AddCommGrpCat.{u + 1} a b).inv.naturality_assoc (cokernel.π (φ k)),
    Functor.comp_map, ← Functor.map_comp_assoc, π_comp_quotientSystemMap, Functor.map_comp,
    Category.assoc, π_comp_quotientSystemMap, reassoc_of% (G.map_comp a b)]

/-- **The levelwise quotient of a morphism of systems is a system.** -/
def quotientSystem : EtaleSheafSystem D AddCommGrpCat.{u + 1} where
  obj i := cokernel (φ i)
  map a := quotientSystemMap φ hφ a
  map_comp a b := quotientSystemMap_comp φ hφ a b

/-- The sheaf of the quotient system at level `i` is the cokernel of `φ i`. -/
@[simp]
theorem quotientSystem_obj (i : Iᵒᵖ) : (quotientSystem φ hφ).obj i = cokernel (φ i) := rfl

/-- The transition map of the quotient system along `a` is `quotientSystemMap φ hφ a`. -/
@[simp]
theorem quotientSystem_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    (quotientSystem φ hφ).map a = quotientSystemMap φ hφ a := rfl

include hφ in
/-- **A morphism of systems, in the vocabulary of
`Stacks.EtaleCohomology.systemTransitionMap`.** -/
theorem systemTransitionMap_naturality_of_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
      systemTransitionMap F a ≫ φ i := by
  rw [systemTransitionMap_eq, systemTransitionMap_eq,
    (inverseImageIsoPullbackAb (D.map a)).inv.naturality_assoc (φ j) (G.map a),
    hφ a, Category.assoc]

/-- **The levelwise projections form a morphism of systems from `G` to the quotient**, in the
vocabulary of `Stacks.EtaleCohomology.systemTransitionMap`. -/
theorem systemTransitionMap_quotientSystem {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (cokernel.π (φ j)) ≫
        systemTransitionMap (quotientSystem φ hφ) a =
      systemTransitionMap G a ≫ cokernel.π (φ i) := by
  show (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (cokernel.π (φ j)) ≫
      (inverseImageIsoPullbackAb (D.map a)).inv.app (cokernel (φ j)) ≫
        quotientSystemMap φ hφ a =
    ((inverseImageIsoPullbackAb (D.map a)).inv.app (G.obj j) ≫ G.map a) ≫ cokernel.π (φ i)
  rw [(inverseImageIsoPullbackAb (D.map a)).inv.naturality_assoc (cokernel.π (φ j))
      (quotientSystemMap φ hφ a),
    π_comp_quotientSystemMap, Category.assoc]

/-! ### The projection onto the quotient, in the quotient system's own spelling

The sheaf of the quotient system at a level *is* the cokernel, but `(quotientSystem φ hφ).obj i`
and `cokernel (φ i)` are not the same expression, and a composite written with one of them is
well-typed with the other only up to unfolding — so `rw`, which must build a motive, fails on it.
The declarations below are the cokernel property of the quotient written entirely in the first
spelling, which is the one every consumer of the quotient *system* is in. -/

/-- **The projection of `G_i` onto the quotient system's sheaf at `i`.** The body is
`CategoryTheory.Limits.cokernel.π`; what the ascription does is write the target as
`(quotientSystem φ hφ).obj i`. -/
def quotientSystemπ (i : Iᵒᵖ) : G.obj i ⟶ (quotientSystem φ hφ).obj i := cokernel.π (φ i)

/-- The composite of the embedding with the projection vanishes. -/
theorem comp_quotientSystemπ (i : Iᵒᵖ) : φ i ≫ quotientSystemπ φ hφ i = 0 :=
  cokernel.condition (φ i)

/-- The projection onto the quotient is an epimorphism. -/
theorem epi_quotientSystemπ (i : Iᵒᵖ) : Epi (quotientSystemπ φ hφ i) :=
  (inferInstance : Epi (cokernel.π (φ i)))

/-- **The embedding and the projection form a short exact sequence at every level** where the
embedding is a monomorphism. -/
theorem shortExact_quotientSystemπ (i : Iᵒᵖ) (hm : Mono (φ i)) :
    (ShortComplex.mk (φ i) (quotientSystemπ φ hφ i) (comp_quotientSystemπ φ hφ i)).ShortExact :=
  let := hm
  { exact := ShortComplex.cokernelSequence_exact (φ i)
    mono_f := hm
    epi_g := epi_quotientSystemπ φ hφ i }

/-- The inverse image of the projection along any morphism of schemes is an epimorphism: inverse
image is a left adjoint. -/
theorem epi_map_quotientSystemπ {Y : Scheme.{u}}
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}] {i : Iᵒᵖ} (k : Y ⟶ D.obj i) :
    Epi ((etaleAbelianInverseImage.{u, u + 1} k).map (quotientSystemπ φ hφ i)) := by
  have := epi_quotientSystemπ φ hφ i
  exact Functor.map_epi _ _

/-- **The inverse image of the projection is a cokernel.** A map out of `k^{-1}G_i` killing
`k^{-1}F_i` factors uniquely through `k^{-1}Q_i`; inverse image is a left adjoint, so it preserves
the cokernel. This is the only property of the quotient the dévissage of [Stacks, Tag 09YQ] uses,
and stating it here is what keeps the two spellings of the quotient's sheaf from meeting in a
rewrite. -/
theorem existsUnique_desc_quotientSystem {Y : Scheme.{u}}
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}] {i : Iᵒᵖ} (k : Y ⟶ D.obj i)
    {H : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}}
    (t : (etaleAbelianInverseImage.{u, u + 1} k).obj (G.obj i) ⟶ H)
    (ht : (etaleAbelianInverseImage.{u, u + 1} k).map (φ i) ≫ t = 0) :
    ∃! s : (etaleAbelianInverseImage.{u, u + 1} k).obj ((quotientSystem φ hφ).obj i) ⟶ H,
      (etaleAbelianInverseImage.{u, u + 1} k).map (quotientSystemπ φ hφ i) ≫ s = t := by
  have := epi_map_quotientSystemπ φ hφ k
  obtain ⟨w, hw⟩ : ∃ w : (etaleAbelianInverseImage.{u, u + 1} k).obj (cokernel (φ i)) ⟶ H,
      (etaleAbelianInverseImage.{u, u + 1} k).map (cokernel.π (φ i)) ≫ w = t := by
    refine ⟨(PreservesCokernel.iso (etaleAbelianInverseImage.{u, u + 1} k) (φ i)).hom ≫
      cokernel.desc _ t ht, ?_⟩
    rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
  exact ⟨w, hw, fun y hy => (cancel_epi ((etaleAbelianInverseImage.{u, u + 1} k).map
    (quotientSystemπ φ hφ i))).mp (hy.trans hw.symm)⟩

/-- **The projections form a morphism of systems from `G` to the quotient**, in the vocabulary of
`Stacks.EtaleCohomology.systemTransitionMap` and in the quotient system's own spelling. -/
theorem systemTransitionMap_quotientSystemπ {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (quotientSystemπ φ hφ j) ≫
        systemTransitionMap (quotientSystem φ hφ) a =
      systemTransitionMap G a ≫ quotientSystemπ φ hφ i :=
  systemTransitionMap_quotientSystem φ hφ a

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
