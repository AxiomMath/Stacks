module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.OpenRestriction

/-!
# Two stratified sheaves on one stratification

`AlgebraicGeometry.IsStratifiedSheaf B X P F` says that each affine open of `X` carries a finite
partition by constructible locally closed subschemes on whose strata the inverse image of `F`
satisfies `P`; both parts of Stacks 03RW are of this shape, with `P` finite local constancy
resp. local constancy of finite type. The partition is existentially quantified, so two such
sheaves come with two unrelated partitions.

This file replaces the two by one. Given two sheaves stratified by `P`, every affine open
carries a single partition on whose strata the inverse images of *both* satisfy `P`: refine the
two partitions against each other with
`AlgebraicGeometry.ConstructibleStratification.inf` and transport `P` along the projection of a
refined stratum onto the stratum it refines.

This is the step that every comparison of two constructible sheaves begins with — a morphism of
constructible sheaves, or a short exact sequence of them, as in Stacks 03RZ.

## Main results

* `AlgebraicGeometry.exists_stratification_isStratifiedSheaf_pair`: two sheaves stratified by
  `P` are stratified by `P` on a common refinement.

## Implementation notes

Two properties of `P` are hypotheses, because neither holds for an arbitrary `P` and together
they are exactly what the refinement step consumes:

* invariance under isomorphism of sheaves, which for finite local constancy is
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_congr`; it is needed because inverse image along
  a composite agrees with the composite of the inverse images only up to the canonical
  isomorphism `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`, inverse image being a chosen
  left adjoint;
* stability under inverse image along an **immersion** of the big étale site. The projection of
  a refined stratum onto a stratum it refines is an immersion, by
  `AlgebraicGeometry.ConstructibleStratification.isImmersion_interFst`, so the hypothesis is
  only imposed for immersions and not for arbitrary morphisms of the site.

For `P` finite local constancy the second hypothesis is the one statement this library does not
have: that the inverse image of a finite locally constant abelian sheaf is finite locally
constant (Stacks 093R for sheaves of sets, whose only form here is
`CategoryTheory.MorphismOfTopoi.isConstant_inverseImage`). Isolating it as a hypothesis here is
deliberate, so that the result is unconditional and the remaining gap is a single named
statement rather than a weakened theorem.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Two sheaves stratified by `P` are stratified by `P` on one common stratification.** On a
given affine open the two partitions witnessing the hypotheses are refined against each other,
and `P` is carried from a stratum to the refined strata inside it along the projection, which is
an immersion. -/
public theorem exists_stratification_isStratifiedSheaf_pair (X : B.Scheme)
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPImmersion : ∀ (T T' : B.Scheme) (g : T' ⟶ T), IsImmersion (B.inclusion.map g) →
      ∀ G : Sheaf (SmallEtale.topology B T.obj T.property) D, P T G →
        P T' (((smallEtaleBaseChange B g).sheafPullback D
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B T'.obj T'.property)).obj G))
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) D}
    (hF : IsStratifiedSheaf B X P F) (hG : IsStratifiedSheaf B X P G)
    (V : X.obj.affineOpens) :
    ∃ r : ConstructibleStratification B X V.1, ∀ k,
      P (r.piece k) (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback D
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj F) ∧
        P (r.piece k) (((smallEtaleBaseChange B (r.inclusion k)).sheafPullback D
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).obj G) := by
  have key := fun (H : Sheaf (SmallEtale.topology B X.obj X.property) D) T T' c a ha h =>
    hPIso _ ((smallEtaleSheafPullbackCompIso B T' T X a c D).app H) (hPImmersion _ _ a ha _ h)
  obtain ⟨s, hs⟩ := hF V
  obtain ⟨t, ht⟩ := hG V
  refine ⟨s.inf t, fun k => ⟨?_, ?_⟩⟩
  · obtain ⟨i, a, hai, hfac⟩ := ConstructibleStratification.inf_factorsThrough_fst s t k
    rw [← hfac]
    exact key F _ _ _ a hai (hs i)
  · obtain ⟨j, b, hbj, hfac⟩ := ConstructibleStratification.inf_factorsThrough_snd s t k
    rw [← hfac]
    exact key G _ _ _ b hbj (ht j)

end AlgebraicGeometry

end
