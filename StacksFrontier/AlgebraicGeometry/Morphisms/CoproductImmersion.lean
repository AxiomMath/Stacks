module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension

/-!
# Immersions out of a binary coproduct of schemes

A morphism out of a disjoint union `X ⨿ Y` of schemes is an immersion of the same kind as its
two restrictions as soon as their images are *disjoint*: the open-immersion case is Mathlib's
`AlgebraicGeometry.isOpenImmersion_sigmaDesc` read through
`AlgebraicGeometry.coprodIsoSigma`, and the closed-immersion case is proved here, there being
no indexed-coproduct version of it to transport.

Disjointness of the images is necessary — a morphism out of a coproduct is injective on points
only if the two images are disjoint — but for *immersions* it is not sufficient, which is why
no immersion version appears below. The inclusion of `𝔸¹ ∖ {0}` and the inclusion of the origin
are immersions with disjoint images, yet the induced bijection `(𝔸¹ ∖ {0}) ⨿ {0} ⟶ 𝔸¹` is not
an embedding: the origin is open in the source and not in the target. What the two statements
below use beyond disjointness is that each of the two images is open, respectively that each is
closed and the two are therefore separated by their complements.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isClosedImmersion_coprodDesc`: a morphism out of a binary coproduct whose
  two restrictions are closed immersions with disjoint images is a closed immersion.
* `AlgebraicGeometry.isOpenImmersion_coprodDesc`: the same for open immersions.
* `AlgebraicGeometry.quasiCompact_coprodDesc`: a morphism out of a binary coproduct whose two
  restrictions are quasi-compact is quasi-compact; disjointness is not needed here.

## What is and is not proved

The closed-immersion statement is proved through
`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`: the morphism is finite because a
binary coproduct of finite morphisms is finite, and it is a monomorphism because it is
surjective on stalks — being so on each member of the coproduct open cover — and injective on
points, which is where disjointness of the images enters.

No Stacks attribute is carried: none of these statements is a labelled result of the source.
They are the shape in which a finite disjoint union of subschemes of one scheme is recognised,
used for instance when a disjoint union of schemes projective over a base is embedded into a
single projective space over that base.

The analogous statement for *immersions* with disjoint images is **false**, by the example
above, and is not proved here in any form.

## References

* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {T X Y : Scheme.{u}} (a : X ⟶ T) (b : Y ⟶ T)

/-- **A morphism out of a binary coproduct of schemes whose two restrictions are closed
immersions with disjoint images is a closed immersion.** It is finite because a binary
coproduct of finite morphisms is finite, and a monomorphism because it is surjective on stalks
and injective on points; `AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono` assembles
the two.

Surjectivity on stalks is checked on the two members of the coproduct open cover, where the
morphism restricts to `a` and to `b`. Injectivity on points is where disjointness of the images
is used: two points of the same summand have equal images only if they are equal, and two
points of different summands have distinct images. -/
theorem isClosedImmersion_coprodDesc [IsClosedImmersion a] [IsClosedImmersion b]
    (hd : Disjoint (Set.range a.base) (Set.range b.base)) :
    IsClosedImmersion (coprod.desc a b) := by
  have hl : ∀ x : X, (coprod.desc a b).base ((coprod.inl : X ⟶ X ⨿ Y).base x) = a.base x :=
    fun x => congrArg (fun k : X ⟶ T => k.base x) (coprod.inl_desc a b)
  have hr : ∀ x : Y, (coprod.desc a b).base ((coprod.inr : Y ⟶ X ⨿ Y).base x) = b.base x :=
    fun x => congrArg (fun k : Y ⟶ T => k.base x) (coprod.inr_desc a b)
  have hsos : SurjectiveOnStalks (coprod.desc a b) := by
    refine IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{u, 0} X Y) ?_
    rintro (_ | _)
    · show SurjectiveOnStalks ((coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.desc a b)
      rw [coprod.inl_desc]; infer_instance
    · show SurjectiveOnStalks ((coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.desc a b)
      rw [coprod.inr_desc]; infer_instance
  have hinj : Function.Injective (coprod.desc a b).base := by
    intro p q hpq
    obtain ⟨p', rfl⟩ := (coprodMk X Y).surjective p
    obtain ⟨q', rfl⟩ := (coprodMk X Y).surjective q
    obtain (p' | p') := p' <;> obtain (q' | q') := q' <;>
      simp only [coprodMk_inl, coprodMk_inr] at hpq ⊢
    · exact congrArg _ ((Scheme.Hom.isClosedEmbedding a).injective
        ((hl p').symm.trans (hpq.trans (hl q'))))
    · exact absurd ((hl p').symm.trans (hpq.trans (hr q')))
        (Set.disjoint_iff_forall_ne.mp hd ⟨p', rfl⟩ ⟨q', rfl⟩)
    · exact absurd ((hl q').symm.trans (hpq.symm.trans (hr p')))
        (Set.disjoint_iff_forall_ne.mp hd ⟨q', rfl⟩ ⟨p', rfl⟩)
    · exact congrArg _ ((Scheme.Hom.isClosedEmbedding b).injective
        ((hr p').symm.trans (hpq.trans (hr q'))))
  exact (IsClosedImmersion.iff_isFinite_and_mono (coprod.desc a b)).2
    ⟨inferInstance, hsos.mono_of_injective hinj⟩

/-- **A morphism out of a binary coproduct of schemes whose two restrictions are open
immersions with disjoint images is an open immersion.** This is Mathlib's
`AlgebraicGeometry.isOpenImmersion_sigmaDesc` for the two-element family of
`AlgebraicGeometry.coprodIsoSigma`, transported along that isomorphism by
`AlgebraicGeometry.coprodIsoSigma_inv_comp_coprodDesc`. -/
theorem isOpenImmersion_coprodDesc [IsOpenImmersion a] [IsOpenImmersion b]
    (hd : Disjoint (Set.range a.base) (Set.range b.base)) :
    IsOpenImmersion (coprod.desc a b) := by
  have hfam : ∀ i, IsOpenImmersion (coprodDescFamily a b i) := by
    rintro ⟨i⟩; cases i <;> assumption
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion (coprodIsoSigma X Y).inv,
    coprodIsoSigma_inv_comp_coprodDesc]
  refine isOpenImmersion_sigmaDesc
    (fun i : ULift.{u} WalkingPair => (WalkingPair.casesOn i.down X Y : Scheme.{u}))
    (coprodDescFamily a b) ?_
  rintro ⟨i⟩ ⟨j⟩ hij
  cases i <;> cases j
  · exact absurd rfl hij
  · exact hd
  · exact hd.symm
  · exact absurd rfl hij

/-- **A morphism out of a binary coproduct of schemes whose two restrictions are quasi-compact
is quasi-compact.** The preimage of a quasi-compact open of the target is the union of the
images in the coproduct of the two preimages, hence compact. No disjointness is needed. -/
theorem quasiCompact_coprodDesc [QuasiCompact a] [QuasiCompact b] :
    QuasiCompact (coprod.desc a b) := by
  have hl : ∀ x : X, (coprod.desc a b).base ((coprod.inl : X ⟶ X ⨿ Y).base x) = a.base x :=
    fun x => congrArg (fun k : X ⟶ T => k.base x) (coprod.inl_desc a b)
  have hr : ∀ x : Y, (coprod.desc a b).base ((coprod.inr : Y ⟶ X ⨿ Y).base x) = b.base x :=
    fun x => congrArg (fun k : Y ⟶ T => k.base x) (coprod.inr_desc a b)
  refine ⟨fun U hUo hUc => ?_⟩
  have hset : (coprod.desc a b).base ⁻¹' U =
      (coprod.inl : X ⟶ X ⨿ Y).base '' (a.base ⁻¹' U) ∪
        (coprod.inr : Y ⟶ X ⨿ Y).base '' (b.base ⁻¹' U) := by
    refine Set.eq_of_subset_of_subset (fun p hp => ?_) (Set.union_subset ?_ ?_)
    · obtain ⟨p', rfl⟩ := (coprodMk X Y).surjective p
      obtain (p' | p') := p'
      · rw [coprodMk_inl] at hp ⊢
        exact Or.inl ⟨p', by rwa [Set.mem_preimage, ← hl p'], rfl⟩
      · rw [coprodMk_inr] at hp ⊢
        exact Or.inr ⟨p', by rwa [Set.mem_preimage, ← hr p'], rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [Set.mem_preimage, hl x]
      exact hx
    · rintro _ ⟨x, hx, rfl⟩
      rw [Set.mem_preimage, hr x]
      exact hx
  rw [hset]
  exact (((‹QuasiCompact a›).isCompact_preimage U hUo hUc).image
      (coprod.inl : X ⟶ X ⨿ Y).base.hom.continuous_toFun).union
    (((‹QuasiCompact b›).isCompact_preimage U hUo hUc).image
      (coprod.inr : Y ⟶ X ⨿ Y).base.hom.continuous_toFun)

end AlgebraicGeometry

end
