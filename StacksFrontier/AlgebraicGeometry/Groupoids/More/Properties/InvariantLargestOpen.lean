module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.LargestTargetOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic

/-!
# Invariance of the largest open on which the source map has a target-local property

Let `G` be a groupoid scheme whose source and target maps are both coverings for one of the
Zariski, fppf, étale, smooth or syntomic topologies, and let `P` be a property of morphisms of
schemes which is local on the target for that topology. Then the largest open of the object
scheme over which the source map has `P` is invariant under the arrows of `G`.

## Main results

* `AlgebraicGeometry.largestTargetOpen_precomp_iso` and
  `AlgebraicGeometry.largestTargetOpen_eq_of_isPullback_snd`: the largest open of the target is
  unchanged by precomposition with an isomorphism, hence depends only on a cartesian square and
  not on the chosen model of the fibre product.
* `AlgebraicGeometry.isInvariantOpen_largestTargetOpen_source`: **Stacks 03JC**.

## Implementation notes

The largest open is `AlgebraicGeometry.largestTargetOpen` applied to the source map, and the
four non-Zariski topologies are covered uniformly by
`AlgebraicGeometry.IsDescentMorphismClass`; the Zariski case is separate because its class of
covering morphisms is the open immersions, which are not stable under the base changes the
other argument uses. In the Zariski case the two coverings force the source map to be an
isomorphism and the source and target maps to coincide, so the statement is immediate. In the
remaining cases the two inverse images of the open agree, because the scheme of composable
pairs is simultaneously the base change of the source map along the target map and along the
source map; this is the pair of cartesian squares of Tag 04LF.

Each covering is a one-member family, represented by `CategoryTheory.Presieve.ofArrows` on
`Unit`.

## References

* [Stacks Project, Tag 03JC](https://stacks.math.columbia.edu/tag/03JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The largest open of the target on which a morphism has a property is unchanged by
precomposition with an isomorphism. -/
theorem largestTargetOpen_precomp_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X X' Y : Scheme.{u}} (e : X ≅ X') (f : X' ⟶ Y) :
    largestTargetOpen P (e.hom ≫ f) = largestTargetOpen P f := by
  unfold largestTargetOpen
  congr 1
  ext U
  simp only [Set.mem_ofPred_eq, morphismRestrict_comp]
  exact P.cancel_left_of_respectsIso (e.hom ∣_ (f ⁻¹ᵁ U)) (f ∣_ U)

/-- The largest open of the target depends only on the cartesian square, not on the chosen
model of the fibre product. -/
theorem largestTargetOpen_eq_of_isPullback_snd (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y Z W : Scheme.{u}} {fst : X ⟶ Y} {snd : X ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g) :
    largestTargetOpen P snd = largestTargetOpen P (pullback.snd f g) := by
  have : HasPullback f g := h.hasPullback
  simpa [h.isoPullback_hom_snd] using
    largestTargetOpen_precomp_iso P h.isoPullback (pullback.snd f g)

/-- **Stacks Project, Tag 03JC.** For a groupoid scheme whose source and target maps are
coverings for one of the five topologies, the largest open of the object scheme over which the
source map has a target-local property is invariant. -/
@[stacks 03JC]
theorem isInvariantOpen_largestTargetOpen_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (P Q : MorphismProperty Scheme.{u})
    (hQ : (Q = (@IsOpenImmersion : MorphismProperty Scheme.{u})) ∨ IsDescentMorphismClass Q)
    [P.IsLocalAtTarget (Scheme.precoverage Q)]
    (hs : Presieve.ofArrows (fun _ : Unit => G.arrows.left)
      (fun _ => G.source.left) ∈ Scheme.precoverage Q G.objects.left)
    (ht : Presieve.ofArrows (fun _ : Unit => G.arrows.left)
      (fun _ => G.target.left) ∈ Scheme.precoverage Q G.objects.left) :
    IsInvariantOpen G (largestTargetOpen P G.source.left) := by
  rw [Scheme.ofArrows_mem_precoverage_iff] at hs ht
  rcases hQ with hQ | hQ
  · subst Q
    have : IsOpenImmersion G.source.left := hs.2 ()
    have hrange : G.source.left.opensRange = ⊤ := by
      refine TopologicalSpace.Opens.ext ?_
      ext x
      exact ⟨fun _ ↦ trivial, fun _ ↦ let ⟨_, r, hr⟩ := hs.1 x; ⟨r, hr⟩⟩
    have : IsIso G.source.left :=
      isIso_of_isOpenImmersion_of_opensRange_eq_top G.source.left hrange
    have hsi : G.source.left ≫ G.identity.left = 𝟙 G.arrows.left :=
      (cancel_mono G.source.left).1 (by simp [Category.assoc, identity_left_comp_source_left G])
    have hst : G.source.left = G.target.left := calc
      G.source.left = G.source.left ≫ G.identity.left ≫ G.target.left := by
        simp [identity_left_comp_target_left G]
      _ = G.target.left := by simp [← Category.assoc, hsi]
    intro r hr
    simpa [hst] using hr
  · have hleft : IsPullback (pullback.fst G.source G.target).left
        (pullback.snd G.source G.target).left G.source.left G.target.left :=
      (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
    have hright : IsPullback G.comp.left (pullback.snd G.source G.target).left
        G.source.left G.source.left :=
      (GroupoidScheme.comp_source_isPullback G).map (Over.forget S)
    have hpreimage :
        G.target.left ⁻¹ᵁ largestTargetOpen P G.source.left =
          G.source.left ⁻¹ᵁ largestTargetOpen P G.source.left := by
      rw [← largestTargetOpen_baseChange P Q hQ _ _ (ht.2 ()),
        ← largestTargetOpen_baseChange P Q hQ _ _ (hs.2 ())]
      exact (largestTargetOpen_eq_of_isPullback_snd P hleft).symm.trans
        (largestTargetOpen_eq_of_isPullback_snd P hright)
    intro r hr
    have hr' : r ∈ G.source.left ⁻¹ᵁ largestTargetOpen P G.source.left := by simpa using hr
    rw [← hpreimage] at hr'
    simpa using hr'

end AlgebraicGeometry

end
