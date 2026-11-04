module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Glueing two schemes along an open: the pushout of a span of open immersions

A glueing datum with two charts is the same thing as a span of open immersions
`X ⟵ W ⟶ Y`: the prescribed overlap is the image of `W` in either chart and the prescribed
transition isomorphism is the one induced by the span. This file describes the resulting scheme,
its two charts and the universal property.

The scheme itself is `CategoryTheory.Limits.pushout f g`, which exists because
`AlgebraicGeometry.Scheme.IsLocallyDirected` makes `CategoryTheory.Limits.span f g` a locally
directed diagram of open immersions, whence `HasPushout f g` and `IsOpenImmersion` for each of
the two legs. Conversely, a scheme covered by *two* opens is the pushout of the span formed by
their intersection.

## Main results

* `AlgebraicGeometry.isPushout_opens_ι_of_sup_eq_top`: if the opens `U, V` of a scheme `S`
  satisfy `U ⊔ V = ⊤`, then the square formed by `U ⊓ V ⟶ U`, `U ⊓ V ⟶ V` and the two
  inclusions `U.ι`, `V.ι` is a pushout square.
* `AlgebraicGeometry.existsUnique_comp_ι_eq_of_sup_eq_top`: a morphism out of `S` is the same
  thing as a pair of morphisms out of `U` and `V` that agree on `U ⊓ V`.
* `AlgebraicGeometry.opensRange_pushout_inl_sup_opensRange_pushout_inr`: the two charts of the
  pushout of a span of open immersions cover it.
* `AlgebraicGeometry.preimage_opensRange_pushout_inl`: inside the second chart, the overlap of
  the two charts is exactly the image of the span's vertex.
* `AlgebraicGeometry.isPullback_pushout_inl_inr`: equivalently, the pushout square of a span of
  open immersions is also cartesian.

## Implementation notes

The translation between the two shapes is
`AlgebraicGeometry.pullback_ι_ι_comp_eq_of_homOfLE_comp_eq` and its flip: the compatibility
condition that `AlgebraicGeometry.Scheme.Cover.glueMorphisms` asks for is phrased over
`pullback U.ι V.ι`, whereas a span of opens of a single scheme has the honest intersection
`U ⊓ V` as its vertex. Mathlib's `AlgebraicGeometry.isPullback_opens_inf` identifies the two,
and `CategoryTheory.IsPullback.isoPullback` turns that identification into the isomorphism that
cancels.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two morphisms that agree on a pullback square `P` of `f` and `g` agree on the categorical
pullback of `f` along `g`. -/
private lemma pullback_comp_eq_of_isPullback {P A B S T : Scheme.{u}} {f : A ⟶ S} {g : B ⟶ S}
    {p : P ⟶ A} {q : P ⟶ B} (hP : IsPullback p q f g) {a : A ⟶ T} {b : B ⟶ T}
    (w : p ≫ a = q ≫ b) : pullback.fst f g ≫ a = pullback.snd f g ≫ b := by
  rw [← cancel_epi hP.isoPullback.hom, ← Category.assoc, ← Category.assoc,
    hP.isoPullback_hom_fst, hP.isoPullback_hom_snd]
  exact w

/-- Two morphisms out of opens `U` and `V` of a scheme `S` that agree on `U ⊓ V` agree on the
categorical pullback of `U.ι` along `V.ι`. -/
lemma pullback_ι_ι_comp_eq_of_homOfLE_comp_eq {S T : Scheme.{u}} {U V : S.Opens}
    {a : U.toScheme ⟶ T} {b : V.toScheme ⟶ T}
    (w : S.homOfLE inf_le_left ≫ a = S.homOfLE inf_le_right ≫ b) :
    pullback.fst U.ι V.ι ≫ a = pullback.snd U.ι V.ι ≫ b :=
  pullback_comp_eq_of_isPullback (isPullback_opens_inf U V) w

/-- The version of `AlgebraicGeometry.pullback_ι_ι_comp_eq_of_homOfLE_comp_eq` for the pullback
taken in the other order. -/
lemma pullback_ι_ι_comp_eq_of_homOfLE_comp_eq_flip {S T : Scheme.{u}} {U V : S.Opens}
    {a : U.toScheme ⟶ T} {b : V.toScheme ⟶ T}
    (w : S.homOfLE inf_le_left ≫ a = S.homOfLE inf_le_right ≫ b) :
    pullback.fst V.ι U.ι ≫ b = pullback.snd V.ι U.ι ≫ a :=
  pullback_comp_eq_of_isPullback (isPullback_opens_inf U V).flip w.symm

/-- A scheme covered by two opens is glued from them: the square formed by the two inclusions of
the intersection and the two inclusions into the ambient scheme is a pushout square. -/
@[stacks 01JA "the two-chart glueing as a pushout square of schemes"]
theorem isPushout_opens_ι_of_sup_eq_top {S : Scheme.{u}} {U V : S.Opens} (h : U ⊔ V = ⊤) :
    IsPushout (S.homOfLE inf_le_left) (S.homOfLE inf_le_right) U.ι V.ι := by
  have hsq : S.homOfLE (inf_le_left (a := U) (b := V)) ≫ U.ι
      = S.homOfLE (inf_le_right (a := U) (b := V)) ≫ V.ι := by
    rw [S.homOfLE_ι, S.homOfLE_ι]
  have hcover : TopologicalSpace.IsOpenCover (fun b : Bool ↦ cond b U V) := by
    simpa [TopologicalSpace.IsOpenCover, iSup_bool_eq] using h
  let 𝒰 := S.openCoverOfIsOpenCover _ hcover
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_)
  · intro s
    refine 𝒰.glueMorphisms (fun b ↦ b.rec s.inr s.inl) ?_
    intro x y
    cases x <;> cases y
    · exact congrArg (· ≫ s.inr) (fst_eq_snd_of_mono_eq V.ι)
    · show pullback.fst V.ι U.ι ≫ s.inr = pullback.snd V.ι U.ι ≫ s.inl
      exact pullback_ι_ι_comp_eq_of_homOfLE_comp_eq_flip s.condition
    · show pullback.fst U.ι V.ι ≫ s.inl = pullback.snd U.ι V.ι ≫ s.inr
      exact pullback_ι_ι_comp_eq_of_homOfLE_comp_eq s.condition
    · exact congrArg (· ≫ s.inl) (fst_eq_snd_of_mono_eq U.ι)
  · exact fun s ↦ 𝒰.ι_glueMorphisms _ _ true
  · exact fun s ↦ 𝒰.ι_glueMorphisms _ _ false
  · intro s m h₁ h₂
    refine 𝒰.hom_ext _ _ fun b ↦ ?_
    rw [𝒰.ι_glueMorphisms]
    cases b
    exacts [h₂, h₁]

/-- The mapping property for morphisms out of a glueing with two charts: if the opens `U, V` of a
scheme `S` satisfy `U ⊔ V = ⊤`, then a morphism out of `S` is the same thing as a pair of
morphisms out of `U` and out of `V` agreeing on `U ⊓ V`. -/
@[stacks 01JA "the two-chart case of the mapping property for morphisms out of a glueing"]
theorem existsUnique_comp_ι_eq_of_sup_eq_top {S T : Scheme.{u}} {U V : S.Opens}
    (h : U ⊔ V = ⊤) {a : U.toScheme ⟶ T} {b : V.toScheme ⟶ T}
    (w : S.homOfLE inf_le_left ≫ a = S.homOfLE inf_le_right ≫ b) :
    ∃! m : S ⟶ T, U.ι ≫ m = a ∧ V.ι ≫ m = b := by
  refine ⟨(isPushout_opens_ι_of_sup_eq_top h).desc a b w,
    ⟨IsPushout.inl_desc .., IsPushout.inr_desc ..⟩, fun m hm ↦ ?_⟩
  exact (isPushout_opens_ι_of_sup_eq_top h).hom_ext
    (hm.1.trans (IsPushout.inl_desc ..).symm) (hm.2.trans (IsPushout.inr_desc ..).symm)

section Span

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- The two charts of the scheme obtained by glueing `X` and `Y` along a span of open immersions
cover it. -/
@[stacks 01JA "the two-chart case of part (1): the charts cover the glued scheme"]
theorem opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  obtain (_ | (_ | _)) := i
  · refine Or.inl ⟨f xi, ?_⟩
    have hw : f ≫ pushout.inl f g = colimit.ι (span f g) WalkingSpan.zero := by
      simpa using colimit.w (span f g) WalkingSpan.Hom.fst
    rw [← hxi, ← Scheme.Hom.comp_apply, hw]
  · exact Or.inl ⟨xi, hxi⟩
  · exact Or.inr ⟨xi, hxi⟩

/-- Inside the second chart of the scheme obtained by glueing `X` and `Y` along a span of open
immersions, the overlap with the first chart is exactly the image of the span's vertex. -/
@[stacks 01JA "the two-chart case of part (2): the overlap of the two charts"]
theorem preimage_opensRange_pushout_inl :
    (pushout.inr f g) ⁻¹ᵁ (pushout.inl f g).opensRange = g.opensRange := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨k, fi, fj, z, hz₁, hz₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp hx
    cases fi with
    | id => cases fj
    | init j => cases fj with
      | init j' => exact ⟨z, by simpa using hz₂⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f z, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]⟩

/-- The pushout square of a span of open immersions of schemes is also cartesian: the span's
vertex is the intersection of the two charts of the glued scheme. -/
@[stacks 01JA "the two-chart case of part (2), as a cartesian square"]
theorem isPullback_pushout_inl_inr :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) :=
  IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    pushout.condition.symm (preimage_opensRange_pushout_inl f g)

end Span

end AlgebraicGeometry

end
