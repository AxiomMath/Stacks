module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications

/-!
# The fibre square of a morphism over a subspace it is an isomorphism over

Let `f : V ⟶ W` be a morphism of presheaves on the big fppf site of `S` and let `T` be a
subfunctor of `W` such that the base change `f⁻¹T ⟶ T` is an isomorphism. Then the part of the
fibre square `V ×_W V` lying over `T` is exactly the diagonal: a section of `V ×_W V` whose
image in `W` is a section of `T` has its two projections equal.

## Main results

* `AlgebraicGeometry.Space.mono_preimage_ι_comp`: the restriction of `f` to `f⁻¹T` is a
  monomorphism.
* `AlgebraicGeometry.Space.eq_of_comp_eq_of_range_le`: two morphisms to `V` which agree in `W`
  and whose common composite lands in `T` are equal.
* `AlgebraicGeometry.Space.fst_eq_snd_of_range_le` and
  `AlgebraicGeometry.Space.eq_diagonal_of_range_le`: a morphism into `V ×_W V` lying over `T`
  has equal projections, and is the diagonal of its first projection.
* `AlgebraicGeometry.Space.isPullback_diagonal_fromPreimage`: the restricted diagonal
  `f⁻¹T ⟶ V ×_W V` and the base change `f⁻¹T ⟶ T` present `f⁻¹T` as the fibre product
  `(V ×_W V) ×_W T`.
* `AlgebraicGeometry.Space.preimage_fst_comp_eq_range_diagonal`: the subfunctor of `V ×_W V`
  lying over `T` is the range of the diagonal restricted to `f⁻¹T`.
* `AlgebraicGeometry.Space.le_preimage_openComplement_of_disjoint_diagonal`: a subfunctor of
  `V ×_W V` disjoint from that diagonal lies over the open complement of `T`.

## Implementation notes

`f⁻¹T` is `CategoryTheory.Subfunctor.preimage` and the base change `f⁻¹T ⟶ T` is
`CategoryTheory.Subfunctor.fromPreimage`, whose square over `f` is a fibre product by
`CategoryTheory.Subfunctor.isPullback_fromPreimage`; so the hypothesis of this file is
`IsIso (T.fromPreimage f)`.

Everything rests on one observation: the inclusion of `T` is a monomorphism, hence so is the
composite `f⁻¹T ⟶ T ⟶ W`, which is the restriction of `f` to `f⁻¹T` by
`CategoryTheory.Subfunctor.fromPreimage_ι`. Two sections of `V` over a section of `T` are
therefore equal, and a section of the fibre square over `T` is the diagonal of its first
projection.

`T` is an arbitrary subfunctor: neither closedness of `T` nor any property of `f` beyond the
assumed invertibility of `f⁻¹T ⟶ T` is used. Statements are phrased for morphisms out of an
arbitrary presheaf rather than for sections, so no Yoneda bookkeeping is needed; the
subfunctor form `AlgebraicGeometry.Space.preimage_fst_comp_eq_range_diagonal` is the one place
where sections are converted to morphisms, via `CategoryTheory.yonedaEquiv`.

This is the step `U ×_W T = ∅` of the proof of Stacks 0BGY, where `U` is the complement of the
diagonal in `V ×_W V` for a separated étale `f`: once the part of `V ×_W V` over `T` is known
to be the diagonal, `U` is disjoint from it, so both projections `U ⟶ V` land over the open
complement of `T`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism to `V` lands in the preimage of `T` exactly when its composite with `f` lands
in `T`. -/
private theorem range_le_preimage_iff {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W)
    (T : Subfunctor W) (v : P ⟶ V) :
    Subfunctor.range v ≤ T.preimage f ↔ Subfunctor.range (v ≫ f) ≤ T := by
  rw [Subfunctor.range_comp, Subfunctor.image_le_iff]

/-- The restriction of `f` to the preimage of `T` is a monomorphism, because it is the
inclusion of `T` precomposed with the isomorphism `f⁻¹T ⟶ T`. -/
theorem mono_preimage_ι_comp (f : V ⟶ W) (T : Subfunctor W)
    (hT : IsIso (T.fromPreimage f)) : Mono ((T.preimage f).ι ≫ f) := by
  rw [← T.fromPreimage_ι f]
  infer_instance

/-- Two morphisms to `V` which become equal in `W` and whose common composite lands in `T`
are equal: the restriction of `f` to `f⁻¹T` is a monomorphism. -/
theorem eq_of_comp_eq_of_range_le {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W)
    (T : Subfunctor W) (hT : IsIso (T.fromPreimage f)) {v₁ v₂ : P ⟶ V}
    (hcomp : v₁ ≫ f = v₂ ≫ f) (hle : Subfunctor.range (v₁ ≫ f) ≤ T) : v₁ = v₂ := by
  have h₁ : Subfunctor.range v₁ ≤ T.preimage f :=
    (range_le_preimage_iff B S hS f T v₁).2 hle
  have h₂ : Subfunctor.range v₂ ≤ T.preimage f :=
    (range_le_preimage_iff B S hS f T v₂).2 (hcomp ▸ hle)
  have key : Subfunctor.lift v₁ h₁ ≫ ((T.preimage f).ι ≫ f)
      = Subfunctor.lift v₂ h₂ ≫ ((T.preimage f).ι ≫ f) := by
    rw [← Category.assoc, Subfunctor.lift_ι, ← Category.assoc, Subfunctor.lift_ι]
    exact hcomp
  rw [← Subfunctor.lift_ι v₁ h₁, ← Subfunctor.lift_ι v₂ h₂,
    (mono_preimage_ι_comp B S hS f T hT).right_cancellation _ _ key]

/-- A morphism into the fibre square of `f` whose image in `W` lands in `T` has its two
projections equal: over `T` the fibre square of `f` is the diagonal. -/
theorem fst_eq_snd_of_range_le {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W)
    (T : Subfunctor W) (hT : IsIso (T.fromPreimage f)) (q : P ⟶ pullback f f)
    (hq : Subfunctor.range (q ≫ pullback.fst f f ≫ f) ≤ T) :
    q ≫ pullback.fst f f = q ≫ pullback.snd f f := by
  refine eq_of_comp_eq_of_range_le B S hS f T hT ?_ ?_
  · rw [Category.assoc, Category.assoc, ← pullback.condition]
  · rw [Category.assoc]
    exact hq

/-- A morphism into the fibre square of `f` whose image in `W` lands in `T` is the diagonal of
its first projection. -/
theorem eq_diagonal_of_range_le {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W)
    (T : Subfunctor W) (hT : IsIso (T.fromPreimage f)) (q : P ⟶ pullback f f)
    (hq : Subfunctor.range (q ≫ pullback.fst f f ≫ f) ≤ T) :
    (q ≫ pullback.fst f f) ≫ pullback.diagonal f = q := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    exact fst_eq_snd_of_range_le B S hS f T hT q hq

/-- The restricted diagonal, followed by the structure morphism of the fibre square, is the
restriction of `f` to the preimage of `T`. -/
private theorem diagonal_preimage_comp (f : V ⟶ W) (T : Subfunctor W) :
    ((T.preimage f).ι ≫ pullback.diagonal f) ≫ (pullback.fst f f ≫ f)
      = T.fromPreimage f ≫ T.ι := by
  rw [T.fromPreimage_ι f, Category.assoc, pullback.diagonal_fst_assoc]

/-- The restricted diagonal `f⁻¹T ⟶ V ×_W V` and the base change `f⁻¹T ⟶ T` exhibit `f⁻¹T` as
the fibre product `(V ×_W V) ×_W T`: the part of the fibre square of `f` lying over `T` is the
diagonal. -/
theorem isPullback_diagonal_fromPreimage (f : V ⟶ W) (T : Subfunctor W)
    (hT : IsIso (T.fromPreimage f)) :
    IsPullback ((T.preimage f).ι ≫ pullback.diagonal f) (T.fromPreimage f)
      (pullback.fst f f ≫ f) T.ι := by
  have hw := diagonal_preimage_comp B S hS f T
  have hran : ∀ s : PullbackCone (pullback.fst f f ≫ f) T.ι,
      Subfunctor.range (s.fst ≫ pullback.fst f f ≫ f) ≤ T := fun s => by
    rw [s.condition]
    exact le_of_le_of_eq (Subfunctor.range_comp_le s.snd T.ι) (Subfunctor.range_ι T)
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => Subfunctor.lift (s.fst ≫ pullback.fst f f)
      ((range_le_preimage_iff B S hS f T _).2 (hran s))) (fun s => ?_) (fun s => ?_)
    (fun s m hm _ => ?_))
  · rw [← Category.assoc, Subfunctor.lift_ι]
    exact eq_diagonal_of_range_le B S hS f T hT s.fst (hran s)
  · rw [← cancel_mono T.ι, Category.assoc, T.fromPreimage_ι f, Subfunctor.lift_ι_assoc,
      Category.assoc, s.condition]
  · have hmono : Mono ((T.preimage f).ι ≫ pullback.diagonal f) := mono_comp _ _
    refine hmono.right_cancellation _ _ ?_
    rw [hm, ← Category.assoc, Subfunctor.lift_ι]
    exact (eq_diagonal_of_range_le B S hS f T hT s.fst (hran s)).symm

/-- The morphism out of a representable presheaf named by a section of a subfunctor lands in
that subfunctor. -/
private theorem range_yonedaEquiv_symm_le {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (G : Subfunctor F) {A : BigFppfOver B S hS} {x : F.obj (op A)} (hx : x ∈ G.obj (op A)) :
    Subfunctor.range (yonedaEquiv.symm x) ≤ G := by
  rintro C y ⟨g, rfl⟩
  exact G.map g.op hx

/-- Precomposing the morphism named by a section with a morphism of presheaves names the
image of that section. -/
private theorem yonedaEquiv_symm_comp_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    {A : BigFppfOver B S hS} (x : F.obj (op A)) :
    yonedaEquiv.symm x ≫ p = yonedaEquiv.symm (p.app (op A) x) :=
  yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply])

/-- The subfunctor of the fibre square of `f` lying over `T` is the range of the diagonal
restricted to `f⁻¹T`; so a subfunctor of `V ×_W V` disjoint from the diagonal is disjoint from
the part lying over `T`. -/
theorem preimage_fst_comp_eq_range_diagonal (f : V ⟶ W) (T : Subfunctor W)
    (hT : IsIso (T.fromPreimage f)) :
    T.preimage (pullback.fst f f ≫ f)
      = Subfunctor.range ((T.preimage f).ι ≫ pullback.diagonal f) := by
  refine le_antisymm (fun A x hx => ?_) ?_
  · have hq : Subfunctor.range (yonedaEquiv.symm x ≫ pullback.fst f f ≫ f) ≤ T := by
      rw [yonedaEquiv_symm_comp_eq]
      exact range_yonedaEquiv_symm_le B S hS T hx
    have hle : Subfunctor.range (yonedaEquiv.symm x ≫ pullback.fst f f) ≤ T.preimage f :=
      (range_le_preimage_iff B S hS f T _).2 (by rw [Category.assoc]; exact hq)
    refine ⟨yonedaEquiv (Subfunctor.lift _ hle), ?_⟩
    rw [← yonedaEquiv_comp, ← Category.assoc, Subfunctor.lift_ι,
      eq_diagonal_of_range_le B S hS f T hT _ hq, Equiv.apply_symm_apply]
  · rw [range_le_preimage_iff, diagonal_preimage_comp]
    exact le_of_le_of_eq (Subfunctor.range_comp_le (T.fromPreimage f) T.ι)
      (Subfunctor.range_ι T)

/-- A subfunctor of the fibre square of `f` disjoint from the diagonal over `f⁻¹T` lies over
the open complement of `T`. Since `pullback.fst f f ≫ f = pullback.snd f f ≫ f`, the same
statement holds verbatim for the second projection. -/
theorem le_preimage_openComplement_of_disjoint_diagonal (f : V ⟶ W) (T : Subfunctor W)
    (hT : IsIso (T.fromPreimage f)) (U : Subfunctor (pullback f f))
    (hU : U ⊓ Subfunctor.range ((T.preimage f).ι ≫ pullback.diagonal f) = ⊥) :
    U ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f) := by
  intro A x hx A' a ha
  have hdiag : (pullback f f).map a x
      ∈ (Subfunctor.range ((T.preimage f).ι ≫ pullback.diagonal f)).obj A' := by
    rw [← preimage_fst_comp_eq_range_diagonal B S hS f T hT]
    show (pullback.fst f f ≫ f).app A' ((pullback f f).map a x) ∈ T.obj A'
    rw [NatTrans.naturality_apply]
    exact ha
  have hbot : (pullback f f).map a x ∈ (⊥ : Subfunctor (pullback f f)).obj A' := by
    rw [← hU]
    exact ⟨U.map a hx, hdiag⟩
  simp at hbot

end AlgebraicGeometry.Space

end
