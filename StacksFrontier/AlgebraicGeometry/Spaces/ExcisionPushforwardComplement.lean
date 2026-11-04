module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforward

/-!
# The presheaf of pairs is unchanged over the open complement

Let `f : V ⟶ W` and `h : Y ⟶ V` be morphisms of algebraic spaces over a scheme `S`, let `W₀` be
a subfunctor of `W` and suppose that `h` becomes an isomorphism over `V⁰ = f^{-1}W₀`, that is,
that `Y ⟶ V` is a modification of `V` outside `V⁰`.

Then the presheaf of pairs of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforward.lean` is unchanged over `W₀`: its
base change along the inclusion of `W₀` is an isomorphism. This is the step
`X ×_{g, W} W⁰ = W⁰` of the proof of Stacks 0BGY. Over `W₀` the second component of a pair is
forced, because a morphism to `V` landing in `V⁰` has exactly one lift to `Y`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_lift_of_range_le`: a morphism to `V` whose image lies in
  `V⁰` has exactly one lift along `h`.
* `AlgebraicGeometry.Space.excisionSpace_hom_ext_of_range_le`: two morphisms to the presheaf of
  pairs which agree over `W` and lie over `W₀` are equal.
* `AlgebraicGeometry.Space.isIso_pullback_snd_excisionProj`: **the step `X ×_{g, W} W⁰ = W⁰`.**

## Implementation notes

Existence and uniqueness of the lift are read off the assumed invertibility of
`CategoryTheory.Limits.pullback.snd h V₀.ι` directly, rather than through the terminality of the
base change in the slice category: the inverse of that projection composed with the first
projection *is* the lift, and two lifts give two morphisms into the fibre product with the same
second component, hence are equal because the second projection is a monomorphism.

Uniqueness of a section of the presheaf of pairs over a section of `W₀` is proved by
destructing the two pairs and substituting the equality of their first components, which brings
the two second components into the same type; the dependence of the type of the second component
on the first is what makes this the only available route.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting a morphism which lands in the invariance locus -/

section Lift

variable {V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : Y ⟶ V) (V₀ : Subfunctor V)
  (hiso : IsIso (pullback.snd h V₀.ι)) {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : P ⟶ V)
  (hc : Subfunctor.range c ≤ V₀)

include hiso hc in
/-- Two lifts along `h` of a morphism landing in the invariance locus are equal. -/
theorem lift_unique_of_range_le {b₁ b₂ : P ⟶ Y} (h₁ : b₁ ≫ h = c) (h₂ : b₂ ≫ h = c) :
    b₁ = b₂ := by
  have _ := hiso
  have e₁ : b₁ ≫ h = Subfunctor.lift c hc ≫ V₀.ι := by rw [Subfunctor.lift_ι, h₁]
  have e₂ : b₂ ≫ h = Subfunctor.lift c hc ≫ V₀.ι := by rw [Subfunctor.lift_ι, h₂]
  have hqeq : pullback.lift b₁ (Subfunctor.lift c hc) e₁ =
      pullback.lift b₂ (Subfunctor.lift c hc) e₂ :=
    (cancel_mono (pullback.snd h V₀.ι)).1 (by simp only [pullback.lift_snd])
  rw [← pullback.lift_fst b₁ (Subfunctor.lift c hc) e₁, hqeq, pullback.lift_fst]

include hiso hc in
/-- **A morphism to `V` whose image lies in the invariance locus has exactly one lift along
`h`.** -/
theorem existsUnique_lift_of_range_le : ∃! b : P ⟶ Y, b ≫ h = c := by
  have _ := hiso
  refine ⟨Subfunctor.lift c hc ≫ inv (pullback.snd h V₀.ι) ≫ pullback.fst h V₀.ι, ?_,
    fun b hb => lift_unique_of_range_le B S hS h V₀ hiso c hc hb ?_⟩ <;>
  simp only [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Subfunctor.lift_ι]

end Lift

/-! ### The image of a section -/

/-- A morphism out of a representable presheaf whose universal section lies in a subfunctor has
its whole image in that subfunctor. -/
theorem range_le_of_yonedaEquiv_mem {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F)
    {A : (BigFppfOver B S hS)ᵒᵖ} (ψ : yoneda.obj A.unop ⟶ F)
    (hψ : yonedaEquiv ψ ∈ G.obj A) : Subfunctor.range ψ ≤ G := by
  intro C z hz
  obtain ⟨k, rfl⟩ := hz
  rw [← map_yonedaEquiv ψ k]
  exact G.map k.op hψ

/-! ### The image of the second projection of a fibre product -/

variable {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)

/-- The second projection of the fibre product of a morphism landing in `W₀` with `f` lands in
the preimage of `W₀`. -/
theorem range_pullback_snd_le_preimage_of_range_le {W₀ : Subfunctor W}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : P ⟶ W) (hw : Subfunctor.range w ≤ W₀) :
    Subfunctor.range (pullback.snd w f) ≤ W₀.preimage f := by
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, ← pullback.condition]
  exact (Subfunctor.range_comp_le _ _).trans hw

/-! ### Uniqueness of a pair over the open complement -/

variable (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y) (W₀ : Subfunctor W)
  (hiso : IsIso (pullback.snd h (W₀.preimage f).ι))

include hiso in
/-- **Over `W₀` the second component of a pair is forced.** Two pairs with the same first
component, that component landing in `W₀`, are equal. -/
theorem relativeMorphism_ext_of_range_le
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q₁ q₂ : RelativeMorphism B S hS V Y W f (h ≫ f) T}
    (hq₁ : q₁.morphism ≫ h = pullback.snd q₁.base f)
    (hq₂ : q₂.morphism ≫ h = pullback.snd q₂.base f)
    (hbase : q₁.base = q₂.base) (hle : Subfunctor.range q₁.base ≤ W₀) : q₁ = q₂ := by
  obtain ⟨b₁, m₁, c₁⟩ := q₁
  obtain ⟨b₂, m₂, c₂⟩ := q₂
  cases hbase
  refine RelativeMorphism.ext_of_heq rfl (heq_of_eq ?_)
  exact lift_unique_of_range_le B S hS h (W₀.preimage f) hiso (pullback.snd b₁ f)
    (range_pullback_snd_le_preimage_of_range_le B S hS f b₁ hle) hq₁ hq₂

include hiso in
/-- **Two morphisms to the presheaf of pairs which agree over `W` and lie over `W₀` are
equal.** -/
theorem excisionSpace_hom_ext_of_range_le {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u₁ u₂ : P ⟶ excisionSpace B S hS f h hV hW hY)
    (huw : u₁ ≫ excisionProj B S hS f h hV hW hY = u₂ ≫ excisionProj B S hS f h hV hW hY)
    (hle : Subfunctor.range (u₁ ≫ excisionProj B S hS f h hV hW hY) ≤ W₀) : u₁ = u₂ := by
  ext A t
  refine Subtype.ext ((excisionBaseEquiv B S hS f h hV hW hY A).injective ?_)
  refine relativeMorphism_ext_of_range_le B S hS f h W₀ hiso
    ((mem_excisionSub_iff B S hS f h hV hW hY _).1 (u₁.app A t).2)
    ((mem_excisionSub_iff B S hS f h hV hW hY _).1 (u₂.app A t).2) ?_ ?_
  · exact yonedaEquiv.injective (ConcreteCategory.congr_hom (NatTrans.congr_app huw A) t)
  · exact range_le_of_yonedaEquiv_mem B S hS W₀ _ (hle A ⟨t, rfl⟩)

/-! ### The presheaf of pairs over the open complement -/

include hiso in
/-- The tautological lift over `W₀`: the second projection of `W₀ ×_W V` lifts to `Y`. -/
theorem exists_lift_pullback_snd_ι :
    ∃ b : pullback W₀.ι f ⟶ Y, b ≫ h = pullback.snd W₀.ι f :=
  let e := existsUnique_lift_of_range_le B S hS h (W₀.preimage f) hiso
    (pullback.snd W₀.ι f)
    (range_pullback_snd_le_preimage_of_range_le B S hS f W₀.ι (Subfunctor.range_ι W₀).le)
  ⟨e.choose, e.choose_spec.1⟩

/-- The section of the presheaf of pairs over `W₀`. -/
noncomputable def excisionComplementSection :
    W₀.toFunctor ⟶ excisionSpace B S hS f h hV hW hY :=
  excisionDesc B S hS f h hV hW hY W₀.ι
    (exists_lift_pullback_snd_ι B S hS f h W₀ hiso).choose
    (exists_lift_pullback_snd_ι B S hS f h W₀ hiso).choose_spec

/-- The section of the presheaf of pairs over `W₀` lies over the inclusion of `W₀`. -/
theorem excisionComplementSection_comp_excisionProj :
    excisionComplementSection B S hS f h hV hW hY W₀ hiso ≫
        excisionProj B S hS f h hV hW hY = W₀.ι :=
  excisionDesc_comp_excisionProj B S hS f h hV hW hY _ _ _

include hiso in
/-- **The step `X ×_{g, W} W⁰ = W⁰` of the proof of Stacks 0BGY.** The presheaf of pairs is
unchanged over `W₀`: over a section of `W₀` the second component of a pair is the unique lift
of the tautological morphism, so the base change of the projection along the inclusion of `W₀`
is an isomorphism. -/
theorem isIso_pullback_snd_excisionProj :
    IsIso (pullback.snd (excisionProj B S hS f h hV hW hY) W₀.ι) := by
  have hdesc := excisionComplementSection_comp_excisionProj B S hS f h hV hW hY W₀ hiso
  refine ⟨⟨pullback.lift (excisionComplementSection B S hS f h hV hW hY W₀ hiso)
    (𝟙 W₀.toFunctor) (by rw [hdesc, Category.id_comp]), ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine excisionSpace_hom_ext_of_range_le B S hS f h hV hW hY W₀ hiso _ _ ?_ ?_
      · rw [Category.assoc, hdesc, pullback.condition]
      · rw [Category.assoc, hdesc]
        exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι W₀).le
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

end AlgebraicGeometry.Space

end
