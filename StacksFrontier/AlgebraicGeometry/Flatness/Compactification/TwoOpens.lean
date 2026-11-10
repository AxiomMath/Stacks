module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformImage
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.CommonAdmissibleBlowups
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.IsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ProperExtension
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ProperSections
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ValuativeLifts
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBaseSeparated

/-!
# A compactification from two compactifiable opens with dense intersection

Let `S` be a Noetherian scheme, let `f : U ⟶ S` be separated and of finite type and let
`U = U₁ ∪ U₂` be a cover by two opens, each compactifiable over `S`, whose intersection is dense
in `U`. Then `U` is compactifiable over `S`.

## Main results

* `AlgebraicGeometry.exists_separated_boundary_blowups` is the first half of the construction:
  proper extensions of the two opens whose boundaries become disjoint after a further
  admissible blowup.
* `AlgebraicGeometry.hasCompactification_of_two_opens` is [Stacks, Tag 0F40].

## Implementation notes

The argument is the one of [Stacks, Tag 0F40]. Arrange the two compactifications `Uᵢ ⊆ Xᵢ` so
that `Uᵢ` is scheme-theoretically dense, and extend the inclusion `Uᵢ ⟶ U` to a proper
`ψᵢ : Vᵢ ⟶ U` on an open `Vᵢ` of a blowup of `Xᵢ` ([Stacks, Tag 0F3Z]). Writing `Zᵢ` for the
part of `Vᵢ` over the complement of `Uᵢ`, a further `Vᵢ`-admissible blowup ([Stacks, Tag 0F3V])
makes the closures of the two pieces of the boundary disjoint.

Next form `V₁₂ = V₁ ×_U V₂` and let `Z₁₂` be its scheme-theoretic image in `X₁ ×_S X₂`. The
first projection `Z₁₂ ⟶ X₁` is an isomorphism near the part of the boundary of `V₁` lying over
`U₂`, so [Stacks, Tag 0F3W] supplies a blowup after which that holds near the closure of that
part; combined with the disjointness upstairs this shows `Z₁₂` misses the product of the two
"opposite" boundary closures, which is the key emptiness. Identifying the image of the lifted
section with a strict transform is [Stacks, Tag 0F3Y]; the two constructions of the blowup are
matched by `Stacks.Blowup.strictTransformIso`.

Gluing `U` to `Xᵢ` minus the closure of the opposite boundary gives separated finite-type
`Wᵢ ⟶ S` containing `U` as a dense open; the gluing is `AlgebraicGeometry.SpanGlue.desc` of the
span of the two open immersions, whose finiteness and separatedness properties are
`AlgebraicGeometry.SpanGlue.locallyOfFiniteType_desc`,
`AlgebraicGeometry.SpanGlue.compactSpace_glued` and
`AlgebraicGeometry.SpanGlue.isSeparated_desc`. Then [Stacks, Tag 0F3X] puts admissible blowups
of the `Wᵢ` inside one separated finite-type `W ⟶ S`. The emptiness above says that for a
valuation ring over `S` with fraction field mapping into `U₁ ∩ U₂`, at least one of the two
limits avoids its boundary, hence lifts to `Wᵢ` and therefore to `W`; so `W ⟶ S` is universally
closed by the valuative criterion, and `U` is open and scheme-theoretically dense in it.

## References

* [Stacks Project, Tag 0F40](https://stacks.math.columbia.edu/tag/0F40)
* [Stacks Project, Tag 0F3Z](https://stacks.math.columbia.edu/tag/0F3Z)
* [Stacks Project, Tag 0F3Y](https://stacks.math.columbia.edu/tag/0F3Y)
* [Stacks Project, Tag 0F3X](https://stacks.math.columbia.edu/tag/0F3X)
* [Stacks Project, Tag 0F3W](https://stacks.math.columbia.edu/tag/0F3W)
* [Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V)
* [Stacks Project, Tag 0F3U](https://stacks.math.columbia.edu/tag/0F3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Compactification

universe u

namespace AlgebraicGeometry

/-- **Proper extensions of the two opens with separated boundaries.** For each of the two
compactifications, [Stacks, Tag 0F3Z] gives a `Uᵢ`-admissible blowup of it containing an open
subscheme mapping properly to `U` and extending the inclusion of `Uᵢ`, and [Stacks, Tag 0F3V]
then gives a further admissible blowup on which the closures of the two pieces of the boundary
become disjoint. -/
theorem exists_separated_boundary_blowups
    {S U : Scheme.{u}} [IsNoetherian S] [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U]
    (f : U ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (U₁ U₂ : U.Opens) [QuasiCompact U₁.ι] [QuasiCompact U₂.ι]
    (hcover : U₁ ⊔ U₂ = ⊤)
    (j₁ : CompactificationOf (Over.mk (U₁.ι ≫ f)))
    (j₂ : CompactificationOf (Over.mk (U₂.ι ≫ f))) :
    ∃ (Y₁ Y₂ Y₁' Y₂' : Scheme.{u})
      (b₁ : Y₁ ⟶ j₁.space) (b₂ : Y₂ ⟶ j₂.space)
      (c₁ : Y₁' ⟶ Y₁) (c₂ : Y₂' ⟶ Y₂)
      (V₁ : Y₁.Opens) (V₂ : Y₂.Opens)
      (e₁ : U₁.toScheme ⟶ V₁.toScheme) (e₂ : U₂.toScheme ⟶ V₂.toScheme)
      (p₁ : V₁.toScheme ⟶ U) (p₂ : V₂.toScheme ⟶ U),
      Stacks.Blowup.IsAdmissibleBlowup j₁.immersion.opensRange b₁ ∧
      IsProper b₁ ∧ IsOpenImmersion e₁ ∧
      Set.range (e₁ ≫ V₁.ι).base = (b₁ ⁻¹ᵁ j₁.immersion.opensRange : Y₁.Opens) ∧
      e₁ ≫ V₁.ι ≫ b₁ = j₁.immersion ∧
      IsProper p₁ ∧ e₁ ≫ p₁ = U₁.ι ∧ p₁ ≫ f = V₁.ι ≫ b₁ ≫ j₁.toBase ∧
      Stacks.Blowup.IsAdmissibleBlowup j₂.immersion.opensRange b₂ ∧
      IsProper b₂ ∧ IsOpenImmersion e₂ ∧
      Set.range (e₂ ≫ V₂.ι).base = (b₂ ⁻¹ᵁ j₂.immersion.opensRange : Y₂.Opens) ∧
      e₂ ≫ V₂.ι ≫ b₂ = j₂.immersion ∧
      IsProper p₂ ∧ e₂ ≫ p₂ = U₂.ι ∧ p₂ ≫ f = V₂.ι ≫ b₂ ≫ j₂.toBase ∧
      Stacks.Blowup.IsAdmissibleBlowup V₁ c₁ ∧
      Disjoint (closure (c₁.base ⁻¹' (V₁.ι.base '' (p₁.base ⁻¹' ((U₁ : Set U)ᶜ)))))
        (closure (c₁.base ⁻¹' (V₁.ι.base '' (p₁.base ⁻¹' ((U₂ : Set U)ᶜ))))) ∧
      Stacks.Blowup.IsAdmissibleBlowup V₂ c₂ ∧
      Disjoint (closure (c₂.base ⁻¹' (V₂.ι.base '' (p₂.base ⁻¹' ((U₁ : Set U)ᶜ)))))
        (closure (c₂.base ⁻¹' (V₂.ι.base '' (p₂.base ⁻¹' ((U₂ : Set U)ᶜ))))) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨Y₁, b₁, V₁, e₁, p₁, hb₁, he₁open, hrange₁, hcomm₁, hp₁, he₁, hbase₁⟩ :=
    exists_isAdmissibleBlowup_properExtension f U₁ j₁
  obtain ⟨Y₂, b₂, V₂, e₂, p₂, hb₂, he₂open, hrange₂, hcomm₂, hp₂, he₂, hbase₂⟩ :=
    exists_isAdmissibleBlowup_properExtension f U₂ j₂
  have : IsProper b₁ := isProper_of_isAdmissibleBlowup j₁.immersion.opensRange b₁ hb₁
  have : IsProper b₂ := isProper_of_isAdmissibleBlowup j₂.immersion.opensRange b₂ hb₂
  have : CompactSpace j₁.space := (quasiCompact_iff_compactSpace j₁.toBase).mp inferInstance
  have : CompactSpace j₂.space := (quasiCompact_iff_compactSpace j₂.toBase).mp inferInstance
  have : QuasiSeparatedSpace j₁.space := quasiSeparatedSpace_of_quasiSeparated j₁.toBase
  have : QuasiSeparatedSpace j₂.space := quasiSeparatedSpace_of_quasiSeparated j₂.toBase
  have : CompactSpace Y₁ := (quasiCompact_iff_compactSpace (b₁ ≫ j₁.toBase)).mp inferInstance
  have : CompactSpace Y₂ := (quasiCompact_iff_compactSpace (b₂ ≫ j₂.toBase)).mp inferInstance
  have : QuasiSeparatedSpace Y₁ := quasiSeparatedSpace_of_quasiSeparated (b₁ ≫ j₁.toBase)
  have : QuasiSeparatedSpace Y₂ := quasiSeparatedSpace_of_quasiSeparated (b₂ ≫ j₂.toBase)
  obtain ⟨Y₁', c₁, hc₁, hdisj₁⟩ :=
    blowup_separates_proper_preimages_of_open_complements (S := S) (U := U) (Y := Y₁)
      V₁ p₁ hp₁ U₁ U₂ hcover
  obtain ⟨Y₂', c₂, hc₂, hdisj₂⟩ :=
    blowup_separates_proper_preimages_of_open_complements (S := S) (U := U) (Y := Y₂)
      V₂ p₂ hp₂ U₁ U₂ hcover
  exact ⟨Y₁, Y₂, Y₁', Y₂', b₁, b₂, c₁, c₂, V₁, V₂, e₁, e₂, p₁, p₂,
    hb₁, inferInstance, he₁open, hrange₁, hcomm₁, hp₁, he₁, hbase₁,
    hb₂, inferInstance, he₂open, hrange₂, hcomm₂, hp₂, he₂, hbase₂,
    hc₁, hdisj₁, hc₂, hdisj₂⟩


/-- A proper extension `p : V ⟶ U` of the open `W ⊆ U` over `S`, trimmed to the open `T` of the
ambient scheme away from the closure of the boundary, gives a section `W ⟶ T` whose graph is a
closed immersion into the fibre product `U ×_S T`. -/
private theorem exists_closedImmersion_of_trimmed_section {S U Y : Scheme.{u}}
    (f : U ⟶ S) (q : Y ⟶ S) [IsSeparated q] (W : U.Opens) (V T : Y.Opens)
    (e : W.toScheme ⟶ V.toScheme) [IsOpenImmersion e]
    (p : V.toScheme ⟶ U) [IsProper p] (he : e ≫ p = W.ι) (h : p ≫ f = V.ι ≫ q)
    (hT : (T : Set Y) = (closure (V.ι.base '' (p.base ⁻¹' ((W : Set U)ᶜ))))ᶜ) :
    ∃ (g : W.toScheme ⟶ T.toScheme) (_ : IsOpenImmersion g) (_ : g ≫ T.ι = e ≫ V.ι)
      (hglue : W.ι ≫ f = g ≫ T.ι ≫ q), IsClosedImmersion (pullback.lift W.ι g hglue) := by
  have hsec := section_range_disjoint_boundary_closure W V e p he
  have hrange : Set.range (e ≫ V.ι).base ⊆ Set.range T.ι := fun x hx => by
    simpa [Scheme.Opens.range_ι, hT] using Set.disjoint_left.mp hsec hx
  obtain ⟨hET, hTW⟩ : Set.range e.base ⊆ Set.range (V.ι ⁻¹ᵁ T).ι ∧ V.ι ⁻¹ᵁ T ≤ p ⁻¹ᵁ W := by
    obtain rfl : T = ⟨_, isClosed_closure.isOpen_compl⟩ := SetLike.coe_injective hT
    exact ⟨(section_closedImmersion_away_from_boundary W V e p he hsec).1,
      open_compl_closure_boundary_le_preimage W V p⟩
  have hg := IsOpenImmersion.lift_fac _ _ hrange
  have hglue : W.ι ≫ f = IsOpenImmersion.lift T.ι _ hrange ≫ T.ι ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, ← h, ← Category.assoc, he]
  exact ⟨_, inferInstance, hg, hglue,
    section_closedImmersion_in_fiberProduct f q W V T e p he h _ hg hglue hET hTW⟩

/-- **Stacks Project, Tag 0F40.** A separated finite-type scheme over a Noetherian base has a
compactification as soon as it is covered by two compactifiable open subschemes whose
intersection is dense. -/
@[stacks 0F40]
theorem hasCompactification_of_two_opens
    {S U : Scheme.{u}} (f : U ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (U₁ U₂ : U.Opens) (hcover : U₁ ⊔ U₂ = ⊤)
    (hdense : Dense ((U₁ ⊓ U₂ : U.Opens) : Set U))
    (h₁ : HasCompactification (U₁.ι ≫ f)) (h₂ : HasCompactification (U₂.ι ≫ f)) :
    HasCompactification f := by
  classical
  let : CompactSpace U := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated f
  let : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨j₁, -, -⟩ := exists_dense_compactification_of_compactification (U₁.ι ≫ f) h₁
  obtain ⟨j₂, -, -⟩ := exists_dense_compactification_of_compactification (U₂.ι ≫ f) h₂
  obtain ⟨Y₁, Y₂, Y₁', Y₂', b₁, b₂, c₁, c₂, V₁, V₂,
    e₁, e₂, p₁, p₂, hb₁, hb₁proper, he₁open, hrange₁, hcomm₁, hp₁, he₁, hbase₁,
    hb₂, hb₂proper, he₂open, hrange₂, hcomm₂, hp₂, he₂, hbase₂,
    hc₁, hdisj₁, hc₂, hdisj₂⟩ :=
    exists_separated_boundary_blowups f U₁ U₂ hcover j₁ j₂
  let : IsOpenImmersion e₁ := he₁open
  let : IsOpenImmersion e₂ := he₂open
  let : IsProper p₁ := hp₁
  let : IsProper p₂ := hp₂
  let : IsProper b₁ := hb₁proper
  let : IsProper b₂ := hb₂proper
  let : IsProper c₁ := isProper_of_isAdmissibleBlowup V₁ c₁ hc₁
  let : IsProper c₂ := isProper_of_isAdmissibleBlowup V₂ c₂ hc₂
  obtain ⟨V₁', k₁, e₁', p₁', hV₁', hk₁iso, hk₁, he₁'k, hp₁'k,
    he₁'open, hp₁', he₁', hcomm₁'⟩ :=
    transport_proper_extension_across_blowup U₁ V₁ e₁ p₁ he₁ c₁ hc₁
  obtain ⟨V₂', k₂, e₂', p₂', hV₂', hk₂iso, hk₂, he₂'k, hp₂'k,
    he₂'open, hp₂', he₂', hcomm₂'⟩ :=
    transport_proper_extension_across_blowup U₂ V₂ e₂ p₂ he₂ c₂ hc₂
  let : IsIso k₁ := hk₁iso
  let : IsIso k₂ := hk₂iso
  let : IsOpenImmersion e₁' := he₁'open
  let : IsOpenImmersion e₂' := he₂'open
  let : IsProper p₁' := hp₁'
  let : IsProper p₂' := hp₂'
  have hset₁₁ := preimage_image_transport V₁ V₁' c₁ hV₁' k₁ hk₁ p₁ p₁' hp₁'k ((U₁ : Set U)ᶜ)
  have hset₁₂ := preimage_image_transport V₁ V₁' c₁ hV₁' k₁ hk₁ p₁ p₁' hp₁'k ((U₂ : Set U)ᶜ)
  have hset₂₁ := preimage_image_transport V₂ V₂' c₂ hV₂' k₂ hk₂ p₂ p₂' hp₂'k ((U₁ : Set U)ᶜ)
  have hset₂₂ := preimage_image_transport V₂ V₂' c₂ hV₂' k₂ hk₂ p₂ p₂' hp₂'k ((U₂ : Set U)ᶜ)
  have hdisj₁' : Disjoint
      (closure (V₁'.ι.base '' (p₁'.base ⁻¹' ((U₁ : Set U)ᶜ))))
      (closure (V₁'.ι.base '' (p₁'.base ⁻¹' ((U₂ : Set U)ᶜ)))) := by
    simpa only [← hset₁₁, ← hset₁₂] using hdisj₁
  have hdisj₂' : Disjoint
      (closure (V₂'.ι.base '' (p₂'.base ⁻¹' ((U₁ : Set U)ᶜ))))
      (closure (V₂'.ι.base '' (p₂'.base ⁻¹' ((U₂ : Set U)ᶜ)))) := by
    simpa only [← hset₂₁, ← hset₂₂] using hdisj₂
  have : IsNoetherian Y₁' := isNoetherian_of_isProper (c₁ ≫ b₁ ≫ j₁.toBase)
  have : IsNoetherian Y₂' := isNoetherian_of_isProper (c₂ ≫ b₂ ≫ j₂.toBase)
  have hbase₁' : p₁' ≫ f = V₁'.ι ≫ c₁ ≫ b₁ ≫ j₁.toBase := by
    rw [hp₁'k, Category.assoc, hbase₁, reassoc_of% hk₁]
  have hbase₂' : p₂' ≫ f = V₂'.ι ≫ c₂ ≫ b₂ ≫ j₂.toBase := by
    rw [hp₂'k, Category.assoc, hbase₂, reassoc_of% hk₂]
  set Q₁old : Y₁' ⟶ S := c₁ ≫ b₁ ≫ j₁.toBase with hQ₁old
  set Q₂ : Y₂' ⟶ S := c₂ ≫ b₂ ≫ j₂.toBase with hQ₂
  have : IsSeparated Q₁old := by rw [hQ₁old]; infer_instance
  have : IsSeparated Q₂ := by rw [hQ₂]; infer_instance
  have : IsProper Q₁old := by rw [hQ₁old]; infer_instance
  have : IsProper Q₂ := by rw [hQ₂]; infer_instance
  let B₁ : Set Y₁' := V₁'.ι.base '' (p₁'.base ⁻¹' ((U₁ : Set U)ᶜ))
  let B₂ : Set Y₂' := V₂'.ι.base '' (p₂'.base ⁻¹' ((U₂ : Set U)ᶜ))
  -- The image of `U₂` inside `Y₂'`, trimmed to the part of `V₂'` lying over `U₂`.
  set a₂ : U₂.toScheme ⟶ Y₂' := e₂' ≫ V₂'.ι with ha₂
  have : CompactSpace U₂.toScheme := (quasiCompact_iff_compactSpace U₂.ι).mp inferInstance
  have : QuasiCompact a₂ := by rw [ha₂]; infer_instance
  set O₂ : a₂.image.Opens := a₂.imageι ⁻¹ᵁ V₂' with hO₂
  set p₂E : O₂.toScheme ⟶ U := (a₂.imageι ∣_ V₂') ≫ p₂' with hp₂E
  have : IsProper p₂E := by rw [hp₂E]; infer_instance
  have : IsIso (p₂E ∣_ U₂) :=
    isIso_restrict_proper_extension_image U₂ V₂' e₂' p₂' he₂' inferInstance
  have hE₂range : Set.range a₂.toImage.base ⊆ (O₂ : Set a₂.image) := by
    rintro _ ⟨x, rfl⟩
    change a₂.imageι.base (a₂.toImage.base x) ∈ (V₂' : Set Y₂')
    have hx := congrArg (fun m : U₂.toScheme ⟶ Y₂' => m.base x) (Scheme.Hom.toImage_imageι a₂)
    change a₂.imageι.base (a₂.toImage.base x) = V₂'.ι.base (e₂'.base x) at hx
    rw [hx]
    exact (e₂'.base x).2
  set e₂E : U₂.toScheme ⟶ O₂.toScheme := IsOpenImmersion.lift O₂.ι a₂.toImage
    (by simpa only [Scheme.Opens.range_ι] using hE₂range) with he₂Edef
  have he₂EO : e₂E ≫ O₂.ι = a₂.toImage := IsOpenImmersion.lift_fac _ _ _
  have hiV : (a₂.imageι ∣_ V₂') ≫ V₂'.ι = O₂.ι ≫ a₂.imageι := morphismRestrict_ι _ _
  have he₂E : e₂E ≫ p₂E = U₂.ι := by
    have heV : e₂E ≫ (a₂.imageι ∣_ V₂') = e₂' := by
      refine (cancel_mono V₂'.ι).1 ?_
      rw [Category.assoc, hiV, ← Category.assoc, he₂EO, Scheme.Hom.toImage_imageι, ha₂]
    rw [hp₂E, ← Category.assoc, heV, he₂']
  have he₂Ecanonical : inv (p₂E ∣_ U₂) ≫ (p₂E ⁻¹ᵁ U₂).ι = e₂E := by
    have hrange : Set.range e₂E.base ⊆ (p₂E ⁻¹ᵁ U₂ : Set O₂.toScheme) := by
      rintro _ ⟨x, rfl⟩
      have hx := congrArg (fun m : U₂.toScheme ⟶ U => m.base x) he₂E
      change p₂E.base (e₂E.base x) = U₂.ι.base x at hx
      change p₂E.base (e₂E.base x) ∈ (U₂ : Set U)
      rw [hx]
      exact x.2
    set t : U₂.toScheme ⟶ (p₂E ⁻¹ᵁ U₂).toScheme := IsOpenImmersion.lift (p₂E ⁻¹ᵁ U₂).ι e₂E
      (by simpa only [Scheme.Opens.range_ι] using hrange) with htdef
    have ht : t ≫ (p₂E ∣_ U₂) = 𝟙 U₂.toScheme := by
      refine (cancel_mono U₂.ι).1 ?_
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, htdef,
        IsOpenImmersion.lift_fac, he₂E, Category.id_comp]
    have htinv : t = inv (p₂E ∣_ U₂) := by
      refine (cancel_mono (p₂E ∣_ U₂)).1 ?_
      rw [ht, IsIso.inv_hom_id]
    rw [← htinv, htdef, IsOpenImmersion.lift_fac]
  -- The part of `V₁'` lying over `U₂`, and the open of `Y₁'` it spans.
  let N₂ : V₁'.toScheme.Opens := p₁' ⁻¹ᵁ U₂
  set W : Y₁'.Opens := V₁'.ι ''ᵁ N₂ with hWdef
  set eW : W.toScheme ≅ N₂.toScheme := IsOpenImmersion.isoOfRangeEq W.ι (N₂.ι ≫ V₁'.ι)
    (by simp [hWdef, Set.range_comp]) with heWdef
  have heW : eW.hom ≫ N₂.ι ≫ V₁'.ι = W.ι := by
    simpa only [Category.assoc] using IsOpenImmersion.isoOfRangeEq_hom_fac W.ι (N₂.ι ≫ V₁'.ι)
      (by simp [hWdef, Set.range_comp])
  set rW : W.toScheme ⟶ U₂.toScheme := eW.hom ≫ (p₁' ∣_ U₂) with hrWdef
  have hrW : rW ≫ U₂.ι = eW.hom ≫ N₂.ι ≫ p₁' := by
    rw [hrWdef, Category.assoc, morphismRestrict_ι]
  set t₂ : W.toScheme ⟶ O₂.toScheme := rW ≫ inv (p₂E ∣_ U₂) ≫ (p₂E ⁻¹ᵁ U₂).ι with ht₂def
  have ht₂section : t₂ = rW ≫ e₂E := by rw [ht₂def, ← he₂Ecanonical]
  have ht₂ : t₂ ≫ p₂E = rW ≫ U₂.ι := by rw [ht₂section, Category.assoc, he₂E]
  have he₂Image : e₂E ≫ O₂.ι ≫ a₂.imageι = e₂' ≫ V₂'.ι := by
    rw [← Category.assoc, he₂EO, Scheme.Hom.toImage_imageι, ha₂]
  have hsW : W.ι ≫ Q₁old = (t₂ ≫ O₂.ι ≫ a₂.imageι) ≫ Q₂ := by
    calc
      W.ι ≫ Q₁old = (eW.hom ≫ N₂.ι ≫ V₁'.ι) ≫ Q₁old := by rw [heW]
      _ = (eW.hom ≫ N₂.ι ≫ p₁') ≫ f := by
        rw [hQ₁old] at hbase₁'
        simp only [Category.assoc]
        rw [← hbase₁']
      _ = (rW ≫ U₂.ι) ≫ f := by rw [hrW]
      _ = (t₂ ≫ p₂E) ≫ f := by rw [ht₂]
      _ = (t₂ ≫ O₂.ι ≫ a₂.imageι) ≫ Q₂ := by
        rw [hp₂E]
        simp only [Category.assoc]
        rw [hbase₂', ← Category.assoc (Scheme.Hom.imageι a₂ ∣_ V₂') V₂'.ι Q₂, hiV]
        simp only [Category.assoc]
  set sW : W.toScheme ⟶ pullback Q₁old Q₂ :=
    pullback.lift W.ι (t₂ ≫ O₂.ι ≫ a₂.imageι) hsW with hsWdef
  have hsW₁ : sW ≫ pullback.fst Q₁old Q₂ = W.ι := pullback.lift_fst _ _ _
  have hsW₂ : sW ≫ pullback.snd Q₁old Q₂ = rW ≫ e₂' ≫ V₂'.ι := by
    rw [hsWdef, pullback.lift_snd, ht₂section, Category.assoc, he₂Image]
  have hWcompact : IsCompact (W : Set Y₁') := TopologicalSpace.NoetherianSpace.isCompact _
  have : IsIso ((sW.imageι ≫ pullback.fst Q₁old Q₂) ∣_ W) :=
    isIso_morphismRestrict_imageι_comp_of_section (pullback.fst Q₁old Q₂) W
      (hWcompact.isRetrocompact W.2) sW hsW₁
  set P₁ : sW.image ⟶ Y₁' := sW.imageι ≫ pullback.fst Q₁old Q₂ with hP₁def
  have : IsProper P₁ := by rw [hP₁def]; infer_instance
  have : CompactSpace sW.image := (quasiCompact_iff_compactSpace P₁).mp inferInstance
  have : QuasiSeparatedSpace sW.image := quasiSeparatedSpace_of_quasiSeparated P₁
  have hB₁V : B₁ ⊆ (V₁' : Set Y₁') := by
    rintro x ⟨v₁, -, rfl⟩
    exact v₁.2
  have hB₁closed : IsClosed (V₁'.ι.base ⁻¹' B₁) := by
    have hc : IsClosed (p₁'.base ⁻¹' ((U₁ : Set U)ᶜ)) :=
      U₁.isOpen.isClosed_compl.preimage p₁'.continuous
    simpa only [B₁, Set.preimage_image_eq _ V₁'.ι.isOpenEmbedding.injective] using hc
  have hWle : W ≤ V₁' := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := hx
    exact v.2
  have hB₁W : B₁ ⊆ (W : Set Y₁') := by
    rintro x ⟨v, hvbad, rfl⟩
    have hv₂ : p₁'.base v ∈ U₂ := by
      have hcov : p₁'.base v ∈ U₁ ⊔ U₂ := by simp [hcover]
      rcases hcov with h | h
      · exact absurd h hvbad
      · exact h
    exact ⟨v, hv₂, rfl⟩
  have hV₁compact : IsCompact (V₁' : Set Y₁') := TopologicalSpace.NoetherianSpace.isCompact _
  obtain ⟨I₁, hI₁fp, hI₁disj, Wb₁, hWb₁, hWb₁iso⟩ :=
    exists_isAdmissibleBlowup_strictTransform_isIso_near_closure
      P₁ V₁' hV₁compact B₁ hB₁V hB₁closed ⟨W, hWle, hB₁W, inferInstance⟩
  let : IsIso (strictTransformToBlowUp P₁ I₁ ∣_ Wb₁) := hWb₁iso
  set d₁b : blowUp I₁ ⟶ Y₁' := blowUpToBase I₁ with hd₁bdef
  have hd₁b : Stacks.Blowup.IsAdmissibleBlowup V₁' d₁b :=
    (Stacks.Blowup.isAdmissibleBlowup_iff V₁' d₁b).mpr
      ⟨I₁, hI₁fp, hI₁disj, Iso.refl _, by rw [hd₁bdef, Iso.refl_hom, Category.id_comp]⟩
  have : IsProper d₁b := isProper_of_isAdmissibleBlowup V₁' d₁b hd₁b
  obtain ⟨V₁'', k₁'', e₁'', p₁'', hV₁'', hk₁''iso, hk₁'',
    he₁''k, hp₁''k, he₁''open, hp₁'', he₁'', hcomm₁''⟩ :=
    transport_proper_extension_across_blowup U₁ V₁' e₁' p₁' he₁' d₁b hd₁b
  let : IsIso k₁'' := hk₁''iso
  let : IsOpenImmersion e₁'' := he₁''open
  let : IsProper p₁'' := hp₁''
  have hbase₁'' : p₁'' ≫ f = V₁''.ι ≫ d₁b ≫ Q₁old := by
    rw [hp₁''k, Category.assoc, hbase₁', reassoc_of% hk₁'']
  have hB₁'' := preimage_image_transport V₁' V₁'' d₁b hV₁'' k₁'' hk₁''
    p₁' p₁'' hp₁''k ((U₁ : Set U)ᶜ)
  have hC₁'' := preimage_image_transport V₁' V₁'' d₁b hV₁'' k₁'' hk₁''
    p₁' p₁'' hp₁''k ((U₂ : Set U)ᶜ)
  have : IsIso (d₁b ∣_ V₁') := isIso_morphismRestrict_of_isAdmissibleBlowup V₁' d₁b hd₁b
  have : IsIso (d₁b ∣_ W) := Stacks.RestrictIso.isIso_morphismRestrict_of_le d₁b hWle
    inferInstance
  set lW : W.toScheme ⟶ blowUp I₁ := inv (d₁b ∣_ W) ≫ (d₁b ⁻¹ᵁ W).ι with hlWdef
  have hlW : lW ≫ d₁b = W.ι := by
    rw [hlWdef, Category.assoc, ← morphismRestrict_ι d₁b W, IsIso.inv_hom_id_assoc]
  have hsWb : lW ≫ (d₁b ≫ Q₁old) = (sW ≫ pullback.snd Q₁old Q₂) ≫ Q₂ := by
    rw [← Category.assoc, hlW, ← hsW₁, Category.assoc, Category.assoc, pullback.condition]
  set sWb : W.toScheme ⟶ pullback (d₁b ≫ Q₁old) Q₂ :=
    pullback.lift lW (sW ≫ pullback.snd Q₁old Q₂) hsWb with hsWbdef
  have hsWb₁ : sWb ≫ pullback.fst (d₁b ≫ Q₁old) Q₂ ≫ d₁b = sW ≫ pullback.fst Q₁old Q₂ := by
    rw [← Category.assoc, hsWbdef, pullback.lift_fst, hlW, hsW₁]
  have hsWb₂ : sWb ≫ pullback.snd (d₁b ≫ Q₁old) Q₂ = sW ≫ pullback.snd Q₁old Q₂ :=
    pullback.lift_snd _ _ _
  have : CompactSpace W.toScheme := (quasiCompact_iff_compactSpace W.ι).mp inferInstance
  obtain ⟨jST, aST, hjST₁, -, haST⟩ :=
    Stacks.Blowup.exists_iso_image_strictTransform_of_centre Q₁old Q₂ V₁' d₁b sW sWb
      (by
        rintro y ⟨x, rfl⟩
        rw [hsW₁]
        exact hWle x.2)
      hsWb₁ hsWb₂ I₁ (blowUpIso I₁) (blowUpIso_hom_blowUpToBase I₁) hI₁disj
  set pImg : sWb.image ⟶ blowUp I₁ := sWb.imageι ≫ pullback.fst (d₁b ≫ Q₁old) Q₂ with hpImgdef
  set qImg : sWb.image ⟶ Y₂' := sWb.imageι ≫ pullback.snd (d₁b ≫ Q₁old) Q₂ with hqImgdef
  have hproj₁ : sWb.toImage ≫ pImg = lW := by
    rw [hpImgdef, ← Category.assoc, Scheme.Hom.toImage_imageι, hsWbdef, pullback.lift_fst]
  have hproj₂ : sWb.toImage ≫ qImg = rW ≫ e₂' ≫ V₂'.ι := by
    rw [hqImgdef, ← Category.assoc, Scheme.Hom.toImage_imageι, hsWb₂, hsW₂]
  set α : sWb.image ≅ Stacks.StrictTransform.scheme P₁ (blowUpToBase I₁) (exceptionalIdeal I₁) :=
    aST ≪≫ (Stacks.Blowup.strictTransformIso P₁ I₁).symm with hαdef
  have hST : strictTransformToBlowUp P₁ I₁ ≫ (blowUpIso I₁).hom =
      (Stacks.Blowup.strictTransformIso P₁ I₁).hom ≫ Stacks.Blowup.strictTransformMap P₁ I₁ := by
    rw [Stacks.Blowup.strictTransformIso_hom_strictTransformMap]
    simp only [strictTransformToBlowUp, Category.assoc]
  have hpImg : pImg = α.hom ≫ strictTransformToBlowUp P₁ I₁ := by
    have hmap : jST ≫ pullback.fst (d₁b ≫ Q₁old) Q₂ =
        (Stacks.Blowup.strictTransformIso P₁ I₁).inv ≫ strictTransformToBlowUp P₁ I₁ := by
      refine (cancel_mono (blowUpIso I₁).hom).1 ?_
      rw [Category.assoc, hjST₁, Category.assoc, hST, Iso.inv_hom_id_assoc]
      rfl
    rw [hpImgdef, ← haST, Category.assoc, hmap, hαdef]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have : IsIso (pImg ∣_ Wb₁) := by
    rw [hpImg]
    exact isIso_restrict_of_iso_over α (strictTransformToBlowUp P₁ I₁) Wb₁
  let Q₁ : blowUp I₁ ⟶ S := d₁b ≫ Q₁old
  have : IsSeparated Q₁ := by dsimp only [Q₁]; infer_instance
  have : IsProper Q₁ := by dsimp only [Q₁]; infer_instance
  have : IsNoetherian (blowUp I₁) := isNoetherian_of_isProper Q₁
  have hbase₁new : p₁'' ≫ f = V₁''.ι ≫ Q₁ := hbase₁''
  let B₁'' : Set (blowUp I₁) := V₁''.ι.base '' (p₁''.base ⁻¹' ((U₁ : Set U)ᶜ))
  have hB₁near : closure B₁'' ⊆ (Wb₁ : Set (blowUp I₁)) := by
    rw [show B₁'' = d₁b.base ⁻¹' B₁ from hB₁''.symm]
    exact hWb₁
  let C₂ : Set Y₂' := V₂'.ι.base '' (p₂'.base ⁻¹' ((U₁ : Set U)ᶜ))
  have hImgDisj : Disjoint (pImg.base ⁻¹' closure B₁'') (qImg.base ⁻¹' closure B₂) := by
    refine disjoint_image_boundaries_of_isIso_near_closure pImg qImg sWb.toImage Wb₁
      B₁'' C₂ B₂ hB₁near ?_ ?_ hdisj₂'
    · intro x hx
      have hxB : d₁b.base x ∈ B₁ := show x ∈ d₁b.base ⁻¹' B₁ by rw [hB₁'']; exact hx
      have hxW : x ∈ d₁b ⁻¹ᵁ W := hB₁W hxB
      obtain ⟨w, hw⟩ :=
        (ConcreteCategory.bijective_of_isIso (inv (d₁b ∣_ W)).base).surjective ⟨x, hxW⟩
      refine ⟨w, ?_⟩
      have hLW : lW.base w = x := by
        rw [hlWdef]
        change (d₁b ⁻¹ᵁ W).ι.base ((inv (d₁b ∣_ W)).base w) = x
        rw [hw]
        rfl
      have hp := congrArg (fun m : W.toScheme ⟶ blowUp I₁ => m.base w) hproj₁
      change pImg.base (sWb.toImage.base w) = lW.base w at hp
      exact hp.trans hLW
    · intro w hw
      have hpw := congrArg (fun m : W.toScheme ⟶ blowUp I₁ => m.base w) hproj₁
      change pImg.base (sWb.toImage.base w) = lW.base w at hpw
      have hbad : lW.base w ∈ B₁'' := hpw ▸ hw
      have hxB : d₁b.base (lW.base w) ∈ B₁ :=
        show lW.base w ∈ d₁b.base ⁻¹' B₁ by rw [hB₁'']; exact hbad
      have hdw := congrArg (fun m : W.toScheme ⟶ Y₁' => m.base w) hlW
      change d₁b.base (lW.base w) = W.ι.base w at hdw
      have hwB : W.ι.base w ∈ B₁ := hdw ▸ hxB
      obtain ⟨v, hvbad, hveq⟩ := hwB
      have hve : v = N₂.ι.base (eW.hom.base w) := by
        refine V₁'.ι.isOpenEmbedding.injective ?_
        have hh := congrArg (fun m : W.toScheme ⟶ Y₁' => m.base w) heW
        change V₁'.ι.base (N₂.ι.base (eW.hom.base w)) = W.ι.base w at hh
        exact hveq.trans hh.symm
      have hrw := congrArg (fun m : W.toScheme ⟶ U => m.base w) hrW
      change U₂.ι.base (rW.base w) = p₁'.base (N₂.ι.base (eW.hom.base w)) at hrw
      have hrbad : U₂.ι.base (rW.base w) ∉ U₁ := by
        rw [hrw, ← hve]
        exact hvbad
      have hp₂w := congrArg (fun m : U₂.toScheme ⟶ U => m.base (rW.base w)) he₂'
      change p₂'.base (e₂'.base (rW.base w)) = U₂.ι.base (rW.base w) at hp₂w
      have hC : (rW ≫ e₂' ≫ V₂'.ι).base w ∈ C₂ := by
        refine ⟨e₂'.base (rW.base w), ?_, rfl⟩
        change p₂'.base (e₂'.base (rW.base w)) ∉ U₁
        rw [hp₂w]
        exact hrbad
      have hqw := congrArg (fun m : W.toScheme ⟶ Y₂' => m.base w) hproj₂
      change qImg.base (sWb.toImage.base w) = (rW ≫ e₂' ≫ V₂'.ι).base w at hqw
      change qImg.base (sWb.toImage.base w) ∈ closure C₂
      rw [hqw]
      exact subset_closure hC
  -- Trim the two ambient schemes away from the opposite boundaries and glue.
  let T₁ : (blowUp I₁).Opens := ⟨(closure B₁'')ᶜ, isClosed_closure.isOpen_compl⟩
  let T₂ : Y₂'.Opens := ⟨(closure B₂)ᶜ, isClosed_closure.isOpen_compl⟩
  obtain ⟨g₁, hg₁open, hg₁fac, hglue₁', hclosedCross₁⟩ :=
    exists_closedImmersion_of_trimmed_section f Q₁ U₁ V₁'' T₁ e₁'' p₁'' he₁'' hbase₁new rfl
  obtain ⟨g₂, hg₂open, hg₂fac, hglue₂', hclosedCross₂⟩ :=
    exists_closedImmersion_of_trimmed_section f Q₂ U₂ V₂' T₂ e₂' p₂' he₂' hbase₂' rfl
  have : CompactSpace T₁.toScheme := (quasiCompact_iff_compactSpace T₁.ι).mp inferInstance
  have : CompactSpace T₂.toScheme := (quasiCompact_iff_compactSpace T₂.ι).mp inferInstance
  set q₁ : T₁.toScheme ⟶ S := T₁.ι ≫ Q₁ with hq₁def
  set q₂ : T₂.toScheme ⟶ S := T₂.ι ≫ Q₂ with hq₂def
  have hglue₁ : U₁.ι ≫ f = g₁ ≫ q₁ := hglue₁'
  have hglue₂ : U₂.ι ≫ f = g₂ ≫ q₂ := hglue₂'
  have : LocallyOfFiniteType q₁ := by rw [hq₁def]; infer_instance
  have : LocallyOfFiniteType q₂ := by rw [hq₂def]; infer_instance
  have : IsSeparated q₁ := by rw [hq₁def]; infer_instance
  have : IsSeparated q₂ := by rw [hq₂def]; infer_instance
  set F₁ : SpanGlue.glued U₁.ι g₁ ⟶ S := SpanGlue.desc U₁.ι g₁ f q₁ hglue₁ with hF₁def
  set F₂ : SpanGlue.glued U₂.ι g₂ ⟶ S := SpanGlue.desc U₂.ι g₂ f q₂ hglue₂ with hF₂def
  set u₁ : U ⟶ SpanGlue.glued U₁.ι g₁ := SpanGlue.ι₁ U₁.ι g₁ with hu₁def
  set u₂ : U ⟶ SpanGlue.glued U₂.ι g₂ := SpanGlue.ι₁ U₂.ι g₂ with hu₂def
  have : IsOpenImmersion u₁ := SpanGlue.isOpenImmersion_ι₁ U₁.ι g₁
  have : IsOpenImmersion u₂ := SpanGlue.isOpenImmersion_ι₁ U₂.ι g₂
  have hFu₁ : u₁ ≫ F₁ = f := SpanGlue.ι₁_desc U₁.ι g₁ f q₁ hglue₁
  have hFu₂ : u₂ ≫ F₂ = f := SpanGlue.ι₁_desc U₂.ι g₂ f q₂ hglue₂
  have : LocallyOfFiniteType F₁ := SpanGlue.locallyOfFiniteType_desc U₁.ι g₁ f q₁ hglue₁
  have : LocallyOfFiniteType F₂ := SpanGlue.locallyOfFiniteType_desc U₂.ι g₂ f q₂ hglue₂
  have : CompactSpace (SpanGlue.glued U₁.ι g₁) := SpanGlue.compactSpace_glued U₁.ι g₁
  have : CompactSpace (SpanGlue.glued U₂.ι g₂) := SpanGlue.compactSpace_glued U₂.ι g₂
  have : QuasiCompact F₁ := (quasiCompact_iff_compactSpace F₁).2 inferInstance
  have : QuasiCompact F₂ := (quasiCompact_iff_compactSpace F₂).2 inferInstance
  have : IsSeparated F₁ := SpanGlue.isSeparated_desc U₁.ι g₁ f q₁ hglue₁ hclosedCross₁
  have : IsSeparated F₂ := SpanGlue.isSeparated_desc U₂.ι g₂ f q₂ hglue₂ hclosedCross₂
  obtain ⟨W₁', W₂', Wall, d₁, d₂, jW₁, jW₂, v₁, v₂, v, F,
    hd₁, hd₂, hjW₁, hjW₂, hFft, hFqc, hFsep, hv₁, hv₂,
    hvj₁, hvj₂, hdF₁, hdF₂, hvF⟩ :=
    exists_common_isAdmissibleBlowup_isOpenImmersion f F₁ F₂ u₁ u₂ hFu₁ hFu₂
  have : IsProper d₁ := isProper_of_isAdmissibleBlowup u₁.opensRange d₁ hd₁
  have : IsProper d₂ := isProper_of_isAdmissibleBlowup u₂.opensRange d₂ hd₂
  have : IsOpenImmersion v₁ := isOpenImmersion_lift_admissibleBlowup u₁ d₁ v₁ hd₁ hv₁
  have : IsOpenImmersion v₂ := isOpenImmersion_lift_admissibleBlowup u₂ d₂ v₂ hd₂ hv₂
  let : IsOpenImmersion jW₁ := hjW₁
  let : IsOpenImmersion jW₂ := hjW₂
  have : IsOpenImmersion v := by rw [← hvj₁]; infer_instance
  let : LocallyOfFiniteType F := hFft
  let : QuasiCompact F := hFqc
  let : IsSeparated F := hFsep
  set A : U.Opens := U₁ ⊓ U₂ with hAdef
  have hAdense : DenseRange A.ι := by
    change Dense (Set.range A.ι.base)
    simpa only [Scheme.Opens.range_ι, hAdef] using hdense
  set r₁ : A.toScheme ⟶ U₁.toScheme := U.homOfLE (by rw [hAdef]; exact inf_le_left) with hr₁def
  set r₂ : A.toScheme ⟶ U₂.toScheme := U.homOfLE (by rw [hAdef]; exact inf_le_right) with hr₂def
  have hr₁ : r₁ ≫ U₁.ι = A.ι := by simp [hr₁def]
  have hr₂ : r₂ ≫ U₂.ι = A.ι := by simp [hr₂def]
  set tW₁ : T₁.toScheme ⟶ SpanGlue.glued U₁.ι g₁ := SpanGlue.ι₂ U₁.ι g₁ with htW₁def
  set tW₂ : T₂.toScheme ⟶ SpanGlue.glued U₂.ι g₂ := SpanGlue.ι₂ U₂.ι g₂ with htW₂def
  have hrt₁ : (r₁ ≫ g₁) ≫ tW₁ = A.ι ≫ u₁ := by
    have h : U₁.ι ≫ u₁ = g₁ ≫ tW₁ := SpanGlue.glue_condition U₁.ι g₁
    rw [Category.assoc, ← h, ← Category.assoc, hr₁]
  have hrt₂ : (r₂ ≫ g₂) ≫ tW₂ = A.ι ≫ u₂ := by
    have h : U₂.ι ≫ u₂ = g₂ ≫ tW₂ := SpanGlue.glue_condition U₂.ι g₂
    rw [Category.assoc, ← h, ← Category.assoc, hr₂]
  have htW₁ : tW₁ ≫ F₁ = T₁.ι ≫ Q₁ := SpanGlue.ι₂_desc U₁.ι g₁ f q₁ hglue₁
  have htW₂ : tW₂ ≫ F₂ = T₂.ι ≫ Q₂ := SpanGlue.ι₂_desc U₂.ι g₂ f q₂ hglue₂
  have hcross : ∀ (D : ValuativeCommSq F) (g : Spec (.of D.K) ⟶ A.toScheme)
      (hh₁ : Spec (.of D.R) ⟶ blowUp I₁) (hh₂ : Spec (.of D.R) ⟶ Y₂'),
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hh₁ = (g ≫ r₁ ≫ g₁) ≫ T₁.ι →
      hh₁ ≫ Q₁ = D.i₂ →
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hh₂ = (g ≫ r₂ ≫ g₂) ≫ T₂.ι →
      hh₂ ≫ Q₂ = D.i₂ →
      hh₁.base (IsLocalRing.closedPoint D.R) ∈ T₁ ∨
        hh₂.base (IsLocalRing.closedPoint D.R) ∈ T₂ := by
    intro D g hh₁ hh₂ hg₁ hbb₁ hg₂ hbb₂
    by_contra hgood
    obtain ⟨hnot₁, hnot₂⟩ := not_or.mp hgood
    have hbad₁ : hh₁.base (IsLocalRing.closedPoint D.R) ∈ closure B₁'' := by
      simpa [T₁] using hnot₁
    have hbad₂ : hh₂.base (IsLocalRing.closedPoint D.R) ∈ closure B₂ := by
      simpa [T₂] using hnot₂
    set aK : Spec (.of D.K) ⟶ V₁'.toScheme := g ≫ r₁ ≫ e₁' with haKdef
    have haKbase : aK ≫ p₁' = (g ≫ r₂) ≫ U₂.ι := by
      rw [haKdef, Category.assoc, Category.assoc, he₁', hr₁, Category.assoc, hr₂]
    have haKrange : Set.range aK.base ⊆ (N₂ : Set V₁'.toScheme) := by
      rintro _ ⟨x, rfl⟩
      have hh := congrArg (fun m : Spec (.of D.K) ⟶ U => m.base x) haKbase
      change p₁'.base (aK.base x) = U₂.ι.base ((g ≫ r₂).base x) at hh
      change p₁'.base (aK.base x) ∈ (U₂ : Set U)
      rw [hh]
      exact ((g ≫ r₂).base x).2
    set gN₂ : Spec (.of D.K) ⟶ N₂.toScheme := IsOpenImmersion.lift N₂.ι aK
      (by simpa only [Scheme.Opens.range_ι] using haKrange) with hgN₂def
    set gW : Spec (.of D.K) ⟶ W.toScheme := gN₂ ≫ eW.inv with hgWdef
    have hgWold : gW ≫ W.ι = aK ≫ V₁'.ι := by
      rw [hgWdef, ← heW, Category.assoc, Iso.inv_hom_id_assoc, hgN₂def, ← Category.assoc,
        IsOpenImmersion.lift_fac]
    have hgWr : gW ≫ rW = g ≫ r₂ := by
      refine (cancel_mono U₂.ι).1 ?_
      rw [Category.assoc, hrW, hgWdef, Category.assoc, Iso.inv_hom_id_assoc, hgN₂def,
        ← Category.assoc, IsOpenImmersion.lift_fac, haKbase]
    have hWliftle : d₁b ⁻¹ᵁ W ≤ V₁'' := by
      rw [hV₁'']
      exact d₁b.preimage_mono hWle
    set gV : Spec (.of D.K) ⟶ V₁''.toScheme :=
      gW ≫ inv (d₁b ∣_ W) ≫ (blowUp I₁).homOfLE hWliftle with hgVdef
    have hgVambient : gV ≫ V₁''.ι = gW ≫ lW := by
      simp only [hgVdef, hlWdef, Category.assoc, Scheme.homOfLE_ι]
    have hgVk : gV ≫ k₁'' = aK := by
      refine (cancel_mono V₁'.ι).1 ?_
      rw [Category.assoc, hk₁'', ← Category.assoc, hgVambient, Category.assoc, hlW, hgWold]
    have hgVsection : gV = g ≫ r₁ ≫ e₁'' := by
      refine (cancel_mono k₁'').1 ?_
      rw [hgVk, haKdef]
      simp only [Category.assoc, he₁''k]
    have hgen₁ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hh₁ =
        gW ≫ sWb ≫ pullback.fst Q₁ Q₂ := by
      rw [hg₁]
      calc (g ≫ r₁ ≫ g₁) ≫ T₁.ι = g ≫ r₁ ≫ (g₁ ≫ T₁.ι) := by simp only [Category.assoc]
        _ = g ≫ r₁ ≫ e₁'' ≫ V₁''.ι := by rw [hg₁fac]
        _ = gV ≫ V₁''.ι := by rw [hgVsection]; simp only [Category.assoc]
        _ = gW ≫ lW := hgVambient
        _ = gW ≫ sWb ≫ pullback.fst Q₁ Q₂ := by
          rw [show sWb ≫ pullback.fst Q₁ Q₂ = lW from pullback.lift_fst _ _ _]
    have hgen₂ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hh₂ =
        gW ≫ sWb ≫ pullback.snd Q₁ Q₂ := by
      rw [hg₂]
      calc (g ≫ r₂ ≫ g₂) ≫ T₂.ι = g ≫ r₂ ≫ (g₂ ≫ T₂.ι) := by simp only [Category.assoc]
        _ = (g ≫ r₂) ≫ e₂' ≫ V₂'.ι := by rw [hg₂fac]; simp only [Category.assoc]
        _ = (gW ≫ rW) ≫ e₂' ≫ V₂'.ι := by rw [hgWr]
        _ = gW ≫ sWb ≫ pullback.snd Q₁ Q₂ := by
          rw [show sWb ≫ pullback.snd Q₁ Q₂ = rW ≫ e₂' ≫ V₂'.ι from
            (pullback.lift_snd _ _ _).trans hsW₂]
          simp only [Category.assoc]
    have hbase : hh₁ ≫ Q₁ = hh₂ ≫ Q₂ := hbb₁.trans hbb₂.symm
    have hno := valuative_pair_not_in_disjoint_image_boundaries Q₁ Q₂ sWb
      (closure B₁'') (closure B₂) hImgDisj
      { R := D.R, K := D.K, i₁ := gW ≫ sWb ≫ pullback.fst Q₁ Q₂, i₂ := D.i₂,
        commSq := ⟨by
          calc (gW ≫ sWb ≫ pullback.fst Q₁ Q₂) ≫ Q₁
              = (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hh₁) ≫ Q₁ := by rw [hgen₁]
            _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ (hh₁ ≫ Q₁) :=
                Category.assoc _ _ _
            _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := by rw [hbb₁]⟩ }
      gW hh₁ hh₂ hbase hgen₁ hgen₂
    exact hno ⟨hbad₁, hbad₂⟩
  have hvaluative : ∀ (D : ValuativeCommSq F) (g : Spec (.of D.K) ⟶ A.toScheme),
      g ≫ A.ι ≫ v = D.i₁ → Nonempty D.commSq.LiftStruct := by
    intro D g hg
    set kk₁ : Spec (.of D.K) ⟶ T₁.toScheme := g ≫ r₁ ≫ g₁ with hkk₁def
    set kk₂ : Spec (.of D.K) ⟶ T₂.toScheme := g ≫ r₂ ≫ g₂ with hkk₂def
    have hk₁ : kk₁ ≫ tW₁ = (g ≫ A.ι) ≫ u₁ := by
      rw [hkk₁def, Category.assoc, hrt₁, Category.assoc]
    have hk₂ : kk₂ ≫ tW₂ = (g ≫ A.ι) ≫ u₂ := by
      rw [hkk₂def, Category.assoc, hrt₂, Category.assoc]
    have hE₁w : (kk₁ ≫ T₁.ι) ≫ Q₁ =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := by
      rw [Category.assoc, ← htW₁, reassoc_of% hk₁, hFu₁, ← hvF, reassoc_of% hg]
      exact D.commSq.w
    have hE₂w : (kk₂ ≫ T₂.ι) ≫ Q₂ =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := by
      rw [Category.assoc, ← htW₂, reassoc_of% hk₂, hFu₂, ← hvF, reassoc_of% hg]
      exact D.commSq.w
    set E₁ : ValuativeCommSq Q₁ :=
      { R := D.R, K := D.K, i₁ := kk₁ ≫ T₁.ι, i₂ := D.i₂, commSq := ⟨hE₁w⟩ } with hE₁def
    set E₂ : ValuativeCommSq Q₂ :=
      { R := D.R, K := D.K, i₁ := kk₂ ≫ T₂.ι, i₂ := D.i₂, commSq := ⟨hE₂w⟩ } with hE₂def
    have hval {X : Scheme.{u}} (q : X ⟶ S) [hq : IsProper q] : ValuativeCriterion q := by
      rw [IsProper.eq_valuativeCriterion] at hq
      exact hq.1.1.1
    obtain ⟨l₁⟩ : Nonempty E₁.commSq.LiftStruct := ⟨(hval Q₁ E₁).some.default⟩
    obtain ⟨l₂⟩ : Nonempty E₂.commSq.LiftStruct := ⟨(hval Q₂ E₂).some.default⟩
    have hl₁left : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₁.l = kk₁ ≫ T₁.ι :=
      l₁.fac_left
    have hl₁right : l₁.l ≫ Q₁ = D.i₂ := l₁.fac_right
    have hl₂left : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l₂.l = kk₂ ≫ T₂.ι :=
      l₂.fac_left
    have hl₂right : l₂.l ≫ Q₂ = D.i₂ := l₂.fac_right
    have hgood := hcross D g l₁.l l₂.l
      (by rw [hl₁left, hkk₁def]) hl₁right (by rw [hl₂left, hkk₂def]) hl₂right
    rcases hgood with hgood | hgood
    · exact valuativeLift_of_chosen_proper_limit_to_common_model Q₁ F₁ F T₁ tW₁ u₁ v v₁ d₁ jW₁
        htW₁ hv₁ hvj₁ hdF₁ D (g ≫ A.ι) (by simpa only [Category.assoc] using hg)
        kk₁ hk₁ l₁.l hl₁left hl₁right hgood
    · exact valuativeLift_of_chosen_proper_limit_to_common_model Q₂ F₂ F T₂ tW₂ u₂ v v₂ d₂ jW₂
        htW₂ hv₂ hvj₂ hdF₂ D (g ≫ A.ι) (by simpa only [Category.assoc] using hg)
        kk₂ hk₂ l₂.l hl₂left hl₂right hgood
  exact exists_compactification_of_valuative_ambient f A.ι v F hAdense hvF hvaluative

end AlgebraicGeometry

end
