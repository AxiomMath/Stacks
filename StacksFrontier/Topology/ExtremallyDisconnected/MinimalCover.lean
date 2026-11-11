module

public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.ExtremallyDisconnected.Rainwater
public import StacksFrontier.Topology.ExtremallyDisconnected.Retract

/-!
# The minimal extremally disconnected cover of a quasi-compact Hausdorff space

Let `X` be a quasi-compact Hausdorff space and let `π : β(X_disc) → X` be the extension of the
identity, where `β(X_disc)` is the Stone–Čech compactification of `X` with the discrete topology
(realised as `Ultrafilter X`). Stacks 090D constructs the canonical cover of `X`: a closed subset
`E ⊆ β(X_disc)` with `π(E) = X`, minimal among such closed subsets (Stacks 08YM), and shows that
`E` is extremally disconnected. Its uniqueness is `minimal_cover_unique`.

## Main results

* `exists_minimal_extremallyDisconnected_cover` (Stacks 090D): the minimal closed subset of
  `β(X_disc)` surjecting onto `X` exists and is extremally disconnected.
* `exists_minimal_extremallyDisconnected_cover_space` (Stacks 090D): the same cover as a space
  `X' → X` that is minimal in the sense of `minimal_cover_unique` and `minimal_cover_card_le`.

## References

* [Stacks Project, Tag 090D](https://stacks.math.columbia.edu/tag/090D)
-/

@[expose] public section

open Function Set Topology

universe u

/-- The core of Stacks 090D: a closed `E ⊆ β(X_disc)` surjecting onto `X` under the extension of
the identity, no proper closed subset of which surjects onto `X`, and which is extremally
disconnected. -/
private theorem exists_minimal_cover_aux
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∃ E : Set (Ultrafilter X), IsClosed E ∧ Ultrafilter.extend (id : X → X) '' E = univ ∧
      (∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ →
        E.domRestrict (Ultrafilter.extend (id : X → X)) '' E₀ ≠ univ) ∧
      ExtremallyDisconnected E := by
  set π : Ultrafilter X → X := Ultrafilter.extend id
  have hπ : Continuous π := continuous_ultrafilter_extend id
  have hπsurj : Surjective π := fun x =>
    ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (id : X → X)) x⟩
  -- Stacks 08YM: a minimal compact subset `E` surjecting onto `X`.
  obtain ⟨E, hEc, hEsurj, hEmin⟩ := exists_compact_surjective_zorn_subset hπ hπsurj
  have hEclosed : IsClosed E := (isCompact_iff_compactSpace.mpr hEc).isClosed
  refine ⟨E, hEclosed, hEsurj, hEmin, ?_⟩
  set ρ : E → X := E.domRestrict π
  have hρ : Continuous ρ := hπ.comp continuous_subtype_val
  have hρsurj : Surjective ρ := by
    intro x
    obtain ⟨e, he, hex⟩ : x ∈ π '' E := hEsurj ▸ mem_univ x
    exact ⟨⟨e, he⟩, hex⟩
  -- Lift `π` along `ρ` using that `β(X_disc)` is projective (Stacks 08YN).
  obtain ⟨f, hf, hρf⟩ := ultrafilter_projective X hπ hρ hρsurj
  -- The selfmap `s = f|_E` of `E` lies over `X`.
  set s : E → E := f ∘ Subtype.val
  have hs : Continuous s := hf.comp continuous_subtype_val
  have hρs : ∀ e, ρ (s e) = ρ e := fun e => congr_fun hρf e.1
  -- `s` is surjective: its image is a closed subset of `E` surjecting onto `X`.
  have hssurj : Surjective s := by
    rw [← range_eq_univ]
    by_contra hne
    refine hEmin (range s) hne (isCompact_range hs).isClosed ?_
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨e, rfl⟩ := hρsurj x
    exact ⟨s e, mem_range_self e, hρs e⟩
  -- `s` is the identity, by Rainwater's lemma (Stacks 090B) and minimality of `E`.
  have hsid : s = id := by
    by_contra hne
    obtain ⟨E₁, hE₁c, hE₁ne, hE₁⟩ := rainwater_lemma s hs hssurj hne
    refine hEmin E₁ hE₁ne hE₁c (eq_univ_of_forall fun x => ?_)
    obtain ⟨e, rfl⟩ := hρsurj x
    rcases (hE₁ ▸ mem_univ e : e ∈ E₁ ∪ s '' E₁) with he | ⟨e₁, he₁, rfl⟩
    · exact ⟨e, he, rfl⟩
    · exact ⟨e₁, he₁, (hρs e₁).symm⟩
  -- So `E` is a retract of the extremally disconnected space `β(X_disc)`.
  have : ExtremallyDisconnected (Ultrafilter X) :=
    CompactT2.Projective.extremallyDisconnected (ultrafilter_projective X)
  exact extremallyDisconnected_of_retract hf continuous_subtype_val hsid

/-- **Stacks 090D, the minimal cover.** Let `X` be a quasi-compact Hausdorff space and let
`π : β(X_disc) → X` be the extension of the identity of `X`, where `β(X_disc) = Ultrafilter X` is
the Stone–Čech compactification of `X` with the discrete topology. There is a closed subset
`E ⊆ β(X_disc)` with `π(E) = X` such that no proper closed subset of `E` maps onto `X`, and this
`E` is extremally disconnected; thus `π|_E : E → X` is a continuous surjection
from a quasi-compact Hausdorff extremally disconnected space, minimal in the sense of 090D. -/
@[stacks 090D "existence of a minimal cover: the minimal closed E ⊆ β(X_disc) mapping onto X \
  is extremally disconnected"]
theorem exists_minimal_extremallyDisconnected_cover
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∃ E : Set (Ultrafilter X), IsClosed E ∧ Ultrafilter.extend (id : X → X) '' E = univ ∧
      (∀ E' ⊆ E, IsClosed E' → Ultrafilter.extend (id : X → X) '' E' = univ → E' = E) ∧
      ExtremallyDisconnected E := by
  obtain ⟨E, hEclosed, hEsurj, hEmin, hEed⟩ := exists_minimal_cover_aux X
  refine ⟨E, hEclosed, hEsurj, fun E' hE'E hE'c hE'surj => ?_, hEed⟩
  refine hE'E.antisymm fun e he => ?_
  by_contra he'
  refine hEmin (Subtype.val ⁻¹' E') (fun h => he' ?_)
    (hE'c.preimage continuous_subtype_val) ?_
  · simpa using congrArg (fun S : Set E => (⟨e, he⟩ : E) ∈ S) h
  · rw [← hE'surj, ← image_image_val_eq_domRestrict_image, image_preimage_eq_inter_range,
      Subtype.range_coe, inter_eq_left.mpr hE'E]

/-- **Stacks 090D, the minimal cover as a space.** Every quasi-compact Hausdorff space `X` admits
a continuous surjection `π : X' → X` from a quasi-compact Hausdorff extremally disconnected space
`X'` such that no proper closed subset of `X'` maps onto `X`. This is the minimality hypothesis of
`minimal_cover_unique`, which makes `X'` unique up to homeomorphism over `X`. -/
@[stacks 090D "existence of a minimal cover, as a space X' → X"]
theorem exists_minimal_extremallyDisconnected_cover_space
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : CompactSpace X')
        (_ : T2Space X') (_ : ExtremallyDisconnected X')
        (π : X' → X), Continuous π ∧ Surjective π ∧
          ∀ E : Set X', IsClosed E → E ≠ univ → π '' E ≠ univ := by
  obtain ⟨E, hEclosed, hEsurj, hEmin, hEed⟩ := exists_minimal_cover_aux X
  have : CompactSpace E := isCompact_iff_compactSpace.mp hEclosed.isCompact
  refine ⟨E, inferInstance, inferInstance, inferInstance, hEed,
    E.domRestrict (Ultrafilter.extend (id : X → X)),
    (continuous_ultrafilter_extend id).comp continuous_subtype_val, fun x => ?_,
    fun E₀ hE₀c hE₀ne => hEmin E₀ hE₀ne hE₀c⟩
  obtain ⟨e, he, hex⟩ : x ∈ Ultrafilter.extend (id : X → X) '' E := hEsurj ▸ mem_univ x
  exact ⟨⟨e, he⟩, hex⟩

end
