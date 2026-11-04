module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful

/-!
# Descending a morphism into an étale scheme along an étale surjection

Let `k : M ⟶ X` be a surjective étale morphism, let `a : A ⟶ X` be an arbitrary scheme over `X`
and let `u : U ⟶ X` be étale. A morphism `β : A ×_X M ⟶ U` over `X` whose two restrictions to
`(A ×_X M) ×_A (A ×_X M)` agree is the restriction along the projection `A ×_X M ⟶ A` of a
morphism `A ⟶ U` over `X`.

This is the single-morphism case of descent of morphisms for an étale covering. No
quasi-compactness hypothesis is made on `k`, so
`AlgebraicGeometry.exists_desc_of_surjective_flat_quasiCompact'` does not apply.

## Main results

* `AlgebraicGeometry.exists_hom_of_pullbackFst_comp_eq_of_etale_surjective` — the statement
  above.

## Implementation notes

The proof is the graph argument of Stacks Project, Tag 0BTK, carried out directly on fibre
products instead of on descent data. Write `π : P = A ×_X M ⟶ A` for the projection, which is
again surjective and étale, and `T = U ×_X A` for the fibre product with its two projections.
The graph `s = (β, π) : P ⟶ T` induces a section `r : P ⟶ T ×_X M` of the projection
`pV : T ×_X M ⟶ P`, which is étale because it is a base change of `T ⟶ A`; so `r` is an open
immersion by `AlgebraicGeometry.isOpenImmersion_of_section_of_etale`.

The hypothesis on `β` says exactly that two generalized points of `P` over one point of `A` have
the same image under `β`, and that makes the range of `r` invariant for the two projections of
the self fibre product of `T ×_X M ⟶ T`. Since that projection is an open surjection, hence
submersive, the range descends to an open subscheme `O ⊆ T` by
`Stacks.Etale.exists_isOpen_preimage_eq_of_isQuotientMap`. Then `O ⟶ A` is étale and admits a
section after base change along the surjection `π`, so it is an isomorphism by
`AlgebraicGeometry.isIso_of_etale_of_isPullback_id`, and the composite of its inverse with
`O ⟶ U` is the required morphism.

## References

* [Stacks Project, Tag 0BTK](https://stacks.math.columbia.edu/tag/0BTK)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **Descending a morphism into an étale scheme along an étale surjection.** Let `k : M ⟶ X` be
surjective and étale, let `a : A ⟶ X` be arbitrary and let `u : U ⟶ X` be étale. A morphism
`β : A ×_X M ⟶ U` over `X` whose two restrictions along the projections of
`(A ×_X M) ×_A (A ×_X M)` agree is the restriction of a morphism `A ⟶ U` over `X`. -/
theorem exists_hom_of_pullbackFst_comp_eq_of_etale_surjective {X A U M : Scheme.{u}} (a : A ⟶ X)
    (u : U ⟶ X) [Etale u] (k : M ⟶ X) [Etale k] [Surjective k] (β : pullback a k ⟶ U)
    (hβ : β ≫ u = pullback.fst a k ≫ a)
    (hcomp : pullback.fst (pullback.fst a k) (pullback.fst a k) ≫ β =
      pullback.snd (pullback.fst a k) (pullback.fst a k) ≫ β) :
    ∃ γ : A ⟶ U, γ ≫ u = a ∧ pullback.fst a k ≫ γ = β := by
  set T : Scheme.{u} := pullback u a with hT
  set π : pullback a k ⟶ A := pullback.fst a k with hπ
  have _ : Etale π := by rw [hπ]; infer_instance
  have _ : Surjective π := by rw [hπ]; infer_instance
  set gT : T ⟶ A := pullback.snd u a with hgT
  set uT : T ⟶ U := pullback.fst u a with huT
  have _ : Etale gT := by rw [hgT]; infer_instance
  set s : pullback a k ⟶ T := pullback.lift β π hβ with hs
  have hsg : s ≫ gT = π := by rw [hs, hgT]; exact pullback.lift_snd _ _ _
  have hsu : s ≫ uT = β := by rw [hs, huT]; exact pullback.lift_fst _ _ _
  set qB : pullback (gT ≫ a) k ⟶ T := pullback.fst (gT ≫ a) k with hqB
  set qM : pullback (gT ≫ a) k ⟶ M := pullback.snd (gT ≫ a) k with hqM
  have _ : Etale qB := by rw [hqB]; infer_instance
  have _ : Surjective qB := by rw [hqB]; infer_instance
  have hpVw : (qB ≫ gT) ≫ a = qM ≫ k := by
    rw [Category.assoc, hqB, hqM]
    exact pullback.condition
  set pV : pullback (gT ≫ a) k ⟶ pullback a k :=
    pullback.lift (qB ≫ gT) qM hpVw with hpV
  have hpVfst : pV ≫ π = qB ≫ gT := by rw [hpV, hπ]; exact pullback.lift_fst _ _ _
  have hpVsnd : pV ≫ pullback.snd a k = qM := by rw [hpV]; exact pullback.lift_snd _ _ _
  have hrw : s ≫ gT ≫ a = pullback.snd a k ≫ k := by
    rw [← Category.assoc, hsg, hπ]
    exact pullback.condition
  set r : pullback a k ⟶ pullback (gT ≫ a) k :=
    pullback.lift s (pullback.snd a k) hrw with hr
  have hrfst : r ≫ qB = s := by rw [hr, hqB]; exact pullback.lift_fst _ _ _
  have hrsnd : r ≫ qM = pullback.snd a k := by rw [hr, hqM]; exact pullback.lift_snd _ _ _
  have hrsec : r ≫ pV = 𝟙 (pullback a k) := by
    refine pullback.hom_ext ?_ ?_
    · change (r ≫ pV) ≫ π = 𝟙 (pullback a k) ≫ π
      rw [Category.assoc, hpVfst, ← Category.assoc, hrfst, hsg, Category.id_comp]
    · show (r ≫ pV) ≫ pullback.snd a k = 𝟙 (pullback a k) ≫ pullback.snd a k
      rw [Category.assoc, hpVsnd, hrsnd, Category.id_comp]
  have hV : IsPullback qB pV gT π := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd a k) (v₂₂ := a)
    · rw [hpVsnd, hqB, hqM]
      exact IsPullback.of_hasPullback (gT ≫ a) k
    · exact hpVfst.symm
    · rw [hπ]
      exact IsPullback.of_hasPullback a k
  have _ : Etale pV :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hV inferInstance
  have _ : IsOpenImmersion r := isOpenImmersion_of_section_of_etale pV r hrsec
  have hinv : ∀ {Z : Scheme.{u}} (x y : Z ⟶ pullback a k), x ≫ π = y ≫ π → x ≫ s = y ≫ s := by
    intro Z x y hxy
    refine pullback.hom_ext ?_ ?_
    · change (x ≫ s) ≫ uT = (y ≫ s) ≫ uT
      rw [Category.assoc, Category.assoc, hsu]
      calc x ≫ β
          = pullback.lift x y hxy ≫ pullback.fst π π ≫ β := by rw [pullback.lift_fst_assoc]
        _ = pullback.lift x y hxy ≫ pullback.snd π π ≫ β := by rw [hcomp]
        _ = y ≫ β := by rw [pullback.lift_snd_assoc]
    · change (x ≫ s) ≫ gT = (y ≫ s) ≫ gT
      rw [Category.assoc, Category.assoc, hsg, hxy]
  have hvs : pullback.fst s qB ≫ s = pullback.snd s qB ≫ qB := pullback.condition
  have hvb : pullback.fst s qB ≫ π = (pullback.snd s qB ≫ pV) ≫ π := by
    rw [Category.assoc, hpVfst, ← Category.assoc, ← hvs, Category.assoc, hsg]
  have hbr : (pullback.snd s qB ≫ pV) ≫ r = pullback.snd s qB := by
    refine pullback.hom_ext ?_ ?_
    · change ((pullback.snd s qB ≫ pV) ≫ r) ≫ qB = pullback.snd s qB ≫ qB
      rw [Category.assoc, hrfst, ← hvs]
      exact (hinv _ _ hvb).symm
    · change ((pullback.snd s qB ≫ pV) ≫ r) ≫ qM = pullback.snd s qB ≫ qM
      rw [Category.assoc, hrsnd, Category.assoc, hpVsnd]
  have hsat : ∀ x y, qB x = qB y →
      (x ∈ Set.range r.base ↔ y ∈ Set.range r.base) := by
    suffices H : ∀ x y, qB x = qB y → x ∈ Set.range r.base → y ∈ Set.range r.base from
      fun x y h ↦ ⟨H x y h, H y x h.symm⟩
    intro x y hxy hx
    obtain ⟨t, rfl⟩ := hx
    have he : s t = qB y := by
      rw [← hrfst]
      exact hxy
    obtain ⟨c, -, hc₂⟩ := Scheme.Pullback.exists_preimage_pullback t y he
    exact ⟨(pullback.snd s qB ≫ pV) c, (congrArg (fun m ↦ m c) hbr).trans hc₂⟩
  have hqq : Topology.IsQuotientMap qB :=
    qB.isOpenMap.isQuotientMap qB.continuous qB.surjective
  obtain ⟨O₀, hO₀open, hO₀⟩ :=
    Stacks.Etale.exists_isOpen_preimage_eq_of_isQuotientMap hqq
      ((Stacks.Etale.preimage_pullback_fst_eq_preimage_pullback_snd_iff qB
        (Set.range r.base)).mpr hsat) r.isOpenEmbedding.isOpen_range
  set O : T.Opens := ⟨O₀, hO₀open⟩ with hO
  have hOpre : qB ⁻¹ᵁ O = r.opensRange := TopologicalSpace.Opens.ext hO₀
  have hsrange : Set.range s.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    have ht : r t ∈ qB ⁻¹' O₀ := by
      rw [hO₀]
      exact ⟨t, rfl⟩
    have hgt : qB (r t) = s t := by
      simpa using congrArg (fun m : pullback a k ⟶ T ↦ m t) hrfst
    exact hgt ▸ ht
  set σ : pullback a k ⟶ O.toScheme := IsOpenImmersion.lift O.ι s hsrange with hσdef
  have hσ : σ ≫ O.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hgraph : IsPullback σ r O.ι qB :=
    IsOpenImmersion.isPullback σ r O.ι qB (hrfst.trans hσ.symm) (by simpa using hOpre)
  have _ : Etale (O.ι ≫ gT) := by rw [hgT]; infer_instance
  have hsection : IsPullback σ (𝟙 (pullback a k)) (O.ι ≫ gT) π := by
    simpa only [hrsec] using hgraph.paste_vert hV
  have _ : IsIso (O.ι ≫ gT) := isIso_of_etale_of_isPullback_id (O.ι ≫ gT) π σ hsection
  refine ⟨inv (O.ι ≫ gT) ≫ O.ι ≫ uT, ?_, ?_⟩
  · have hcond : O.ι ≫ uT ≫ u = (O.ι ≫ gT) ≫ a := by
      rw [hgT, huT, Category.assoc, pullback.condition]
    rw [Category.assoc, Category.assoc, hcond, IsIso.inv_hom_id_assoc]
  · have hσinv : π ≫ inv (O.ι ≫ gT) = σ := by
      rw [← cancel_mono (O.ι ≫ gT)]
      simpa using hsection.w.symm
    rw [← Category.assoc, hσinv, ← Category.assoc, hσ, hsu]

end AlgebraicGeometry

end

end
