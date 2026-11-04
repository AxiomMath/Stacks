module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Dominance
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# Gluing the proper charts of Chow's lemma along a common dense open

Having immersed the common dense open `U` of a finite affine cover `X = ⋃ Vᵢ` into a scheme `P`
projective over `S`, the Stacks proof of Chow's lemma over a Noetherian base (Tag 0200) forms,
for each `i`, the fibre product of the scheme-theoretic image of `U` in `P` with `Vᵢ`, and glues
these along the open subscheme of `P` they cover. The glued morphism to `X` is proper because it
is proper over each `Vᵢ`, and it is an isomorphism over `U` because each chart already contains
the whole inverse image of `U`.

This file contains those two steps.

## Main results

* `AlgebraicGeometry.exists_chart_of_image`: over an affine open `V ⊇ U` of `X`, the
  scheme-theoretic image of `U` in `P` carries a proper chart.
* `AlgebraicGeometry.exists_modification_of_dense_charts`: compatible proper charts over an open
  cover of `X`, all containing a common scheme-theoretically dominant open `U`, glue to a proper
  morphism to `X` which is an isomorphism over `U`.

## Implementation notes

`exists_chart_of_image` gets properness of its chart by factoring the comparison morphism
`a.image ⟶ j.image` through a projective space over `S`: both composites are proper, so the
comparison is proper by cancellation, and the chart is its base change.

The gluing in `exists_modification_of_dense_charts` is `Scheme.Cover.glueMorphisms` over the
cover of `O = ⨆ i, range (j i)` by the charts. Its cocycle condition is checked on `U`, where
all the charts agree by construction, and propagated by
`AlgebraicGeometry.eq_of_comp_isSchemeTheoreticallyDominant` — the target `X` is separated over
`S`, which is where the separatedness hypothesis of Chow's lemma is used. Properness of the
glued morphism is then Zariski-local on `X`, and over each member of the cover it follows from
`AlgebraicGeometry.isIso_pullbackLift_of_isProper_of_isDominant`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u v

/-- **The scheme-theoretic image of a dense open chart has a proper chart over each affine open
of `X` containing it.** Here `a : U ⟶ P` is the chart of `U` in a scheme `P` proper over `S`,
`j` is the chart of `V` in a projective space over `S`, and `r` is the projection of `P` onto
that projective space through which `a` factors. -/
theorem exists_chart_of_image {X S P : Scheme.{u}} (f : X ⟶ S) (q : P ⟶ S) [IsProper q]
    (U V : X.Opens) (hUV : U ≤ V) (a : U.toScheme ⟶ P) [IsImmersion a] [QuasiCompact a] (n : ℕ)
    (j : V.toScheme ⟶ ProjectiveSpace n S) [IsImmersion j] [QuasiCompact j]
    (hj : j ≫ (ProjectiveSpace n S ↘ S) = V.ι ≫ f) (r : P ⟶ ProjectiveSpace n S)
    (hr : r ≫ (ProjectiveSpace n S ↘ S) = q) (har : a ≫ r = X.homOfLE hUV ≫ j) :
    ∃ (W : Scheme.{u}) (e : W ⟶ a.image) (p : W ⟶ V.toScheme) (s : U.toScheme ⟶ W),
      IsOpenImmersion e ∧ IsProper p ∧ s ≫ e = a.toImage ∧ s ≫ p = X.homOfLE hUV ∧
        e ≫ a.imageι ≫ q = p ≫ V.ι ≫ f := by
  have : IsSchemeTheoreticallyDominant a.toImage := isSchemeTheoreticallyDominant_toImage a
  have hk : j.imageι.ker ≤ (a.imageι ≫ r).ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    have H : (a.toImage ≫ (a.imageι ≫ r)).ker = (a.imageι ≫ r).ker := by
      rw [Scheme.Hom.ker_comp, a.toImage.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← H, ← Category.assoc, a.toImage_imageι, har]
    exact Scheme.Hom.le_ker_comp _ _
  let r' : a.image ⟶ j.image := IsClosedImmersion.lift j.imageι (a.imageι ≫ r) hk
  have hr' : r' ≫ j.imageι = a.imageι ≫ r := IsClosedImmersion.lift_fac _ _ _
  have hr'base : r' ≫ (j.imageι ≫ (ProjectiveSpace n S ↘ S)) = a.imageι ≫ q := by
    rw [← Category.assoc, hr', Category.assoc, hr]
  have : IsProper (r' ≫ (j.imageι ≫ (ProjectiveSpace n S ↘ S))) := by
    rw [hr'base]; infer_instance
  have : IsProper r' := IsProper.of_comp r' (j.imageι ≫ (ProjectiveSpace n S ↘ S))
  have ha : a.toImage ≫ r' = X.homOfLE hUV ≫ j.toImage := by
    apply (cancel_mono j.imageι).mp
    rw [Category.assoc, hr', ← Category.assoc, a.toImage_imageι, Category.assoc,
      j.toImage_imageι, har]
  refine ⟨pullback r' j.toImage, pullback.fst _ _, pullback.snd _ _,
    pullback.lift a.toImage (X.homOfLE hUV) ha, inferInstance, inferInstance,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  rw [← hr'base, pullback.condition_assoc, Scheme.Hom.toImage_imageι_assoc, hj]

/-- Scheme-theoretic dominance of `a` descends to `b` along an open immersion `c` with
`b ≫ c = a`. -/
private theorem isSchemeTheoreticallyDominant_of_comp_eq {A B C : Scheme.{u}} (b : A ⟶ B)
    (c : B ⟶ C) (a : A ⟶ C) (hbc : b ≫ c = a) [IsOpenImmersion c] [QuasiCompact a]
    [IsSchemeTheoreticallyDominant a] : IsSchemeTheoreticallyDominant b := by
  subst hbc
  exact IsSchemeTheoreticallyDominant.of_comp_isOpenImmersion b c

/-- A property `P` stable under isomorphisms passes from a proper `b` to the base change
`pullback.snd p i`, when `b` and a dominant open immersion `a` are compatible over `p` and `i`. -/
private theorem snd_of_comp_eq_of_isDominant {X Y U V : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] (a : V ⟶ Y) (b : V ⟶ U) (i : U ⟶ X)
    (p : Y ⟶ X) [IsOpenImmersion a] [IsDominant a] [IsOpenImmersion i] [IsProper b]
    [IsSeparated p] (h : a ≫ p = b ≫ i) (hb : P b) : P (pullback.snd p i) := by
  have := isIso_pullbackLift_of_isProper_of_isDominant a b i p h
  refine (P.cancel_left_of_respectsIso (pullback.lift a b h) _).mp ?_
  rwa [pullback.lift_snd]

/-- **Compatible proper charts over an open cover of `X` glue to a proper modification which is
an isomorphism over the common dense open.** The charts `W i` sit inside a scheme `Z` separated
over `S` by open immersions `j i`, map properly to the members `V i` of an open cover of `X`,
and all contain the fixed open `U` of `X` by maps `s i` compatible with both. -/
theorem exists_modification_of_dense_charts {X S Z : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (q : Z ⟶ S) [IsSeparated q] (U : X.Opens) (a : U.toScheme ⟶ Z) [IsOpenImmersion a]
    [QuasiCompact a] [IsSchemeTheoreticallyDominant a] {I : Type u} [Nonempty I]
    (V : I → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ V i) (hUV : ∀ i, U ≤ V i) (W : I → Scheme.{u})
    (j : ∀ i, W i ⟶ Z) (p : ∀ i, W i ⟶ (V i).toScheme) (s : ∀ i, U.toScheme ⟶ W i)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsProper (p i)] (hsj : ∀ i, s i ≫ j i = a)
    (hsp : ∀ i, s i ≫ p i = X.homOfLE (hUV i))
    (hbase : ∀ i, j i ≫ q = p i ≫ (V i).ι ≫ f) :
    ∃ (Y : Scheme.{u}) (e : Y ⟶ Z) (π : Y ⟶ X) (t : U.toScheme ⟶ Y),
      IsOpenImmersion e ∧ IsProper π ∧ e ≫ q = π ≫ f ∧ t ≫ e = a ∧ t ≫ π = U.ι ∧
        IsIso (π ∣_ U) := by
  classical
  let O : Z.Opens := ⨆ i, (j i).opensRange
  have hjO (i) : Set.range (j i) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_iSup (fun i => (j i).opensRange) i
  let k (i) : W i ⟶ O.toScheme := IsOpenImmersion.lift O.ι (j i) (hjO i)
  have hk (i) : k i ≫ O.ι = j i := IsOpenImmersion.lift_fac _ _ _
  have haO : Set.range a ⊆ Set.range O.ι := by
    let i : I := Classical.choice inferInstance
    rw [← hsj i]
    exact (Set.range_comp_subset_range (s i) (j i)).trans (hjO i)
  let t : U.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι a haO
  have ht : t ≫ O.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hsk (i) : s i ≫ k i = t := by
    apply (cancel_mono O.ι).mp
    simp only [Category.assoc, hk, ht, hsj]
  have hcompat (i i' : I) :
      pullback.fst (k i) (k i') ≫ p i ≫ (V i).ι =
        pullback.snd (k i) (k i') ≫ p i' ≫ (V i').ι := by
    let b := pullback.lift (s i) (s i') ((hsk i).trans (hsk i').symm)
    let c := pullback.fst (k i) (k i') ≫ k i ≫ O.ι
    have hbc : b ≫ c = a := by
      change pullback.lift (s i) (s i') _ ≫ pullback.fst (k i) (k i') ≫ k i ≫ O.ι = a
      rw [pullback.lift_fst_assoc, ← Category.assoc, hsk, ht]
    have := isSchemeTheoreticallyDominant_of_comp_eq b c a hbc
    apply eq_of_comp_isSchemeTheoreticallyDominant b _ _ f
    · simp only [Category.assoc, ← hbase]
      rw [← hk i, ← hk i']
      simp only [← Category.assoc, pullback.condition]
    · change pullback.lift (s i) (s i') ((hsk i).trans (hsk i').symm) ≫
          pullback.fst (k i) (k i') ≫ p i ≫ (V i).ι =
        pullback.lift (s i) (s i') ((hsk i).trans (hsk i').symm) ≫
          pullback.snd (k i) (k i') ≫ p i' ≫ (V i').ι
      rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, ← Category.assoc, ← Category.assoc,
        hsp, hsp, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  let C : O.toScheme.OpenCover :=
    { I₀ := I
      X := W
      f := k
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, inferInstance⟩
        obtain ⟨i, y, hy⟩ := Opens.mem_iSup.mp x.2
        exact ⟨i, y, O.ι.isOpenEmbedding.injective (by rw [← hk i] at hy; exact hy)⟩ }
  let π : O.toScheme ⟶ X := C.glueMorphisms (fun i => p i ≫ (V i).ι) hcompat
  have hkπ (i : I) : k i ≫ π = p i ≫ (V i).ι := C.ι_glueMorphisms _ hcompat i
  have hπkey (i : I) : k i ≫ (O.ι ≫ q) = k i ≫ (π ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, hk, hkπ, Category.assoc, hbase]
  have hπbase : O.ι ≫ q = π ≫ f := C.hom_ext _ _ hπkey
  have : IsSeparated (π ≫ f) := by rw [← hπbase]; infer_instance
  have : IsSeparated π := IsSeparated.of_comp π f
  have htπ : t ≫ π = U.ι := by
    let i : I := Classical.choice inferInstance
    rw [← hsk i, Category.assoc, hkπ, ← Category.assoc, hsp, Scheme.homOfLE_ι]
  have := isSchemeTheoreticallyDominant_of_comp_eq t O.ι a ht
  have : QuasiCompact (t ≫ O.ι) := ht ▸ inferInstance
  have : QuasiCompact t := QuasiCompact.of_comp t O.ι
  have hproper (i : I) : IsProper (pullback.snd π (V i).ι) := by
    have hdom : IsDominant (s i ≫ k i) := by
      rw [hsk]
      infer_instance
    have : IsDominant (k i) := IsDominant.of_comp (s i) (k i)
    exact snd_of_comp_eq_of_isDominant (P := @IsProper) (k i) (p i) (V i).ι π (hkπ i) inferInstance
  have hc : IsOpenCover V := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have : IsProper π :=
    (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsProper)
      (X.openCoverOfIsOpenCover V hc)).mpr hproper
  have htid : t ≫ π = 𝟙 U.toScheme ≫ U.ι := by simpa using htπ
  have hiso : IsIso (pullback.snd π U.ι) :=
    snd_of_comp_eq_of_isDominant (P := MorphismProperty.isomorphisms Scheme) t (𝟙 U.toScheme) U.ι
      π htid (MorphismProperty.isomorphisms.infer_property _)
  refine ⟨O.toScheme, O.ι, π, t, inferInstance, inferInstance, hπbase, ht, htπ, ?_⟩
  rw [morphismRestrict]
  infer_instance

end AlgebraicGeometry
