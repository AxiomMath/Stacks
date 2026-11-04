module

public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The proper part of the closed fibre over a henselian pair, through Chow's lemma

Let `(A, I)` be a henselian pair, let `X` be separated and of finite type over `Spec A` and let
`Y` be an open and closed subscheme of the closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)` which is
proper over `Spec (A ⧸ I)`.  [Stacks, Tag 0CT9] says that `Y` is then the closed fibre of an
open and closed subscheme `W ⊆ X` which is proper over `Spec A`.

## Main results

* `AlgebraicGeometry.exists_isClopen_isProper_range_eq_of_henselianPair_of_compactification`:
  the statement for a morphism factoring as an open immersion followed by a proper morphism.
* `AlgebraicGeometry.exists_isClopen_isProper_range_eq_of_henselianPair`: [Stacks, Tag 0CT9]
  with the closed fibre of `W` recorded as an equality of subsets.
* `AlgebraicGeometry.exists_isClopen_isProper_of_henselianPair`: [Stacks, Tag 0CT9].

## References

* [Stacks Project, Tag 0CT9](https://stacks.math.columbia.edu/tag/0CT9)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [EGA III, Proposition 5.5.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The range of one leg of a cartesian square of schemes is the preimage of the range of the
opposite one. -/
private theorem range_eq_preimage_range_of_isPullback {P X Y S : Scheme.{u}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hp : IsPullback a b f g) :
    Set.range a = f ⁻¹' Set.range g := by
  rw [← hp.isoPullback_hom_fst]
  change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
  rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- Let `(A, I)` be a henselian pair, let `f : X ⟶ Spec A` be separated and of finite type and let
`f` factor as an open immersion `j : X ⟶ P` followed by a proper `π : P ⟶ Spec A`.  An open and
closed subscheme `i : Y ⟶ X ×_{Spec A} Spec (A ⧸ I)` of the closed fibre which is proper over
`Spec (A ⧸ I)` is then the closed fibre of an open and closed subscheme `w : W ⟶ X` proper over
`Spec A`, the closed fibre being recorded as an equality of subsets. -/
theorem exists_isClopen_isProper_range_eq_of_henselianPair_of_compactification (A : Type u)
    [CommRing A] (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] {P : Scheme.{u}} (j : X ⟶ P)
    (π : P ⟶ Spec (.of A)) [IsOpenImmersion j] [IsProper π] (hj : j ≫ π = f) {Y : Scheme.{u}}
    (i : Y ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    [IsOpenImmersion i] [IsClosedImmersion i]
    [IsProper (i ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (W : Scheme.{u}) (w : W ⟶ X), IsOpenImmersion w ∧ IsClosedImmersion w ∧
      IsProper (w ≫ f) ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹' Set.range w =
        Set.range i := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  obtain ⟨W, w, hwo, hwc, hwp, e, he⟩ :=
    exists_isClopen_isProper_of_henselianPair_of_compactification A I hI f
      ⟨P, j, π, inferInstance, inferInstance, hj⟩
      (fun π _ ↦ Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper π) i
  refine ⟨W, w, hwo, hwc, hwp, ?_⟩
  change e.hom ≫ pullbackMapOfFac w f (w ≫ f) rfl q = i at he
  rw [← range_eq_preimage_range_of_isPullback
    (isPullback_pullbackMapOfFac w f (w ≫ f) rfl q), ← he]
  show _ = Set.range (pullbackMapOfFac w f (w ≫ f) rfl q ∘ e.hom)
  rw [Set.range_comp, e.hom.surjective.range_eq, Set.image_univ]

/-- Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be separated and of finite type.  An
open and closed subscheme `i : Y ⟶ X ×_{Spec A} Spec (A ⧸ I)` of the closed fibre which is proper
over `Spec (A ⧸ I)` is the closed fibre of an open and closed subscheme `w : W ⟶ X` which is
proper over `Spec A`, the closed fibre being recorded as an equality of subsets. -/
@[ega "III 5.5.1" "more general"]
theorem exists_isClopen_isProper_range_eq_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] {Y : Scheme.{u}}
    (i : Y ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    [IsOpenImmersion i] [IsClosedImmersion i]
    [IsProper (i ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (W : Scheme.{u}) (w : W ⟶ X), IsOpenImmersion w ∧ IsClosedImmersion w ∧
      IsProper (w ≫ f) ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹' Set.range w =
        Set.range i := by
  classical
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hinj : Function.Injective (pullback.fst f q) :=
    (pullback.fst f q).isClosedEmbedding.injective
  have : QuasiSeparatedSpace (Spec (.of A)) := quasiSeparatedSpace_of_isAffine _
  obtain ⟨n, X', φ, ι, hφp, hφs, hιi, hfac⟩ :=
    hasChowModification_of_compactSpace_quasiSeparatedSpace f
  have : IsProper φ := hφp
  have : Surjective φ := hφs
  have : IsImmersion ι := hιi
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace φ
  have : QuasiSeparatedSpace (ProjectiveSpace n (Spec (.of A))) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace n (Spec (.of A)) ↘ Spec (.of A))
  have : QuasiCompact ι := inferInstance
  have hcfac : ι.toImage ≫ ι.imageι ≫ (ProjectiveSpace n (Spec (.of A)) ↘ Spec (.of A)) =
      φ ≫ f := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact hfac.symm
  let φ₀ := pullbackMapOfFac φ f (φ ≫ f) rfl q
  have hφ₀ := isPullback_pullbackMapOfFac φ f (φ ≫ f) rfl q
  have hφ₀f : ∀ x, pullback.fst f q (φ₀ x) = φ (pullback.fst (φ ≫ f) q x) := fun x ↦ by
    rw [← Scheme.Hom.comp_apply φ₀ (pullback.fst f q), hφ₀.w, Scheme.Hom.comp_apply]
  have : IsProper φ₀ := MorphismProperty.of_isPullback hφ₀.flip ‹IsProper φ›
  have : Surjective φ₀ := MorphismProperty.of_isPullback hφ₀.flip ‹Surjective φ›
  have hYclopen : IsClopen (Set.range i) :=
    ⟨i.isClosedEmbedding.isClosed_range, i.isOpenEmbedding.isOpen_range⟩
  obtain ⟨Y', i', hi'o, hi'c, hi'r⟩ :=
    exists_isOpenImmersion_isClosedImmersion_range_eq (hYclopen.preimage φ₀.continuous)
  have : IsOpenImmersion i' := hi'o
  have : IsClosedImmersion i' := hi'c
  have hsub : Set.range (i' ≫ φ₀) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have hy : i' y ∈ φ₀ ⁻¹' Set.range i := hi'r ▸ Set.mem_range_self y
    rwa [Scheme.Hom.comp_apply]
  let t := IsOpenImmersion.lift i (i' ≫ φ₀) hsub
  have ht : t ≫ i = i' ≫ φ₀ := IsOpenImmersion.lift_fac i (i' ≫ φ₀) hsub
  have : IsProper (t ≫ i) := by rw [ht]; infer_instance
  have : IsProper t := IsProper.of_comp t i
  have hφ₀s : φ₀ ≫ pullback.snd f q = pullback.snd (φ ≫ f) q := pullback.lift_snd _ _ _
  have : IsProper (i' ≫ pullback.snd (φ ≫ f) q) := by
    rw [← hφ₀s, ← Category.assoc, ← ht, Category.assoc]
    infer_instance
  obtain ⟨W', w', hw'o, hw'c, hw'p, hw'r⟩ :=
    exists_isClopen_isProper_range_eq_of_henselianPair_of_compactification A I hI (φ ≫ f)
      ι.toImage (ι.imageι ≫ (ProjectiveSpace n (Spec (.of A)) ↘ Spec (.of A))) hcfac i'
  have : IsOpenImmersion w' := hw'o
  have : IsClosedImmersion w' := hw'c
  have : IsProper (w' ≫ φ ≫ f) := hw'p
  have hw'clopen : IsClopen (Set.range w') :=
    ⟨w'.isClosedEmbedding.isClosed_range, w'.isOpenEmbedding.isOpen_range⟩
  obtain ⟨V', v', hv'o, hv'c, hv'r⟩ :=
    exists_isOpenImmersion_isClosedImmersion_range_eq hw'clopen.compl
  have : IsOpenImmersion v' := hv'o
  have : IsClosedImmersion v' := hv'c
  have hfib : ∀ x : X', f (φ x) ∈ PrimeSpectrum.zeroLocus (I : Set A) →
      ∃ x₀, pullback.fst (φ ≫ f) q x₀ = x := by
    intro x hx
    show x ∈ Set.range (pullback.fst (φ ≫ f) q)
    rw [Scheme.Pullback.range_fst, range_spec_map_quotient_mk I]
    show (φ ≫ f) x ∈ PrimeSpectrum.zeroLocus (I : Set A)
    simpa only [Scheme.Hom.comp_apply] using hx
  have hmem : ∀ x₀ : ↥(pullback (φ ≫ f) q),
      pullback.fst (φ ≫ f) q x₀ ∈ Set.range w' ↔ φ₀ x₀ ∈ Set.range i :=
    Set.ext_iff.mp (hw'r.trans hi'r)
  have hclosedW : IsClosed (Set.range (w' ≫ φ)) := (w' ≫ φ).isClosedMap.isClosed_range
  have hclosedQ : IsClosed (Set.range (v' ≫ φ)) := (v' ≫ φ).isClosedMap.isClosed_range
  have hw'pa : IsProper ((w' ≫ φ) ≫ f) := by rw [Category.assoc]; exact hw'p
  have hdisj : (w' ≫ φ) ⁻¹' Set.range (v' ≫ φ) ⊆ (∅ : Set W') := by
    refine subset_of_isClosed_of_forall_mem_zeroLocus I hI ((w' ≫ φ) ≫ f)
      ((w' ≫ φ) ≫ f).isClosedMap (hclosedQ.preimage (w' ≫ φ).continuous) isOpen_empty ?_
    intro x hx hxQ
    obtain ⟨y, hy⟩ := hxQ
    exfalso
    have he : φ (v' y) = φ (w' x) := by simpa only [Scheme.Hom.comp_apply] using hy
    have hxz : f (φ (w' x)) ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      simp only [Scheme.Hom.comp_apply] at hx
      exact hx
    obtain ⟨x₀, hx₀⟩ := hfib (w' x) hxz
    obtain ⟨y₀, hy₀⟩ := hfib (v' y) (by rwa [he])
    have h1 : φ₀ x₀ ∈ Set.range i := (hmem x₀).mp (hx₀ ▸ Set.mem_range_self x)
    have h2 : φ₀ y₀ ∉ Set.range i := by
      intro hcon
      have hw := (hmem y₀).mpr hcon
      rw [hy₀] at hw
      exact (hv'r ▸ Set.mem_range_self y : v' y ∈ (Set.range w')ᶜ) hw
    have hcoll : pullback.fst f q (φ₀ x₀) = pullback.fst f q (φ₀ y₀) := by
      rw [hφ₀f, hφ₀f, hx₀, hy₀, he]
    exact h2 (hinj hcoll ▸ h1)
  have hcover : Set.range (w' ≫ φ) ∪ Set.range (v' ≫ φ) = Set.univ := by
    refine Set.eq_univ_of_forall fun z ↦ ?_
    obtain ⟨z', rfl⟩ := φ.surjective z
    by_cases hz : z' ∈ Set.range w'
    · obtain ⟨a, rfl⟩ := hz
      exact Or.inl ⟨a, Scheme.Hom.comp_apply w' φ a⟩
    · have hz' : z' ∈ Set.range v' := by rw [hv'r]; exact hz
      obtain ⟨b, rfl⟩ := hz'
      exact Or.inr ⟨b, Scheme.Hom.comp_apply v' φ b⟩
  have hcompl : (Set.range (w' ≫ φ))ᶜ = Set.range (v' ≫ φ) := by
    apply Set.eq_of_subset_of_subset
    · intro z hz
      exact (Set.eq_univ_iff_forall.mp hcover z).resolve_left hz
    · intro z hz hzW
      obtain ⟨a, ha⟩ := hzW
      refine hdisj (show a ∈ (w' ≫ φ) ⁻¹' Set.range (v' ≫ φ) from ?_)
      rw [Set.mem_preimage, ha]
      exact hz
  have hWclopen : IsClopen (Set.range (w' ≫ φ)) := by
    refine ⟨hclosedW, ?_⟩
    have hc : IsClosed (Set.range (w' ≫ φ))ᶜ := by rw [hcompl]; exact hclosedQ
    simpa using hc.isOpen_compl
  obtain ⟨W, w, hwo, hwc, hwr⟩ := exists_isOpenImmersion_isClosedImmersion_range_eq hWclopen
  have : IsOpenImmersion w := hwo
  have : IsClosedImmersion w := hwc
  let s := IsOpenImmersion.lift w (w' ≫ φ) hwr.ge
  have hs : s ≫ w = w' ≫ φ := IsOpenImmersion.lift_fac w (w' ≫ φ) hwr.ge
  have : Surjective s := by
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨x, hx⟩ : w a ∈ Set.range (w' ≫ φ) := by
      rw [← hwr]
      exact Set.mem_range_self a
    refine ⟨x, w.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply s w, hs]
    exact hx
  have hu : UniversallyClosed (s ≫ w ≫ f) := by
    rw [← Category.assoc, hs, Category.assoc]
    infer_instance
  have : IsProper (w ≫ f) := isProper_of_comp_surjective s (w ≫ f)
  refine ⟨W, w, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [hwr]
  apply Set.eq_of_subset_of_subset
  · intro x₀ hx₀
    obtain ⟨a, ha⟩ := hx₀
    have hφa : φ (w' a) = pullback.fst f q x₀ := by
      simpa only [Scheme.Hom.comp_apply] using ha
    have hz : f (φ (w' a)) ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      rw [hφa]
      have hmr : pullback.fst f q x₀ ∈ Set.range (pullback.fst f q) := Set.mem_range_self x₀
      rw [Scheme.Pullback.range_fst, range_spec_map_quotient_mk I] at hmr
      exact hmr
    obtain ⟨a₀, ha₀⟩ := hfib (w' a) hz
    have h1 : φ₀ a₀ ∈ Set.range i := (hmem a₀).mp (ha₀ ▸ Set.mem_range_self a)
    have k : pullback.fst f q (φ₀ a₀) = pullback.fst f q x₀ := by
      rw [hφ₀f, ha₀, hφa]
    rw [hinj k] at h1
    exact h1
  · intro x₀ hx₀
    obtain ⟨z₀, hz₀⟩ := φ₀.surjective x₀
    obtain ⟨a, ha⟩ := (hmem z₀).mpr (hz₀ ▸ hx₀)
    show pullback.fst f q x₀ ∈ Set.range (w' ≫ φ)
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply (pullback.fst (φ ≫ f) q) φ,
      ← hφ₀.w, Scheme.Hom.comp_apply, hz₀]

/-- Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be separated and of finite type.  An
open and closed subscheme `i : Y ⟶ X ×_{Spec A} Spec (A ⧸ I)` of the closed fibre which is proper
over `Spec (A ⧸ I)` is the closed fibre of an open and closed subscheme `w : W ⟶ X` which is
proper over `Spec A`: there is an isomorphism `Y ≅ W ×_{Spec A} Spec (A ⧸ I)` over the closed
fibre. -/
@[stacks 0CT9 "the whole statement"]
theorem exists_isClopen_isProper_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] {Y : Scheme.{u}}
    (i : Y ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    [IsOpenImmersion i] [IsClosedImmersion i]
    [IsProper (i ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (W : Scheme.{u}) (w : W ⟶ X) (_ : IsOpenImmersion w) (_ : IsClosedImmersion w)
      (_ : IsProper (w ≫ f)),
      let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      let w₀ : pullback (w ≫ f) q ⟶ pullback f q :=
        pullback.lift (pullback.fst (w ≫ f) q ≫ w) (pullback.snd (w ≫ f) q)
          (by rw [Category.assoc]; exact pullback.condition)
      ∃ e : Y ≅ pullback (w ≫ f) q, e.hom ≫ w₀ = i := by
  classical
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  obtain ⟨W, w, hwo, hwc, hwp, hwr⟩ :=
    exists_isClopen_isProper_range_eq_of_henselianPair A I hI f i
  have : IsOpenImmersion w := hwo
  have : IsClosedImmersion w := hwc
  have : IsProper (w ≫ f) := hwp
  refine ⟨W, w, inferInstance, inferInstance, inferInstance, ?_⟩
  show ∃ e : Y ≅ pullback (w ≫ f) q, e.hom ≫ pullbackMapOfFac w f (w ≫ f) rfl q = i
  have : IsOpenImmersion (pullbackMapOfFac w f (w ≫ f) rfl q) :=
    MorphismProperty.of_isPullback (isPullback_pullbackMapOfFac w f (w ≫ f) rfl q).flip
      inferInstance
  have hr : Set.range i = Set.range (pullbackMapOfFac w f (w ≫ f) rfl q) := by
    rw [range_eq_preimage_range_of_isPullback (isPullback_pullbackMapOfFac w f (w ≫ f) rfl q),
      hwr]
  exact ⟨IsOpenImmersion.isoOfRangeEq i (pullbackMapOfFac w f (w ≫ f) rfl q) hr,
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

end AlgebraicGeometry

end
