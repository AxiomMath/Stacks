module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ProperFiniteFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FiniteFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# A proper surface over a two-dimensional local base is an isomorphism off the closed point

Let `A` be a local ring of Krull dimension at least two and let `f : W ⟶ Spec A` be a proper
morphism from an irreducible scheme of dimension at most two inducing an isomorphism
`A ≅ Γ(W, 𝒪_W)`. Then `f` is an isomorphism over every open of `Spec A` avoiding the closed
point, in particular over the punctured spectrum.

## Main results

* `AlgebraicGeometry.three_le_topologicalKrullDim_of_specializes`: three successive strict
  specializations in a `T0` space give dimension at least three.
* `AlgebraicGeometry.eq_of_specializes_of_map_eq_of_topologicalKrullDim_le_two`: the point-set
  heart of the argument: in the situation above two points of a fibre over a non-closed point
  that specialize to one another coincide.
* `AlgebraicGeometry.isIso_morphismRestrict_of_finite_preimage_singleton`: a proper morphism to
  an affine scheme which is an isomorphism on global sections is an isomorphism over every open
  of the target over which its fibres are finite.
* `AlgebraicGeometry.finite_preimage_singleton_of_ne_closedPoint`: in the situation above the
  fibres of `f` over the points other than the closed point are finite.
* `AlgebraicGeometry.isIso_morphismRestrict_of_closedPoint_not_mem`: the main theorem, `f` is an
  isomorphism over every open avoiding the closed point.
* `AlgebraicGeometry.isIso_morphismRestrict_puncturedSpectrum`: the same over the punctured
  spectrum `Spec A ∖ {𝔪}`.

## Implementation notes

The finiteness of the fibres is purely topological. `f` is dominant because it is injective on
global sections, so the generic point `η` of `W` lies over the generic point of `Spec A`. A
nontrivial specialization `x ⤳ y` inside the fibre over a point `q ≠ 𝔪` lifts, along the closed
map `f`, to a chain `x ⤳ y ⤳ z` with `z` over `𝔪`; if `x ≠ η` the chain `η ⤳ x ⤳ y ⤳ z` has
length three, and if `x = η` then `q` is the generic point and a chain of length two in
`Spec A` lifts to a chain of length three starting at `η`. Either way `dim W ≥ 3`. Hence each
fibre of a point `q ≠ 𝔪` is a Noetherian `T1` sober space, so finite.

Over a basic open `D(r)` avoiding `𝔪` the restriction of `f` is then proper with finite fibres,
so finite by [Stacks, Tag 02LS], so affine; and `Γ(D(r), 𝒪) ⟶ Γ(f⁻¹D(r), 𝒪_W)` is the
localization at `r` of the isomorphism `A ≅ Γ(W, 𝒪_W)` (the qcqs lemma), hence an isomorphism.
An affine morphism to an affine scheme which is an isomorphism on global sections is an
isomorphism, and such basic opens cover every open avoiding `𝔪`.

## References

* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Three successive strict specializations `a ⤳ b ⤳ c ⤳ d` in a `T0` space give a chain of
four irreducible closed subsets, so the space has Krull dimension at least three. -/
theorem three_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X] [T0Space X]
    {a b c d : X} (hab : a ⤳ b) (hbc : b ⤳ c) (hcd : c ⤳ d) (hab' : a ≠ b) (hbc' : b ≠ c)
    (hcd' : c ≠ d) : (3 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  have hlt : ∀ {x y : X}, x ⤳ y → x ≠ y →
      IrreducibleCloseds.closureSingleton y < IrreducibleCloseds.closureSingleton x := by
    intro x y h hne
    refine lt_of_le_of_ne (specializes_iff_closure_subset.1 h) fun heq ↦ hne ?_
    have hcl : closure ({y} : Set X) = closure {x} := congrArg SetLike.coe heq
    exact (inseparable_iff_closure_eq.2 hcl.symm).eq
  have h := Order.LTSeries.length_le_krullDim
    ((((RelSeries.singleton _ (IrreducibleCloseds.closureSingleton d)).snoc
      (IrreducibleCloseds.closureSingleton c) (by simpa using hlt hcd hcd')).snoc
      (IrreducibleCloseds.closureSingleton b) (by simpa using hlt hbc hbc')).snoc
      (IrreducibleCloseds.closureSingleton a) (by simpa using hlt hab hab'))
  simpa [topologicalKrullDim] using h

/-- **The point-set heart of the argument.** Let `f : W → S` be a specializing map of `T0`
spaces, `W` of Krull dimension at most two with a point `η` specializing to every point, and
assume `f η` specializes to every point of `S`, that `S` has a point `s₀` to which every point
specializes, and that `S` has a strict specialization `p₁ ⤳ p₂` with `p₁ ≠ f η`. Then two points
of a fibre over a point `q ≠ s₀` which specialize to one another are equal. -/
theorem eq_of_specializes_of_map_eq_of_topologicalKrullDim_le_two {W S : Type*}
    [TopologicalSpace W] [TopologicalSpace S] [T0Space W] {f : W → S} (hf : SpecializingMap f)
    (hW : topologicalKrullDim W ≤ 2) {η : W} (hη : ∀ w, η ⤳ w) (hgen : ∀ s, f η ⤳ s)
    {s₀ : S} (hs₀ : ∀ s, s ⤳ s₀) {p₁ p₂ : S} (hηp₁ : f η ≠ p₁) (h₁₂ : p₁ ⤳ p₂)
    (h₁₂' : p₁ ≠ p₂) {q : S} (hq : q ≠ s₀) {x y : W} (hxy : x ⤳ y) (hx : f x = q)
    (hy : f y = q) : x = y := by
  by_contra hne
  have h3 : ¬ (3 : WithBot ℕ∞) ≤ topologicalKrullDim W := fun h ↦
    absurd (h.trans hW) (by decide)
  by_cases hηx : η = x
  · subst hηx
    obtain ⟨y₁, hyy₁, hy₁⟩ := hf (show f y ⤳ p₁ by rw [hy, ← hx]; exact hgen p₁)
    obtain ⟨y₂, hy₁y₂, hy₂⟩ := hf (show f y₁ ⤳ p₂ by rw [hy₁]; exact h₁₂)
    refine h3 (three_le_topologicalKrullDim_of_specializes hxy hyy₁ hy₁y₂ hne ?_ ?_)
    · rintro rfl
      exact hηp₁ (hx.trans (hy.symm.trans hy₁))
    · rintro rfl
      exact h₁₂' (hy₁.symm.trans hy₂)
  · obtain ⟨z, hyz, hz⟩ := hf (show f y ⤳ s₀ from hs₀ _)
    refine h3 (three_le_topologicalKrullDim_of_specializes (hη x) hxy hyz hηx hne ?_)
    rintro rfl
    exact hq (hy.symm.trans hz)

/-- A proper morphism `f : X ⟶ Y` to an affine scheme which induces an isomorphism
`Γ(Y, 𝒪_Y) ≅ Γ(X, 𝒪_X)` is an isomorphism over every open `V ⊆ Y` over whose points the fibres
of `f` are finite. Over a basic open inside `V` the restriction of `f` is finite by
[Stacks, Tag 02LS], hence affine, and it is an isomorphism on global sections because both sides
are the localization of `Γ(Y, 𝒪_Y) ≅ Γ(X, 𝒪_X)` at the same element. -/
theorem isIso_morphismRestrict_of_finite_preimage_singleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsProper f] [IsIso f.appTop] (V : Y.Opens)
    (hV : ∀ y ∈ V, (f ⁻¹' {y}).Finite) : IsIso (f ∣_ V) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hD : ∀ r : Γ(Y, ⊤), Y.basicOpen r ≤ V → IsIso (f ∣_ Y.basicOpen r) := by
    intro r hr
    have hc : IsCompact (f ⁻¹ᵁ (⊤ : Y.Opens)).1 := by simpa using isCompact_univ
    have hqs : IsQuasiSeparated (f ⁻¹ᵁ (⊤ : Y.Opens)).1 := by simpa using isQuasiSeparated_univ
    have : IsIso (f.app ⊤) := inferInstanceAs (IsIso f.appTop)
    have happ : IsIso (f.app (Y.basicOpen r)) :=
      Stacks.AlgebraicGeometry.isIso_app_basicOpen f (isAffineOpen_top Y) hc hqs r
    have : IsAffine (Y.basicOpen r) := (isAffineOpen_top Y).basicOpen r
    have : IsProper (f ∣_ Y.basicOpen r) := IsZariskiLocalAtTarget.restrict ‹_› _
    have hfin : IsFinite (f ∣_ Y.basicOpen r) := by
      refine (isFinite_iff_isProper_and_forall_finite_preimage_singleton _).2
        ⟨inferInstance, fun u ↦ ?_⟩
      refine ((hV u.1 (hr u.2)).preimage Subtype.val_injective.injOn).subset fun x hx ↦ ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      exact (morphismRestrict_base_coe f _ x).symm.trans (congrArg Subtype.val hx)
    have : IsAffine (f ⁻¹ᵁ Y.basicOpen r) := isAffine_of_isAffineHom (f ∣_ Y.basicOpen r)
    have key : ∀ W : Y.Opens, W = Y.basicOpen r → IsIso (f.app W) := by
      rintro _ rfl
      exact happ
    have hΓ : IsIso (f ∣_ Y.basicOpen r).appTop := by
      rw [morphismRestrict_appTop]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (key _ (Scheme.Opens.ι_image_top _))
        (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f _ ⊤)).op).isIso_hom
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine (f ∣_ Y.basicOpen r))).2 ?_
    exact (inferInstance : IsIso (Spec.map (f ∣_ Y.basicOpen r).appTop))
  let I := {r : Γ(Y, ⊤) // Y.basicOpen r ≤ V}
  let U : I → V.toScheme.Opens := fun r ↦ V.ι ⁻¹ᵁ Y.basicOpen r.1
  have hU : iSup U = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top Y).exists_basicOpen_le (V := V) x trivial
    exact Opens.mem_iSup.2 ⟨⟨r, hr⟩, hxr⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU
    fun i ↦ ?_
  have hi : V.ι ''ᵁ U i = Y.basicOpen i.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 i.2
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (U i) ≪≫ morphismRestrictEq f hi)).2 ?_
  exact hD i.1 i.2

variable {A : Type u} [CommRing A] [IsLocalRing A] {W : Scheme.{u}} (f : W ⟶ Spec (.of A))

/-- Let `A` be a local ring of Krull dimension at least two and `f : W ⟶ Spec A` a proper
morphism from an irreducible scheme of Krull dimension at most two which is an isomorphism on
global sections. Then the fibre of `f` over every point other than the closed point is finite. -/
theorem finite_preimage_singleton_of_ne_closedPoint (hA : 2 ≤ ringKrullDim A)
    [IrreducibleSpace W] [IsProper f] [IsIso f.appTop] (hW : topologicalKrullDim W ≤ 2)
    (q : Spec (.of A)) (hq : q ≠ closedPoint A) : (f ⁻¹' {q}).Finite := by
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
  have hdom : IsDominant f :=
    isDominant_of_of_appTop_injective (ConcreteCategory.bijective_of_isIso f.appTop).1
  set η := genericPoint W
  have hη : ∀ w : W, η ⤳ w := fun w ↦ (genericPoint_spec W).specializes (Set.mem_univ w)
  have hgen : ∀ s : Spec (.of A), f η ⤳ s := by
    intro s
    rw [specializes_iff_mem_closure]
    have hsub : Set.range f ⊆ closure {f η} := by
      rintro _ ⟨w, rfl⟩
      exact specializes_iff_mem_closure.1 ((hη w).map f.continuous)
    refine closure_minimal hsub isClosed_closure ?_
    rw [f.denseRange.closure_range]
    exact Set.mem_univ s
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (show ((2 : ℕ) : WithBot ℕ∞) ≤ _ from hA)
  let i₀ : Fin (l.length + 1) := ⟨0, by omega⟩
  let i₁ : Fin (l.length + 1) := ⟨1, by omega⟩
  let i₂ : Fin (l.length + 1) := ⟨2, by omega⟩
  have h01 : l i₀ < l i₁ := l.strictMono (show i₀ < i₁ from Fin.lt_def.2 (by simp [i₀, i₁]))
  have h12 : l i₁ < l i₂ := l.strictMono (show i₁ < i₂ from Fin.lt_def.2 (by simp [i₁, i₂]))
  let p₁ : Spec (.of A) := l i₁
  let p₂ : Spec (.of A) := l i₂
  have hηp₁ : f η ≠ p₁ := by
    intro h
    have h10 : p₁ ⤳ (l i₀ : Spec (.of A)) := h ▸ hgen _
    exact (lt_irrefl _) (h01.trans_le ((PrimeSpectrum.le_iff_specializes _ _).2 h10))
  have h₁₂ : p₁ ⤳ p₂ := (PrimeSpectrum.le_iff_specializes _ _).1 h12.le
  have h₁₂' : p₁ ≠ p₂ := h12.ne
  have heq : ∀ {x y : W}, x ⤳ y → f x = q → f y = q → x = y := fun hxy hx hy ↦
    eq_of_specializes_of_map_eq_of_topologicalKrullDim_le_two f.isClosedMap.specializingMap hW
      hη hgen (s₀ := (closedPoint A : PrimeSpectrum A)) (fun s ↦ specializes_closedPoint s)
      hηp₁ h₁₂ h₁₂' hq hxy hx hy
  have : IsLocallyNoetherian (f.fiber q) := isLocallyNoetherian_fiber_of_locallyOfFiniteType f q
  have : IsNoetherian (f.fiber q) := {}
  have hmap : ∀ a : f.fiber q, f (f.fiberι q a) = q := fun a ↦ by
    have : f.fiberι q a ∈ Set.range (f.fiberι q) := ⟨a, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have : T1Space (f.fiber q) := by
    refine t1Space_iff_specializes_imp_eq.2 fun a b hab ↦ ?_
    exact (f.fiberι q).isEmbedding.injective
      (heq (hab.map (f.fiberι q).continuous) (hmap a) (hmap b))
  have : Finite (f.fiber q) := Stacks.SteinFactorization.finite_of_noetherianSpace_of_t1Space _
  have : Finite (f ⁻¹' {q} : Set W) := Finite.of_equiv _ (f.fiberHomeo q).toEquiv
  exact Set.toFinite _

/-- **A proper surface over a two-dimensional local base with the right global functions is an
isomorphism off the closed point.** Let `A` be a local ring of Krull dimension at least two and
`f : W ⟶ Spec A` a proper morphism from an irreducible scheme of Krull dimension at most two
inducing an isomorphism `A ≅ Γ(W, 𝒪_W)`. Then `f` is an isomorphism over every open `U` of
`Spec A` not containing the closed point. -/
theorem isIso_morphismRestrict_of_closedPoint_not_mem (hA : 2 ≤ ringKrullDim A)
    [IrreducibleSpace W] [IsProper f] [IsIso f.appTop] (hW : topologicalKrullDim W ≤ 2)
    (U : (Spec (.of A)).Opens) (hU : (closedPoint A : Spec (.of A)) ∉ U) : IsIso (f ∣_ U) :=
  isIso_morphismRestrict_of_finite_preimage_singleton f U fun q hq ↦
    finite_preimage_singleton_of_ne_closedPoint f hA hW q fun h ↦ hU (h ▸ hq)

/-- The punctured spectrum `Spec A ∖ {𝔪}` of a local ring, as an open of `Spec A`. -/
def puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A] : (Spec (.of A)).Opens :=
  ⟨{(closedPoint A : PrimeSpectrum A)}ᶜ, (isClosed_singleton_closedPoint A).isOpen_compl⟩

/-- **The main theorem over the punctured spectrum.** Under the hypotheses of
`AlgebraicGeometry.isIso_morphismRestrict_of_closedPoint_not_mem`, `f` is an isomorphism over
`Spec A ∖ {𝔪}`. -/
theorem isIso_morphismRestrict_puncturedSpectrum (hA : 2 ≤ ringKrullDim A)
    [IrreducibleSpace W] [IsProper f] [IsIso f.appTop] (hW : topologicalKrullDim W ≤ 2) :
    IsIso (f ∣_ puncturedSpectrum A) :=
  isIso_morphismRestrict_of_closedPoint_not_mem f hA hW _ fun h ↦ h rfl

end AlgebraicGeometry

end
