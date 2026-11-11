module

public import StacksFrontier.CategoryTheory.Sites.Representable.EffectiveEpiFamily

/-! # Stability properties of fpqc coverings

Stacks 022D: isomorphisms are fpqc coverings, and fpqc coverings are stable under composition
and base change. "Fpqc covering" is Stacks' own notion (Definition 022B), formalized as
`IsFpqcCoveringFamily`; the bridge `isFpqcCoveringFamily_iff_flat_and_quasiCompactCover`
identifies it with "flat members and a `QuasiCompactCover`", which is how the proofs reach
Mathlib's quasi-compact cover API.

## Main results

* `isFpqcCoveringFamily_iff_flat_and_quasiCompactCover`: bridge to Mathlib.
* `IsFpqcCoveringFamily.of_isIso`, `IsFpqcCoveringFamily.sigma`,
  `IsFpqcCoveringFamily.pullback_fst`: Stacks 022D (1), (2), (3).
* `isFpqcCoveringFamily_of_isIso_and_comp_and_pullback`: Stacks 022D, all three parts.

Tags covered: 022D.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

section Stability

universe w₁ w₂ u₁

/-- **Bridge to Mathlib.** A family `{ f i : T' i ⟶ T }` is an fpqc covering in the sense of
Stacks 022B exactly when every `f i` is flat and the pre-`0`-hypercover `⟨ι, T', f⟩` is a
`QuasiCompactCover`, i.e. every affine open of `T` is covered by the images of finitely many
quasi-compact opens of the members. -/
theorem isFpqcCoveringFamily_iff_flat_and_quasiCompactCover {ι : Type*} {T : Scheme}
    {T' : ι → Scheme} {f : ∀ i, T' i ⟶ T} :
    IsFpqcCoveringFamily T' f ↔
      (∀ i, Flat (f i)) ∧ QuasiCompactCover (⟨ι, T', f⟩ : PreZeroHypercover T) := by
  refine ⟨fun hf => ⟨hf.flat, ?_⟩, fun ⟨hflat, hqc⟩ => ⟨hflat, fun U hU => ?_⟩⟩
  · rw [quasiCompactCover_iff]
    intro U hU
    obtain ⟨n, a, W, hWaff, hcov⟩ := hf.covers U hU
    exact IsCompactOpenCovered.of_finite
      (f := fun i => ⇑((⟨ι, T', f⟩ : PreZeroHypercover T).f i)) a W
      (fun j => (hWaff j).isCompact) hcov
  · exact QuasiCompactCover.exists_isAffineOpen_of_isCompact
      (⟨ι, T', f⟩ : PreZeroHypercover T) hU.isCompact

/-- **Stacks 022D (1).** If `f : T' ⟶ T` is an isomorphism, then the one-member family
`{ f : T' ⟶ T }` is an fpqc covering of `T`. -/
theorem IsFpqcCoveringFamily.of_isIso {T T' : Scheme} (f : T' ⟶ T) [IsIso f] :
    IsFpqcCoveringFamily (fun _ : Unit => T') (fun _ => f) :=
  isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mpr
    ⟨fun _ => inferInstance, QuasiCompactCover.singleton (S := T) f⟩

/-- **Stacks 022D (2).** If `{ f i : T' i ⟶ T }` is an fpqc covering and for each `i` the
family `{ g i j : T'' i j ⟶ T' i }` is an fpqc covering of `T' i`, then the composite family
`{ g i j ≫ f i : T'' i j ⟶ T }`, indexed by the pairs `(i, j)`, is an fpqc covering of `T`. -/
theorem IsFpqcCoveringFamily.sigma {ι : Type w₁} {T : Scheme.{u₁}} {T' : ι → Scheme.{u₁}}
    {f : ∀ i, T' i ⟶ T} (hf : IsFpqcCoveringFamily T' f) {J : ι → Type w₂}
    {T'' : ∀ i, J i → Scheme.{u₁}} {g : ∀ i j, T'' i j ⟶ T' i}
    (hg : ∀ i, IsFpqcCoveringFamily (T'' i) (g i)) :
    IsFpqcCoveringFamily (fun p : Σ i, J i => T'' p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) := by
  obtain ⟨hfl, hqc⟩ := isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mp hf
  have hg' i := isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mp (hg i)
  refine isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mpr ⟨fun p => ?_, ?_⟩
  · have := hfl p.1
    have := (hg' p.1).1 p.2
    infer_instance
  · let 𝒰 : PreZeroHypercover T := ⟨ι, T', f⟩
    let 𝒱 : ∀ i, PreZeroHypercover (T' i) := fun i => ⟨J i, T'' i, g i⟩
    have h𝒱 : ∀ i, QuasiCompactCover (𝒱 i) := fun i => (hg' i).2
    refine ⟨fun {U} hU => ?_⟩
    obtain ⟨s, hs, V, hcV, hU⟩ := hU.isCompactOpenCovered 𝒰
    have (i) (hi) : IsCompactOpenCovered ((𝒱 i).f ·) (V i hi) :=
      QuasiCompactCover.isCompactOpenCovered_of_isCompact (𝒱 i) (hcV i hi)
    choose t ht W hcW hV using this
    have : Finite s := hs
    have (i) (hi) : Finite (t i hi) := ht i hi
    refine .of_finite (κ := Σ (i : s), t i.1 i.2) (fun p ↦ ⟨p.1, p.2⟩)
      (fun p ↦ W _ p.1.2 _ p.2.2) (fun p ↦ hcW ..) ?_
    simpa [𝒰, 𝒱, ← hV, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion,
      Set.image_image] using! hU

/-- **Stacks 022D (3).** If `{ f i : T' i ⟶ T }` is an fpqc covering and `g : S ⟶ T` is any
morphism of schemes, then the base change `{ S ×_T T' i ⟶ S }` (first projections) is an
fpqc covering of `S`. -/
theorem IsFpqcCoveringFamily.pullback_fst {ι : Type*} {T : Scheme.{u₁}} {T' : ι → Scheme.{u₁}}
    {f : ∀ i, T' i ⟶ T} (hf : IsFpqcCoveringFamily T' f) {S : Scheme.{u₁}} (g : S ⟶ T) :
    IsFpqcCoveringFamily (fun i => pullback g (f i)) (fun i => pullback.fst g (f i)) := by
  obtain ⟨hfl, hqc⟩ := isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mp hf
  refine isFpqcCoveringFamily_iff_flat_and_quasiCompactCover.mpr ⟨fun i => ?_, ?_⟩
  · have := hfl i
    infer_instance
  · exact (inferInstance : QuasiCompactCover ((⟨ι, T', f⟩ : PreZeroHypercover T).pullback₁ g))

/-- **Stacks 022D.** Let `T` be a scheme.
1. If `T' ⟶ T` is an isomorphism, then `{ T' ⟶ T }` is an fpqc covering of `T`.
2. If `{ T i ⟶ T }` is an fpqc covering and for each `i` the family `{ T i j ⟶ T i }` is an
   fpqc covering, then `{ T i j ⟶ T }` (indexed by all pairs `(i, j)`) is an fpqc covering.
3. If `{ T i ⟶ T }` is an fpqc covering and `T' ⟶ T` is a morphism of schemes, then
   `{ T' ×_T T i ⟶ T' }` is an fpqc covering.

Here "fpqc covering" is Stacks' own notion `IsFpqcCoveringFamily` (Definition 022B). -/
@[stacks 022D "all three parts, for fpqc coverings in the sense of Definition 022B \
(`IsFpqcCoveringFamily`: flat members, every affine open of the base covered by the images of \
finitely many affine opens): (1) an isomorphism is an fpqc covering, (2) composites of fpqc \
coverings are fpqc coverings, (3) base changes of fpqc coverings are fpqc coverings"]
theorem isFpqcCoveringFamily_of_isIso_and_comp_and_pullback :
    (∀ {T T' : Scheme.{u₁}} (f : T' ⟶ T) [IsIso f],
      IsFpqcCoveringFamily (fun _ : Unit => T') (fun _ => f)) ∧
    (∀ {ι : Type w₁} {T : Scheme.{u₁}} {T' : ι → Scheme.{u₁}} {f : ∀ i, T' i ⟶ T}
      {J : ι → Type w₂} {T'' : ∀ i, J i → Scheme.{u₁}} {g : ∀ i j, T'' i j ⟶ T' i},
      IsFpqcCoveringFamily T' f → (∀ i, IsFpqcCoveringFamily (T'' i) (g i)) →
      IsFpqcCoveringFamily (fun p : Σ i, J i => T'' p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1)) ∧
    (∀ {ι : Type w₁} {T : Scheme.{u₁}} {T' : ι → Scheme.{u₁}} {f : ∀ i, T' i ⟶ T}
      {S : Scheme.{u₁}} (g : S ⟶ T), IsFpqcCoveringFamily T' f →
      IsFpqcCoveringFamily (fun i => pullback g (f i)) (fun i => pullback.fst g (f i))) :=
  ⟨fun f _ => .of_isIso f, fun hf hg => hf.sigma hg, fun g hf => hf.pullback_fst g⟩

end Stability
