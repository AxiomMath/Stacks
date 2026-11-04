module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# Japanese, universally Japanese and Nagata schemes

A scheme is Japanese (when integral), universally Japanese, or Nagata when every point has an
affine open neighbourhood whose ring of sections is a Japanese, universally Japanese, or Nagata
ring respectively.

For an integral scheme, being Japanese can be checked on every affine open, on one affine open
cover, or on one open cover by Japanese schemes, and the property is inherited by nonempty open
subschemes. A scheme is Nagata exactly when it is locally Noetherian and universally Japanese,
and — in the locally Noetherian case — exactly when every integral closed subscheme is Japanese.

## Main definitions

* `IsUniversallyJapaneseScheme` is the universally Japanese condition for schemes.

## Main results

* `isJapaneseScheme_tfae` gives four equivalent characterizations of a Japanese integral scheme.
* `isJapaneseScheme_open` shows the property passes to nonempty open subschemes.
* `isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme` characterizes Nagata
  schemes by local Noetherianity together with universal Japaneseness.

## Implementation notes

An affine open neighbourhood is represented by an affine open together with membership of the
given point, and the ring of sections is then tested with the corresponding ring predicate.
Since `IsJapaneseScheme` takes an `IsIntegral` instance, Japanese-ness of an open subscheme is
packaged together with the assertion that the open subscheme is integral. Nonemptiness is made
explicit wherever a ring of sections of an integral scheme is regarded as a domain.

## References

* [Stacks Project, Tag 033S](https://stacks.math.columbia.edu/tag/033S)
* [Stacks Project, Tag 033V](https://stacks.math.columbia.edu/tag/033V)
* [Stacks Project, Tag 033Y](https://stacks.math.columbia.edu/tag/033Y)
* [Stacks Project, Tag 033Z](https://stacks.math.columbia.edu/tag/033Z)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/-- A scheme is **universally Japanese** if every point has an affine open neighbourhood whose
ring of sections is universally Japanese. -/
@[stacks 033S "universally_japanese_scheme",
  ega "IV 5.11.4",
  sga "4 IX 2.14.2"]
public def IsUniversallyJapaneseScheme
    (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ IsUniversallyJapaneseRing Γ(X, U.val)

/-- A nonempty open subscheme of a Japanese integral scheme is integral and Japanese. -/
private theorem isJapaneseScheme_open_aux (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseScheme X) (U : X.Opens) [Nonempty U] :
    ∃ hU : IsIntegral U.toScheme, @IsJapaneseScheme U.toScheme hU := by
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : U.toScheme.affineOpens := ⟨V₀, hV₀⟩
  let W : X.affineOpens :=
    ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩
  let : Nonempty W.1 := ⟨⟨U.ι x, ⟨x, hxV, rfl⟩⟩⟩
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let : IsDomain Γ(U.toScheme, V.1) := IsIntegral.component_integral V.1
  exact ⟨V, hxV,
    IsJapaneseRing.of_ringEquiv (U.ι.appIso V.1).commRingCatIsoToRingEquiv
      (isJapaneseScheme_forall_affineOpens X hX W)⟩

/-- **Stacks Project, Tag 033V.** For an integral scheme, Japanese-ness is equivalent to
Japanese-ness of the section ring of every nonempty affine open, to the existence of an affine
open cover with Japanese section rings, and to the existence of an open cover by Japanese
schemes. -/
@[stacks 033V "equivalent conditions"]
public theorem isJapaneseScheme_tfae (X : Scheme.{u}) [IsIntegral X] :
    List.TFAE [
      IsJapaneseScheme X,
      ∀ U : X.affineOpens, ∀ _hU : Nonempty U.1,
        letI : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
        IsJapaneseRing Γ(X, U.1),
      ∃ (I : Type u) (U : I → X.affineOpens),
        TopologicalSpace.IsOpenCover (fun i ↦ (U i).1) ∧
          ∀ i, ∃ _hU : Nonempty (U i).1,
            letI : IsDomain Γ(X, (U i).1) := IsIntegral.component_integral (U i).1
            IsJapaneseRing Γ(X, (U i).1),
      ∃ (I : Type u) (U : I → X.Opens),
        TopologicalSpace.IsOpenCover U ∧
        ∀ i, ∃ hU : IsIntegral (U i).toScheme,
            @IsJapaneseScheme (U i).toScheme hU] := by
  classical
  tfae_have 1 → 2 := fun h U _ ↦ isJapaneseScheme_forall_affineOpens X h U
  tfae_have 2 → 1 := by
    intro h x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨W, hW⟩, hxW, h ⟨W, hW⟩ ⟨⟨x, hxW⟩⟩⟩
  tfae_have 1 → 3 := by
    intro h
    let U : X → X.affineOpens := fun x => Classical.choose (h x)
    refine ⟨X, U, ?_, ?_⟩
    · show (⨆ x : X, (U x).1) = ⊤
      exact top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (Classical.choose_spec (h x)).1⟩
    · intro x
      obtain ⟨hx, hj⟩ := Classical.choose_spec (h x)
      exact ⟨⟨⟨x, hx⟩⟩, hj⟩
  tfae_have 3 → 1 := by
    rintro ⟨I, U, hcover, hprop⟩ x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, (U i).1 from by rw [hcover]; trivial)
    obtain ⟨hU, hj⟩ := hprop i
    let : Nonempty (U i).1 := ⟨⟨x, hxi⟩⟩
    exact ⟨U i, hxi, hj⟩
  tfae_have 1 → 4 := by
    intro h
    let V : X → X.affineOpens := fun x => Classical.choose (h x)
    refine ⟨X, fun x => (V x).1, ?_, ?_⟩
    · show (⨆ x : X, (V x).1) = ⊤
      exact top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (Classical.choose_spec (h x)).1⟩
    intro x
    let : Nonempty (V x).1 := ⟨⟨x, (Classical.choose_spec (h x)).1⟩⟩
    exact isJapaneseScheme_open_aux X h (V x).1
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hcover, hprop⟩ x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, U i from by rw [hcover]; trivial)
    obtain ⟨hInt, hj⟩ := hprop i
    let : IsIntegral (U i).toScheme := hInt
    let xU : (U i).toScheme := ⟨x, hxi⟩
    obtain ⟨V, hxV, hjV⟩ := hj xU
    let W : X.affineOpens :=
      ⟨(U i).ι ''ᵁ V.1, V.2.image_of_isOpenImmersion (U i).ι⟩
    have hxW : x ∈ W.1 := ⟨xU, hxV, rfl⟩
    let : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    let : Nonempty V.1 := ⟨⟨xU, hxV⟩⟩
    let : IsDomain Γ((U i).toScheme, V.1) := IsIntegral.component_integral V.1
    exact ⟨W, hxW, IsJapaneseRing.of_ringEquiv
      ((U i).ι.appIso V.1).commRingCatIsoToRingEquiv.symm hjV⟩
  tfae_finish

/-- **Stacks Project, Tag 033V.** Every nonempty open subscheme of a Japanese integral scheme is
Japanese. -/
@[stacks 033V "open subschemes"]
public theorem isJapaneseScheme_open (X : Scheme.{u}) [IsIntegral X] (hX : IsJapaneseScheme X)
    (U : X.Opens) [Nonempty U] :
    ∃ hU : IsIntegral U.toScheme, @IsJapaneseScheme U.toScheme hU :=
  isJapaneseScheme_open_aux X hX U

/-- A ring is Nagata exactly when it is universally Japanese and Noetherian. -/
@[ega "IV 7.7.2"]
private theorem isNagataRing_iff_isUniversallyJapaneseRing_and_isNoetherianRing
    {R : Type u} [CommRing R] :
    IsNagataRing R ↔ (IsUniversallyJapaneseRing R ∧ IsNoetherianRing R) :=
  (isNagataRing_tfae (R := R)).out 1 3

/-- A scheme is Nagata if and only if it is locally Noetherian and universally Japanese. -/
@[stacks 033Z, stacks 033U "the forward implication: a Nagata scheme is locally Noetherian"]
public theorem isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme
    (X : Scheme.{u}) :
    IsNagataScheme X ↔
      (IsLocallyNoetherian X ∧
        IsUniversallyJapaneseScheme X) := by
  classical
  refine ⟨fun hX ↦ ?_, fun ⟨hNoetherian, hJapanese⟩ x ↦ ?_⟩
  · choose U hxU hU using hX
    simp_rw [isNagataRing_iff_isUniversallyJapaneseRing_and_isNoetherianRing] at hU
    have hcover : (⨆ x : X, (U x : X.Opens)) = ⊤ :=
      top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
    exact ⟨isLocallyNoetherian_of_affine_cover hcover fun x ↦ (hU x).2,
      fun x ↦ ⟨U x, hxU x, (hU x).1⟩⟩
  · obtain ⟨U, hxU, hU⟩ := hJapanese x
    exact ⟨U, hxU, isNagataRing_iff_isUniversallyJapaneseRing_and_isNoetherianRing.mpr
      ⟨hU, hNoetherian.component_noetherian U⟩⟩

add_to_stacks 033S "japanese_scheme" IsJapaneseScheme
add_to_stacks 033S "nagata_scheme" IsNagataScheme
add_to_stacks 033Y nagata_iff_integral_closed_subschemes_japanese

end
