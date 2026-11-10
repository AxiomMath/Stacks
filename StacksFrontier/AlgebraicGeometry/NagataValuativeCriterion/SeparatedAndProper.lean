module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.General.Nagata
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian

/-!
# Separatedness and properness over a Nagata base

Over a Nagata base `S`, separatedness and properness of a morphism `f : X ⟶ Y` between schemes
locally of finite type over `S` can be tested on the one-dimensional test diagrams of
`HasEssentiallyFiniteTypeValuativeExtension`: `f` is separated exactly when the lift in such a
diagram is unique, and — for quasi-compact `f` — proper exactly when it exists and is unique.

## Main definitions

* `HasEssentiallyFiniteTypeValuativeUniqueness`: in every one-dimensional finite-type test
  diagram there is *at most one* lift.
* `HasEssentiallyFiniteTypeValuativeLift`: in every such diagram there is *exactly one* lift.

## Main results

* `isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness`: tag `0GWW`.
* `isProper_iff_hasEssentiallyFiniteTypeValuativeLift`: tag `0GWX`.
* `isDominant_specMap_algebraMap_fractionRing`: the morphism `Spec K ⟶ Spec A` attached to the
  fraction field of a domain is dominant.

## Implementation notes

The two new conditions are transcribed with the same `let`-bindings as
`HasEssentiallyFiniteTypeValuativeExtension`, and for the same reason are introduced only by
term-mode binders, which zeta-reduce them; an `intro` would leave the fraction field sitting
over a let-bound variable that typeclass synthesis refuses to unfold.

Only uniqueness, not existence, is needed for `0GWW`, so no quasi-compactness is assumed there,
matching the source.  The source proves it by applying `0GWV` to the diagonal of `f`: the
diagonal is quasi-compact because `f` is locally of finite type, and the extension condition for
the diagonal says exactly that the two projections of a test morphism `C ⟶ X ×_Y X` agree.

Both conditions quantify over a morphism `g : Spec K ⟶ C \ {c}` cutting out the generic point,
rather than constructing it.  Such a `g` exists and is unique, the puncture being an open
subscheme containing the generic point of `C`, so this is the source's condition; it is also the
form in which the statement of tag `0GWV` phrases its item (3).

## References

* [Stacks Project, Tag 0GWW](https://stacks.math.columbia.edu/tag/0GWW)
* [Stacks Project, Tag 0GWX](https://stacks.math.columbia.edu/tag/0GWX)
* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.NagataValuativeCriterion

open Stacks.AlgebraicGeometry.Tag05JXGeneral

/-! ### The uniqueness and lifting conditions -/

/-- The one-dimensional finite-type test for uniqueness of extensions over a normal integral
scheme: the test diagrams are those of `HasEssentiallyFiniteTypeValuativeExtension`, and in each
of them there is at most one lift. -/
def HasEssentiallyFiniteTypeValuativeUniqueness
    {S X Y : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S) : Prop :=
  ∀ (C : Scheme.{u}) (p : C ⟶ S),
    LocallyOfFiniteType p → QuasiCompact p →
    IsNormal C → IsIntegral C →
    ∀ (c : C) (hc : IsClosed ({c} : Set C))
      (_hdim : ringKrullDim (C.presheaf.stalk c) = 1),
      let U : C.Opens := ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩
      ∀ (q : C ⟶ Y) (a : U.toScheme ⟶ X),
        q ≫ hY = p → a ≫ f = U.ι ≫ q →
        ∀ (hdom : IsDomain (C.presheaf.stalk c)),
          letI := hdom
          let A := C.presheaf.stalk c
          let i : Spec (.of (FractionRing A)) ⟶ Spec (.of A) :=
            Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
          ∀ (g : Spec (.of (FractionRing A)) ⟶ U.toScheme),
            g ≫ U.ι = i ≫ C.fromSpecStalk c →
            ∀ l₁ l₂ : Spec (.of A) ⟶ X,
              l₁ ≫ f = C.fromSpecStalk c ≫ q → i ≫ l₁ = g ≫ a →
              l₂ ≫ f = C.fromSpecStalk c ≫ q → i ≫ l₂ = g ≫ a → l₁ = l₂

/-- The one-dimensional finite-type test for existence and uniqueness of extensions over a
normal integral scheme: in each test diagram of
`HasEssentiallyFiniteTypeValuativeExtension` there is exactly one lift. -/
def HasEssentiallyFiniteTypeValuativeLift
    {S X Y : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S) : Prop :=
  ∀ (C : Scheme.{u}) (p : C ⟶ S),
    LocallyOfFiniteType p → QuasiCompact p →
    IsNormal C → IsIntegral C →
    ∀ (c : C) (hc : IsClosed ({c} : Set C))
      (_hdim : ringKrullDim (C.presheaf.stalk c) = 1),
      let U : C.Opens := ⟨({c} : Set C)ᶜ, hc.isOpen_compl⟩
      ∀ (q : C ⟶ Y) (a : U.toScheme ⟶ X),
        q ≫ hY = p → a ≫ f = U.ι ≫ q →
        ∀ (hdom : IsDomain (C.presheaf.stalk c)),
          letI := hdom
          let A := C.presheaf.stalk c
          let i : Spec (.of (FractionRing A)) ⟶ Spec (.of A) :=
            Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
          ∀ (g : Spec (.of (FractionRing A)) ⟶ U.toScheme),
            g ≫ U.ι = i ≫ C.fromSpecStalk c →
            ∃! l : Spec (.of A) ⟶ X,
              (l ≫ f = C.fromSpecStalk c ≫ q) ∧ (i ≫ l = g ≫ a)

/-- Existence together with uniqueness in every one-dimensional finite-type test diagram is
existence and uniqueness. -/
theorem hasEssentiallyFiniteTypeValuativeLift_iff {S X Y : Scheme.{u}} (f : X ⟶ Y) (hY : Y ⟶ S) :
    HasEssentiallyFiniteTypeValuativeLift f hY ↔
      HasEssentiallyFiniteTypeValuativeExtension f hY ∧
        HasEssentiallyFiniteTypeValuativeUniqueness f hY := by
  constructor
  · intro h
    refine ⟨fun C p hp hqc hn hint c hc hdim q a hq ha hdom g hg => ?_,
      fun C p hp hqc hn hint c hc hdim q a hq ha hdom g hg l₁ l₂ hl₁ hg₁ hl₂ hg₂ => ?_⟩
    · exact (h C p hp hqc hn hint c hc hdim q a hq ha hdom g hg).exists
    · exact (h C p hp hqc hn hint c hc hdim q a hq ha hdom g hg).unique ⟨hl₁, hg₁⟩ ⟨hl₂, hg₂⟩
  · rintro ⟨hext, huniq⟩
    refine fun C p hp hqc hn hint c hc hdim q a hq ha hdom g hg => ?_
    obtain ⟨l, hl⟩ := hext C p hp hqc hn hint c hc hdim q a hq ha hdom g hg
    exact ⟨l, hl, fun l' hl' =>
      huniq C p hp hqc hn hint c hc hdim q a hq ha hdom g hg l' l hl'.1 hl'.2 hl.1 hl.2⟩

/-! ### Restricting a morphism to the diagonal -/

/-- A morphism `a` with `a ≫ Δ_f = ι ≫ q` is recovered from `q` by the first projection. -/
theorem eq_comp_fst_of_comp_diagonal {X Y Z W : Scheme.{u}} (f : X ⟶ Y) {a : Z ⟶ X} {ι : Z ⟶ W}
    {q : W ⟶ pullback f f} (ha : a ≫ pullback.diagonal f = ι ≫ q) :
    a = ι ≫ q ≫ pullback.fst f f := by
  rw [← Category.assoc, ← ha, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- A morphism `a` with `a ≫ Δ_f = ι ≫ q` is recovered from `q` by the second projection. -/
theorem eq_comp_snd_of_comp_diagonal {X Y Z W : Scheme.{u}} (f : X ⟶ Y) {a : Z ⟶ X} {ι : Z ⟶ W}
    {q : W ⟶ pullback f f} (ha : a ≫ pullback.diagonal f = ι ≫ q) :
    a = ι ≫ q ≫ pullback.snd f f := by
  rw [← Category.assoc, ← ha, Category.assoc, pullback.diagonal_snd, Category.comp_id]

/-! ### The generic point of the spectrum of a domain -/

/-- The morphism `Spec (Frac A) ⟶ Spec A` induced by the inclusion of a domain into its fraction
field is dominant: the inclusion is injective, so its kernel is contained in the nilradical. -/
theorem isDominant_specMap_algebraMap_fractionRing (A : Type u) [CommRing A] [IsDomain A] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) := by
  rw [isDominant_iff, DenseRange]
  change DenseRange (PrimeSpectrum.comap (algebraMap A (FractionRing A)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A (FractionRing A))]
  exact bot_le

/-! ### Separatedness -/

/-- **Stacks Project, Tag 0GWW.**  Over a Nagata base `S`, a morphism `f : X ⟶ Y` between schemes
locally of finite type over `S` is separated if and only if the lift in every one-dimensional
finite-type test diagram is unique.

Uniqueness for a separated morphism holds because `Spec (Frac 𝒪_{C,c}) ⟶ Spec 𝒪_{C,c}` is
dominant and `Spec 𝒪_{C,c}` is reduced.  Conversely the extension condition for the diagonal of
`f` follows from the assumed uniqueness, and tag `0GWV` turns it into universal closedness of the
diagonal, which for an immersion means that it is a closed immersion. -/
@[stacks 0GWW]
theorem isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] :
    IsSeparated f ↔ HasEssentiallyFiniteTypeValuativeUniqueness f hY := by
  constructor
  · intro hsep
    refine fun C p _hp _hqc _hn _hint c hc _hdim q a _hq _ha hdom g _hg
      l₁ l₂ hl₁ hg₁ hl₂ hg₂ => ?_
    have := hdom
    have : IsSeparated f := hsep
    have := isDominant_specMap_algebraMap_fractionRing (C.presheaf.stalk c : Type u)
    exact ext_of_isDominant_of_isSeparated f (hl₁.trans hl₂.symm) _ (hg₁.trans hg₂.symm)
  · intro huniq
    have : IsLocallyNoetherian S := isLocallyNoetherian_of_isNagataScheme hS
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian hY
    have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp_eq hY f hf
    have : QuasiSeparated f := quasiSeparated_of_locallyOfFiniteType f
    have hδ : pullback.diagonal f ≫ (pullback.fst f f ≫ hX) = hX := by
      rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    have htest : HasEssentiallyFiniteTypeValuativeExtension (pullback.diagonal f)
        (pullback.fst f f ≫ hX) := by
      refine fun C p hp hqc hn hint c hc hdim q a hq ha hdom g hg => ?_
      have hfst := eq_comp_fst_of_comp_diagonal f ha
      have hsnd := eq_comp_snd_of_comp_diagonal f ha
      have key := huniq C p hp hqc hn hint c hc hdim (q ≫ pullback.fst f f ≫ f) a
        (by simpa only [Category.assoc, hf] using hq)
        (by simp only [hfst, ← Category.assoc])
        hdom g hg
        (C.fromSpecStalk c ≫ q ≫ pullback.fst f f)
        (C.fromSpecStalk c ≫ q ≫ pullback.snd f f)
        (by simp only [Category.assoc])
        (by simp only [hfst, ← Category.assoc, hg])
        (by simp only [Category.assoc, pullback.condition])
        (by simp only [hsnd, ← Category.assoc, hg])
      refine ⟨C.fromSpecStalk c ≫ q ≫ pullback.fst f f, ?_,
        by simp only [hfst, ← Category.assoc, hg]⟩
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using key
    have : UniversallyClosed (pullback.diagonal f) :=
      ((universallyClosed_tfae_essentiallyFiniteType hX (pullback.fst f f ≫ hX)
        (pullback.diagonal f) hδ hS).out 3 1).mp htest
    exact ⟨IsClosedImmersion.of_isPreimmersion _
      (pullback.diagonal f).isClosedMap.isClosed_range⟩

/-! ### Properness -/

/-- **Stacks Project, Tag 0GWX.**  Over a Nagata base `S`, a quasi-compact morphism `f : X ⟶ Y`
between schemes locally of finite type over `S` is proper if and only if every one-dimensional
finite-type test diagram admits exactly one lift.

This is formal from tags `0GWV` and `0GWW` and the definition of a proper morphism as one that is
locally of finite type, separated and universally closed. -/
@[stacks 0GWX]
theorem isProper_iff_hasEssentiallyFiniteTypeValuativeLift
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] [QuasiCompact f] :
    IsProper f ↔ HasEssentiallyFiniteTypeValuativeLift f hY := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp_eq hY f hf
  have hclosed := (universallyClosed_tfae_essentiallyFiniteType hX hY f hf hS).out 1 3
  rw [hasEssentiallyFiniteTypeValuativeLift_iff, ← hclosed,
    ← isSeparated_iff_hasEssentiallyFiniteTypeValuativeUniqueness hX hY f hf hS]
  refine ⟨fun h => ⟨h.toUniversallyClosed, h.toIsSeparated⟩, fun h => ?_⟩
  have := h.1
  have := h.2
  exact ⟨⟩

end Stacks.AlgebraicGeometry.NagataValuativeCriterion
