module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatNeighbourhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# A relative `H₁`-regular immersion is regular, and stays regular after base change

Let `f : X ⟶ S` be locally of finite presentation and let `i : Z ⟶ X` be a relative
`H₁`-regular immersion over `S`.  Then `i` is a regular immersion, and so is its base change
along any `S' ⟶ S`.  This is part (2) of Stacks tag 063V.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_of_isRelativeH1RegularImmersion` and
  `Stacks.AlgebraicGeometry.isRegularImmersion_baseChange_of_isRelativeH1RegularImmersion`:
  **part (2) of Stacks tag 063V**, regularity and its stability under arbitrary base change.
* `Stacks.AlgebraicGeometry.isRegularImmersion_of_isRelativeQuasiRegularImmersion_of_flat_open`:
  Stacks tag 063U with the ambient morphism required to be flat only on an open neighbourhood of
  the image of the immersion.
* `Stacks.AlgebraicGeometry.exists_closedFactor_of_range_subset`: an immersion is closed in any
  open subscheme of `i.coborderRange` containing its image.

## Implementation notes

Stacks tag 063U (`Stacks.AlgebraicGeometry.isRegularImmersion_of_isRelativeQuasiRegularImmersion`
and `Stacks.AlgebraicGeometry.isRegularImmersion_baseChange_of_isRelativeQuasiRegularImmersion`)
asks the ambient morphism to be flat everywhere, which part (1) of tag 063V does not supply:  it
only produces an open neighbourhood of the image on which `f` is flat.  So the first step is to
weaken the flatness hypothesis of tag 063U to flatness on such a neighbourhood `U`.  That is done
by testing regularity on the open `U ⊓ i.coborderRange`
(`Stacks.AlgebraicGeometry.isRegularImmersion_iff_of_open`), where the immersion is closed and
the ambient morphism is flat, and applying the closed-immersion form
`Stacks.AlgebraicGeometry.isRegularIdealSheaf_definingIdealOfHom` of tag 063U there.

With that weakening in hand both halves of part (2) are the same statement applied twice: over
`S` to `i` itself, and over `S'` to the base change of `i`, whose flat neighbourhood is the
preimage of `U`.  In particular no base-change theorem for `H₁`-regularity is needed — the
base change is fed in as a *quasi-regular* immersion, by the quasi-regular half of Stacks tag
063R (`Stacks.AlgebraicGeometry.isQuasiRegularImmersion_baseChange_of_flat`).

## References

* [Stacks Project, Lemma 31.23.6 (Tag 063V)](https://stacks.math.columbia.edu/tag/063V)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry

/-- **An immersion is closed in any open subscheme of `i.coborderRange` containing its image.**
The factorization is `AlgebraicGeometry.IsOpenImmersion.lift`, and its range is the preimage of
the range of `i`, which is closed in `i.coborderRange` and hence in the smaller open. -/
theorem exists_closedFactor_of_range_subset {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hVc : V ≤ i.coborderRange) (hrange : Set.range i.base ⊆ (V : Set X)) :
    ∃ j : Z ⟶ V.toScheme, IsClosedImmersion j ∧ j ≫ V.ι = i := by
  have hsub : Set.range i.base ⊆ Set.range V.ι.base := by rwa [V.range_ι]
  set j := IsOpenImmersion.lift V.ι i hsub
  have hij : j ≫ V.ι = i := IsOpenImmersion.lift_fac V.ι i hsub
  refine ⟨j, ?_, hij⟩
  have : IsImmersion j := by
    have : IsImmersion (j ≫ V.ι) := by
      rw [hij]
      infer_instance
    exact IsImmersion.of_comp j V.ι
  apply IsClosedImmersion.of_isPreimmersion
  have hpre : Set.range j.base = V.ι.base ⁻¹' Set.range i.base := by
    have hw (w : Z) : V.ι (j.base w) = i w := by
      simpa using congrArg (fun k : Z ⟶ X => k w) hij
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, (hw w).symm⟩
    · rintro ⟨w, hwz⟩
      exact ⟨w, V.ι.isOpenEmbedding.injective ((hw w).trans hwz)⟩
  rw [hpre]
  exact (isClosed_preimage_val_coborder (s := Set.range i.base)).preimage
    (continuous_inclusion hVc)

/-- **Stacks Project, Tag 063U, with flatness only near the immersed scheme.**  A relative
quasi-regular immersion into a scheme locally of finite presentation over the base is a regular
immersion as soon as the ambient morphism is flat on one open subscheme containing the image. -/
@[ega "IV 19.2.4" "c′) ⇒ c)"]
theorem isRegularImmersion_of_isRelativeQuasiRegularImmersion_of_flat_open
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsImmersion i]
    [LocallyOfFinitePresentation f] (U : X.Opens)
    (hrange : Set.range i.base ⊆ (U : Set X)) (hflat : Flat (U.ι ≫ f))
    (hi : IsRelativeQuasiRegularImmersion f i) : IsRegularImmersion i := by
  obtain ⟨j, _, hij⟩ := exists_closedFactor_of_range_subset i (U ⊓ i.coborderRange) inf_le_right
    (fun x hx => ⟨hrange hx, subset_coborder hx⟩)
  have _ : Flat ((U ⊓ i.coborderRange).ι ≫ f) := by
    rw [← Scheme.Opens.isoOfLE_inv_ι (inf_le_left : U ⊓ i.coborderRange ≤ U),
      Category.assoc, Category.assoc]
    infer_instance
  have _ : Flat (j ≫ (U ⊓ i.coborderRange).ι ≫ f) := by
    rw [← Category.assoc, hij]
    exact hi.1
  rw [isRegularImmersion_iff_of_open i (U ⊓ i.coborderRange) j hij]
  exact isRegularIdealSheaf_definingIdealOfHom ((U ⊓ i.coborderRange).ι ≫ f) j
    ((_root_.Stacks.AlgebraicGeometry.isQuasiRegularImmersion_iff_of_open i
      (U ⊓ i.coborderRange) j hij).mp hi.2)

/-- **Stacks Project, Tag 063V, part (2): the immersion is regular.**  A relative `H₁`-regular
immersion into a scheme locally of finite presentation over the base is a regular immersion. -/
@[stacks 063V "part (2): the immersion is regular"]
theorem isRegularImmersion_of_isRelativeH1RegularImmersion {S X Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsImmersion i] [LocallyOfFinitePresentation f]
    (hi : AlgebraicGeometry.IsRelativeH1RegularImmersion f i) : IsRegularImmersion i := by
  obtain ⟨U, hU, hflat⟩ := exists_open_flat_of_isRelativeH1RegularImmersion f i hi
  exact isRegularImmersion_of_isRelativeQuasiRegularImmersion_of_flat_open f i U hU hflat
    ⟨hi.1, isQuasiRegularImmersion_of_isH1RegularImmersion i hi.2⟩

/-- **Stacks Project, Tag 063V, part (2): regularity after an arbitrary base change.**  A
relative `H₁`-regular immersion into a scheme locally of finite presentation over the base
remains a regular immersion after any change of the base scheme. -/
@[stacks 063V "part (2): the immersion stays regular after any base change"]
theorem isRegularImmersion_baseChange_of_isRelativeH1RegularImmersion {S X Z S' : Scheme.{u}}
    (f : X ⟶ S) (i : Z ⟶ X) [IsImmersion i] [LocallyOfFinitePresentation f]
    (hi : AlgebraicGeometry.IsRelativeH1RegularImmersion f i) (g : S' ⟶ S) :
    IsRegularImmersion (pullback.fst (pullback.snd g f) i) := by
  obtain ⟨U, hU, hflat⟩ := exists_open_flat_of_isRelativeH1RegularImmersion f i hi
  have _ : Flat (i ≫ f) := hi.1
  refine isRegularImmersion_of_isRelativeQuasiRegularImmersion_of_flat_open (pullback.fst g f)
    (pullback.fst (pullback.snd g f) i) (pullback.snd g f ⁻¹ᵁ U) ?_ ?_ ⟨?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    have hw : pullback.snd g f ((pullback.fst (pullback.snd g f) i) w)
        = i ((pullback.snd (pullback.snd g f) i) w) := by
      simpa using congrArg (fun k : pullback (pullback.snd g f) i ⟶ X => k w)
        (pullback.condition (f := pullback.snd g f) (g := i))
    change pullback.snd g f ((pullback.fst (pullback.snd g f) i) w) ∈ (U : Set X)
    rw [hw]
    exact hU ⟨_, rfl⟩
  · exact MorphismProperty.of_isPullback
      (((isPullback_morphismRestrict (pullback.snd g f) U).flip.paste_horiz
        (IsPullback.of_hasPullback g f)).flip) hflat
  · exact flat_comp_of_isPullback (IsPullback.of_hasPullback g f)
      (IsPullback.of_hasPullback (pullback.snd g f) i)
  · exact isQuasiRegularImmersion_baseChange_of_flat f i
      (isQuasiRegularImmersion_of_isH1RegularImmersion i hi.2) g

end Stacks.AlgebraicGeometry

end
