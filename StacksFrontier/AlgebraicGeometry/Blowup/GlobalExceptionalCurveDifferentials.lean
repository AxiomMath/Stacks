module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# The differentials of the exceptional divisor of a blowup at a regular surface point

Let `W` be a scheme and `w ∈ W` a closed point whose local ring is regular of Krull dimension
two. Blow `W` up in the reduced point `{w}` and let `E` be the exceptional divisor, with its
structure morphism `E ⟶ Z` over the centre `Z`. Then

`Ω_{E/Z}` is finite locally free of rank one.

This is the globalization, to a closed point of an arbitrary scheme, of
`Stacks.Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre`, which is
available only over the spectrum of a regular local ring of dimension two.

## Main definitions

* `Stacks.Blowup.centrePoint`: the lift of `Spec κ(w) ⟶ W` through the centre of the blowup in
  the reduced closed point `{w}`.

## Main results

The elided prefix is `Stacks.Blowup`.

* `exists_isPullback_blowUpToBase_of_comap_eq`: blowing up commutes with flat base change, for
  the Rees-datum construction `Stacks.Blowup.blowUp` of the blowup, with the centre upstairs
  carried as an ideal sheaf that is only propositionally the inverse image of the centre
  downstairs.
* `isIso_centrePoint` and `isPullback_centrePoint`: the centre of the blowup in a reduced closed
  point is the spectrum of the residue field there, and it is the base change of the closed point
  of `Spec 𝒪_{W,w}`.
* `smoothOfRelativeDimension_one_exceptionalToCentre_vanishingIdeal`: the structure morphism of
  the exceptional divisor over the centre is smooth of relative dimension one.
* `isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal`:
  **the statement above.**

## Implementation notes

**Why the bare isomorphism with the projective line does not suffice.** The globalization
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal` produces an
isomorphism `𝐏¹_{κ(w)} ≅ E` of schemes with no compatibility with the structure morphism over the
centre, and a morphism `E ⟶ Spec κ` is not determined by the scheme `E`: for `κ = 𝔽_p(t)` the
composite of the projection `𝐏¹_κ ⟶ Spec κ` with `Spec` of the Frobenius of `κ` is another
morphism out of the same scheme, and it is not smooth, `κ` being inseparable over `κ^p`. So the
rank of `Ω_{E/Z}` has to be read off a morphism, not off `E`.

**The route is the flat base change along `Spec 𝒪_{W,w} ⟶ W`.** Over the spectrum of the local
ring the exceptional divisor *is* the projective line over the residue field *over* `Spec κ`
(`Stacks.Blowup.exists_iso_projectiveLine_exceptionalToCentre`), hence a smooth curve, hence
smooth of relative dimension one. The transport downstairs compares two cartesian squares:

* the exceptional divisor of each blowup is the fibre product of that blowup with its centre
  (`Stacks.Blowup.isPullback_exceptionalToCentre`), and
* the two blowups sit in a cartesian square over `g = Spec 𝒪_{W,w} ⟶ W`
  (`exists_isPullback_blowUpToBase_of_comap_eq`), `g` being flat.

Pasting those two makes the exceptional divisor upstairs the fibre product of the blowup
downstairs with the *upstairs* centre `Spec κ`. The comparison of centres is an isomorphism —
not because of flatness, but because `Spec κ(w) ⟶ W` and the centre `Z ⟶ W` are closed
immersions with the same ideal sheaf (`AlgebraicGeometry.vanishingIdeal_singleton_eq_ker`) — so
the two centres may be exchanged, and then the exceptional divisors correspond by uniqueness of a
fibre product. The two structure morphisms over the centre therefore differ by an isomorphism at
each end, and `Ω` of a morphism smooth of relative dimension one is finite locally free of rank
one ([Stacks, Tag 02G1]).

**Why the two blowup constructions both appear.** `Stacks.Blowup.exceptionalToCentre` is phrased
with the Rees-datum blowup `Stacks.Blowup.blowUp`, while flat base change
(`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`, [Stacks, Tag 0805]) is proved for
`AlgebraicGeometry.blowUp`. The two are isomorphic over the base by `Stacks.Blowup.blowUpIso`,
and `exists_isPullback_blowUpToBase_of_comap_eq` moves the cartesian square across that
isomorphism; nothing else about the fork is used here.

**No `@[stacks]` attribute is placed.** This is the form in which the consumers of
[Stacks, Tag 0AGQ] use the structure of the exceptional divisor, not an assertion of that tag:
the base is a general scheme rather than the spectrum of a local ring, and the conclusion is a
statement about relative differentials.

## References

* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Smooth of relative dimension `n` is invariant under an isomorphism at each end.** Mathlib
records `SmoothOfRelativeDimension n` as stable under base change and under composition, but not
as respecting isomorphisms, and the composition instance cannot be applied to `n` directly: the
unit `0 + n` of the composite with an isomorphism is only propositionally `n`. -/
theorem smoothOfRelativeDimension_of_iso {A B A' B' : Scheme.{u}} {n : ℕ} (f : A ⟶ B)
    (f' : A' ⟶ B') (α : A' ≅ A) (β : B' ≅ B) (h : α.hom ≫ f = f' ≫ β.hom)
    [SmoothOfRelativeDimension n f'] : SmoothOfRelativeDimension n f := by
  have hf : f = α.inv ≫ f' ≫ β.hom := by rw [← h]; simp
  have h₀ : SmoothOfRelativeDimension (0 + (n + 0)) (α.inv ≫ f' ≫ β.hom) := inferInstance
  rw [Nat.add_zero, Nat.zero_add] at h₀
  rw [hf]
  exact h₀

end AlgebraicGeometry

namespace Stacks.Blowup

/-! ### Flat base change for the Rees-datum blowup -/

/-- **Blowing up commutes with flat base change**, for the Rees-datum construction
`Stacks.Blowup.blowUp`. This is [Stacks, Tag 0805], which
`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap` proves for `AlgebraicGeometry.blowUp`,
carried across the comparison `Stacks.Blowup.blowUpIso` of the two constructions.

The centre upstairs is an argument `J` with the equation `hJ` rather than written out, so that
the statement applies to an ideal sheaf that is only propositionally the inverse image of `I`. -/
theorem exists_isPullback_blowUpToBase_of_comap_eq {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂) [Flat g]
    (I : X₂.IdealSheafData) (J : X₁.IdealSheafData) (hJ : J = I.comap g) :
    ∃ h : blowUp J ⟶ blowUp I, IsPullback (blowUpToBase J) h g (blowUpToBase I) := by
  subst hJ
  obtain ⟨h, hp⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap g I
  refine ⟨(blowUpIso (I.comap g)).hom ≫ h ≫ (blowUpIso I).inv, ?_⟩
  exact hp.of_iso (blowUpIso (I.comap g)).symm (Iso.refl _) (blowUpIso I).symm (Iso.refl _)
    (by simp [← blowUpIso_hom_comp]) (by simp) (by simp) (by simp [← blowUpIso_hom_comp])

/-! ### The centre of a blowup in a reduced closed point -/

section Centre

variable {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W))

/-- The ideal sheaf of the morphism `Spec κ(w) ⟶ Spec 𝒪_{W,w} ⟶ W` is the ideal sheaf of the
reduced closed point `{w}`. -/
theorem ker_residuePoint_comp_fromSpecStalk :
    (residuePoint (W.presheaf.stalk w) ≫ W.fromSpecStalk w).ker =
      Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) :=
  (AlgebraicGeometry.vanishingIdeal_singleton_eq_ker w hw).symm

include hw in
/-- That morphism is a closed immersion, the point being closed. -/
theorem isClosedImmersion_residuePoint_comp_fromSpecStalk :
    IsClosedImmersion (residuePoint (W.presheaf.stalk w) ≫ W.fromSpecStalk w) :=
  isClosed_singleton_iff_isClosedImmersion.mp hw

/-- The centre of the blowup in `{w}` and `Spec κ(w) ⟶ W` have the same ideal sheaf. -/
theorem ker_subschemeι_vanishingIdeal_eq :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι.ker =
      (residuePoint (W.presheaf.stalk w) ≫ W.fromSpecStalk w).ker :=
  (Scheme.IdealSheafData.ker_subschemeι _).trans
    (ker_residuePoint_comp_fromSpecStalk w hw).symm

/-- The lift of `Spec κ(w) ⟶ W` through the centre of the blowup in the reduced closed point
`{w}`. -/
def centrePoint :
    Spec (.of (ResidueField (W.presheaf.stalk w))) ⟶
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subscheme :=
  IsClosedImmersion.lift _ (residuePoint (W.presheaf.stalk w) ≫ W.fromSpecStalk w)
    (ker_subschemeι_vanishingIdeal_eq w hw).le

/-- `centrePoint w hw` followed by the inclusion of the centre is `Spec κ(w) ⟶ W`. -/
@[simp]
theorem centrePoint_comp :
    centrePoint w hw ≫
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι =
      residuePoint (W.presheaf.stalk w) ≫ W.fromSpecStalk w :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The centre of the blowup in a reduced closed point is the spectrum of the residue field
there.** Both `Spec κ(w) ⟶ W` and the centre are closed immersions with the same ideal sheaf. -/
theorem isIso_centrePoint : IsIso (centrePoint w hw) :=
  have := isClosedImmersion_residuePoint_comp_fromSpecStalk w hw
  IsClosedImmersion.isIso_lift _ _ (ker_subschemeι_vanishingIdeal_eq w hw)

/-- The inverse image of the centre of the blowup in `{w}` along `Spec 𝒪_{W,w} ⟶ W` is the
closed point of `𝒪_{W,w}`. -/
theorem comap_ker_subschemeι_vanishingIdeal :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι.ker.comap
        (W.fromSpecStalk w) = (residuePoint (W.presheaf.stalk w)).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact AlgebraicGeometry.vanishingIdeal_singleton_comap_fromSpecStalk w hw

/-- **The centre of the blowup in a reduced closed point is the base change of the closed point
of `Spec 𝒪_{W,w}`** along `Spec 𝒪_{W,w} ⟶ W`. -/
theorem isPullback_centrePoint :
    IsPullback (residuePoint (W.presheaf.stalk w)) (centrePoint w hw) (W.fromSpecStalk w)
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _ (centrePoint_comp w hw).symm
    (comap_ker_subschemeι_vanishingIdeal w hw)

end Centre

/-! ### The globalization -/

variable {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W))

/-- **The structure morphism of the exceptional divisor over the centre is smooth of relative
dimension one**, for the blowup of a scheme in a reduced closed point whose local ring is regular
of dimension two.

Over `Spec 𝒪_{W,w}` the exceptional divisor is the projective line over the residue field, over
`Spec κ`, hence a smooth curve, hence smooth of relative dimension one. The two squares that
present the exceptional divisors as fibre products paste over the flat base change
`Spec 𝒪_{W,w} ⟶ W`, and the comparison of centres is an isomorphism, so the structure morphism
downstairs is the one upstairs composed with an isomorphism at each end. -/
theorem smoothOfRelativeDimension_one_exceptionalToCentre_vanishingIdeal
    (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    SmoothOfRelativeDimension 1
      (exceptionalToCentre
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι) := by
  have := hreg
  have : Flat (W.fromSpecStalk w) := flat_fromSpecStalk W w
  have := isIso_centrePoint w hw
  obtain ⟨hmap, hB⟩ :=
    exists_isPullback_blowUpToBase_of_comap_eq (W.fromSpecStalk w)
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι.ker
      (residuePoint (W.presheaf.stalk w)).ker
      (comap_ker_subschemeι_vanishingIdeal w hw).symm
  have hP : IsPullback
      ((exceptionalIdeal (residuePoint (W.presheaf.stalk w)).ker).subschemeι ≫ hmap)
      (exceptionalToCentre (residuePoint (W.presheaf.stalk w)) ≫ centrePoint w hw)
      (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι.ker)
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι := by
    refine ((isPullback_exceptionalToCentre (residuePoint (W.presheaf.stalk w))).paste_horiz
      hB.flip).of_iso (Iso.refl _) (Iso.refl _) (asIso (centrePoint w hw)) (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp
  have : SmoothOfRelativeDimension 1
      (exceptionalToCentre (residuePoint (W.presheaf.stalk w))) := by
    have := isCurve_exceptionalToCentre (W.presheaf.stalk w) hdim
    have := smooth_exceptionalToCentre (W.presheaf.stalk w) hdim
    exact AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve _ _
  refine AlgebraicGeometry.smoothOfRelativeDimension_of_iso _
    (exceptionalToCentre (residuePoint (W.presheaf.stalk w)))
    (hP.isoIsPullback _ _
      (isPullback_exceptionalToCentre
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι))
    (asIso (centrePoint w hw)) ?_
  exact hP.isoIsPullback_hom_snd _ _ (isPullback_exceptionalToCentre _)

/-- **`Ω_{E/Z}` is finite locally free of rank one** for the blowup of a scheme in a reduced
closed point whose local ring is regular of dimension two, where `E` is the exceptional divisor
and `Z` the centre.

The structure morphism `E ⟶ Z` is smooth of relative dimension one, and the sheaf of relative
differentials of such a morphism is finite locally free of rank one ([Stacks, Tag 02G1]).

This is the globalization of
`Stacks.Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre`, and it
is the hypothesis `s = 1` of the twist dichotomy for a point blowup at a closed point of an
arbitrary scheme. -/
theorem isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal
    (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials
        (exceptionalToCentre
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).subschemeι)) 1 :=
  have := smoothOfRelativeDimension_one_exceptionalToCentre_vanishingIdeal w hw hreg hdim
  AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials _

end Stacks.Blowup

end
