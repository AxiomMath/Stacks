module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.FreeSections
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalClassify
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSyntomicOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Finite

/-!
# A finite syntomic morphism is locally a base change of the universal family

Let `f : Y ⟶ X` be finite and syntomic and let `x` be a point of `X` lying in the image of `f`.
Then there are an integer `d ≥ 1`, an open neighbourhood `U` of `x` and a morphism from `U` to
the open subscheme `U_d ⊂ X_d` of Tag 0FL0 such that the restriction `f⁻¹(U) ⟶ U` of `f` is the
base change along it of the restriction `V_d = π_d^{-1}(U_d) ⟶ U_d` of the universal finite free
family `π_d` of rank `d` of Tag 0FKZ. This is Tag 0FL4.

## Main results

* `AlgebraicGeometry.exists_isPullback_universalFamily`: the cartesian square over `X_d`.
* `AlgebraicGeometry.exists_isPullback_universalFamily_restrict`: the middle square of the
  source's diagram, over `U_d`.

## Implementation notes

The square is produced affine-locally and then transported. Over a small enough affine open `U`
the sections `Γ(Y, f⁻¹(U))` are free over `Γ(X, U)` on a basis whose first vector is `1`
(`AlgebraicGeometry.exists_isAffineOpen_basis_one`), and the structure constants of that basis
classify a map out of the universal coefficient ring which makes the resulting square of rings a
pushout (`AlgebraicGeometry.isPushout_universalFamily_of_basis_one`); `Spec` turns it into a
cartesian square of affine schemes, which
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality` transports onto the restriction `f ∣_ U`.
That the classifying morphism factors through the open subscheme of Tag 0FL0 is the universal
property of the latter, applied to the base change `f ∣_ U`, which is syntomic because `f` is.
The square over `U_d` is then obtained by cancelling the cartesian square of the open immersion
`V_d ⊂ Y_d` over `U_d ⊂ X_d`.

*The hypothesis on the point.* Example 0FKZ has `d ≥ 1`, and the universal family of rank
`d ≥ 1` is faithfully flat, hence surjective; so a base change of it along a morphism out of a
nonempty scheme is nonempty. A point of `X` outside the image of `f` has an empty fibre and
local rank `0`, and for such a point no diagram as in the source exists. The statement here is
the one for a point of the image, which is what the source's proof produces: it chooses a basis
`1 = e_1, …, e_d`, so `d ≥ 1`.

## References

* [Stacks Project, Tag 0FL4](https://stacks.math.columbia.edu/tag/0FL4)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.FiniteFreeAlgebra

universe u

namespace AlgebraicGeometry

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The canonical base change of a morphism along the lower edge of a cartesian square is
syntomic as soon as the left edge of the square is: the two are isomorphic. -/
private theorem syntomic_pullback_snd_of_isPullback {V U Yd Xd : Scheme.{u}} {fU : V ⟶ U}
    {π : Yd ⟶ Xd} {g : U ⟶ Xd} {q : V ⟶ Yd} (hsq : IsPullback q fU π g)
    (h : Syntomic fU) : Syntomic (pullback.snd π g) := by
  have hrespects : MorphismProperty.RespectsIso (@Syntomic : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (MorphismProperty.cancel_left_of_respectsIso
    (@Syntomic : MorphismProperty Scheme.{u}) hsq.isoPullback.hom _).mp ?_
  rwa [hsq.isoPullback_hom_snd]

/-- **Stacks Project, Tag 0FL4**, with the cartesian square written over `X_d`. For a finite
syntomic `f : Y ⟶ X` and a point `x` of `X` in the image of `f` there are `d ≥ 1`, an open
`U ∋ x` and a morphism `U ⟶ U_d` to the open subscheme of Tag 0FL0 such that `f⁻¹(U) ⟶ U` is the
base change of `π_d` along `U ⟶ U_d ⊂ X_d`. -/
theorem exists_isPullback_universalFamily (hf : IsFinite f ∧ Syntomic f) (x : X)
    (hx : ∃ y : Y, f.base y = x) :
    ∃ (d : ℕ) (_ : NeZero d) (U : X.Opens) (_ : x ∈ U)
      (gU : U.toScheme ⟶ (universalSyntomicOpen.{u} d).toScheme)
      (q : (f ⁻¹ᵁ U).toScheme ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)),
      IsPullback q (f ∣_ U) (universalFamily.{u} d (universalAlgebraStructure d))
        (gU ≫ (universalSyntomicOpen.{u} d).ι) := by
  have h3 := locallyOfFinitePresentation_and_lci_fibers_of_finite_flat_lci
    (flat_and_isLocalCompleteIntersectionMorphism_of_finite_syntomic hf)
  have : Stacks.Morphisms.IsFiniteLocallyFree f :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mpr
      ⟨hf.1, h3.1.1.2, h3.1.2⟩
  obtain ⟨U, hU, hxU, d, hd, b, hb⟩ := exists_isAffineOpen_basis_one f x hx
  have hVY : IsAffineOpen (f ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage U hU
  obtain ⟨φ, Φ, hpush⟩ :=
    isPushout_universalFamily_of_basis_one (f.app U) (universalAlgebraStructure d) b hb
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hsq : IsPullback (hVY.isoSpec.hom ≫ Spec.map Φ) (f ∣_ U)
      (universalFamily.{u} d (universalAlgebraStructure d))
      (hU.isoSpec.hom ≫ Spec.map φ) := by
    refine hpb.of_iso' hVY.isoSpec (Iso.refl _) hU.isoSpec (Iso.refl _) (by simp) ?_
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl) (by simp)
    simpa only [IsAffineOpen.isoSpec_hom] using Scheme.Opens.toSpecΓ_naturality f U
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@Syntomic : MorphismProperty Scheme.{u}) := syntomic_isStableUnderBaseChange
  have hsynU : Syntomic (f ∣_ U) := hbc.of_isPullback (isPullback_morphismRestrict f U).flip hf.2
  obtain ⟨gU, hgU⟩ := (factorsThrough_universalSyntomicOpen_iff.{u} d U.toScheme
    (hU.isoSpec.hom ≫ Spec.map φ)).mpr (syntomic_pullback_snd_of_isPullback hsq hsynU)
  refine ⟨d, hd, U, hxU, gU, hVY.isoSpec.hom ≫ Spec.map Φ, ?_⟩
  rwa [hgU]

/-- Restricting a cartesian square along an open subscheme of the lower right corner: if the
square over `X_d` is cartesian and its lower edge factors through an open `U_d`, then the square
over `U_d`, with upper right corner the preimage of `U_d`, is cartesian. -/
private theorem exists_isPullback_restrict_of_isPullback {V U Yd Xd : Scheme.{u}} (fU : V ⟶ U)
    (π : Yd ⟶ Xd) (Ud : Xd.Opens) (gU : U ⟶ Ud.toScheme) (q : V ⟶ Yd)
    (hsq : IsPullback q fU π (gU ≫ Ud.ι)) :
    ∃ q' : V ⟶ (π ⁻¹ᵁ Ud).toScheme, IsPullback q' fU (π ∣_ Ud) gU := by
  have hrange : Set.range q.base ⊆ Set.range (π ⁻¹ᵁ Ud).ι.base := by
    rw [Scheme.Opens.range_ι, Set.range_subset_iff]
    intro z
    show π.base (q.base z) ∈ Ud
    have hw : π.base (q.base z) = Ud.ι.base (gU.base (fU.base z)) := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : V ⟶ Xd => k.base z) hsq.w
    rw [hw]
    exact (gU.base (fU.base z)).2
  have hfac : IsOpenImmersion.lift (π ⁻¹ᵁ Ud).ι q hrange ≫ (π ⁻¹ᵁ Ud).ι = q :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ Ud).ι q hrange, ?_⟩
  have hp : fU ≫ gU = IsOpenImmersion.lift (π ⁻¹ᵁ Ud).ι q hrange ≫ (π ∣_ Ud) := by
    rw [← cancel_mono Ud.ι]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, reassoc_of% hfac]
    exact hsq.w.symm
  refine (IsPullback.of_bot ?_ hp (isPullback_morphismRestrict π Ud)).flip
  rw [hfac]
  exact hsq.flip

/-- **Stacks Project, Tag 0FL4.** For a finite syntomic morphism `f : Y ⟶ X` and a point `x` of
`X` in the image of `f` there are an integer `d ≥ 1`, an open `U ∋ x` with preimage
`V = f⁻¹(U)`, and a morphism `U ⟶ U_d` into the open subscheme of Tag 0FL0, for which the middle
square of the source's diagram — `V ⟶ V_d = π_d^{-1}(U_d)` over `U ⟶ U_d` — is cartesian. -/
@[stacks 0FL4 "the diagram, at a point of the image of `f`: the integer `d`, the open `U ∋ x` \
with `V = f⁻¹(U)`, the morphism `U ⟶ U_d` into the open subscheme of Lemma 0FL0, and the \
cartesian middle square over the restriction of `π_d` of Example 0FKZ to `V_d = π_d⁻¹(U_d)`. A \
point outside the image of `f` is excluded, and must be: the local rank of `f` there is `0`, \
whereas Example 0FKZ has `d ≥ 1`, so `π_d` is surjective and no base change of it along a \
morphism out of a nonempty `U` has empty fibres."]
theorem exists_isPullback_universalFamily_restrict (hf : IsFinite f ∧ Syntomic f) (x : X)
    (hx : ∃ y : Y, f.base y = x) :
    ∃ (d : ℕ) (_ : NeZero d) (U : X.Opens) (_ : x ∈ U)
      (gU : U.toScheme ⟶ (universalSyntomicOpen.{u} d).toScheme)
      (q : (f ⁻¹ᵁ U).toScheme ⟶ (universalFamily.{u} d (universalAlgebraStructure d) ⁻¹ᵁ
        universalSyntomicOpen.{u} d).toScheme),
      IsPullback q (f ∣_ U)
        (universalFamily.{u} d (universalAlgebraStructure d) ∣_
          universalSyntomicOpen.{u} d) gU := by
  obtain ⟨d, hd, U, hxU, gU, q, hsq⟩ := exists_isPullback_universalFamily f hf x hx
  obtain ⟨q', hq'⟩ := exists_isPullback_restrict_of_isPullback (f ∣_ U)
    (universalFamily.{u} d (universalAlgebraStructure d)) (universalSyntomicOpen.{u} d) gU q hsq
  exact ⟨d, hd, U, hxU, gU, q', hq'⟩

/-- The complementary case of Tag 0FL4: a point of the target outside the image of a finite
morphism has an open neighbourhood whose preimage is empty, so that there the fibre of `f` is
empty and no base change of a universal family of rank `d ≥ 1` can describe it. -/
theorem exists_eq_bot_preimage_of_notMem_range [IsFinite f] (x : X)
    (hx : ¬ ∃ y : Y, f.base y = x) :
    ∃ U : X.Opens, x ∈ U ∧ f ⁻¹ᵁ U = ⊥ := by
  have : IsIntegralHom f := ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).1
  have : UniversallyClosed f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp inferInstance |>.1
  have hcl : IsClosed (Set.range f.base) := by
    simpa only [Set.image_univ] using f.isClosedMap _ isClosed_univ
  refine ⟨⟨(Set.range f.base)ᶜ, hcl.isOpen_compl⟩, hx, ?_⟩
  ext y
  simp

end AlgebraicGeometry

end
