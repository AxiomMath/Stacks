module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Inverse images of closed subspaces of algebraic spaces (Stacks 083Q)

For a morphism `f : Y ⟶ X` of algebraic spaces over `S` and a closed subspace `Z` of `X`, the
inverse image of `Z` is the subfunctor of `Y` whose sections map into `Z`, that is Mathlib's
`CategoryTheory.Subfunctor.preimage`. Its underlying presheaf is the fibre product `Z ×_X Y`,
and it is a closed subspace of `Y`.

Taking the inverse image to be the pointwise preimage, rather than a chosen fibre product,
means its sections and functoriality come from Mathlib directly and downstream statements can
write `Z.preimage f` with no conversion. The identification with `Z ×_X Y` is recorded as a
pullback square: the lift of a competing cone is the universal map into the preimage, which
exists because the cone's second leg lands in the preimage by the cone condition. Closedness
then follows from stability of closed immersions of algebraic spaces under base change
(Stacks 02YW), and algebraicity from algebraicity of the fibre product (Stacks 02X2).

## Main results

* `CategoryTheory.Subfunctor.isPullback_preimage`: **Stacks 083Q**, the identification of the
  inverse image with the fibre product.
* `AlgebraicGeometry.Space.isClosedSubspace_preimage`: **Stacks 083Q**, the inverse image of a
  closed subspace is a closed subspace.
* `CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`: a leg of a cartesian square has as
  range the inverse image of the range of the opposite leg, which is what makes an image
  subfunctor base change on the nose.
* `CategoryTheory.Subfunctor.eq_of_range_eq_of_comp_eq_id`: two morphisms split by one retraction
  are equal as soon as their ranges are.
* `AlgebraicGeometry.Space.inv_toRange_comp`: a monomorphism of type-valued functors is the
  inclusion of its range, read backwards along the isomorphism onto that range.

## References

* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- The second leg of any cone over `Z.ι` and `f` lands in the preimage of `Z` along `f`. -/
private lemma range_snd_le_preimage {C : Type*} [Category C] {X Y : C ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X) (s : PullbackCone Z.ι f) :
    Subfunctor.range s.snd ≤ Z.preimage f := by
  intro i y hy
  obtain ⟨a, rfl⟩ := hy
  have hv : f.app i (s.snd.app i a) = (Z.ι.app i) (s.fst.app i a) := by
    simpa using (congrArg (fun k => k a) (congr_app s.condition i)).symm
  show f.app i (s.snd.app i a) ∈ Z.obj i
  rw [hv]
  exact (s.fst.app i a).property

add_to_stacks 083Q "inverse-image construction" CategoryTheory.Subfunctor.preimage

/-- **Stacks 083Q.** The inverse image of a subfunctor along a morphism of presheaves is
canonically the fibre product of that subfunctor with the source of the morphism. -/
@[stacks 083Q "fibre-product characterization"]
theorem isPullback_preimage {C : Type*} [Category C] {X Y : C ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X) :
    IsPullback (Z.fromPreimage f) (Z.preimage f).ι Z.ι f := by
  have hc : Z.fromPreimage f ≫ Z.ι = (Z.preimage f).ι ≫ f :=
    Subfunctor.fromPreimage_ι Z f
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc) ?_
  refine PullbackCone.IsLimit.mk hc (fun s =>
    Subfunctor.lift s.snd (range_snd_le_preimage f Z s)) ?_ ?_ ?_
  · intro s
    apply (cancel_mono Z.ι).mp
    rw [Category.assoc, hc, ← Category.assoc, Subfunctor.lift_ι, s.condition]
  · intro s
    simp [Subfunctor.lift_ι]
  · intro s m hm₁ hm₂
    apply (cancel_mono (Z.preimage f).ι).mp
    simpa [Subfunctor.lift_ι] using hm₂

/-- The range of one leg of a cartesian square of presheaves of types is the inverse image of the
range of the opposite leg: a section of the target of the square's other leg comes from the corner
exactly when its image in the bottom right corner comes from that leg. -/
theorem range_eq_preimage_of_isPullback {C : Type*} [Category C] {W X Y Z : C ⥤ Type u}
    {f : W ⟶ X} {g : W ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (sq : IsPullback f g a b) :
    Subfunctor.range f = (Subfunctor.range b).preimage a := by
  ext i w
  show w ∈ Set.range (f.app i) ↔ a.app i w ∈ Set.range (b.app i)
  simpa using congrArg (fun s : Set _ => w ∈ s)
    (Limits.Types.range_fst_of_isPullback (sq.map ((evaluation _ _).obj i)))

/-- Two morphisms of presheaves of types which are split by a common retraction and have the same
range are equal: a section of the source is recovered from its image by the retraction, so a point
of the common range has the same preimage under both. -/
theorem eq_of_range_eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C ⥤ Type u} {f g : Y ⟶ X}
    (r : X ⟶ Y) (hf : f ≫ r = 𝟙 Y) (hg : g ≫ r = 𝟙 Y)
    (h : Subfunctor.range f = Subfunctor.range g) : f = g := by
  ext i w
  obtain ⟨v, hv⟩ : f.app i w ∈ Set.range (g.app i) := by
    have hmem : f.app i w ∈ (Subfunctor.range f).obj i := ⟨w, rfl⟩
    rwa [h] at hmem
  have hr (k : Y ⟶ X) (hk : k ≫ r = 𝟙 Y) (u) : r.app i (k.app i u) = u := by
    simpa using congrArg (fun m => m u) (congr_app hk i)
  obtain rfl : v = w := by rw [← hr g hg v, hv, hr f hf w]
  exact hv.symm

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

/-- The inclusion of the range of a monomorphism of type-valued functors is that monomorphism
read through the isomorphism onto its range. -/
theorem inv_toRange_comp {C : Type*} [Category C] {F F' : C ⥤ Type u} (f : F' ⟶ F) [Mono f] :
    (asIso (Subfunctor.toRange f)).inv ≫ f = (Subfunctor.range f).ι :=
  (asIso (Subfunctor.toRange f)).inv_comp_eq.2 (Subfunctor.toRange_ι f).symm

/-- A subfunctor of a presheaf on the big fppf site of `S` is a *`Q`-subspace*, for a property
`Q` of morphisms of schemes, when it is an algebraic space over `S` and its inclusion is
representable by morphisms of the site whose underlying morphisms of schemes have `Q`. At the open
immersions, the closed immersions and the immersions this is `IsOpenSubspace`, `IsClosedSubspace`
and `IsLocallyClosedSubspace`, parts (2), (4) and (6) of Stacks 02YU. -/
abbrev IsSubspaceWith (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Q : MorphismProperty Scheme.{u}) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) : Prop :=
  IsAlgebraicSpace B S hS Z.toFunctor ∧
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf Z.ι

/-- **Stacks 083Q, at an arbitrary property `Q`.** The inverse image of a `Q`-subspace along a
morphism of algebraic spaces is a `Q`-subspace: it is the base change of the inclusion
(`CategoryTheory.Subfunctor.isPullback_preimage`), algebraic by Stacks 02X2, and representability
by morphisms with `Q` is stable under base change. -/
theorem isSubspaceWith_preimage {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Q : MorphismProperty Scheme.{u}} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X)
    (Z : Subfunctor X) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsSubspaceWith B S hS Q Z) : IsSubspaceWith B S hS Q (Z.preimage f) := by
  have hsq := Subfunctor.isPullback_preimage f Z
  exact ⟨isAlgebraicSpace_of_iso B S hS hsq.isoPullback
      (isAlgebraicSpace_pullback B S hS Z.ι f hZ.1 hY hX),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hZ.2⟩

/-- **Stacks 083Q.** The inverse image of a closed subspace of an algebraic space along a
morphism of algebraic spaces over `S` is a closed subspace of the source. -/
@[stacks 083Q "closedness of inverse image"]
theorem isClosedSubspace_preimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) (Z : Subfunctor X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsClosedSubspace B S hS Z) :
    IsClosedSubspace B S hS (Z.preimage f) :=
  isSubspaceWith_preimage f Z hX hY hZ

end AlgebraicGeometry.Space

end
