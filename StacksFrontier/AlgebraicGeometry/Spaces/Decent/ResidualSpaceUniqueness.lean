module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Uniqueness of the residual space at a point (Stacks 06QZ)

Any two residual spaces of an algebraic space `X` over `S` at a point `x` of `|X|`, in the
sense of **Stacks 06R0**, are isomorphic over `X` by a unique isomorphism. Together with the
existence statement of `AlgebraicGeometry.Space.exists_isResidualSpaceAt` this is the whole of
**Stacks 06QZ**: there is a unique monomorphism `Z ⟶ X` with `Z` reduced, locally Noetherian
and `|Z|` the singleton `{x}`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_iso_of_isResidualSpaceAt` is the uniqueness assertion:
  two residual spaces of `X` at `x` are isomorphic over `X`, by exactly one isomorphism.
* `AlgebraicGeometry.Space.existsUnique_isResidualSpaceAt` is **Stacks 06QZ**, existence and
  uniqueness together.

## References

* [Stacks Project, Tag 06QX](https://stacks.math.columbia.edu/tag/06QX)
* [Stacks Project, Tag 06QY](https://stacks.math.columbia.edu/tag/06QY)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ResidualSpaceUniqueness :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for limits of cospans of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_ResidualSpaceUniqueness
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Two residual spaces `f : Z ⟶ X` and `f' : Z' ⟶ X` of an algebraic space `X` over `S` at a
point `x` of `|X|` are isomorphic over `X`, and the isomorphism over `X` is unique. -/
theorem existsUnique_iso_of_isResidualSpaceAt (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS X} {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Z ⟶ X) (f' : Z' ⟶ X)
    (hf : IsResidualSpaceAt B S hS X x f) (hf' : IsResidualSpaceAt B S hS X x f') :
    ∃! e : Z' ≅ Z, e.hom ≫ f = f' := by
  obtain ⟨hZ, hmono, hred, hnoeth, hne, hsub, hsupp⟩ := hf
  obtain ⟨hZ', hmono', hred', hnoeth', hne', hsub', hsupp'⟩ := hf'
  have _ : Mono f := hmono
  have _ : Mono f' := hmono'
  have hcover : HasLocallyOfFinitePresentationFlatFieldCover B S hS Z :=
    (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B S hS Z hZ).mp
      ⟨hred, hnoeth, hne, hsub⟩
  have hcover' : HasLocallyOfFinitePresentationFlatFieldCover B S hS Z' :=
    (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B S hS Z' hZ').mp
      ⟨hred', hnoeth', hne', hsub'⟩
  have hW : IsAlgebraicSpace B S hS (pullback f' f) :=
    isAlgebraicSpace_pullback B S hS f' f hZ' hZ hX
  have hsq : IsPullback (pullback.fst f' f) (pullback.snd f' f) f' f :=
    IsPullback.of_hasPullback f' f
  obtain ⟨z⟩ := hne
  obtain ⟨z'⟩ := hne'
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS hsq z' z
    ((hsupp' z').trans (hsupp z).symm)
  have _ : Mono (pullback.fst f' f) := pullback.fst_of_mono
  have _ : Mono (pullback.snd f' f) := pullback.snd_of_mono
  have hfst : IsIso (pullback.fst f' f) :=
    (isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover B S hS hW hZ'
      (pullback.fst f' f) hcover').resolve_left fun h ↦ h.false w
  have hsnd : IsIso (pullback.snd f' f) :=
    (isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover B S hS hW hZ
      (pullback.snd f' f) hcover).resolve_left fun h ↦ h.false w
  have hcomm : (inv (pullback.fst f' f) ≫ pullback.snd f' f) ≫ f = f' := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have hcomm' : ((asIso (pullback.fst f' f)).symm ≪≫ asIso (pullback.snd f' f)).hom ≫ f = f' := by
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
    exact hcomm
  refine ⟨(asIso (pullback.fst f' f)).symm ≪≫ asIso (pullback.snd f' f), hcomm', fun e he => ?_⟩
  refine Iso.ext ?_
  rw [← cancel_mono f, he]
  exact hcomm'.symm

/-- Every point `x` of an algebraic space `X` over `S` has a unique residual space: there is a
monomorphism `Z ⟶ X` with `Z` a reduced, locally Noetherian algebraic space whose point set is
the singleton `{x}`, and any two such are isomorphic over `X` by exactly one isomorphism. -/
@[stacks 06QZ]
theorem existsUnique_isResidualSpaceAt (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    (∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : Z ⟶ X), IsResidualSpaceAt B S hS X x f) ∧
      ∀ (Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : Z ⟶ X) (f' : Z' ⟶ X),
        IsResidualSpaceAt B S hS X x f → IsResidualSpaceAt B S hS X x f' →
        ∃! e : Z' ≅ Z, e.hom ≫ f = f' :=
  ⟨exists_isResidualSpaceAt B S hS hX x,
    fun _ _ f f' hf hf' => existsUnique_iso_of_isResidualSpaceAt B S hS hX f f' hf hf'⟩

end AlgebraicGeometry.Space

end
