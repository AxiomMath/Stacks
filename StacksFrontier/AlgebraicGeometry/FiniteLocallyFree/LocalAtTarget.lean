module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# Finite local freeness of a morphism is Zariski local on the base

Being finite locally free is a property of a morphism of schemes that can be checked on the
members of any open cover of the target. Both halves of that statement come from the
corresponding statements for the direct image of the structure sheaf, because restricting the
target to an open `V` replaces that direct image by the direct image along the restricted
morphism.

## Main results

* `Stacks.Morphisms.restrictPushforwardStructureSheafIso`: the restriction to an open of the
  target of the direct image of the structure sheaf is the direct image of the structure sheaf
  along the restricted morphism.
* `Stacks.Morphisms.isFiniteLocallyFree_respectsIso`: being finite locally free is invariant
  under isomorphisms of the source and of the target.
* `Stacks.Morphisms.isFiniteLocallyFree_isZariskiLocalAtTarget`: being finite locally free is
  Zariski local on the base.

## Implementation notes

The source and target isomorphism invariance are both reduced to the behaviour of the direct
image of the structure sheaf: along an isomorphism of the source the direct image of the
structure sheaf is unchanged, and along an isomorphism of the target it is the direct image of
the given one, which is a restriction.

The pointwise form of the definition, `Stacks.Morphisms.isFiniteLocallyFree_iff_pointwise`, and
the Zariski locality of affineness, `Stacks.Morphisms.isAffineHom_isZariskiLocalAtTarget`, are
both taken from `StacksFrontier/AlgebraicGeometry/Morphisms/FiniteLocallyFree/Local.lean`.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- The restriction to an open `V` of the target of the direct image of the structure sheaf is
the direct image of the structure sheaf along the restriction of the morphism over `V`. -/
noncomputable def restrictPushforwardStructureSheafIso {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) :
    (pushforwardStructureSheaf f).restrict V.ι ≅ pushforwardStructureSheaf (f ∣_ V) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app
      (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward (f ∣_ V)).mapIso
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ V).ι)

/-- Precomposing a finite locally free morphism with an isomorphism keeps it finite locally
free. -/
private theorem isFiniteLocallyFree_precomp {X X' S : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ S)
    (h : IsFiniteLocallyFree f) : IsFiniteLocallyFree (e.hom ≫ f) := by
  have hA : IsAffineHom f := h.toIsAffineHom
  have eu : (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit X'.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Scheme.Modules.pushforwardIsoRestrict e _ ≪≫ Scheme.Modules.restrictUnitIso e.inv
  have E : pushforwardStructureSheaf f ≅ pushforwardStructureSheaf (e.hom ≫ f) :=
    ((Scheme.Modules.pushforward f).mapIso eu).symm ≪≫
      (Scheme.Modules.pushforwardComp e.hom f).app (SheafOfModules.unit X'.ringCatSheaf)
  exact (isFiniteLocallyFree_iff_pointwise _).mpr
    ⟨inferInstance, ((isFiniteLocallyFree_iff_pointwise f).mp h).2.of_iso E⟩

/-- Postcomposing a finite locally free morphism with an isomorphism keeps it finite locally
free. -/
private theorem isFiniteLocallyFree_postcomp {X S S' : Scheme.{u}} (e : S ≅ S') (f : X ⟶ S)
    (h : IsFiniteLocallyFree f) : IsFiniteLocallyFree (f ≫ e.hom) := by
  have hA : IsAffineHom f := h.toIsAffineHom
  have E : (Scheme.Modules.pushforward e.hom).obj (pushforwardStructureSheaf f) ≅
      pushforwardStructureSheaf (f ≫ e.hom) :=
    (Scheme.Modules.pushforwardComp f e.hom).app (SheafOfModules.unit X.ringCatSheaf)
  exact (isFiniteLocallyFree_iff_pointwise _).mpr ⟨inferInstance,
    (((isFiniteLocallyFree_iff_pointwise f).mp h).2.pushforward_of_iso e).of_iso E⟩

/-- Being finite locally free is invariant under isomorphisms of the source and of the
target. -/
instance isFiniteLocallyFree_respectsIso :
    MorphismProperty.RespectsIso (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk _ isFiniteLocallyFree_precomp isFiniteLocallyFree_postcomp

/-- The restriction of a finite locally free morphism over an open of the target is finite
locally free. -/
private theorem isFiniteLocallyFree_restrict {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (h : IsFiniteLocallyFree f) : IsFiniteLocallyFree (f ∣_ V) := by
  have hloc := isAffineHom_isZariskiLocalAtTarget.{u}
  obtain ⟨hA, hM⟩ := (isFiniteLocallyFree_iff_pointwise f).mp h
  exact (isFiniteLocallyFree_iff_pointwise _).mpr
    ⟨IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) hA V,
      (hM.restrict V.ι).of_iso (restrictPushforwardStructureSheafIso f V)⟩

/-- A morphism whose restriction over each member of an open cover of the target is finite
locally free is finite locally free. -/
private theorem isFiniteLocallyFree_of_iSup_eq_top {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type u}
    (U : ι → S.Opens) (hU : iSup U = ⊤) (h : ∀ i, IsFiniteLocallyFree (f ∣_ U i)) :
    IsFiniteLocallyFree f := by
  have hloc := isAffineHom_isZariskiLocalAtTarget.{u}
  refine (isFiniteLocallyFree_iff_pointwise f).mpr ⟨?_, ?_⟩
  · exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsAffineHom) U hU
      fun i ↦ ((isFiniteLocallyFree_iff_pointwise _).mp (h i)).1
  · refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top U hU fun i ↦ ?_
    exact (((isFiniteLocallyFree_iff_pointwise _).mp (h i)).2).of_iso
      (restrictPushforwardStructureSheafIso f (U i)).symm

/-- Being finite locally free is Zariski local on the base. -/
instance isFiniteLocallyFree_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) :=
  IsZariskiLocalAtTarget.mk' isFiniteLocallyFree_restrict isFiniteLocallyFree_of_iSup_eq_top

end Stacks.Morphisms

end
