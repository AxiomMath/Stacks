module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# Finite local freeness of a given rank is Zariski local on the base

Being finite locally free of rank `r` is, like being finite locally free, a property of a
morphism of schemes that can be checked on the members of any open cover of the target.

## Main definitions

* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property`: being finite locally free of rank `r`,
  packaged as a `CategoryTheory.MorphismProperty`.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_pointwise` restates the definition with the
  pointwise form of finite local freeness of the direct image of the structure sheaf.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp`: precomposing with an isomorphism of
  schemes preserves the rank of a finite locally free morphism.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property` respects isomorphisms and is Zariski
  local at the target.

## Implementation notes

The rank is an explicit argument of `Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, so the
morphism property has to be named before the `CategoryTheory.MorphismProperty.RespectsIso` and
`AlgebraicGeometry.IsZariskiLocalAtTarget` instances can be stated; that is the only reason
`IsFiniteLocallyFreeOfRank.property` exists. The proofs are those of the corresponding
statements for `Stacks.Morphisms.IsFiniteLocallyFree`, with the rank carried along: the direct
image of the structure sheaf is unchanged by restricting over an open of the target
(`Stacks.Morphisms.restrictPushforwardStructureSheafIso`), and along an isomorphism of the
target it is the direct image of the structure sheaf of the composite.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- The definition of the rank of a finite locally free morphism, with finite local freeness of
the direct image of the structure sheaf in its pointwise form. -/
theorem isFiniteLocallyFreeOfRank_iff_pointwise {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) :
    IsFiniteLocallyFreeOfRank f r ↔
      IsAffineHom f ∧
        Scheme.Modules.IsFiniteLocallyFreeOfRank (pushforwardStructureSheaf f) r := by
  rw [isFiniteLocallyFreeOfRank_iff, Scheme.Modules.isFiniteLocallyFreeOfRank_iff]

/-- Being finite locally free of rank `r`, as a property of morphisms of schemes. -/
def IsFiniteLocallyFreeOfRank.property (r : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ IsFiniteLocallyFreeOfRank f r

/-- A morphism has `IsFiniteLocallyFreeOfRank.property r` if and only if it is finite locally free
of rank `r`. -/
@[simp]
theorem IsFiniteLocallyFreeOfRank.property_iff {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) :
    IsFiniteLocallyFreeOfRank.property r f ↔ IsFiniteLocallyFreeOfRank f r := Iff.rfl

/-- A morphism with affine fibres whose direct image of the structure sheaf is isomorphic to a
finite locally free module of rank `r` is finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_of_iso {X S : Scheme.{u}} {r : ℕ} (g : X ⟶ S)
    [IsAffineHom g] {M : S.Modules} (E : M ≅ pushforwardStructureSheaf g)
    (hM : M.IsFiniteLocallyFreeOfRank r) : IsFiniteLocallyFreeOfRank g r :=
  (isFiniteLocallyFreeOfRank_iff_pointwise _ r).mpr
    ⟨inferInstance, Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso E hM⟩

/-- Precomposing a finite locally free morphism of rank `r` with an isomorphism keeps it finite
locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_precomp {X X' S : Scheme.{u}} {r : ℕ} (e : X' ≅ X)
    (f : X ⟶ S) (h : IsFiniteLocallyFreeOfRank f r) : IsFiniteLocallyFreeOfRank (e.hom ≫ f) r := by
  have hA : IsAffineHom f := h.toIsAffineHom
  have eu : (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit X'.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Scheme.Modules.pushforwardIsoRestrict e _ ≪≫ Scheme.Modules.restrictUnitIso e.inv
  have E : pushforwardStructureSheaf f ≅ pushforwardStructureSheaf (e.hom ≫ f) :=
    ((Scheme.Modules.pushforward f).mapIso eu).symm ≪≫
      (Scheme.Modules.pushforwardComp e.hom f).app (SheafOfModules.unit X'.ringCatSheaf)
  exact isFiniteLocallyFreeOfRank_of_iso _ E ((isFiniteLocallyFreeOfRank_iff_pointwise f r).mp h).2

/-- Postcomposing a finite locally free morphism of rank `r` with an isomorphism keeps it finite
locally free of rank `r`. -/
public theorem isFiniteLocallyFreeOfRank_postcomp {X S S' : Scheme.{u}} {r : ℕ} (e : S ≅ S')
    (f : X ⟶ S) (h : IsFiniteLocallyFreeOfRank f r) : IsFiniteLocallyFreeOfRank (f ≫ e.hom) r := by
  have hA : IsAffineHom f := h.toIsAffineHom
  exact isFiniteLocallyFreeOfRank_of_iso _
    ((Scheme.Modules.pushforwardComp f e.hom).app (SheafOfModules.unit X.ringCatSheaf))
    (((isFiniteLocallyFreeOfRank_iff_pointwise f r).mp h).2.pushforward_of_iso e)

/-- Being finite locally free of rank `r` is stable under composition with isomorphisms on either
side. -/
instance IsFiniteLocallyFreeOfRank.property_respectsIso (r : ℕ) :
    MorphismProperty.RespectsIso (IsFiniteLocallyFreeOfRank.property.{u} r) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f h ↦ isFiniteLocallyFreeOfRank_precomp e f h)
    (fun e f h ↦ isFiniteLocallyFreeOfRank_postcomp e f h)

/-- The restriction over an open of the target of a finite locally free morphism of rank `r` is
finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_restrict {X S : Scheme.{u}} {r : ℕ} (f : X ⟶ S)
    (V : S.Opens) (h : IsFiniteLocallyFreeOfRank f r) : IsFiniteLocallyFreeOfRank (f ∣_ V) r := by
  have hloc := isAffineHom_isZariskiLocalAtTarget.{u}
  obtain ⟨hA, hM⟩ := (isFiniteLocallyFreeOfRank_iff_pointwise f r).mp h
  exact (isFiniteLocallyFreeOfRank_iff_pointwise _ r).mpr
    ⟨IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) hA V,
      Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
        (restrictPushforwardStructureSheafIso f V) (hM.restrict V.ι)⟩

/-- A morphism whose restriction over each member of an open cover of the target is finite
locally free of rank `r` is finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_of_iSup_eq_top {X S : Scheme.{u}} {r : ℕ} (f : X ⟶ S)
    {ι : Type u} (U : ι → S.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsFiniteLocallyFreeOfRank (f ∣_ U i) r) : IsFiniteLocallyFreeOfRank f r := by
  have hloc := isAffineHom_isZariskiLocalAtTarget.{u}
  refine (isFiniteLocallyFreeOfRank_iff_pointwise f r).mpr ⟨?_, ?_⟩
  · exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsAffineHom) U hU
      fun i ↦ ((isFiniteLocallyFreeOfRank_iff_pointwise _ r).mp (h i)).1
  · exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U hU fun i ↦
      Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
      (restrictPushforwardStructureSheafIso f (U i)).symm
      ((isFiniteLocallyFreeOfRank_iff_pointwise _ r).mp (h i)).2

/-- Being finite locally free of rank `r` is Zariski local on the target. -/
instance IsFiniteLocallyFreeOfRank.property_isZariskiLocalAtTarget (r : ℕ) :
    IsZariskiLocalAtTarget (IsFiniteLocallyFreeOfRank.property.{u} r) :=
  IsZariskiLocalAtTarget.mk' (fun f V h ↦ isFiniteLocallyFreeOfRank_restrict f V h)
    (fun f _ U hU h ↦ isFiniteLocallyFreeOfRank_of_iSup_eq_top f U hU h)

end Stacks.Morphisms

end
