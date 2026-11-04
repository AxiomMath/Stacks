module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Quasi-separated algebraic spaces are Zariski locally quasi-separated over the base

Zariski local quasi-separatedness of an algebraic space asks for a Zariski covering by open
subspaces which are quasi-separated. An algebraic space quasi-separated over the base scheme
of the site admits the trivial such covering, by itself, so it is Zariski locally
quasi-separated over that base.

## Main results

* `AlgebraicGeometry.Space.isZariskiLocallyQuasiSeparatedOver_of_isQuasiSeparatedOver`: an
  algebraic space quasi-separated over its base scheme is Zariski locally quasi-separated
  over it.

## References

* [Stacks Project, Tag 03DY](https://stacks.math.columbia.edu/tag/03DY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-separatedness over `S` transports along an isomorphism of presheaves. -/
theorem isQuasiSeparatedOver_of_iso
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F')
    (hF : IsQuasiSeparatedOver B S hS F) : IsQuasiSeparatedOver B S hS F' := by
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk e (prod.mapIso e e) ?_)).1 hF
  simp [diag]

/-- An algebraic space over `S` which is quasi-separated over `S` is Zariski locally
quasi-separated over `S`. -/
theorem isZariskiLocallyQuasiSeparatedOver_of_isQuasiSeparatedOver
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : _root_.AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hqs : IsQuasiSeparatedOver B S hS F) :
    IsZariskiLocallyQuasiSeparatedOver B S hS F :=
  ⟨PUnit.{u + 1}, fun _ ↦ (⊤ : Subfunctor F), isZariskiCover_top hF,
    fun _ ↦ isQuasiSeparatedOver_of_iso B S hS
      (asIso (Subfunctor.ι (⊤ : Subfunctor F))).symm hqs⟩

end AlgebraicGeometry.Space

end
