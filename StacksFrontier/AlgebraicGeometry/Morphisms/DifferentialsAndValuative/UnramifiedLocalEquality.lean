module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# Equality near one point for maps to an unramified scheme

Two morphisms of schemes over a base agree on a neighbourhood of a point if the target is
unramified over the base and the morphisms agree both at that point and on its residue field.

The two morphisms are compared through the morphism to the fibre product of the target with
itself over the base. Agreeing at the point and on its residue field says exactly that the
induced map from the spectrum of that residue field lands in the diagonal, and the diagonal of
an unramified morphism is an open immersion, so the locus where the two morphisms agree is open
and contains the point.

## Main results

* `AlgebraicGeometry.exists_open_eq_of_residueFieldMap_eq`: an open neighbourhood on which the
  two morphisms agree.

## Implementation notes

Schemes over `S` and their morphisms are represented in the category `Over S`. Once the images
of the chosen point are identified, `AlgebraicGeometry.Scheme.residueFieldCongr` transports the
residue field of the second image to that of the first, so that equality of the two induced
residue-field maps is well typed.

## References

* [Stacks Project, Tag 04HB](https://stacks.math.columbia.edu/tag/04HB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two morphisms that agree at `x` and induce the same residue-field map there agree after
composing with the canonical morphism from the spectrum of the residue field at `x`. -/
public theorem Scheme.fromSpecResidueField_comp_eq_of_residueFieldMap_eq {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (x : X) (hfg : f x = g x)
    (hκ : f.residueFieldMap x = (Y.residueFieldCongr hfg).hom ≫ g.residueFieldMap x) :
    X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g :=
  calc
    X.fromSpecResidueField x ≫ f =
        Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x) :=
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm
    _ = Spec.map (g.residueFieldMap x) ≫ Y.fromSpecResidueField (g x) := by
      rw [hκ, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField hfg]
    _ = X.fromSpecResidueField x ≫ g :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g x

/-- Two morphisms over `S` to a scheme unramified over `S` which have the same value and
induce the same residue-field map at `x` agree on an open neighbourhood of `x`. -/
@[stacks 04HB, ega "IV 17.4.7" "open nbhd U, f|U=g|U"]
public theorem exists_open_eq_of_residueFieldMap_eq {S : Scheme.{u}} {X Y : Over S}
    (f g : X ⟶ Y) (x : X.left) [Unramified Y.hom]
    (hfg : f.left x = g.left x)
    (hκ : f.left.residueFieldMap x =
      (Y.left.residueFieldCongr hfg).hom ≫ g.left.residueFieldMap x) :
    ∃ U : X.left.Opens, x ∈ U ∧ U.ι ≫ f.left = U.ι ≫ g.left := by
  let q : X.left ⟶ pullback Y.hom Y.hom :=
    pullback.lift f.left g.left (by rw [f.w, g.w])
  let p : Spec (X.left.residueField x) := IsLocalRing.closedPoint (X.left.residueField x)
  have hdiag : (X.left.fromSpecResidueField x ≫ f.left) ≫ pullback.diagonal Y.hom =
      X.left.fromSpecResidueField x ≫ q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, q, pullback.lift_fst]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, q, pullback.lift_snd]
        using Scheme.fromSpecResidueField_comp_eq_of_residueFieldMap_eq f.left g.left x hfg hκ
  have hxrange : q x ∈ (pullback.diagonal Y.hom).opensRange := by
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨f.left x, ?_⟩
    have h := congrArg (fun m => m p) hdiag
    change pullback.diagonal Y.hom (f.left ((X.left.fromSpecResidueField x) p)) =
      q ((X.left.fromSpecResidueField x) p) at h
    simpa only [Scheme.fromSpecResidueField_apply x p] using h
  let U : X.left.Opens := q ⁻¹ᵁ (pullback.diagonal Y.hom).opensRange
  have hsub : Set.range (U.ι ≫ q) ⊆ Set.range (pullback.diagonal Y.hom) := by
    rintro z ⟨w, rfl⟩
    exact Scheme.Hom.mem_opensRange.mp w.2
  let l := IsOpenImmersion.lift (pullback.diagonal Y.hom) (U.ι ≫ q) hsub
  have hl : l ≫ pullback.diagonal Y.hom = U.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hxrange, ?_⟩
  calc
    U.ι ≫ f.left = (l ≫ pullback.diagonal Y.hom) ≫ pullback.fst Y.hom Y.hom := by
      rw [hl]
      simp only [Category.assoc, q, pullback.lift_fst]
    _ = (l ≫ pullback.diagonal Y.hom) ≫ pullback.snd Y.hom Y.hom := by simp
    _ = U.ι ≫ g.left := by
      rw [hl]
      simp only [Category.assoc, q, pullback.lift_snd]

end AlgebraicGeometry

end
