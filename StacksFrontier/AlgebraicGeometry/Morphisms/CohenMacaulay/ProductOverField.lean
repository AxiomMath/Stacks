module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen–Macaulay local rings of a product over a field

Let `k` be a field and let `Y`, `Z` be schemes locally of finite type over `k`. If the local rings
`𝒪_{Y, y}` and `𝒪_{Z, z}` are Cohen–Macaulay, then so is the local ring of `Y ×_k Z` at every
point lying over `(y, z)`. This is the step the proof of Stacks 0FFD performs by quoting Algebra,
Lemma 10.163.3 (Stacks 045J): the local homomorphism `𝒪_{Z, z} ⟶ 𝒪_{Y ×_k Z, ζ}` is flat and its
closed fibre is a local ring of the base change of `Y` to `κ(z)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulayAt_iff_of_field`: over a field, a morphism is
  Cohen–Macaulay at a point exactly when the local ring there is Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_pullback_of_field`: the local rings of
  `Y ×_k Z` at points over Cohen–Macaulay points of `Y` and `Z` are Cohen–Macaulay.

## Implementation notes

The proof is the scheme-level form of the source's: the base change `Y ×_k Z ⟶ Z` of `Y ⟶ Spec k`
is Cohen–Macaulay at `ζ` (Stacks 045T (1), `AlgebraicGeometry.isCohenMacaulayAt_pullback`), and
composing with `Z ⟶ Spec k`, Cohen–Macaulay at `z`, gives a morphism to `Spec k` Cohen–Macaulay
at `ζ` (Stacks 0C0W, `AlgebraicGeometry.isCohenMacaulayAt_comp`, which is where Stacks 045J
enters). Over a field the fibre of a morphism is its source and every morphism is flat, so being
Cohen–Macaulay at a point is a property of the local ring alone.

## References

* [Stacks Project, Tag 045J](https://stacks.math.columbia.edu/tag/045J)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Over a field, a morphism locally of finite type is Cohen–Macaulay at a point exactly when the
local ring of its source there is Cohen–Macaulay: the morphism is flat, and its fibre over the
unique point of `Spec k` is its source. -/
@[ega "IV 6.8.1" "(ii), special case"]
theorem isCohenMacaulayAt_iff_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsCohenMacaulayAt f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f) x ↔
      IsCohenMacaulayLocalRing (X.presheaf.stalk x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber_of_locallyOfFiniteType f _
  have : IsIso (f.fiberι (f x)) :=
    isIso_fiberι_of_isIso_fromSpecResidueField f _ (isIso_fromSpecResidueField_of_field k _)
  have hcm := localCM_iff_of_isIso_stalkMap (f.fiberι (f x)) (f.asFiber x) inferInstance
    inferInstance
  rw [f.fiberι_asFiber] at hcm
  refine ⟨fun h ↦ hcm.mp h.2, fun h ↦ ⟨(Flat.iff_flat_stalkMap f).mp inferInstance x, ?_⟩⟩
  exact hcm.mpr h

end Scheme.Hom

/-- **The local rings of a product over a field (Stacks 045J).** Let `Y` and `Z` be locally of
finite type over a field `k` and let `ζ` be a point of `Y ×_k Z`. If the local rings of `Y` and
`Z` at the two images of `ζ` are Cohen–Macaulay, then so is the local ring of `Y ×_k Z` at `ζ`. -/
theorem isCohenMacaulayLocalRing_stalk_pullback_of_field (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sZ] (ζ : (pullback sY sZ : Scheme.{u})) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    letI : IsLocallyNoetherian (pullback sY sZ : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sY sZ ≫ sZ)
    IsCohenMacaulayLocalRing (Y.presheaf.stalk ((pullback.fst sY sZ).base ζ)) →
      IsCohenMacaulayLocalRing (Z.presheaf.stalk ((pullback.snd sY sZ).base ζ)) →
        IsCohenMacaulayLocalRing ((pullback sY sZ : Scheme.{u}).presheaf.stalk ζ) := by
  intro hY hZ
  have hYat := (Scheme.Hom.isCohenMacaulayAt_iff_of_field k sY _).mpr hY
  have hZat := (Scheme.Hom.isCohenMacaulayAt_iff_of_field k sZ _).mpr hZ
  have hsnd := isCohenMacaulayAt_pullback sY sZ
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType sY) ζ hYat
  have hcomp := isCohenMacaulayAt_comp (pullback.snd sY sZ) sZ _
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType sZ)
    (isLocallyNoetherian_fiber_of_locallyOfFiniteType (pullback.snd sY sZ ≫ sZ)) ζ hsnd hZat
  exact (Scheme.Hom.isCohenMacaulayAt_iff_of_field k (pullback.snd sY sZ ≫ sZ) ζ).mp hcomp

end AlgebraicGeometry

end
