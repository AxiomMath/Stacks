module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat morphisms with Cohen–Macaulay source

A flat morphism `f : X ⟶ Y` of locally Noetherian schemes whose source is Cohen–Macaulay is a
Cohen–Macaulay morphism, and the local ring of `Y` at the image of any point of `X` is
Cohen–Macaulay as well.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_of_isCohenMacaulay_source`: the morphism is
  Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulayLocalRing_targetStalk_of_isCohenMacaulay_source`: the local
  rings of the target at image points are Cohen–Macaulay.

## Implementation notes

Both statements come from the flat local criterion
`Module.isMaximalCohenMacaulay_self_iff_of_flat` applied to the stalk map
`𝒪_{Y, f x} → 𝒪_{X, x}`, which is a flat local homomorphism: it says that the source stalk is
Cohen–Macaulay exactly when the target stalk is and the fibre of the stalk map is. The fibre of
the stalk map is identified with the local ring of the scheme-theoretic fibre by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`.

Cohen–Macaulayness of a morphism takes the locally Noetherian fibre witness as an explicit
argument. That witness is **not** an extra hypothesis here: a scheme-theoretic fibre of a
morphism with locally Noetherian source is locally Noetherian, being locally a quotient of a
localization of a Noetherian ring, which is `AlgebraicGeometry.isLocallyNoetherian_fiber`. So
the first result supplies that proof itself and the tag is stated with no hypothesis on the
fibres. The witness is a proposition, so a caller holding some other witness `hf` can use the
result for `f.IsCohenMacaulay hf` directly.

## References

* [Stacks Project, Tag 0C0X](https://stacks.math.columbia.edu/tag/0C0X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0C0X.** A flat morphism of locally Noetherian schemes whose source is
Cohen–Macaulay is a Cohen–Macaulay morphism. -/
@[stacks 0C0X "the morphism is Cohen-Macaulay"]
public theorem isCohenMacaulay_of_isCohenMacaulay_source {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : IsCohenMacaulay X) :
    f.IsCohenMacaulay (isLocallyNoetherian_fiber f) := by
  intro x
  have := isLocallyNoetherian_fiber f (f x)
  change IsFlatAt f.toLRSHom.toShHom x ∧
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
  refine ⟨(Flat.iff_flat_stalkMap f).mp inferInstance x, ?_⟩
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let I : Ideal B := Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal A)
  let Q := B ⧸ I
  let C := (f.fiber (f x)).presheaf.stalk (f.asFiber x)
  let e : Q ≃+* C := quotientStalkEquivFiberStalk f x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  let : Module.Flat A B := Flat.stalkMap f x
  have hBmax : Module.IsMaximalCohenMacaulay B B :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mp
      (isCohenMacaulayLocalRing_stalk X hX x)
  have hQdepth : (Module.depth B (IsLocalRing.maximalIdeal B) Q : WithBot ℕ∞) =
      ringKrullDim Q := ((Module.isMaximalCohenMacaulay_self_iff_of_flat A B).mp hBmax).2
  have hQsurj : Function.Surjective (algebraMap B Q) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  let : Nontrivial Q := ⟨0, 1, fun h => by simpa using congrArg e h⟩
  let : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) hQsurj
  let : IsNoetherianRing Q := inferInstance
  have hQcm : IsCohenMacaulayLocalRing Q := by
    refine (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay Q).mpr ?_
    change (Module.depth Q (IsLocalRing.maximalIdeal Q) Q : WithBot ℕ∞) = ringKrullDim Q
    rw [← Module.depth_eq_depth_self_of_surjective_algebraMap (A := B) (B := Q) hQsurj]
    exact hQdepth
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv e).mp hQcm

/-- **Stacks Project, Tag 0C0X.** For a flat morphism of locally Noetherian schemes whose source
is Cohen–Macaulay, the local ring of the target at the image of any point of the source is
Cohen–Macaulay. -/
@[stacks 0C0X "the target local rings are Cohen-Macaulay", ega "IV 7.5.3" "(iii), special case"]
public theorem isCohenMacaulayLocalRing_targetStalk_of_isCohenMacaulay_source {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : IsCohenMacaulay X) (x : X) :
    IsCohenMacaulayLocalRing (Y.presheaf.stalk (f x)) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  let : Module.Flat A B := Flat.stalkMap f x
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mpr
    (((Module.isMaximalCohenMacaulay_self_iff_of_flat A B).mp
      ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mp
        (isCohenMacaulayLocalRing_stalk X hX x))).1)

end AlgebraicGeometry
