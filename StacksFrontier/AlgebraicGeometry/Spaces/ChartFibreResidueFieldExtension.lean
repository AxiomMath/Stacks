module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Flatness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of a morphism over a residue field extension

Let `g : U ⟶ V` be a morphism of schemes, let `v : V` and let `κ(v) ⟶ K` be an extension of the
residue field at `v`, so that `Spec K ⟶ V` is a `K`-valued point of `V` supported at `v`. The
fibre `U ×_V Spec K` of `g` over that point is the base change along `κ(v) ⟶ K` of the fibre
`U_v = U ×_V Spec κ(v)`, and the projection `U ×_V Spec K ⟶ U_v` is flat, since a ring map out
of a field is flat and flatness is stable under base change. Consequently the induced
homomorphism of local rings is flat, and so is its composite with the structure map of any
strict henselization of the local ring of `U ×_V Spec K`.

## Main results

* `AlgebraicGeometry.flat_SpecMap_of_residueField`: the spectrum of a ring map out of a residue
  field is a flat morphism.
* `AlgebraicGeometry.Scheme.Hom.isPullback_fiber_extendResidueField`: the square exhibiting
  `U_v ×_{κ(v)} Spec K` as the fibre product `U ×_V Spec K`.
* `AlgebraicGeometry.Scheme.Hom.flat_fst_fiber_extendResidueField`: the projection
  `U_v ×_{κ(v)} Spec K ⟶ U_v` is flat.
* `AlgebraicGeometry.Scheme.Hom.flat_stalkMap_fiber_extendResidueField`: the induced
  homomorphism `𝒪_{U_v, u} ⟶ 𝒪_{U_v ×_{κ(v)} Spec K, ū}` of local rings is flat.
* `AlgebraicGeometry.flat_comp_stalkMap_of_isStrictHenselization`: for a flat morphism of
  schemes, the composite of the homomorphism of local rings with the structure map of a strict
  henselization of the local ring at the source point is flat.

## Implementation notes

The fibre `g.fiber v` is by definition `pullback g (V.fromSpecResidueField v)`, so the base
change of the fibre along `Spec K ⟶ Spec κ(v)` is
`pullback (g.fiberToSpecResidueField v) (Spec.map φ)` and the identification with `U ×_V Spec K`
is horizontal pasting of two pullback squares; no comparison isomorphism is constructed, the
statement being the universal property of the composite square.

Flatness of `𝒪_{U_v, u} ⟶ 𝒪^{sh}_{U_v ×_{κ(v)} Spec K, ū}` is obtained by composing
`flat_stalkMap_fiber_extendResidueField` with
`flat_comp_stalkMap_of_isStrictHenselization`; the composite is not stated separately because
spelling the pullback out three times in one type is less legible than composing the two.

## References

* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.StrictHenselization

universe u v

namespace AlgebraicGeometry

/-- **The spectrum of a ring map out of a residue field is flat.** Every module over a field is
free, hence flat. -/
theorem flat_SpecMap_of_residueField {V : Scheme.{u}} {v : V} {S : CommRingCat.{u}}
    (φ : V.residueField v ⟶ S) : Flat (Spec.map φ) := by
  rw [Flat.SpecMap_iff]
  let : Algebra (V.residueField v) S := φ.hom.toAlgebra
  exact (inferInstance : Module.Flat (V.residueField v) S)

variable {U V : Scheme.{u}} (g : U ⟶ V) (v : V) {K : Type u} [Field K]
  (φ : V.residueField v ⟶ .of K)

/-- **The fibre over a `K`-valued point is the fibre over the residue field, base changed.** If
`φ : κ(v) ⟶ K` is an extension of the residue field at `v : V`, then the base change of the
fibre `U_v = U ×_V Spec κ(v)` along `Spec K ⟶ Spec κ(v)` is the fibre product of `g` with the
`K`-valued point `Spec K ⟶ V` supported at `v`. -/
@[ega "III 4.7.1" "X_y = X ×_Y Spec(κ(y))"]
theorem Scheme.Hom.isPullback_fiber_extendResidueField :
    IsPullback (pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ) ≫ g.fiberι v)
      (pullback.snd (g.fiberToSpecResidueField v) (Spec.map φ)) g
      (Spec.map φ ≫ V.fromSpecResidueField v) :=
  IsPullback.paste_horiz
    (IsPullback.of_hasPullback (g.fiberToSpecResidueField v) (Spec.map φ))
    (IsPullback.of_hasPullback g (V.fromSpecResidueField v))

/-- **Extending the residue field is a flat base change of the fibre.** The projection
`U_v ×_{κ(v)} Spec K ⟶ U_v` is the base change of `Spec K ⟶ Spec κ(v)`, which is flat because
`K` is a vector space over `κ(v)`. -/
@[ega "IV 20.6.9" "partial", sga "6 X 7.15" "partial"]
theorem Scheme.Hom.flat_fst_fiber_extendResidueField :
    Flat (pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)) :=
  have : Flat (Spec.map φ) := flat_SpecMap_of_residueField φ
  inferInstance

/-- **The comparison of local rings along a residue field extension of the fibre is flat.** The
homomorphism `𝒪_{U_v, u} ⟶ 𝒪_{U_v ×_{κ(v)} Spec K, ū}` induced at a point `ū` of the base
changed fibre is flat, being a stalk map of a flat morphism. -/
@[ega "IV 20.6.9" "partial"]
theorem Scheme.Hom.flat_stalkMap_fiber_extendResidueField
    (w : ↥(pullback (g.fiberToSpecResidueField v) (Spec.map φ))) :
    (((pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))).stalkMap w).hom.Flat :=
  have : Flat (pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)) :=
    g.flat_fst_fiber_extendResidueField v φ
  Flat.stalkMap _ w

/-- **A strict henselization of the local ring at a point of a flat morphism is flat over the
local ring of the target.** The homomorphism of local rings of a flat morphism of schemes is
flat, a strict henselization is flat over the ring it henselizes, and flatness is stable under
composition. -/
theorem flat_comp_stalkMap_of_isStrictHenselization {W T : Scheme.{u}} (p : W ⟶ T) [Flat p]
    (w : W) {κsep : Type*} [Field κsep]
    [Algebra (maximalIdeal (W.presheaf.stalk w)).ResidueField κsep]
    [IsSepClosure (maximalIdeal (W.presheaf.stalk w)).ResidueField κsep]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra (W.presheaf.stalk w) A]
    (h : IsStrictHenselization (W.presheaf.stalk w) κsep A) :
    ((algebraMap (W.presheaf.stalk w) A).comp (p.stalkMap w).hom).Flat :=
  RingHom.Flat.comp (Flat.stalkMap p w) (RingHom.flat_algebraMap_iff.mpr h.flat)

end AlgebraicGeometry

end
