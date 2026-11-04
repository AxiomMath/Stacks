module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Cartesian squares of opens in the big fppf category over a scheme

Stacks 0E91 is about a scheme `S`, a retrocompact open `U ⊆ S`, a point `s` outside `U`, and the
affine open neighbourhoods `W` of `s`. Assembling it needs two squares to be known cartesian in
the big fppf category over `S`:

* `W ∩ U = U ×_{U ∪ W} W`, which is the hypothesis `hsqW` of the glueing theorem; and
* `V = U ×_S Spec 𝒪_{S,s}`, which is what identifies the tag's `V = Spec 𝒪_{S,s} ∩ U`.

Both are the same statement — the preimage of an open is a fibre product — and both are already
proved for schemes in Mathlib, by `AlgebraicGeometry.isPullback_opens_inf_le` and
`AlgebraicGeometry.isPullback_morphismRestrict`. What is missing is only the passage from schemes
to the site, and that is cheap in this direction: the functor to schemes is faithful and reflects
limits of cospans, so `CategoryTheory.IsPullback.of_map_of_faithful` reflects the square. It even
supplies the commuting condition, so none of the statements below has to produce it separately.

## Main results

* `AlgebraicGeometry.BigFppfOver.isPullback_of_toScheme`: a square of the big fppf category over
  `S` is cartesian as soon as its image in schemes is.
* `AlgebraicGeometry.BigFppfOver.isPullback_opensHom_inf`: **the intersection of two opens of `S`
  is their fibre product over any open containing both** — the square `hsqW` of Stacks 0E91,
  taken over the stage `U ∪ W`.
* `AlgebraicGeometry.BigFppfOver.isPullback_preimageOpensObj`: **the preimage of an open `U` of
  `S` in an object `T` of the site is the fibre product `U ×_S T`** — the square identifying the
  `V` of Stacks 0E91 when `T` is `Spec 𝒪_{S,s}`.

## Implementation notes

The second square is stated for the canonical terminal object `CategoryTheory.Over.mkIdTerminal`
of the site rather than for an abstract terminal object, because the image in schemes of the
structure morphism to it is the structure morphism of the object, which is
`AlgebraicGeometry.FinitePresentationSpacesOver.toScheme_map_mkIdTerminal_from`; for an abstract
terminal object that identification would itself have to be transported.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A square of the big fppf category over `S` is cartesian as soon as its image in schemes
is.** The functor to schemes is faithful and reflects limits of cospans, being a composite of a
forgetful functor of a slice with a full subcategory inclusion. The commuting condition does not
have to be supplied: faithfulness recovers it from the mapped square. -/
theorem isPullback_of_toScheme {P T U' Z : BigFppfOver B S hS} {a : P ⟶ T} {b : P ⟶ U'}
    {f : T ⟶ Z} {g : U' ⟶ Z}
    (h : IsPullback ((toScheme B S hS).map a) ((toScheme B S hS).map b)
      ((toScheme B S hS).map f) ((toScheme B S hS).map g)) :
    IsPullback a b f g :=
  IsPullback.of_map_of_faithful (toScheme B S hS) h

/-- The image in schemes of the inclusion of opens `U ≤ V` as a morphism of the site is the
inclusion `S.homOfLE h`. -/
@[simp]
theorem toScheme_map_opensHom {U V : S.Opens} (h : U ≤ V) :
    (toScheme B S hS).map (opensHom B S hS h) = S.homOfLE h :=
  rfl

/-- **The intersection of two opens of `S` is their fibre product over any open containing
both**, in the big fppf category over `S`. This is the square `hsqW` of Stacks 0E91: for `U` the
retrocompact open and `W` an open neighbourhood of the point, the stage is `Z = U ∪ W` and the
vertex is `U ∩ W`. -/
theorem isPullback_opensHom_inf {U V Z : S.Opens} (hU : U ≤ Z) (hV : V ≤ Z) :
    IsPullback (opensHom B S hS (inf_le_left : U ⊓ V ≤ U))
      (opensHom B S hS (inf_le_right : U ⊓ V ≤ V))
      (opensHom B S hS hU) (opensHom B S hS hV) := by
  refine isPullback_of_toScheme B S hS ?_
  simpa only [toScheme_map_opensHom] using isPullback_opens_inf_le hU hV

/-! ### The preimage of an open in an object of the site -/

/-- The image in schemes of the structure morphism of an object of the site to the canonical
terminal object is the structure morphism of that object. -/
theorem toScheme_map_mkIdTerminal_from (T : BigFppfOver B S hS) :
    (toScheme B S hS).map (Over.mkIdTerminal.from T) = B.inclusion.map T.hom :=
  congrArg B.inclusion.map (Over.mkIdTerminal_from_left T)

/-- **The preimage of an open of `S` in an object of the big fppf category over `S`**, as an
object of that category: its structure morphism is the open immersion of the preimage followed
by the structure morphism of the object. -/
noncomputable def preimageOpensObj (T : BigFppfOver B S hS) (U : S.Opens) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (X := B.obj (contains_opens B T.left.property (T.hom.hom ⁻¹ᵁ U)))
    ((T.hom.hom ⁻¹ᵁ U).ι ≫ T.hom.hom))

/-- The structure morphism of `preimageOpensObj` is the open immersion of the preimage followed
by the structure morphism of `T`. -/
@[simp]
theorem preimageOpensObj_hom_hom (T : BigFppfOver B S hS) (U : S.Opens) :
    (preimageOpensObj B S hS T U).hom.hom = (T.hom.hom ⁻¹ᵁ U).ι ≫ T.hom.hom :=
  rfl

/-- The open immersion of the preimage into the object, as a morphism of the site. -/
noncomputable def preimageOpensIota (T : BigFppfOver B S hS) (U : S.Opens) :
    preimageOpensObj B S hS T U ⟶ T :=
  Over.homMk (ObjectProperty.homMk (T.hom.hom ⁻¹ᵁ U).ι)
    (ObjectProperty.hom_ext _ rfl)

/-- The underlying morphism of schemes of `preimageOpensIota` is the open immersion of the
preimage. -/
@[simp]
theorem preimageOpensIota_left_hom (T : BigFppfOver B S hS) (U : S.Opens) :
    (preimageOpensIota B S hS T U).left.hom = (T.hom.hom ⁻¹ᵁ U).ι :=
  rfl

/-- The restriction of the structure morphism, from the preimage of `U` to `U`, as a morphism of
the site. -/
noncomputable def preimageOpensRestrict (T : BigFppfOver B S hS) (U : S.Opens) :
    preimageOpensObj B S hS T U ⟶ opensObj B S hS U :=
  Over.homMk (ObjectProperty.homMk (T.hom.hom ∣_ U))
    (ObjectProperty.hom_ext _ (isPullback_morphismRestrict T.hom.hom U).w)

/-- The underlying morphism of schemes of `preimageOpensRestrict` is the restriction
`T.hom.hom ∣_ U`. -/
@[simp]
theorem preimageOpensRestrict_left_hom (T : BigFppfOver B S hS) (U : S.Opens) :
    (preimageOpensRestrict B S hS T U).left.hom = T.hom.hom ∣_ U :=
  rfl

/-- **The preimage of an open `U` of `S` in an object `T` of the big fppf category over `S` is
the fibre product `U ×_S T`.** For `T = Spec 𝒪_{S,s}` this is the square identifying the `V` of
Stacks 0E91 with `Spec 𝒪_{S,s} ∩ U`. -/
theorem isPullback_preimageOpensObj (T : BigFppfOver B S hS) (U : S.Opens) :
    IsPullback (preimageOpensRestrict B S hS T U) (preimageOpensIota B S hS T U)
      (Over.mkIdTerminal.from (opensObj B S hS U)) (Over.mkIdTerminal.from T) := by
  refine isPullback_of_toScheme B S hS ?_
  have h : IsPullback ((toScheme B S hS).map (preimageOpensRestrict B S hS T U))
      ((toScheme B S hS).map (preimageOpensIota B S hS T U))
      (B.inclusion.map (opensObj B S hS U).hom) (B.inclusion.map T.hom) :=
    isPullback_morphismRestrict T.hom.hom U
  rwa [← toScheme_map_mkIdTerminal_from B S hS (opensObj B S hS U),
    ← toScheme_map_mkIdTerminal_from B S hS T] at h

end AlgebraicGeometry.BigFppfOver

end
