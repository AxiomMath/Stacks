module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SiteMembership

/-!
# The universal degree-`d` cover pulls back to the cover of the classified structure

Let `d` be positive, let `T` be an affine scheme and let `x : T ⟶ X` be a point of the scheme of
structure constants of **Stacks 05YM**. The structure `x` classifies is the extension of the
universal structure along the map of global sections of `x`, by
`AlgebraicGeometry.FiniteFreeAlgebra.map_universalStructure`, and therefore — by
`AlgebraicGeometry.FiniteFreeAlgebra.isPullback_specCover_map` — its cover is the base change of
the universal cover along `x`.

This is the statement that makes the 1-morphism
`AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` hit the cover of every structure: a point of
the scheme of structure constants is sent by that 1-morphism to the base change of the universal
cover along the point, and the square below identifies that base change with the cover of the
structure the point classifies.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_universalFiniteCoverMap_point`: the cover of
  the structure classified by a point of the scheme of structure constants is the base change of
  the universal cover along that point.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap`: the
  cover of every structure over the global sections of an affine scheme is a base change of the
  universal cover.

## Implementation notes

The base of the universal cover is the spectrum of the global sections of the scheme of structure
constants rather than that scheme itself, because
`AlgebraicGeometry.FiniteFreeAlgebra.specCover` builds the cover of a structure over the spectrum
of its ring of definition. For the same reason the point appears below as
`T.isoSpec.hom ≫ Spec x.appTop`, the morphism to that spectrum which `x` induces; `T` is assumed
affine so that this loses nothing, and that is the only use of the hypothesis.

No `@[stacks]` attribute is placed here. What **Stacks 05YM** asserts is that the scheme of
structure constants represents structures, which is
`AlgebraicGeometry.FiniteFreeAlgebra.representation`; the compatibility of the universal cover
with base change along a point is not part of that statement.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

/-- **The universal cover pulls back to the cover of the classified structure.** For a point `x`
of the scheme of structure constants with affine source `T`, the spectrum of the algebra of the
structure `x` classifies is the fibre product of the spectrum of the algebra of the universal
structure with `T` over the spectrum of the global sections of the scheme of structure
constants. -/
theorem isPullback_universalFiniteCoverMap_point (d : ℕ) [NeZero d] (T : Scheme.{u}) [IsAffine T]
    (x : T ⟶ FiniteFreeAlgebra.scheme.{u} d) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Carrier.mapRingHom x.appTop.hom (universalStructure.{u} d))))
      ((specCover (map x.appTop.hom (universalStructure.{u} d))).hom ≫ T.isoSpec.inv)
      (specCover (universalStructure.{u} d)).hom
      (T.isoSpec.hom ≫ Spec.map x.appTop) :=
  (isPullback_specCover_map x.appTop.hom (universalStructure.{u} d)).of_iso
    (Iso.refl _) (Iso.refl _) T.isoSpec.symm (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- The structure classified by a point of the scheme of structure constants, read through the
identification of **Stacks 05YM**, is the extension of the universal structure along the map of
global sections of the point. -/
theorem map_appTop_universalStructure (d : ℕ) [NeZero d] (T : Scheme.{u})
    (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    map (((representation.{u} d).equiv T).symm m).appTop.hom (universalStructure.{u} d) = m :=
  (map_universalStructure.{u} d (((representation.{u} d).equiv T).symm m)).trans
    ((representation.{u} d).equiv T |>.apply_symm_apply m)

/-- **The cover of every structure over an affine scheme is a base change of the universal
cover.** Given a free `d`-dimensional structure `m` over the global sections of an affine scheme
`T`, the spectrum of the algebra of `m` is the fibre product of the spectrum of the algebra of
the universal structure with `T`, along the point of the scheme of structure constants that
classifies `m`. -/
theorem exists_point_isPullback_universalFiniteCoverMap (d : ℕ) [NeZero d] (T : Scheme.{u})
    [IsAffine T] (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    ∃ (pt : T ⟶ Spec (.of Γ(FiniteFreeAlgebra.scheme.{u} d, ⊤)))
      (g : (specCover m).left ⟶ (specCover (universalStructure.{u} d)).left),
      IsPullback g ((specCover m).hom ≫ T.isoSpec.inv)
        (specCover (universalStructure.{u} d)).hom pt := by
  obtain ⟨x, hm⟩ : ∃ x : T ⟶ FiniteFreeAlgebra.scheme.{u} d,
      map x.appTop.hom (universalStructure.{u} d) = m :=
    ⟨((representation.{u} d).equiv T).symm m, map_appTop_universalStructure d T m⟩
  subst hm
  exact ⟨T.isoSpec.hom ≫ Spec.map x.appTop, _,
    isPullback_universalFiniteCoverMap_point d T x⟩

end AlgebraicGeometry.FiniteFreeAlgebra

end
