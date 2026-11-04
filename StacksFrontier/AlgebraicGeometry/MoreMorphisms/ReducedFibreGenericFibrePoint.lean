module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointGeneralizing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GoingDownNormal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# A point of a normalized base change lies over a generic point of its own fibre

Let `f : X ⟶ S` have normal locally Noetherian source, let `g : T ⟶ S` be integral and flat, and
let `ν` be the normalization of the base change `W = X ×_S T`, assumed locally Noetherian — which
over a Nagata base it is, the normalization being finite there.  **Then `ν ≫ pr₁ : W^ν ⟶ X` lifts
generalizations**, and consequently a point of `W^ν` which is a generic point of an irreducible
component of its own fibre over `S` lies over a point of `X` with the same property.

This is the step of the reduced fibre theorem which hands the finitely many *bad* points of `X`
— the generic points of components of fibres lying outside the smooth locus — the points of the
normalized base change that have to be handled through the elimination of ramification.

The lifting of generalizations is **going down**, and it comes from normality, not from
finiteness: `ν ≫ pr₁` is an integral morphism between normal schemes, so
`AlgebraicGeometry.generalizingMap_base_of_isIntegralHom_of_isNormal` applies.  Finiteness of
`ν ≫ pr₁` would not do, since a finite morphism can raise codimension — the closed immersion of
a closed point into a curve takes coheight `0` to coheight `1` — and over a non-normal `X` a
point of `W^ν` need not lie over a generic point of a fibre at all.

## Main results

* `AlgebraicGeometry.generalizingMap_normalization_comp_pullbackFst`: the normalization of a base
  change, followed by the projection, lifts generalizations.
* `AlgebraicGeometry.mem_genericPoints_asFiber_normalization_pullbackFst`: a generic point of a
  fibre of the normalized base change lies over a generic point of its own fibre of `f`.

## Implementation notes

Local Noetherianness of the normalization is a hypothesis rather than a consequence: the
normalization of a locally Noetherian scheme is locally Noetherian only when it is of finite
type over it, which is the Nagata condition
(`AlgebraicGeometry.Scheme.isFinite_normalization`).  Passing it in keeps this file free of the
Nagata hypothesis, which enters the reduced fibre theorem for other reasons as well.

The hypothesis that `g` is flat is what makes the projection `pr₁` carry generic points to
generic points, as `AlgebraicGeometry.generalizingMap_base_of_isIntegralHom_of_isNormal` demands;
in the reduced fibre theorem `g` is the spectrum of a finite extension of Dedekind domains, which
is finite and flat.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 037F](https://stacks.math.columbia.edu/tag/037F)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- **The normalization of a base change, followed by the projection, lifts generalizations.**
Let `f : X ⟶ S` have normal locally Noetherian source and let `g : T ⟶ S` be integral and flat.
If the normalization `W^ν` of `W = X ×_S T` is locally Noetherian, then
`ν ≫ pr₁ : W^ν ⟶ X` lifts generalizations.

Both ends are normal — the normalization by construction, `X` by hypothesis — and the composite
is integral, being the normalization morphism followed by the base change of the integral `g`.
Its generic points go to generic points: the normalization carries them to generic points of `W`
and the flat projection carries those to generic points of `X`.  That is going down. -/
theorem generalizingMap_normalization_comp_pullbackFst [IsNormal X] [IsLocallyNoetherian X]
    [IsIntegralHom g] [Flat g]
    (hW : ∀ U : (pullback f g : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g : Scheme.{u})) → (irreducibleComponents U).Finite)
    (hN : IsLocallyNoetherian ((pullback f g : Scheme.{u}).normalizationScheme hW)) :
    GeneralizingMap ((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g).base := by
  have _ := hN
  have _ : IsNormal ((pullback f g : Scheme.{u}).normalizationScheme hW) :=
    Scheme.isNormal_normalizationScheme _ hW
  have _ : IsIntegralHom ((pullback f g : Scheme.{u}).normalization hW) :=
    Scheme.isIntegralHom_normalization _ hW
  refine generalizingMap_base_of_isIntegralHom_of_isNormal _ fun z hz => ?_
  rw [Scheme.Hom.comp_apply]
  exact mem_genericPoints_of_generalizingMap (Flat.generalizingMap (pullback.fst f g))
    (Scheme.normalization_mem_genericPoints _ hW hz)

/-- **A generic point of a fibre of the normalized base change lies over a generic point of its
own fibre.** In the situation of
`AlgebraicGeometry.generalizingMap_normalization_comp_pullbackFst`, let `y` be a point of the
normalization of `X ×_S T` which is a generic point of an irreducible component of its own fibre
of `ν ≫ pr₁ ≫ f`.  Then its image in `X` is a generic point of an irreducible component of its
own fibre of `f`.

The generic-point condition is a condition on the ambient scheme — no proper generalization lies
in the same fibre — and as such transports along any morphism lifting generalizations, which
`ν ≫ pr₁` is by going down. -/
theorem mem_genericPoints_asFiber_normalization_pullbackFst [IsNormal X] [IsLocallyNoetherian X]
    [IsIntegralHom g] [Flat g]
    (hW : ∀ U : (pullback f g : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g : Scheme.{u})) → (irreducibleComponents U).Finite)
    (hN : IsLocallyNoetherian ((pullback f g : Scheme.{u}).normalizationScheme hW))
    {y : (pullback f g : Scheme.{u}).normalizationScheme hW}
    (hy : (((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g) ≫ f).asFiber y ∈
      genericPoints ↥((((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g) ≫
        f).fiber ((((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g) ≫
          f).base y))) :
    f.asFiber (((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g).base y) ∈
      genericPoints ↥(f.fiber (f.base
        (((pullback f g : Scheme.{u}).normalization hW ≫ pullback.fst f g).base y))) :=
  mem_genericPoints_asFiber_of_generalizingMap _ f
    (generalizingMap_normalization_comp_pullbackFst f g hW hN) hy

end AlgebraicGeometry

end
