module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage

/-!
# The apex of a cartesian square along an open immersion is a preimage open subscheme

Let

```
W --f'--> X
|          |
i'         i
↓          ↓
Y --f-->  Z
```

be a cartesian square of schemes in which `i` is an open immersion. Then `i'` is an open immersion
too, its image is the inverse image `f⁻¹(i(X))`, and **`W` is isomorphic to the open subscheme
`f ⁻¹ᵁ i.opensRange` of `Y`, compatibly with the two morphisms to `Y`.**

Mathlib has this for its own chosen pullback and for a leg of the form `U.ι`
(`AlgebraicGeometry.pullbackRestrictIsoRestrict`,
`AlgebraicGeometry.isPullback_morphismRestrict`), and it has the converse direction for an
arbitrary open immersion (`AlgebraicGeometry.IsOpenImmersion.isPullback`: a commuting square of
two open immersions is cartesian as soon as the ranges match). What is recorded here is the
direction that reads an *abstract* cartesian square as the preimage open, which is the form in
which a base-change square identifies a corner of a square of schemes over `Spec A_g` with the
part of the corresponding corner over `Spec A` lying over the basic open `D(g)`.

## Main definitions

* `AlgebraicGeometry.isoPreimageOpensRange_of_isPullback`: **the apex of the square is the
  preimage open subscheme.**

## Main results

* `AlgebraicGeometry.isoPreimageOpensRange_of_isPullback_hom_ι`: the identification is compatible
  with the two morphisms to `Y`, which is what makes it usable: a statement about `W` over `Y`
  becomes a statement about the open subscheme.

## Implementation notes

The `Opens`-level content — that the image of `i'` is `f⁻¹(i(X))` for an abstract cartesian square
— is already `AlgebraicGeometry.preimage_opensRange_of_isPullback`
(`StacksFrontier/AlgebraicGeometry/LimitApproxFunctor/Stage.lean`), and is used rather than
reproved;
all that is added here is the passage from that equality of opens to an isomorphism of schemes,
through `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`. The equality of *ranges* which the
latter wants is extracted into
`AlgebraicGeometry.range_base_eq_of_isPullback` so that the compatibility lemma can be stated
against the very same proof term as the definition, rather than relying on proof irrelevance to
identify two of them.

Open immersions are stable under base change by Mathlib's
`AlgebraicGeometry.IsOpenImmersion.isOpenImmersion_stableUnderBaseChange`, so the hypothesis is
only that `i` is one; nothing is assumed of `f`, and in particular no flatness, finiteness or
separatedness hypothesis appears. That stability is invoked through Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`
in a private helper (and directly in the definition);
`Stacks.OpenBaseChangeCharts.isOpenImmersion_of_isPullback`
(`StacksFrontier/AlgebraicGeometry/OpenBaseChangeCharts.lean`) is a similar wrapper, for the
case in which the open immersion is the inclusion `Uo.ι` of an open subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} {f' : W ⟶ X} {i' : W ⟶ Y} {i : X ⟶ Z} {f : Y ⟶ Z}

/-- The base change `i'` of an open immersion `i` along any morphism is an open immersion. -/
private theorem isOpenImmersion_of_isPullback_aux [IsOpenImmersion i] (h : IsPullback f' i' i f) :
    IsOpenImmersion i' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h inferInstance

/-- The image of the base change of an open immersion is the inverse image of its image, read as
an equality of ranges of the underlying continuous maps. This is
`AlgebraicGeometry.preimage_opensRange_of_isPullback` in the shape
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` consumes. -/
theorem range_base_eq_of_isPullback [IsOpenImmersion i] (h : IsPullback f' i' i f) :
    Set.range i'.base = Set.range (f ⁻¹ᵁ i.opensRange).ι.base := by
  have := isOpenImmersion_of_isPullback_aux h
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
    preimage_opensRange_of_isPullback h.flip]

/-- **The apex of a cartesian square one of whose legs is an open immersion is the preimage open
subscheme.** In the square above, `W` is isomorphic to the open subscheme `f ⁻¹ᵁ i.opensRange` of
`Y`; `AlgebraicGeometry.isoPreimageOpensRange_of_isPullback_hom_ι` says the isomorphism is
compatible with the two morphisms to `Y`. -/
noncomputable def isoPreimageOpensRange_of_isPullback [IsOpenImmersion i]
    (h : IsPullback f' i' i f) : W ≅ (f ⁻¹ᵁ i.opensRange).toScheme :=
  haveI := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h
    inferInstance
  IsOpenImmersion.isoOfRangeEq i' (f ⁻¹ᵁ i.opensRange).ι (range_base_eq_of_isPullback h)

/-- **The identification of the apex with the preimage open subscheme is compatible with the two
morphisms to `Y`.** -/
@[reassoc (attr := simp)]
lemma isoPreimageOpensRange_of_isPullback_hom_ι [IsOpenImmersion i]
    (h : IsPullback f' i' i f) :
    (isoPreimageOpensRange_of_isPullback h).hom ≫ (f ⁻¹ᵁ i.opensRange).ι = i' :=
  have := isOpenImmersion_of_isPullback_aux h
  IsOpenImmersion.isoOfRangeEq_hom_fac i' (f ⁻¹ᵁ i.opensRange).ι
    (range_base_eq_of_isPullback h)

/-- The inverse form of the previous compatibility. -/
@[reassoc (attr := simp)]
lemma isoPreimageOpensRange_of_isPullback_inv_comp [IsOpenImmersion i]
    (h : IsPullback f' i' i f) :
    (isoPreimageOpensRange_of_isPullback h).inv ≫ i' = (f ⁻¹ᵁ i.opensRange).ι :=
  have := isOpenImmersion_of_isPullback_aux h
  IsOpenImmersion.isoOfRangeEq_inv_fac i' (f ⁻¹ᵁ i.opensRange).ι
    (range_base_eq_of_isPullback h)

end AlgebraicGeometry

end
