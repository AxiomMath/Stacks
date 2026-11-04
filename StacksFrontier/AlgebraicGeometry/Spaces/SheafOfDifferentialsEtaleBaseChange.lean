module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of differentials on a square of étale charts, and étale base change

Stacks 04CX attaches to a commutative square with top edge `a : U ⟶ X` and left edge
`ψ : U ⟶ V` a comparison map `c_a : a^*Ω_{X/Y} ⟶ Ω_{U/V}`, characterized by carrying
`a^*d_{X/Y}(t)` to `d_{U/V}(a♯ t)`
(`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`, with uniqueness
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`).  Stacks 04CU says that when the two
vertical arrows `a : U ⟶ X` and `b : V ⟶ Y` are étale this map is an isomorphism, and the
identification it provides is `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`.

What this file adds is that the identification of Stacks 04CU **is** the comparison map of
Stacks 04CX for the full square, not only for a square whose bottom edge is an identity:
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale` already treats the case
`b = 𝟙 Y`, and the step from it to an arbitrary étale `b` is the étale-base comparison
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`, which carries one universal
derivation to the other and therefore carries one characterizing property to the other.

The consequence for base change is Stacks 05ZC for an étale `g`: in a cartesian square with
bottom edge `g : Y' ⟶ Y` étale the top edge `g' : X' ⟶ X` is étale too, by Stacks 03FU, so the
square has both vertical arrows étale and its comparison map
`(g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` is an isomorphism.  **This is a special case of Stacks 05ZC and is
not registered for that tag**, which assumes nothing whatever of `g`; it is the part of
Stacks 05ZC that is reachable without the invertibility clause of Stacks 04CS.  See the
provenance section of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean` for what the general
case needs.

## Main results

* `AlgebraicGeometry.Space.universalDerivationHom_comp_sharpIsoHom` and
  `AlgebraicGeometry.Space.pushforwardUniversalDerivationHom_comp_sharpIsoHom`: the étale-base
  comparison of Stacks 04CU carries the universal derivation `d_{U/V}` to `d_{U/Z}`, globally
  and after pushing forward along the top edge.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_sharpIsoHom`: a comparison map of
  Stacks 04CX followed by the étale-base comparison is again a comparison map of Stacks 04CX,
  for the square with the same top and right edges and with left edge the other structure
  morphism.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etaleSquare`: **Stacks 04CU**, the
  invertibility clause on a full square of étale charts — every comparison map of Stacks 04CX
  for a commutative square whose two vertical arrows are étale is an isomorphism.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_isEtale`:
  Stacks 05ZC for an étale `g`, unconditionally.

## Implementation notes

The two derivation calculations are the ones of
`AlgebraicGeometry.Space.universalDerivationHom_comp_toRelativeDifferentials` and
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom_comp_toRelativeDifferentials` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFibreProduct.lean` with the canonical
map of Stacks 05Z8 replaced by the étale-base comparison; the input they consume is
`AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsIsoOfSharpIso` in place of
`AlgebraicGeometry.Space.toRelativeDifferentials_app_d`.

`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_sharpIsoHom` is stated for an arbitrary
isomorphism of the two structure maps rather than for the étale-base comparison of a square,
because that is the shape `AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso` is stated
in and nothing else is used.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU), a base change of an
  étale morphism of algebraic spaces is étale.
* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC), base change of the
  sheaf of differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z U V : AlgebraicSpaces B S hS}

/-! ### The étale-base comparison and the universal derivations -/

/-- The universal derivation `d_{U/V}` followed by the étale-base comparison
`Ω_{U/V} ⟶ Ω_{U/Z}` of Stacks 04CU is the universal derivation `d_{U/Z}`, as a morphism of the
underlying sheaves of sets.  This is
`AlgebraicGeometry.Space.universalDerivation_sheafOfDifferentialsIsoOfSharpIso` read
globally. -/
theorem universalDerivationHom_comp_sharpIsoHom (p : U ⟶ V) (q : U ⟶ Z)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (sharpIsoHom B S hS p q e he) =
      universalDerivationHom B S hS q :=
  Sheaf.hom_ext_sections fun _ t ↦
    universalDerivation_sheafOfDifferentialsIsoOfSharpIso B S hS p q e he t

/-- The composite `a_*d_{U/V} ∘ a♯` of Stacks 04CX followed by the direct image of the
étale-base comparison `Ω_{U/V} ⟶ Ω_{U/Z}` of Stacks 04CU is the composite `a_*d_{U/Z} ∘ a♯` of
Stacks 04CX. -/
theorem pushforwardUniversalDerivationHom_comp_sharpIsoHom (a : U ⟶ X) (p : U ⟶ V) (q : U ⟶ Z)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q) :
    pushforwardUniversalDerivationHom B S hS a p ≫
        (smallEtaleDirectImage B S hS a).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            (sharpIsoHom B S hS p q e he)) =
      pushforwardUniversalDerivationHom B S hS a q := by
  have h1 : structureSharpSet B S hS a ≫ (smallEtaleDirectImage B S hS a).map
        (universalDerivationHom B S hS p ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            (sharpIsoHom B S hS p q e he)) =
      pushforwardUniversalDerivationHom B S hS a p ≫
        (smallEtaleDirectImage B S hS a).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
            (sharpIsoHom B S hS p q e he)) := by
    rw [Functor.map_comp]
    rfl
  rw [← h1, universalDerivationHom_comp_sharpIsoHom]
  rfl

/-- **A comparison map of Stacks 04CX followed by the étale-base comparison of Stacks 04CU is a
comparison map of Stacks 04CX.**  If `c : a^*Ω_{X/Y} ⟶ Ω_{U/V}` is the comparison map of the
square with top edge `a`, right edge `f` and left edge `p : U ⟶ V`, and the structure maps of
`p` and of `q : U ⟶ Z` differ by an isomorphism of their sources, then `c` followed by the
comparison `Ω_{U/V} ⟶ Ω_{U/Z}` is the comparison map of the square with top edge `a`, right
edge `f` and left edge `q`.

Only the characterizing property is used: the adjunct is natural in its right argument, and the
étale-base comparison carries `d_{U/V}` to `d_{U/Z}`. -/
theorem isSheafOfDifferentialsMap_comp_sharpIsoHom (a : U ⟶ X) (f : X ⟶ Y) (p : U ⟶ V)
    (q : U ⟶ Z)
    (e : inverseImageStructureSheaf B S hS q ≅ inverseImageStructureSheaf B S hS p)
    (he : e.hom ≫ structureSharpInverseImage B S hS p =
      structureSharpInverseImage B S hS q)
    {c : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS p}
    (hc : IsSheafOfDifferentialsMap B S hS a f p c) :
    IsSheafOfDifferentialsMap B S hS a f q (c ≫ sharpIsoHom B S hS p q e he) := by
  intro W t
  rw [Adjunction.homEquiv_naturality_right]
  change ((smallEtaleDirectImage B S hS a).map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U)).map
        (sharpIsoHom B S hS p q e he))).hom.app W
      ((((modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS f)
        (sheafOfDifferentials B S hS p) c).val.app W).hom
          ((universalDerivation B S hS f).d t)) = _
  rw [hc W t]
  exact congrArg (fun z ↦ z.hom.app W t)
    (pushforwardUniversalDerivationHom_comp_sharpIsoHom B S hS a p q e he)

/-! ### Stacks 04CU on a full square of étale charts -/

/-- **Stacks 04CU, the invertibility clause on a full square of étale charts.**  Let

```
U --ψ--> V
|        |
a        b
v        v
X --f--> Y
```

be a commutative square of algebraic spaces over `S` whose vertical arrows `a` and `b` are
étale.  Then every comparison map `c : a^*Ω_{X/Y} ⟶ Ω_{U/V}` of Stacks 04CX for that square is
an isomorphism.

`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etale` is this statement for
`b = 𝟙 Y`.  The step to an arbitrary étale `b` is the étale-base comparison
`Ω_{U/V} ≅ Ω_{U/(ψ ≫ b)}` of
`AlgebraicGeometry.Space.sheafOfDifferentialsIsoOfSharpIso`, built from Stacks 03G8 and the
clause `b^{-1}𝒪_Y = 𝒪_V` of Stacks 03LV: composing `c` with it produces, by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp_sharpIsoHom`, a comparison map of the
square with left edge `ψ ≫ b = a ≫ f`, which is invertible by the case already proved. -/
@[stacks 04CU "the identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}` is the canonical one on a full
  square of étale charts: every comparison map of 04CX for a commutative square whose two
  vertical arrows are étale is an isomorphism.  The already registered clause is the case of a
  square whose bottom edge is an identity"]
theorem isIso_of_isSheafOfDifferentialsMap_etaleSquare (f : X ⟶ Y) (a : U ⟶ X) (ψ : U ⟶ V)
    (b : V ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = ψ ≫ b)
    {c : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS ψ}
    (hc : IsSheafOfDifferentialsMap B S hS a f ψ c) : IsIso c := by
  set e := etaleBaseInverseImageStructureSheafIso B S hS ψ b hb with he'
  set he := etaleBaseInverseImageStructureSheafIso_hom_structureSharpInverseImage B S hS ψ b hb
    with hhe
  have hsharp : IsIso (sharpIsoHom B S hS ψ (ψ ≫ b) e he) :=
    (sheafOfDifferentialsIsoOfSharpIso B S hS ψ (ψ ≫ b) e he).isIso_hom
  have : IsIso (c ≫ sharpIsoHom B S hS ψ (ψ ≫ b) e he) :=
    isIso_of_isSheafOfDifferentialsMap_etale B S hS a ha f (ψ ≫ b) hcomm
      (isSheafOfDifferentialsMap_comp_sharpIsoHom B S hS a f ψ (ψ ≫ b) e he hc)
  exact IsIso.of_isIso_comp_right c (sharpIsoHom B S hS ψ (ψ ≫ b) e he)

/-! ### Stacks 05ZC for an étale base change -/

/-- **Stacks 05ZC for an étale `g`.**  Let `p : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `g : Y' ⟶ Y` be **étale** and let `X'`, with its projections `g' : X' ⟶ X` and
`p' : X' ⟶ Y'`, be the base change of `p` by `g`.  Then every comparison map
`c : (g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX is an isomorphism.

The top edge `g'` is étale by Stacks 03FU, so the cartesian square is a square of étale charts
and `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etaleSquare` applies.

This is **not** Stacks 05ZC, which assumes nothing of `g`: the general case needs the
scheme-level statement Morphisms 01V0 through the invertibility clause of Stacks 04CS, and is
`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChange.lean`.  No tag is
registered here. -/
theorem isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_isEtale {X' Y' : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback g' p' p g)
    (hg : IsEtale B S hS g.hom)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c) : IsIso c :=
  isIso_of_isSheafOfDifferentialsMap_etaleSquare B S hS p g' p' g
    (isEtale_of_isPullback B S hS p' g' g p h.flip hg) hg h.w hc

end AlgebraicGeometry.Space

end
