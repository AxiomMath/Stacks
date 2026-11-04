module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso

/-!
# Étale localisation of the naive cotangent complex of a morphism of algebraic spaces

Let `S` be a scheme and consider a commutative square
```
U --g--> V
|p       |q
X --f--> Y
```
of algebraic spaces over `S` with `p` and `q` étale.  Stacks 0D0W asserts that there is a
canonical identification `NL_{X/Y}|_{U_étale} = NL_{U/V}` in `D(𝒪_U)`.  The source's proof is in
two halves: formation of the naive cotangent complex commutes with inverse image, so that
`p⁻¹NL_{X/Y} = NL_{p⁻¹𝒪_X / p⁻¹f⁻¹𝒪_Y}` (Modules on Sites, Lemma 08TZ), and then the two
identifications `p⁻¹𝒪_X = 𝒪_U` and `g⁻¹𝒪_V = p⁻¹f⁻¹𝒪_Y` of Properties of Spaces, Lemma 03LV
turn the right-hand side into `NL_{U/V}`.

This file proves the second half.  The first half is not instantiated here, but Tag 08TZ is NOT
absent from the library for sites: it is
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`
(`StacksFrontier/CategoryTheory/Sites/Modules/NaiveCotangentInverseImageComplex.lean`), an
isomorphism of two-term complexes for an arbitrary morphism of topoi.  What stops it from being
instantiated at `p` is its universe shape, not its absence: it is stated for a morphism of topoi
`Sheaf J (Type (max u v w)) ⟶ Sheaf K (Type (max u' v' w'))` with the ring sheaves valued in the
same ambient section universe, so that universe contains the site's object universe, whereas the
small étale site of an algebraic space has objects in `Type (u + 1)` and structure sheaves in
`CommRingCat.{u}` (`AlgebraicGeometry.Space.smallToposMorphismTypeU`).  Restating 08TZ with the
section universe independent of the site's object universe is what the first half needs.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageNaiveCotangentComplex` is
  `NL_{p⁻¹𝒪_X / p⁻¹f⁻¹𝒪_Y}`, the naive cotangent complex of the inverse image along `p` of the
  structure data of `f`.  This is what Tag 08TZ identifies with `p⁻¹NL_{X/Y}`, at the universe
  shape of `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`.
* `AlgebraicGeometry.Space.etaleSquareBaseRingIso` is the identification
  `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹𝒪_V` of the two base rings, for `q` étale.
* `AlgebraicGeometry.Space.naiveCotangentEtaleLocalisationIso` is the resulting identification
  `NL_{p⁻¹𝒪_X / p⁻¹f⁻¹𝒪_Y} ≅ NL_{U/V}`.

## Main results

* `AlgebraicGeometry.Space.etaleSquareBaseRingIso_fSharpInverseImage`: the square of sheaves of
  commutative rings on `U_étale` that the identification sits in commutes, that is the two
  composite structure maps `p⁻¹f⁻¹𝒪_Y ⟶ p⁻¹𝒪_X ⟶ 𝒪_U` and `g⁻¹𝒪_V ⟶ 𝒪_U` agree.
* `AlgebraicGeometry.Space.naiveCotangentEtaleLocalisationIso_hom`: the forward map of the
  identification is the canonical chain map of Stacks 08TX attached to that square, so the
  identification is canonical and not a second choice.

## Implementation notes

The identification `g⁻¹𝒪_V ≅ p⁻¹f⁻¹𝒪_Y` is assembled out of the composition law of Stacks 03G8
in inverse-image form, which supplies `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` for the commuting square
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso`), followed by the
inverse image along `g` of the identification `q⁻¹𝒪_Y ≅ 𝒪_V` of Stacks 03LV at the étale
morphism `q`.  That `p` is étale enters separately, through the same lemma of Stacks 03LV at `p`,
as the identification `p⁻¹𝒪_X ≅ 𝒪_U` of the top rings.

Both identifications being isomorphisms, the canonical chain map of Stacks 08TX attached to the
resulting square is an isomorphism by
`Stacks.SheafOfModules.isIso_naiveCotangentComplexMapOfSquare`.  The target is read in complexes
of sheaves of `p⁻¹𝒪_X`-modules through restriction of scalars along `p⁻¹𝒪_X ≅ 𝒪_U`; this is the
Lean reading of the source's equality in `D(𝒪_U)`, which is not formulated here — nothing is
said in the derived category.

## References

* [Stacks Project, Tag 0D0W](https://stacks.math.columbia.edu/tag/0D0W)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of
  the naive cotangent complex — absent from the library for sites.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of
  the naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V X Y : AlgebraicSpaces B S hS}

/-- `NL_{p⁻¹𝒪_X / p⁻¹f⁻¹𝒪_Y}`: the naive cotangent complex, on the small étale site of `U`, of
the inverse image along `p : U ⟶ X` of the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of `f : X ⟶ Y`.

This is the complex that Stacks 08TZ identifies with the restriction `p⁻¹NL_{X/Y}` of the
naive cotangent complex of `f`.  That tag is carried for sites by
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`; it is not instantiated at this
universe shape, where the ambient section universe `u` is smaller than the site's object
universe `u + 1`. -/
noncomputable def inverseImageNaiveCotangentComplex (p : U ⟶ X) (f : X ⟶ Y) :
    CochainComplex (_root_.SheafOfModules.{u + 1, u, u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        ((smallEtaleInverseImageRing B S hS p).obj (smallEtaleRingedTopos B S hS X).O))) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS U).J
    ((smallEtaleInverseImageRing B S hS p).obj
      ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O))
    ((smallEtaleInverseImageRing B S hS p).obj (smallEtaleRingedTopos B S hS X).O)
    ((smallEtaleInverseImageRing B S hS p).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)

/-- **Stacks 0D0W, the identification `g⁻¹𝒪_V = p⁻¹f⁻¹𝒪_Y` of the base rings.**  For a commuting
square `p ≫ f = g ≫ q` of algebraic spaces with `q` étale,

`p⁻¹f⁻¹𝒪_Y ≅ g⁻¹𝒪_V`

as sheaves of commutative rings on the small étale site of `U`.  It is the comparison
`p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` of the composition law of Stacks 03G8 followed by the inverse image
along `g` of the identification `q⁻¹𝒪_Y ≅ 𝒪_V` of Stacks 03LV. -/
noncomputable def etaleSquareBaseRingIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V} {q : V ⟶ Y}
    (h : p ≫ f = g ≫ q) (hq : IsEtale B S hS q.hom) :
    (smallEtaleInverseImageRing B S hS p).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O) ≅
      (smallEtaleInverseImageRing B S hS g).obj (smallEtaleRingedTopos B S hS V).O :=
  smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h ≪≫
    (smallEtaleInverseImageRing B S hS g).mapIso
      (etaleInverseImageStructureSheafIso B S hS q hq)

/-- The square of sheaves of commutative rings on `U_étale` in which the identification of base
rings sits commutes: the composite structure map `p⁻¹f⁻¹𝒪_Y ⟶ p⁻¹𝒪_X ⟶ 𝒪_U` is the
identification followed by the structure map `g⁻¹𝒪_V ⟶ 𝒪_U` of `g`. -/
theorem etaleSquareBaseRingIso_fSharpInverseImage {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hq : IsEtale B S hS q.hom) :
    (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage ≫
        (smallEtaleRingedToposHom B S hS p).fSharpInverseImage =
      (etaleSquareBaseRingIso B S hS h hq).hom ≫
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage := by
  simp only [etaleSquareBaseRingIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact (smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage B S hS h).symm

/-- **Stacks 0D0W, the identification of the two naive cotangent complexes.**  For a commuting
square `p ≫ f = g ≫ q` of algebraic spaces over `S` with `p` and `q` étale,

`NL_{p⁻¹𝒪_X / p⁻¹f⁻¹𝒪_Y} ≅ NL_{U/V}`,

the target read in complexes of sheaves of `p⁻¹𝒪_X`-modules through the identification
`p⁻¹𝒪_X ≅ 𝒪_U` of Stacks 03LV.

Both horizontal morphisms of the square of sheaves of rings
```
p⁻¹𝒪_X ──────▸ 𝒪_U
   ▲             ▲
   │             │
p⁻¹f⁻¹𝒪_Y ────▸ g⁻¹𝒪_V
```
are isomorphisms — the top one by Stacks 03LV at the étale morphism `p`, the bottom one by
`AlgebraicGeometry.Space.etaleSquareBaseRingIso` — so the canonical chain map of Stacks 08TX
attached to it is an isomorphism. -/
@[stacks 0D0W "the canonical identification NL_{X/Y}|_{U_étale} = NL_{U/V} for a commutative
square of algebraic spaces with p and q étale, REDUCED TO THE SECOND HALF OF THE SOURCE'S PROOF.
What is proved is `NL_{p⁻¹O_X / p⁻¹f⁻¹O_Y} ≅ NL_{U/V}`: the two identifications of Tag 03LV,
`p⁻¹O_X = O_U` and `q⁻¹O_Y = O_V`, together with the composition law of Tag 03G8 for the square,
make the data defining the two complexes correspond, and the canonical chain map of Tag 08TX
between them is then an isomorphism. The FIRST half, `p⁻¹NL_{X/Y} = NL_{p⁻¹O_X / p⁻¹f⁻¹O_Y}`
(Modules on Sites, Lemma 08TZ), is not instantiated here, so the source of this isomorphism is
not yet known to be the restriction `NL_{X/Y}|_{U_étale}`. Tag 08TZ itself IS carried for sites,
as `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`, for an arbitrary morphism of
topoi; what is missing is only its universe shape, which ties the ambient section universe of
each topos to a universe containing its site's object universe, whereas the small étale site has
objects in `Type (u + 1)` and structure sheaves in `CommRingCat.{u}`.
Carried beyond the source's statement: the étale hypotheses are hypotheses `IsEtale p.hom` and
`IsEtale q.hom` in the big-fppf-site presentation of algebraic spaces; the identification is an
isomorphism of cochain complexes of sheaves of `p⁻¹O_X`-modules, the target being `NL_{U/V}` read
there by restriction of scalars along `p⁻¹O_X ≅ O_U`, and NOTHING is asserted in the derived
category `D(O_U)`"]
noncomputable def naiveCotangentEtaleLocalisationIso {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom) :
    inverseImageNaiveCotangentComplex B S hS p f ≅
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
          (underlyingRingHomOfSite.{u, u + 1, u}
            (etaleInverseImageStructureSheafIso B S hS p hp).hom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex B S hS g) :=
  Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS U).J _ _ _ _ _ _
    (etaleSquareBaseRingIso B S hS h hq) (etaleInverseImageStructureSheafIso B S hS p hp)
    (etaleSquareBaseRingIso_fSharpInverseImage B S hS h hq)

/-- The forward map of `AlgebraicGeometry.Space.naiveCotangentEtaleLocalisationIso` is the
canonical chain map of Stacks 08TX attached to the square of sheaves of rings, so the
identification is canonical. -/
@[stacks 0D0W "the identification is the canonical chain map of Tag 08TX, not an arbitrary
isomorphism; same scope as `naiveCotangentEtaleLocalisationIso`"]
theorem naiveCotangentEtaleLocalisationIso_hom {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V}
    {q : V ⟶ Y} (h : p ≫ f = g ≫ q) (hp : IsEtale B S hS p.hom)
    (hq : IsEtale B S hS q.hom) :
    (naiveCotangentEtaleLocalisationIso B S hS h hp hq).hom =
      Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u + 1, u, u}
        (smallEtaleRingedTopos B S hS U).J _ _ _ _ _ _
        (etaleSquareBaseRingIso B S hS h hq).hom
        (etaleInverseImageStructureSheafIso B S hS p hp).hom
        (etaleSquareBaseRingIso_fSharpInverseImage B S hS h hq) :=
  rfl

end AlgebraicGeometry.Space

end
