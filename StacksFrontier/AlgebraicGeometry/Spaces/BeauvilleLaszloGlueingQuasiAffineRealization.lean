module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineFlatPresentation

/-!
# The affine equivalence read at bare objects (Stacks 0F9U, steps 3 and 4)

The proof of Stacks 0F9U uses the affine equivalence of Stacks 0F9Q twice, and both times on
*bare* objects rather than on objects of the two full subcategories the equivalence is stated
between.

Step 3 uses essential surjectivity: the affine triple assembled out of the affine-space bundles
of Stacks 0F82 is the image of an affine algebraic space `T` over `X`, glueable for the pair.
What the construction then needs of `T` is an `AlgebraicGeometry.AlgebraicSpaces` object, an
isomorphism of `BeauvilleLaszlo.Space.GlueingData` — not of objects of the subcategory of
triples with affine components — and the two properties separately, since the later steps apply
`AlgebraicGeometry.Space.IsGlueableAlgebraicSpace` to `T` on its own.

Step 4 uses fullness: the two projections `p₀, p₁ : W → T` are obtained from the two projections
of the triple, and again the input is a morphism of `GlueingData` and the output a morphism of
`AlgebraicSpaces`.

Both readings are bookkeeping around `CategoryTheory.Functor.objObjPreimageIso` and
`CategoryTheory.Functor.map_preimage`:
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction` is a
`CategoryTheory.ObjectProperty.lift` of the gluing functor of Stacks 0F9N, so its action on
objects and on morphisms is that functor's on the nose, and
`CategoryTheory.ObjectProperty.FullSubcategory` has the ambient homs.

## Main results

* `BeauvilleLaszlo.Space.exists_affineGlueable_iso_of_affineComponents`: **Stacks 0F9U, step 3.**
  A cartesian gluing triple with affine components is the image under the gluing functor of
  Stacks 0F9N of an affine algebraic space over `X` which is glueable for the pair.
* `BeauvilleLaszlo.Space.exists_hom_of_hom_glueingFunctor`: **Stacks 0F9U, step 4.** A morphism
  between the images of two affine glueable algebraic spaces over `X` comes from a morphism of
  algebraic spaces over `X`.
* `BeauvilleLaszlo.Space.existsUnique_hom_of_hom_glueingFunctor`: the same with uniqueness, from
  faithfulness, which is what pins `p₀` and `p₁` down.

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))
  (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)

/-- **Stacks 0F9U, step 3.** Let `(g : R → R', f)` be a glueing pair and let `Wa` be a cartesian
gluing triple over the canonical square whose three components are affine. Then there is an
algebraic space `T` over `X = Spec R` which is affine and glueable for `(g, f)`, together with an
isomorphism of gluing triples from the image of `T` under the gluing functor of Stacks 0F9N
to `Wa`.

This is essential surjectivity of `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction`, with
the conclusion read on bare objects: the realizing object is the underlying algebraic space of the
preimage, its two properties are the two components of that preimage's subcategory property, and
the isomorphism of triples is the image of the comparison isomorphism under the inclusion of the
subcategory of triples with affine components. -/
theorem exists_affineGlueable_iso_of_affineComponents
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (Wa : GlueingData B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX'))
    (hWa : affineComponents B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
      (canGU g f B hU' hU) (canGX' g f B hU' hX') Wa) :
    ∃ T : AlgebraicSpaces B (Spec (.of R)) hX,
      AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1 ∧
        AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T ∧
          Nonempty
            ((canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj T ≅ Wa) := by
  have : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).EssSurj :=
    canonicalAffineGlueableRestriction_essSurj g f B hU' hU hX' hX hcomm hglue
  refine ⟨((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).objPreimage ⟨Wa, hWa⟩).1,
    ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).objPreimage
      ⟨Wa, hWa⟩).property.1,
    ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).objPreimage
      ⟨Wa, hWa⟩).property.2,
    ⟨(ObjectProperty.ι _).mapIso
      ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).objObjPreimageIso ⟨Wa, hWa⟩)⟩⟩

/-- **Stacks 0F9U, step 4.** A morphism between the gluing triples of two affine glueable
algebraic spaces over `X = Spec R` is the image of a morphism of algebraic spaces over `X`.

This is fullness of `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction` read on bare
objects. -/
theorem exists_hom_of_hom_glueingFunctor
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (T Z : AlgebraicSpaces B (Spec (.of R)) hX)
    (hT : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (hTg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T)
    (hZ : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX Z.1)
    (hZg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z)
    (φ : (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj T ⟶
      (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj Z) :
    ∃ p : T ⟶ Z,
      (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.map p = φ := by
  have : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Full :=
    canonicalAffineGlueableRestriction_full g f B hU' hU hX' hX hcomm hglue
  refine ⟨(ObjectProperty.ι _).map
    ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).preimage
      (ObjectProperty.homMk (X := (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).obj
          ⟨T, hT, hTg⟩)
        (Y := (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).obj ⟨Z, hZ, hZg⟩) φ)),
        ?_⟩
  show (ObjectProperty.ι _).map
      ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
        ((canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).preimage _)) =
    (ObjectProperty.ι _).map (ObjectProperty.homMk
      (X := (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).obj ⟨T, hT, hTg⟩)
      (Y := (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).obj ⟨Z, hZ, hZg⟩) φ)
  rw [Functor.map_preimage]

/-- **Stacks 0F9U, step 4, with uniqueness.** The morphism of algebraic spaces produced by
fullness is unique, by faithfulness. This is the form the source uses when it says that the two
projections are determined by their base changes to `U` and `X'`: those base changes are the
components of the morphism of triples, and the triple determines the morphism. -/
theorem existsUnique_hom_of_hom_glueingFunctor
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (T Z : AlgebraicSpaces B (Spec (.of R)) hX)
    (hT : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX T.1)
    (hTg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX T)
    (hZ : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX Z.1)
    (hZg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z)
    (φ : (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj T ⟶
      (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.obj Z) :
    ∃! p : T ⟶ Z,
      (canonicalGlueingFunctorSpec g f B hU' hU hX' hX hcomm).functor.map p = φ := by
  have : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Faithful :=
    canonicalAffineGlueableRestriction_faithful g f B hU' hU hX' hX hcomm hglue
  obtain ⟨p, hp⟩ := exists_hom_of_hom_glueingFunctor g f B hU' hU hX' hX hcomm hglue
    T Z hT hTg hZ hZg φ
  refine ⟨p, hp, fun q hq => ?_⟩
  have hq' : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
        (ObjectProperty.homMk (X := (⟨T, hT, hTg⟩ :
          (affineGlueableSpaces g f B hX).FullSubcategory)) (Y := ⟨Z, hZ, hZg⟩) q) =
      (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map
        (ObjectProperty.homMk (X := (⟨T, hT, hTg⟩ :
          (affineGlueableSpaces g f B hX).FullSubcategory)) (Y := ⟨Z, hZ, hZg⟩) p) :=
    ObjectProperty.hom_ext _ (hq.trans hp.symm)
  show (ObjectProperty.ι _).map (ObjectProperty.homMk
      (X := (⟨T, hT, hTg⟩ : (affineGlueableSpaces g f B hX).FullSubcategory))
      (Y := ⟨Z, hZ, hZg⟩) q) =
    (ObjectProperty.ι _).map (ObjectProperty.homMk
      (X := (⟨T, hT, hTg⟩ : (affineGlueableSpaces g f B hX).FullSubcategory))
      (Y := ⟨Z, hZ, hZg⟩) p)
  rw [(canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).map_injective hq']

end BeauvilleLaszlo.Space

end
