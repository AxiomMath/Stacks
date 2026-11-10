module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack

/-!
# The natural map from the Picard stack to the stack of coherent sheaves (Stacks 0D03)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
flat, of finite presentation and proper.  Stacks 0D03 asserts that the natural map
`Pic_{X/B} ⟶ Coh_{X/B}` is representable by open immersions.  Its first paragraph constructs
that map: a triple `(T, g, L)` of the Picard stack of Section 0372 goes to the same triple
viewed in Situation 08KB, and a morphism `(h, α)` of the Picard stack goes to the morphism
`(h, α)` of `Coh_{X/B}`.

The map on objects is `AlgebraicGeometry.Space.picardObjectToCoherent`; this file extends it to
morphisms and shows that it identifies the hom-sets.

## Main definitions

* `AlgebraicGeometry.Space.picardToCoherentHom`: **Stacks 0D03, the natural map on morphisms.**
* `AlgebraicGeometry.Space.picardToCoherentHomEquiv`: **Stacks 0D03, the natural map on hom-sets
  is a bijection**, so the natural map is fully faithful and `Pic_{X/B}` is the full subcategory
  of `Coh_{X/B}` on the objects whose module is invertible.

## Implementation notes

**The map is the identity on data.**  A morphism of `Pic_{X/B}` is a pair `(h, α)` of a morphism
`h : T ⟶ T'` of test schemes over the base and an isomorphism `α : (X_h)^*L' ⟶ L`
(`AlgebraicGeometry.Space.PicardHom`), and a morphism of `Coh_{X/B}` is a pair of exactly the
same two data (`AlgebraicGeometry.Space.CoherentHom`); the base change `X_T` of the Picard
situation underlying a coherent situation is the base change of that coherent situation
(`AlgebraicGeometry.Space.CoherentSituation.toPicardSituation`), and the induced morphism `X_h`
of base changes is the same in both.  So the map on morphisms carries the pair across unchanged
and the two hom-sets are in bijection.

**Why the fibres are subsingletons.**  An object of `Pic_{X/B}` over an object `(T, g, F)` of
`Coh_{X/B}` is the same triple together with a proof that `F` is invertible, and the hom-sets
agree; so `Pic_{X/B}` is the full subcategory of `Coh_{X/B}` cut out by invertibility of the
module.  That is the structural reason the tag asserts an *open immersion* rather than a general
morphism, and it is the shape the open-locus mechanism of
`StacksFrontier/AlgebraicGeometry/Stacks/ObjectPropertyOpenLocus.lean` consumes.

**Where the rest of the tag is.**  The object and hom maps are assembled into the 1-morphism of
categories fibred in groupoids `AlgebraicGeometry.Space.picardToCoherent`, and representability
by open immersions is
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent`,
both in `StacksFrontier/AlgebraicGeometry/Quot/PicardStackOpenImmersion.lean`.

## References

* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D03, the natural map on morphisms.**  A morphism `(h, α)` of `Pic_{X/B}` — a
morphism `h` of test schemes over the base together with an isomorphism `α : (X_h)^*L' ⟶ L` —
goes to the morphism `(h, α)` of `Coh_{X/B}`.

The two hom-types are the same pair of data, the base change and the induced morphism of base
changes of the Picard situation underlying a coherent situation being those of the coherent
situation, so nothing is transported. -/
def picardToCoherentHom (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom)
    {A C : PicardObject D.toPicardSituation} (m : PicardHom A C) :
    CoherentHom (picardObjectToCoherent D hflat hproper A)
      (picardObjectToCoherent D hflat hproper C) where
  base := m.base
  fibre := m.fibre
  isIso_fibre := m.isIso_fibre

/-- The natural map on morphisms keeps the morphism of test schemes. -/
@[simp]
theorem picardToCoherentHom_base (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) {A C : PicardObject D.toPicardSituation}
    (m : PicardHom A C) :
    (picardToCoherentHom D hflat hproper m).base = m.base :=
  rfl

/-- The natural map on morphisms keeps the comparison of modules. -/
@[simp]
theorem picardToCoherentHom_fibre (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) {A C : PicardObject D.toPicardSituation}
    (m : PicardHom A C) :
    (picardToCoherentHom D hflat hproper m).fibre = m.fibre :=
  rfl

/-- **Stacks 0D03, the natural map on hom-sets is a bijection.**  The hom-sets of `Pic_{X/B}`
and of `Coh_{X/B}` between two objects and their images are the same pair of data — a morphism of
test schemes over the base and an isomorphism of the inverse image of the module of the target
with the module of the source — so the natural map identifies them.

So the natural map is fully faithful, and `Pic_{X/B}` is the full subcategory of `Coh_{X/B}` on
the objects whose module is invertible: the fibre of the map over an object `(T, g, F)` of
`Coh_{X/B}` is the set of proofs that `F` is invertible, which is a subsingleton.  That is the
structural reason the tag asserts an *open immersion* rather than a general morphism. -/
@[stacks 0D03 "the natural map Picardstack_{X/B} -> Cohstack_{X/B} on hom-sets, together with \
  picardObjectToCoherent on objects: the first part of the source's proof, in which the triple (T, \
  g, L) of Section 0372 is sent to the same triple in Situation 08KB and the morphism (h, a) to \
  the morphism (h, a). The map on hom-sets is a BIJECTION, so the natural map is fully faithful \
  and Picardstack_{X/B} is the full subcategory of Cohstack_{X/B} on the objects with invertible \
  module. The binders are D and the tag's own flatness and properness of f, which the object map \
  needs. The whole statement of the tag is \
  isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent of \
  Quot/PicardStackOpenImmersion.lean."]
def picardToCoherentHomEquiv (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (A C : PicardObject D.toPicardSituation) :
    PicardHom A C ≃ CoherentHom (picardObjectToCoherent D hflat hproper A)
      (picardObjectToCoherent D hflat hproper C) where
  toFun m := picardToCoherentHom D hflat hproper m
  invFun m := ⟨m.base, m.fibre, m.isIso_fibre⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection of hom-sets of `AlgebraicGeometry.Space.picardToCoherentHomEquiv` is the
natural map on morphisms. -/
@[simp]
theorem picardToCoherentHomEquiv_apply (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (A C : PicardObject D.toPicardSituation) (m : PicardHom A C) :
    picardToCoherentHomEquiv D hflat hproper A C m = picardToCoherentHom D hflat hproper m :=
  rfl

end AlgebraicGeometry.Space

end
