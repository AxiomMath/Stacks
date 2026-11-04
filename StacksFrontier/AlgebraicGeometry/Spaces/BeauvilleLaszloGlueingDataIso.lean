module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing

/-!
# Morphisms and isomorphisms of Beauville--Laszlo glueing triples

Fix a square of schemes `U ← U' → X'` in a big fppf site. A cartesian glueing triple
(`BeauvilleLaszlo.Space.GlueingData`) consists of algebraic spaces over `U`, over `U'` and over
`X'` together with two arrows from the middle one to the restrictions of the outer two, both
required to be isomorphisms. This module provides the basic calculus of morphisms between such
triples: extensionality, a constructor from the three components and the two commutative squares,
the corresponding constructor for isomorphisms, and the *glueing isomorphism* of a triple, which
packages the two structure arrows into a single comparison between the two restrictions of the
outer components.

## Main definitions

* `BeauvilleLaszlo.Space.glueingDataHomMk`: a morphism of glueing triples built from its three
  components and the two squares they are required to satisfy.
* `BeauvilleLaszlo.Space.glueingDataIsoMk`: an isomorphism of glueing triples built from
  isomorphisms of the three components.
* `BeauvilleLaszlo.Space.glueingDataCompare`: the glueing isomorphism of a cartesian triple,
  comparing the restriction of its `U`-component with the restriction of its `X'`-component.
* `BeauvilleLaszlo.Space.glueingDataIsoMk_of_compare`: an isomorphism of glueing triples built from
  isomorphisms of the `U`- and `X'`-components alone, compatible with the glueing isomorphisms.

## Main results

* `BeauvilleLaszlo.Space.hom_ext_of_overU_of_overX`: a morphism of cartesian glueing triples is
  determined by its components over `U` and over `X'`.
* `BeauvilleLaszlo.Space.glueingDataHomMk_overU'`,
  `BeauvilleLaszlo.Space.glueingDataHomMk_overU`,
  `BeauvilleLaszlo.Space.glueingDataHomMk_overX'`: the components of `glueingDataHomMk`.
* `BeauvilleLaszlo.Space.glueingDataIsoMk_hom_overU'`,
  `BeauvilleLaszlo.Space.glueingDataIsoMk_hom_overU`,
  `BeauvilleLaszlo.Space.glueingDataIsoMk_hom_overX'`: the components of `glueingDataIsoMk`.
* `BeauvilleLaszlo.Space.glueingDataIsoMk_of_compare_overU`,
  `BeauvilleLaszlo.Space.glueingDataIsoMk_of_compare_overX'`: the components of
  `glueingDataIsoMk_of_compare`.

## Implementation notes

Glueing triples form a full subcategory of an iterated comma category, so a morphism is an
`ObjectProperty.homMk` of two nested `CommaMorphism`s and extensionality is
`ObjectProperty.hom_ext` followed by `Comma.hom_ext` twice. The `U'`-component is then redundant:
the square for the `U`-component exhibits it as determined by the `U`-component after cancelling
the structure arrow of the target, which is an isomorphism because the triple is cartesian. This
is why `hom_ext_of_overU_of_overX` only mentions the outer two components, and why
`glueingDataIsoMk_of_compare` needs no middle isomorphism as input — it manufactures the forced
one from the glueing isomorphisms.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace BeauvilleLaszlo.Space

variable (B : BigFppfSite.{u}) (U' U X' : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U)
  (hX' : B.Contains X') (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')

/-- A morphism of cartesian glueing triples is determined by its components over `U` and over
`X'`: the component over `U'` is forced by the square for the `U`-component. -/
theorem hom_ext_of_overU_of_overX
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'} {a b : D ⟶ E}
    (h₁ : (overU B U' U X' hU' hU hX' gU gX').map a = (overU B U' U X' hU' hU hX' gU gX').map b)
    (h₂ : (overX' B U' U X' hU' hU hX' gU gX').map a =
      (overX' B U' U X' hU' hU hX' gU gX').map b) : a = b := by
  have : IsIso E.obj.left.hom := E.property.1
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · apply Comma.hom_ext
    · apply (cancel_mono E.obj.left.hom).mp
      have ha := a.hom.left.w
      have hb := b.hom.left.w
      dsimp at ha hb
      rw [ha, hb]
      exact congrArg (fun t ↦ D.obj.left.hom ≫ (baseChange B U' U hU' hU gU).map t) h₁
    · exact h₁
  · exact h₂

/-- A morphism of cartesian glueing triples built from its three components `mU'`, `mU`, `mX'`
and the two squares expressing compatibility with the structure arrows. -/
noncomputable def glueingDataHomMk
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (mU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (mU : (overU B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (mX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : mU' ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map mU)
    (hmX' : mU' ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map mX') :
    D ⟶ E :=
  ObjectProperty.homMk
    { left :=
        { left := mU'
          right := mU
          w := hmU }
      right := mX'
      w := hmX' }

/-- The `U'`-component of `glueingDataHomMk` is the given one. -/
theorem glueingDataHomMk_overU'
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (mU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (mU : (overU B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (mX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : mU' ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map mU)
    (hmX' : mU' ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map mX') :
    (overU' B U' U X' hU' hU hX' gU gX').map
      (glueingDataHomMk B U' U X' hU' hU hX' gU gX' mU' mU mX' hmU hmX') = mU' :=
  rfl

/-- The `U`-component of `glueingDataHomMk` is the given one. -/
theorem glueingDataHomMk_overU
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (mU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (mU : (overU B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (mX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : mU' ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map mU)
    (hmX' : mU' ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map mX') :
    (overU B U' U X' hU' hU hX' gU gX').map
      (glueingDataHomMk B U' U X' hU' hU hX' gU gX' mU' mU mX' hmU hmX') = mU :=
  rfl

/-- The `X'`-component of `glueingDataHomMk` is the given one. -/
theorem glueingDataHomMk_overX'
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (mU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (mU : (overU B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (mX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ⟶
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : mU' ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map mU)
    (hmX' : mU' ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map mX') :
    (overX' B U' U X' hU' hU hX' gU gX').map
      (glueingDataHomMk B U' U X' hU' hU hX' gU gX' mU' mU mX' hmU hmX') = mX' :=
  rfl

/-- An isomorphism of cartesian glueing triples built from isomorphisms of the three components
and the two squares relating their forward directions to the structure arrows. -/
noncomputable def glueingDataIsoMk
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : eU'.hom ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (hmX' : eU'.hom ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    D ≅ E where
  hom := glueingDataHomMk B U' U X' hU' hU hX' gU gX' eU'.hom eU.hom eX'.hom hmU hmX'
  inv := glueingDataHomMk B U' U X' hU' hU hX' gU gX' eU'.inv eU.inv eX'.inv
    (by
      rw [Iso.inv_comp_eq, ← Category.assoc, hmU, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id])
    (by
      rw [Iso.inv_comp_eq, ← Category.assoc, hmX', Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id])
  hom_inv_id := by
    apply hom_ext_of_overU_of_overX B U' U X' hU' hU hX' gU gX'
    · simp only [Functor.map_comp, glueingDataHomMk_overU, CategoryTheory.Functor.map_id,
        Iso.hom_inv_id]
    · simp only [Functor.map_comp, glueingDataHomMk_overX', CategoryTheory.Functor.map_id,
        Iso.hom_inv_id]
  inv_hom_id := by
    apply hom_ext_of_overU_of_overX B U' U X' hU' hU hX' gU gX'
    · simp only [Functor.map_comp, glueingDataHomMk_overU, CategoryTheory.Functor.map_id,
        Iso.inv_hom_id]
    · simp only [Functor.map_comp, glueingDataHomMk_overX', CategoryTheory.Functor.map_id,
        Iso.inv_hom_id]

/-- The `U'`-component of `glueingDataIsoMk` is the given isomorphism. -/
theorem glueingDataIsoMk_hom_overU'
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : eU'.hom ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (hmX' : eU'.hom ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overU' B U' U X' hU' hU hX' gU gX').map
      (glueingDataIsoMk B U' U X' hU' hU hX' gU gX' eU' eU eX' hmU hmX').hom = eU'.hom :=
  rfl

/-- The `U`-component of `glueingDataIsoMk` is the given isomorphism. -/
theorem glueingDataIsoMk_hom_overU
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : eU'.hom ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (hmX' : eU'.hom ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overU B U' U X' hU' hU hX' gU gX').map
      (glueingDataIsoMk B U' U X' hU' hU hX' gU gX' eU' eU eX' hmU hmX').hom = eU.hom :=
  rfl

/-- The `X'`-component of `glueingDataIsoMk` is the given isomorphism. -/
theorem glueingDataIsoMk_hom_overX'
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU' : (overU' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj E)
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (hmU : eU'.hom ≫ E.1.left.hom = D.1.left.hom ≫ (baseChange B U' U hU' hU gU).map eU.hom)
    (hmX' : eU'.hom ≫ E.1.hom = D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom) :
    (overX' B U' U X' hU' hU hX' gU gX').map
      (glueingDataIsoMk B U' U X' hU' hU hX' gU gX' eU' eU eX' hmU hmX').hom = eX'.hom :=
  rfl

/-- The glueing isomorphism of a cartesian triple: the composite of the inverse of the structure
arrow to the restriction of the `U`-component with the structure arrow to the restriction of the
`X'`-component. Both are isomorphisms because the triple is cartesian. -/
noncomputable def glueingDataCompare (D : GlueingData B U' U X' hU' hU hX' gU gX') :
    (baseChange B U' U hU' hU gU).obj ((overU B U' U X' hU' hU hX' gU gX').obj D) ≅
      (baseChange B U' X' hU' hX' gX').obj ((overX' B U' U X' hU' hU hX' gU gX').obj D) :=
  haveI : IsIso D.1.left.hom := D.2.1
  haveI : IsIso D.1.hom := D.2.2
  (asIso D.1.left.hom).symm ≪≫ asIso D.1.hom

/-- Two cartesian glueing triples are isomorphic as soon as their `U`- and `X'`-components are,
compatibly with the glueing isomorphisms; the middle component isomorphism is then forced. -/
noncomputable def glueingDataIsoMk_of_compare
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (h : (glueingDataCompare B U' U X' hU' hU hX' gU gX' D).hom ≫
        (baseChange B U' X' hU' hX' gX').map eX'.hom =
      (baseChange B U' U hU' hU gU).map eU.hom ≫
        (glueingDataCompare B U' U X' hU' hU hX' gU gX' E).hom) :
    D ≅ E :=
  haveI : IsIso D.1.left.hom := D.2.1
  haveI : IsIso E.1.left.hom := E.2.1
  glueingDataIsoMk B U' U X' hU' hU hX' gU gX'
    (asIso D.1.left.hom ≪≫ (baseChange B U' U hU' hU gU).mapIso eU ≪≫
      (asIso E.1.left.hom).symm) eU eX'
    (by simp)
    (by
      have h' : inv D.1.left.hom ≫ D.1.hom ≫ (baseChange B U' X' hU' hX' gX').map eX'.hom =
          (baseChange B U' U hU' hU gU).map eU.hom ≫ inv E.1.left.hom ≫ E.1.hom := by
        simpa only [glueingDataCompare, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
          Category.assoc] using h
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv,
        Category.assoc, ← h']
      simp)

/-- The `U`-component of `glueingDataIsoMk_of_compare` is the given isomorphism. -/
theorem glueingDataIsoMk_of_compare_overU
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (h : (glueingDataCompare B U' U X' hU' hU hX' gU gX' D).hom ≫
        (baseChange B U' X' hU' hX' gX').map eX'.hom =
      (baseChange B U' U hU' hU gU).map eU.hom ≫
        (glueingDataCompare B U' U X' hU' hU hX' gU gX' E).hom) :
    (overU B U' U X' hU' hU hX' gU gX').map
      (glueingDataIsoMk_of_compare B U' U X' hU' hU hX' gU gX' eU eX' h).hom = eU.hom :=
  rfl

/-- The `X'`-component of `glueingDataIsoMk_of_compare` is the given isomorphism. -/
theorem glueingDataIsoMk_of_compare_overX'
    {D E : GlueingData B U' U X' hU' hU hX' gU gX'}
    (eU : (overU B U' U X' hU' hU hX' gU gX').obj D ≅
      (overU B U' U X' hU' hU hX' gU gX').obj E)
    (eX' : (overX' B U' U X' hU' hU hX' gU gX').obj D ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj E)
    (h : (glueingDataCompare B U' U X' hU' hU hX' gU gX' D).hom ≫
        (baseChange B U' X' hU' hX' gX').map eX'.hom =
      (baseChange B U' U hU' hU gU).map eU.hom ≫
        (glueingDataCompare B U' U X' hU' hU hX' gU gX' E).hom) :
    (overX' B U' U X' hU' hU hX' gU gX').map
      (glueingDataIsoMk_of_compare B U' U X' hU' hU hX' gU gX' eU eX' h).hom = eX'.hom :=
  rfl

end BeauvilleLaszlo.Space

end
