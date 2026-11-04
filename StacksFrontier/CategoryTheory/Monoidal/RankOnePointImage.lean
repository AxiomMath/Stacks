module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndAlgebraFreePoints
public import StacksFrontier.CategoryTheory.Monoidal.MonObjImagePoint

/-!
# The image of a rank-one point of an internal endomorphism monoid

This is the local model of the Saltman construction of [Stacks, Tag 0A2L], carried out in an
arbitrary monoidal closed category.

Let `𝒜` be a monoidal closed category and `F` an object. Suppose given a point `a : 𝟙_ 𝒜 ⟶ F`,
a covector `ahat : F ⟶ 𝟙_ 𝒜`, and a second such pair `c : 𝟙_ 𝒜 ⟶ F`, `chat : F ⟶ 𝟙_ 𝒜`, whose
cross pairings are the identity of the unit:

`a ≫ chat = 𝟙 (𝟙_ 𝒜)` and `c ≫ ahat = 𝟙 (𝟙_ 𝒜)`.

Let `q := ahat ≫ a : F ⟶ F` — on elements the rank-one endomorphism `x ↦ ahat x · a` — and let
`p := MonoidalClosed.curry' q : 𝟙_ 𝒜 ⟶ (internalEnd F).X` be the corresponding point of the
internal endomorphism monoid. The content of this file is that left multiplication by `p`
factors as

`Mon.leftMul (internalEnd F) p = ihomCoord a F ≫ ihomIncl ahat F`,

that the first factor is a split epimorphism and the second a split monomorphism (this is where
the two pairings are used), hence that the image of left multiplication by `p` — the subobject
`p * End F` of `End F` — is `F` itself, and finally that the representation of `internalEnd F`
on that image is the conjugation isomorphism along that identification. In particular the
representation is an isomorphism of monoid objects.

In the intended application `F` is a free sheaf of modules of rank `d ^ d`, `a` is
`Matrix.altVec`, `c` is `Matrix.altCoordVec`, `q` is `Matrix.altProj`, and the two pairings are
`Matrix.sum_altVec_mul_altCoordVec` and `Matrix.sum_altCoordVec_mul_altVec`.

## Main definitions

* `CategoryTheory.MonoidalClosed.imageLeftMulCurry'Iso`: **the image of left multiplication by
  the rank-one point is `F`**, via the strong-epi/mono factorisation
  `ihomCoord a F ≫ ihomIncl ahat F`.

## Main results

* `CategoryTheory.MonoidalClosed.leftMul_curry'_comp`: **left multiplication by the rank-one
  point `curry' (ahat ≫ a)` is `ihomCoord a F ≫ ihomIncl ahat F`.** Needs only
  `MonoidalClosed 𝒜`.
* `CategoryTheory.MonoidalClosed.ihomIncl_comp_ihomCoord_of_pairing` and
  `CategoryTheory.MonoidalClosed.ihomIncl_comp_ihomCoord_of_pairing'`: the two pairings say
  exactly that the two factors compose to the identity of `F` in the other order, so
  `CategoryTheory.MonoidalClosed.isSplitEpi_ihomCoord` and
  `CategoryTheory.MonoidalClosed.isSplitMono_ihomIncl`.
* `CategoryTheory.MonoidalClosed.whiskerRight_ihomIncl_comp_comp`: **the subobject
  `p * End F` of `End F` is `F` with its tautological right `End F`-action**: internal
  composition, restricted along `ihomIncl ahat F`, is the evaluation followed by
  `ihomIncl ahat F`. This is the abstract form of the matrix identity
  `vecMulVec a v * M = vecMulVec a (v ᵥ* M)`.
* `CategoryTheory.MonoidalClosed.imageRep_eq_internalEndCongr`: **the representation of
  `internalEnd F` on the image of left multiplication by the rank-one point is the conjugation
  isomorphism** along `imageLeftMulCurry'Iso`, and
  `CategoryTheory.MonoidalClosed.isIso_imageRep_curry'`: **it is an isomorphism.**

## Implementation notes

`CategoryTheory.MonoidalClosed.comp X Y Z` is *diagrammatic* — its first factor is applied
first — so `CategoryTheory.MonoidalClosed.internalEnd F` is the opposite of the endomorphism
monoid under composition of functions and `p * x` is "`q` then `x`", i.e. `q ≫ x`. This is why
the construction lives on `CategoryTheory.Mon.leftMul` and
`CategoryTheory.Mon.imageActionRight`; see the implementation notes of
`StacksFrontier.CategoryTheory.Monoidal.MonObjImagePoint`.

Every proof is one application of `CategoryTheory.MonoidalClosed.uncurry_injective` followed by
coherence: both `CategoryTheory.MonoidalClosed.ihomCoord` and
`CategoryTheory.MonoidalClosed.ihomIncl` have known uncurryings, and
`CategoryTheory.MonoidalClosed.whiskerLeft_tensorHom_compTranspose` uncurries internal
composition. The identification of the image needs no calculation at all: left multiplication by
the point has been exhibited as a split epi followed by a split mono, and a split epi is a strong
epi, so `CategoryTheory.Limits.image.isoStrongEpiMono` applies.

The hypotheses are kept as tight as each statement allows. Statements that do not mention an image
need only `MonoidalClosed 𝒜`; the image statements add `Abelian 𝒜` (through which the images
exist), and those mentioning `CategoryTheory.Mon.imageActionRight` add `BraidedCategory 𝒜`,
which that construction needs in order to know that tensoring on the right preserves
epimorphisms.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

namespace CategoryTheory.MonoidalClosed

variable {𝒜 : Type*} [Category 𝒜] [MonoidalCategory 𝒜] [MonoidalClosed 𝒜] {F : 𝒜}
  (a : 𝟙_ 𝒜 ⟶ F) (ahat : F ⟶ 𝟙_ 𝒜) (c : 𝟙_ 𝒜 ⟶ F) (chat : F ⟶ 𝟙_ 𝒜)

/-! ### Left multiplication by a rank-one point -/

/-- **Left multiplication by the rank-one point `curry' (ahat ≫ a)` of the internal
endomorphism monoid of `F` is the coordinate at `a` followed by the inclusion at `ahat`.** On
elements the left-hand side is `x ↦ (ahat ≫ a) ≫ x` and the right-hand side is
`x ↦ ahat · x a`, which agree because `(ahat ≫ a) ≫ x` sends `y` to `x (ahat y · a)`.

Needs only `MonoidalClosed 𝒜`. -/
theorem leftMul_curry'_comp :
    Mon.leftMul (internalEnd F) (curry' (ahat ≫ a)) = ihomCoord a F ≫ ihomIncl ahat F := by
  have hleft : Mon.leftMul (internalEnd F) (curry' (ahat ≫ a))
      = (λ_ ((ihom F).obj F)).inv ≫ (curry' (ahat ≫ a) ▷ (ihom F).obj F)
        ≫ MonoidalClosed.comp F F F := rfl
  rw [hleft, curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
  apply uncurry_injective
  rw [uncurry_eq, id_tensor_pre_app_comp_ev, uncurry_ihomCoord_comp_ihomIncl]

/-! ### The two pairings split the two factors -/

/-- The pairing `a ≫ chat = 𝟙 (𝟙_ 𝒜)` says that the inclusion at `chat` is a section of the
coordinate at `a`. Needs only `MonoidalClosed 𝒜`. -/
theorem ihomIncl_comp_ihomCoord_of_pairing (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) :
    ihomIncl chat F ≫ ihomCoord a F = 𝟙 F := by
  rw [ihomIncl_comp_ihomCoord, h, MonoidalCategory.id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id]

/-- The pairing `c ≫ ahat = 𝟙 (𝟙_ 𝒜)` says that the coordinate at `c` is a retraction of the
inclusion at `ahat`. Needs only `MonoidalClosed 𝒜`. -/
theorem ihomIncl_comp_ihomCoord_of_pairing' (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    ihomIncl ahat F ≫ ihomCoord c F = 𝟙 F :=
  ihomIncl_comp_ihomCoord_of_pairing c ahat h'

/-- **The coordinate at `a` is a split epimorphism**, split by the inclusion at `chat`. Needs
only `MonoidalClosed 𝒜`. -/
theorem isSplitEpi_ihomCoord (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) : IsSplitEpi (ihomCoord a F) :=
  IsSplitEpi.mk' ⟨ihomIncl chat F, ihomIncl_comp_ihomCoord_of_pairing a chat h⟩

/-- **The inclusion at `ahat` is a split monomorphism**, retracted by the coordinate at `c`.
Needs only `MonoidalClosed 𝒜`. -/
theorem isSplitMono_ihomIncl (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) : IsSplitMono (ihomIncl ahat F) :=
  IsSplitMono.mk' ⟨ihomCoord c F, ihomIncl_comp_ihomCoord_of_pairing' ahat c h'⟩

/-! ### The image of left multiplication by a rank-one point -/

section Image

variable [Abelian 𝒜]

/-- **The image of left multiplication by the rank-one point `curry' (ahat ≫ a)` is `F`
itself.** Left multiplication by the point has been exhibited in `leftMul_curry'_comp` as the
split epimorphism `ihomCoord a F` followed by the split monomorphism `ihomIncl ahat F`; a split
epimorphism is a strong epimorphism, so this is a strong-epi/mono factorisation and
`CategoryTheory.Limits.image.isoStrongEpiMono` identifies its middle object with the image.

Needs `MonoidalClosed 𝒜` and `Abelian 𝒜`, the latter only so that images exist. -/
noncomputable def imageLeftMulCurry'Iso (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    F ≅ Limits.image (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a))) :=
  haveI : IsSplitEpi (ihomCoord a F) := isSplitEpi_ihomCoord a chat h
  haveI : IsSplitMono (ihomIncl ahat F) := isSplitMono_ihomIncl ahat c h'
  Limits.image.isoStrongEpiMono (ihomCoord a F) (ihomIncl ahat F)
    (leftMul_curry'_comp a ahat).symm

/-- The identification of `F` with the image of left multiplication by the rank-one point is
compatible with the inclusion of the image: it carries the inclusion of the image to
`ihomIncl ahat F`. -/
@[reassoc (attr := simp)]
theorem imageLeftMulCurry'Iso_hom_comp_ι (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    (imageLeftMulCurry'Iso a ahat c chat h h').hom
        ≫ Limits.image.ι (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a)))
      = ihomIncl ahat F :=
  have : IsSplitEpi (ihomCoord a F) := isSplitEpi_ihomCoord a chat h
  have : IsSplitMono (ihomIncl ahat F) := isSplitMono_ihomIncl ahat c h'
  Limits.image.isoStrongEpiMono_hom_comp_ι (ihomCoord a F) (ihomIncl ahat F)
    (leftMul_curry'_comp a ahat).symm

/-- The inverse identification composed with `ihomIncl ahat F` is the inclusion of the image. -/
@[reassoc]
theorem imageLeftMulCurry'Iso_inv_comp_ihomIncl (h : a ≫ chat = 𝟙 (𝟙_ 𝒜))
    (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    (imageLeftMulCurry'Iso a ahat c chat h h').inv ≫ ihomIncl ahat F
      = Limits.image.ι (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a))) := by
  rw [← imageLeftMulCurry'Iso_hom_comp_ι a ahat c chat h h', Iso.inv_hom_id_assoc]

end Image

/-! ### The right action on the image is the evaluation -/

/-- **The subobject `p * End F` of `End F` is `F` carrying its tautological right
`End F`-action.** Internal composition, restricted along `ihomIncl ahat F` in its first
variable, is the evaluation followed by `ihomIncl ahat F`: on elements, the morphism
`y ↦ ahat · y` composed with `x` is `y ↦ ahat · x y`. This is the abstract form of the matrix
identity `vecMulVec a v * M = vecMulVec a (v ᵥ* M)` (`Matrix.vecMulVec_altVec_mul`).

Needs only `MonoidalClosed 𝒜`. -/
theorem whiskerRight_ihomIncl_comp_comp :
    (ihomIncl ahat F ▷ (ihom F).obj F) ≫ MonoidalClosed.comp F F F
      = (ihom.ev F).app F ≫ ihomIncl ahat F := by
  have key : ∀ g : F ⊗ (ihom F).obj F ⟶ F,
      (ahat ▷ (F ⊗ (ihom F).obj F)) ≫ (λ_ (F ⊗ (ihom F).obj F)).hom ≫ g
        = (F ◁ g) ≫ (ahat ▷ F) ≫ (λ_ F).hom := fun g => by
    rw [whisker_exchange_assoc, leftUnitor_naturality]
  apply uncurry_injective
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    ← tensorHom_id (ihomIncl ahat F) ((ihom F).obj F), whiskerLeft_tensorHom_compTranspose,
    MonoidalClosed.uncurry_id_eq_ev, uncurry_natural_left, ihomIncl, uncurry_curry,
    comp_whiskerRight, Category.assoc, ← associator_inv_naturality_left_assoc,
    ← leftUnitor_tensor_hom_assoc]
  exact key ((ihom.ev F).app F)

/-! ### The representation on the image is the conjugation isomorphism -/

section Rep

variable [Abelian 𝒜] [BraidedCategory 𝒜]

/-- **The right action of `internalEnd F` on the image of left multiplication by the rank-one
point is the evaluation**, transported along the identification of that image with `F`.

Needs `MonoidalClosed 𝒜`, `Abelian 𝒜` and `BraidedCategory 𝒜`. -/
theorem imageActionRight_curry'_eq (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    Mon.imageActionRight (internalEnd F) (curry' (ahat ≫ a))
      = ((imageLeftMulCurry'Iso a ahat c chat h h').inv ▷ (ihom F).obj F)
        ≫ (ihom.ev F).app F ≫ (imageLeftMulCurry'Iso a ahat c chat h h').hom := by
  have hι : Mon.imageActionRight (internalEnd F) (curry' (ahat ≫ a))
        ≫ Limits.image.ι (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a)))
      = (Limits.image.ι (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a))) ▷ (ihom F).obj F)
        ≫ MonoidalClosed.comp F F F :=
    Mon.imageActionRight_comp_ι _ _
  rw [← cancel_mono (Limits.image.ι (Mon.leftMul (internalEnd F) (curry' (ahat ≫ a)))), hι,
    Category.assoc, Category.assoc,
    imageLeftMulCurry'Iso_hom_comp_ι a ahat c chat h h', ← whiskerRight_ihomIncl_comp_comp ahat,
    ← Category.assoc, ← comp_whiskerRight,
    imageLeftMulCurry'Iso_inv_comp_ihomIncl a ahat c chat h h']

/-- **THE MAIN RESULT: the representation of `internalEnd F` on the image of left multiplication
by the rank-one point `curry' (ahat ≫ a)` is the conjugation isomorphism** induced by the
identification `imageLeftMulCurry'Iso` of that image with `F`.

Both sides are morphisms of monoid objects out of `internalEnd F`, so it is enough to compare
their underlying morphisms of `𝒜`; both are curried right actions, and uncurrying turns the
comparison into `imageActionRight_curry'_eq`.

Needs `MonoidalClosed 𝒜`, `Abelian 𝒜` and `BraidedCategory 𝒜`. -/
theorem imageRep_eq_internalEndCongr (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    Mon.imageRep (internalEnd F) (curry' (ahat ≫ a))
      = (internalEndCongr (imageLeftMulCurry'Iso a ahat c chat h h')).hom := by
  apply Mon.Hom.ext'
  show curry (Mon.imageActionRight (internalEnd F) (curry' (ahat ≫ a)))
    = internalEndCongrHom (imageLeftMulCurry'Iso a ahat c chat h h')
  apply uncurry_injective
  rw [uncurry_curry, uncurry_internalEndCongrHom, imageActionRight_curry'_eq a ahat c chat h h']

/-- **The representation of `internalEnd F` on the image of left multiplication by the rank-one
point is an isomorphism of monoid objects**, being the conjugation isomorphism.

Needs `MonoidalClosed 𝒜`, `Abelian 𝒜` and `BraidedCategory 𝒜`. -/
theorem isIso_imageRep_curry' (h : a ≫ chat = 𝟙 (𝟙_ 𝒜)) (h' : c ≫ ahat = 𝟙 (𝟙_ 𝒜)) :
    IsIso (Mon.imageRep (internalEnd F) (curry' (ahat ≫ a))) := by
  rw [imageRep_eq_internalEndCongr a ahat c chat h h']
  infer_instance

end Rep

end CategoryTheory.MonoidalClosed
