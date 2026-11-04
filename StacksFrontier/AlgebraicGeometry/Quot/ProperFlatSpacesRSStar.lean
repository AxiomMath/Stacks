module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesFiniteProperMono
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFiniteOrderGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberSquareComparisonOfRestriction
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# The stack `Spaces'_{fp, flat, proper}` satisfies (RS*)

Let
```
T  ⟶ T'
↓     ↓
S  ⟶ S'
```
be a pushout of schemes of the big fppf site in which `T ⟶ T'` is a thickening and `T ⟶ S` is
affine.  [Stacks Project, Tag 0D1J] asserts that restriction from the fibre of the stack
`𝒳 = Spaces'_{fp, flat, proper}` of Stacks 0D1D over `S'` to the `2`-fibre product of its fibres
over `S` and `T'` above its fibre over `T` is an equivalence.  This file proves it when the
thickening `T ⟶ T'` has finite order, and deduces that `𝒳` satisfies condition (RS*) of
[Stacks Project, Tag 07Y8], which asks for it only along first order thickenings of affine
schemes.

The proof is the source's.  The pushout `S' = S ⨿_T T'` of schemes is also a pushout of algebraic
spaces (Stacks 07SY).  An object over `S'` is the pushout of its base changes to `S`, `T` and `T'`
(the counit assertion of Stacks 07W3), so morphisms glue; and a compatible pair `(V, U')` of
objects over `S` and `T'` is glued by the pushout `V ⨿_U U'` of algebraic spaces, which recovers
`V` and `U'` by base change (Stacks 07W0) and is flat and locally of finite presentation over
`S'` (clause (3) of Stacks 07W3).  It is proper because its base change `V` to the thickening
`S ⊆ S'` is (Stacks 0BPJ, part (8), the properness clause of Stacks 09ZZ), and then of finite
presentation.  The finite-order gluing results are
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFiniteOrderGluing`.

## Main definitions

* `AlgebraicGeometry.CartesianProperFlatSpaces.structureMap`: the structure morphism of a family,
  to the algebraic space of a scheme equal to its base.
* `AlgebraicGeometry.CartesianProperFlatSpaces.homOfCommaHomIsPullback`: the morphism of families
  given by a cartesian square, as a morphism of the comma category.

## Main results

* `AlgebraicGeometry.isEquivalence_fiberSquareComparison_cartesianProperFlatProjection`: Stacks
  0D1J for a thickening of finite order.
* `AlgebraicGeometry.satisfiesRSStar_cartesianProperFlatProjection` and
  `AlgebraicGeometry.Space.satisfiesRSStar_properFlatSpacesStack`: the stack satisfies (RS*).

## Implementation notes

The comparison functor of (RS*) is built from the chosen cartesian lifts of the fibred
structure.  `CategoryTheory.Functor.isEquivalence_fiberSquareComparison_of_glue` reduces its
being an equivalence to the gluing of morphisms and of objects along arbitrary cartesian
morphisms, which is what is proved here; the morphisms of `CartesianProperFlatSpaces` are the
cartesian squares (Stacks 04U9), so every lift of a morphism of the base is cartesian.

No tag is registered: Stacks 0D1J is stated for a thickening of arbitrary order, and the gluing
of algebraic spaces along such a thickening rests on Stacks 05ZR, which this library does not
have unconditionally.

## References

* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CartesianProperFlatSpaces

/-- The structure morphism of a finitely presented, flat and proper family, as a morphism of
algebraic spaces to the algebraic space of a scheme equal to its base. -/
def structureMap (x : CartesianProperFlatSpaces B S hS) {R : BigFppfOver B S hS}
    (h : x.obj.obj.right = R) :
    x.obj.obj.left ⟶ schemeSpace R :=
  commaHomAsSpaceMap x.obj.obj ≫ schemeSpaceMap (eqToHom h)

/-- The structure morphism of a family with its own base. -/
theorem structureMap_rfl (x : CartesianProperFlatSpaces B S hS) :
    structureMap x rfl = commaHomAsSpaceMap x.obj.obj :=
  (congrArg (commaHomAsSpaceMap x.obj.obj ≫ ·) ((schemeSpaceFunctor B S hS).map_id _)).trans
    (Category.comp_id _)

/-- The structure morphism of a family is of finite presentation, flat and proper. -/
theorem structureMap_props (x : CartesianProperFlatSpaces B S hS) {R : BigFppfOver B S hS}
    (h : x.obj.obj.right = R) :
    Space.IsFinitePresentation B S hS (structureMap x h).hom ∧
      Space.IsFlat B S hS (structureMap x h).hom ∧
        Space.IsProper B S hS (structureMap x h).hom := by
  subst h
  rw [structureMap_rfl]
  exact x.obj.property

/-- **A morphism of families is a cartesian square** (Stacks 04U9).  A morphism `φ : x ⟶ y` lying
over `g : R ⟶ R'` exhibits the space of `x` as the base change of the space of `y` along `g`. -/
theorem isPullback_structureMap {x y : CartesianProperFlatSpaces B S hS}
    {R R' : BigFppfOver B S hS} (hx : x.obj.obj.right = R) (hy : y.obj.obj.right = R')
    (g : R ⟶ R') (φ : x ⟶ y) (hφ : (cartesianProperFlatProjection B S hS).IsHomLift g φ) :
    IsPullback φ.hom.hom.left (structureMap x hx) (structureMap y hy) (schemeSpaceMap g) := by
  subst hx hy
  let g' : (cartesianProperFlatProjection B S hS).obj x ⟶
      (cartesianProperFlatProjection B S hS).obj y := g
  have : (cartesianProperFlatProjection B S hS).IsHomLift g' φ := hφ
  have hg : φ.hom.hom.right = g :=
    (IsHomLift.eq_of_isHomLift (p := cartesianProperFlatProjection B S hS) g' φ).symm
  subst hg
  rw [structureMap_rfl, structureMap_rfl]
  exact isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS φ.hom.hom φ.property

/-- **The morphism of families given by a cartesian square** (Stacks 04U9). -/
def homOfCommaHomIsPullback {x y : CartesianProperFlatSpaces B S hS}
    (m : x.obj.obj ⟶ y.obj.obj)
    (h : IsPullback m.left.hom x.obj.obj.hom y.obj.obj.hom (yoneda.map m.right)) : x ⟶ y :=
  ⟨ObjectProperty.homMk m,
    SpacesDescent.isStronglyCartesian_of_isPullback m.right m rfl rfl (by simp) (by simp)
      (by simp) h⟩

/-- The morphism of families given by a cartesian square has the given underlying square. -/
@[simp]
theorem homOfCommaHomIsPullback_hom_hom {x y : CartesianProperFlatSpaces B S hS}
    (m : x.obj.obj ⟶ y.obj.obj)
    (h : IsPullback m.left.hom x.obj.obj.hom y.obj.obj.hom (yoneda.map m.right)) :
    (homOfCommaHomIsPullback m h).hom.hom = m :=
  rfl

/-- Morphisms of families are equal when their maps of total spaces and of bases are. -/
private theorem hom_ext {x y : CartesianProperFlatSpaces B S hS} {φ ψ : x ⟶ y}
    (hl : φ.hom.hom.left = ψ.hom.hom.left) (hr : φ.hom.hom.right = ψ.hom.hom.right) :
    φ = ψ := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact Comma.hom_ext _ _ hl hr

/-- Morphisms of families lying over the same morphism of the base are equal when their maps of
total spaces are. -/
private theorem hom_ext_of_isHomLift {x y : CartesianProperFlatSpaces B S hS}
    {R R' : BigFppfOver B S hS} (g : R ⟶ R') {φ ψ : x ⟶ y}
    (hφ : (cartesianProperFlatProjection B S hS).IsHomLift g φ)
    (hψ : (cartesianProperFlatProjection B S hS).IsHomLift g ψ)
    (h : φ.hom.hom.left = ψ.hom.hom.left) : φ = ψ :=
  hom_ext h ((IsHomLift.fac' (cartesianProperFlatProjection B S hS) g φ).trans
    (IsHomLift.fac' (cartesianProperFlatProjection B S hS) g ψ).symm)

/-- The base change of a family along a morphism to its base. -/
private def baseChange (x : CartesianProperFlatSpaces B S hS) {R : BigFppfOver B S hS}
    (g : R ⟶ x.obj.obj.right) : CartesianProperFlatSpaces B S hS :=
  ⟨⟨⟨pullback (commaHomAsSpaceMap x.obj.obj) (schemeSpaceMap g), R,
      (pullback.snd (commaHomAsSpaceMap x.obj.obj) (schemeSpaceMap g)).hom⟩,
    ⟨(Space.isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback _ _) x.obj.property.1,
      (Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback _ _) x.obj.property.2.1,
      (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback _ _) x.obj.property.2.2⟩⟩⟩

/-- The cartesian morphism from the base change of a family to the family. -/
private def baseChangeHom (x : CartesianProperFlatSpaces B S hS) {R : BigFppfOver B S hS}
    (g : R ⟶ x.obj.obj.right) : baseChange x g ⟶ x :=
  homOfCommaHomIsPullback
    ⟨pullback.fst (commaHomAsSpaceMap x.obj.obj) (schemeSpaceMap g), g,
      congrArg (fun k => k.hom)
        (pullback.condition (f := commaHomAsSpaceMap x.obj.obj) (g := schemeSpaceMap g))⟩
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _))

/-- The morphism of families over an equality of bases given by an isomorphism of total spaces
compatible with the structure maps. -/
private def homOfIso {x y : CartesianProperFlatSpaces B S hS}
    (h : y.obj.obj.right = x.obj.obj.right) (e : x.obj.obj.left ≅ y.obj.obj.left)
    (he : e.hom ≫ structureMap y h = commaHomAsSpaceMap x.obj.obj) : x ⟶ y :=
  have hsq : e.hom.hom ≫ y.obj.obj.hom = x.obj.obj.hom ≫ yoneda.map (eqToHom h.symm) := by
    have h' : e.hom.hom ≫ y.obj.obj.hom ≫ yoneda.map (eqToHom h) = x.obj.obj.hom :=
      congrArg (fun k => k.hom) he
    rw [← h', Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
      eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  haveI : IsIso e.hom.hom :=
    (inferInstance : IsIso ((ObjectProperty.ι (IsAlgebraicSpace B S hS)).map e.hom))
  homOfCommaHomIsPullback ⟨e.hom, eqToHom h.symm, hsq⟩ (IsPullback.of_horiz_isIso ⟨hsq⟩)

/-- The morphism of families given by an isomorphism of total spaces lies over the identity. -/
private theorem homOfIso_isHomLift {x y : CartesianProperFlatSpaces B S hS}
    (h : y.obj.obj.right = x.obj.obj.right) (e : x.obj.obj.left ≅ y.obj.obj.left)
    (he : e.hom ≫ structureMap y h = commaHomAsSpaceMap x.obj.obj) :
    (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 x.obj.obj.right) (homOfIso h e he) :=
  IsHomLift.of_fac' _ _ _ rfl h (by
    show eqToHom h.symm = _
    rw [Category.id_comp]
    exact (eqToHom_trans _ _).symm)

/-- A morphism of families lying over a morphism of the base is cartesian. -/
private theorem isCartesian_of_isHomLift {x y : CartesianProperFlatSpaces B S hS}
    {R R' : BigFppfOver B S hS} (g : R ⟶ R') (φ : x ⟶ y)
    (h : (cartesianProperFlatProjection B S hS).IsHomLift g φ) :
    (cartesianProperFlatProjection B S hS).IsCartesian g φ :=
  have := (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isStronglyCartesian_homLift
    g φ
  inferInstance

end CartesianProperFlatSpaces

open CartesianProperFlatSpaces

/-- A thickening of schemes of the site gives a thickening of algebraic spaces. -/
theorem isThickeningHom_schemeSpaceMap_of_isThickening {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i)) :
    Space.IsThickeningHom B S hS (schemeSpaceMap i) := by
  have : Surjective ((BigFppfOver.toScheme B S hS).map i) := ⟨hi.2⟩
  refine (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).2 ⟨?_, ?_⟩
  · exact (Space.presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance _).2 hi.1
  · exact Space.isSurjective_yoneda_map B S hS _ this

/-- An affine morphism of schemes of the site gives an affine morphism of algebraic spaces. -/
theorem isAffineHom_schemeSpaceMap_hom_of_isAffineHom {T T' : BigFppfOver B S hS} (f : T ⟶ T')
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) :
    Space.IsAffineHom B S hS (schemeSpaceMap f).hom :=
  Space.isAffineHom_of_presheaf ((Space.presheaf_yoneda_map_iff B S hS
    (P := @AlgebraicGeometry.IsAffineHom.{u}) inferInstance f).mpr hf)

/-- Properness passes from the special fibre of a cartesian square along a thickening of the
base to the total space, for morphisms locally of finite type (Stacks 0BPJ, part (8)). -/
theorem isProper_of_isPullback_of_isThickeningHom {X X' Y Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {i : X ⟶ X'} {j : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (hi : Space.IsThickeningHom B S hS i) (hj : Space.IsThickeningHom B S hS j)
    (hsq : IsPullback f i j f') (hft' : Space.IsLocallyOfFiniteType B S hS f'.hom)
    (hf : Space.IsProper B S hS f.hom) : Space.IsProper B S hS f'.hom := by
  let T := Space.CartesianLocallyFiniteTypeMorphismOfThickenings.ofIsThickeningHom hi hj hsq
    hf.2.1.1 hft'
  refine T.isProper_iff.1 ?_
  show Space.IsProper B S hS (hi.isoRange.inv ≫ f.hom ≫ hj.isoRange.hom)
  exact Space.isProper_comp B S hS T.sourceThickening.1.1 X.property T.targetThickening.1.1 _ _
    (Space.isProper_of_isIso B S hS hi.isoRange.inv)
    (Space.isProper_comp B S hS X.property Y.property T.targetThickening.1.1 _ _ hf
      (Space.isProper_of_isIso B S hS hj.isoRange.hom))

section Square

variable {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')

/-- The algebraic-space form of a pushout of schemes along a thickening of finite order and an
affine morphism: the thickening, its finite order, the affine morphism and the pushout (Stacks
07SY), and the second thickening `Y ⟶ Y'` (Stacks 07RT). -/
theorem spaces_of_isPushout_of_isFiniteOrderThickening
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f))
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    Space.IsThickeningHom B S hS (schemeSpaceMap i) ∧
      Space.IsFiniteOrderThickening B S hS (schemeSpace X')
        (Subfunctor.range (schemeSpaceMap i).hom) ∧
      Space.IsAffineHom B S hS (schemeSpaceMap f).hom ∧
      IsPushout (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap a) (schemeSpaceMap b) ∧
      Space.IsThickeningHom B S hS (schemeSpaceMap b) := by
  have := hf
  have ht := hfin.isThickening
  obtain ⟨hci, n, hn⟩ := hfin
  refine ⟨isThickeningHom_schemeSpaceMap_of_isThickening i ht,
    (Space.isNthOrderThickening_range_yoneda_map B S hS n i ⟨hci, hn⟩).isFiniteOrderThickening,
    isAffineHom_schemeSpaceMap_hom_of_isAffineHom f hf,
    Space.isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS i f a b
      ht hpush,
    isThickeningHom_schemeSpaceMap_of_isThickening b
      (Stacks.Pushout.isThickening_of_isPushout_of_isThickening hpush ht)⟩

/-- **Gluing of objects across a finite-order thickening pushout**, for families whose bases are
the corners of the square on the nose.  See `exists_glue_cartesianProperFlatSpaces`. -/
theorem exists_glue_cartesianProperFlatSpaces_of_isHomLift
    {xU xV xW : CartesianProperFlatSpaces B S hS} {Y' : BigFppfOver B S hS}
    (f : xU.obj.obj.right ⟶ xV.obj.obj.right) (i : xU.obj.obj.right ⟶ xW.obj.obj.right)
    (a : xW.obj.obj.right ⟶ Y') (b : xV.obj.obj.right ⟶ Y')
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) (w : i ≫ a = f ≫ b)
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (u : xU ⟶ xV) (v : xU ⟶ xW) (hfu : u.hom.hom.right = f) (hiv : v.hom.hom.right = i) :
    ∃ (a₀ : CartesianProperFlatSpaces B S hS)
      (_ : (cartesianProperFlatProjection B S hS).obj a₀ = Y') (μ : xV ⟶ a₀) (ν : xW ⟶ a₀),
      (cartesianProperFlatProjection B S hS).IsHomLift b μ ∧
        (cartesianProperFlatProjection B S hS).IsHomLift a ν ∧ u ≫ μ = v ≫ ν := by
  obtain ⟨hiS, hnS, hfS, hE, hbS⟩ :=
    spaces_of_isPushout_of_isFiniteOrderThickening i f a b hfin hf hpush
  have key : ∀ {x y : CartesianProperFlatSpaces B S hS} {g : x.obj.obj.right ⟶ y.obj.obj.right}
      (φ : x ⟶ y), φ.hom.hom.right = g →
      IsPullback φ.hom.hom.left (commaHomAsSpaceMap x.obj.obj) (commaHomAsSpaceMap y.obj.obj)
        (schemeSpaceMap g) := by
    rintro x y g φ rfl
    exact isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS φ.hom.hom φ.property
  have hV := key u hfu
  have hU' := key v hiv
  have := Space.hasPushout_triple_of_isFiniteOrderThickening B S hS hiS hnS hfS hU' hV
  have hG := IsPushout.of_hasPushout v.hom.hom.left u.hom.hom.left
  have hcomm : v.hom.hom.left ≫ commaHomAsSpaceMap xW.obj.obj ≫ schemeSpaceMap a =
      u.hom.hom.left ≫ commaHomAsSpaceMap xV.obj.obj ≫ schemeSpaceMap b := by
    rw [← Category.assoc, hU'.w, ← Category.assoc, hV.w, Category.assoc, Category.assoc, hE.w]
  let g := hG.desc (commaHomAsSpaceMap xW.obj.obj ≫ schemeSpaceMap a)
    (commaHomAsSpaceMap xV.obj.obj ≫ schemeSpaceMap b) hcomm
  have haG : pushout.inl v.hom.hom.left u.hom.hom.left ≫ g =
      commaHomAsSpaceMap xW.obj.obj ≫ schemeSpaceMap a := hG.inl_desc _ _ _
  have hbG : pushout.inr v.hom.hom.left u.hom.hom.left ≫ g =
      commaHomAsSpaceMap xV.obj.obj ≫ schemeSpaceMap b := hG.inr_desc _ _ _
  obtain ⟨hglV, hglW⟩ :=
    Space.isPullback_glued_of_isFiniteOrderThickening hiS hnS hfS hE hU' hV hG haG hbG
  obtain ⟨-, -, hflp, -, -⟩ :=
    Space.glued_properties_iff_of_isFiniteOrderThickening hiS hnS hfS hE hU' hV hG haG hbG
  have hxVp := xV.obj.property
  have hgflp := hflp.2 ⟨⟨hxVp.2.1, hxVp.1.1⟩, ⟨xW.obj.property.2.1, xW.obj.property.1.1⟩⟩
  have hgproper : Space.IsProper B S hS g.hom :=
    isProper_of_isPullback_of_isThickeningHom
      (Space.isThickeningHom_of_isPullback B S hS hglV.flip hbS) hbS hglV.flip
      (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hgflp.2) hxVp.2.2
  let a₀ : CartesianProperFlatSpaces B S hS :=
    ⟨⟨⟨pushout v.hom.hom.left u.hom.hom.left, Y', g.hom⟩,
      ⟨⟨hgflp.2, hgproper.2.1.2, Space.isQuasiSeparated_of_isSeparated B S hS hgproper.1⟩,
        hgflp.1, hgproper⟩⟩⟩
  let μ : xV ⟶ a₀ := homOfCommaHomIsPullback
    ⟨pushout.inr v.hom.hom.left u.hom.hom.left, b, congrArg (fun k => k.hom) hbG⟩
    (AlgebraicSpaces.isPullback_hom B S hS hglV)
  let ν : xW ⟶ a₀ := homOfCommaHomIsPullback
    ⟨pushout.inl v.hom.hom.left u.hom.hom.left, a, congrArg (fun k => k.hom) haG⟩
    (AlgebraicSpaces.isPullback_hom B S hS hglW)
  refine ⟨a₀, rfl, μ, ν, CategoryTheory.IsHomLift.map _ μ, CategoryTheory.IsHomLift.map _ ν,
    hom_ext hG.w.symm ?_⟩
  show u.hom.hom.right ≫ b = v.hom.hom.right ≫ a
  rw [hfu, hiv]
  exact w.symm

/-- **Gluing of objects across a finite-order thickening pushout.**  For a pushout
`Y' = Y ⨿_X X'` of schemes along a thickening `i` of finite order and an affine `f`, every span
`x_Y ⟵ x_X ⟶ x_{X'}` of cartesian morphisms of finitely presented, flat and proper families over
`Y ⟵ X ⟶ X'` is the restriction of a family over `Y'`: the pushout of the three algebraic spaces,
which is flat, of finite presentation and proper over `Y'`. -/
theorem exists_glue_cartesianProperFlatSpaces
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) (w : i ≫ a = f ≫ b)
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (xV : (cartesianProperFlatProjection B S hS).Fiber Y)
    (xW : (cartesianProperFlatProjection B S hS).Fiber X')
    (xU : CartesianProperFlatSpaces B S hS) (u : xU ⟶ Fiber.fiberInclusion.obj xV)
    (v : xU ⟶ Fiber.fiberInclusion.obj xW)
    (hu : (cartesianProperFlatProjection B S hS).IsCartesian f u)
    (hv : (cartesianProperFlatProjection B S hS).IsCartesian i v) :
    ∃ (a₀ : (cartesianProperFlatProjection B S hS).Fiber Y')
      (μ : Fiber.fiberInclusion.obj xV ⟶ Fiber.fiberInclusion.obj a₀)
      (ν : Fiber.fiberInclusion.obj xW ⟶ Fiber.fiberInclusion.obj a₀),
      (cartesianProperFlatProjection B S hS).IsCartesian b μ ∧
        (cartesianProperFlatProjection B S hS).IsCartesian a ν ∧ u ≫ μ = v ≫ ν := by
  obtain ⟨xV, rfl⟩ := xV
  obtain ⟨xW, rfl⟩ := xW
  obtain rfl : (cartesianProperFlatProjection B S hS).obj xU = X :=
    IsHomLift.domain_eq (cartesianProperFlatProjection B S hS) f u
  let u' : xU ⟶ xV := u
  let v' : xU ⟶ xW := v
  have : (cartesianProperFlatProjection B S hS).IsHomLift f u' := hu.toIsHomLift
  have : (cartesianProperFlatProjection B S hS).IsHomLift i v' := hv.toIsHomLift
  obtain ⟨a₀, ha₀, μ, ν, hμ, hν, huv⟩ :=
    exists_glue_cartesianProperFlatSpaces_of_isHomLift f i a b hfin hf w hpush
      u' v' (IsHomLift.eq_of_isHomLift (p := cartesianProperFlatProjection B S hS) f u').symm
      (IsHomLift.eq_of_isHomLift (p := cartesianProperFlatProjection B S hS) i v').symm
  exact ⟨⟨a₀, ha₀⟩, μ, ν, isCartesian_of_isHomLift b μ hμ, isCartesian_of_isHomLift a ν hν, huv⟩

/-- **Morphisms glue across a finite-order thickening pushout.**  A family `a₀` over the pushout
`Y' = Y ⨿_X X'` is the pushout of its restrictions along cartesian morphisms over the square, so
morphisms out of the restrictions to `Y` and `X'` into a family over `Y'` that agree on the
restriction to `X` glue to a unique morphism over `Y'`. -/
private theorem existsUnique_hom_of_isHomLift_of_isPushout
    {a₀ b₀ aV aW aU : CartesianProperFlatSpaces B S hS} {X X' Y : BigFppfOver B S hS}
    {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ a₀.obj.obj.right} {b : Y ⟶ a₀.obj.obj.right}
    (hiS : Space.IsThickeningHom B S hS (schemeSpaceMap i))
    (hnS : Space.IsFiniteOrderThickening B S hS (schemeSpace X')
      (Subfunctor.range (schemeSpaceMap i).hom))
    (hfS : Space.IsAffineHom B S hS (schemeSpaceMap f).hom)
    (hE : IsPushout (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap a) (schemeSpaceMap b))
    (c : aV ⟶ a₀) (d : aW ⟶ a₀) (u : aU ⟶ aV) (v : aU ⟶ aW)
    (hc : (cartesianProperFlatProjection B S hS).IsHomLift b c)
    (hd : (cartesianProperFlatProjection B S hS).IsHomLift a d)
    (hu : (cartesianProperFlatProjection B S hS).IsHomLift f u)
    (hv : (cartesianProperFlatProjection B S hS).IsHomLift i v) (huv : u ≫ c = v ≫ d)
    (hb₀ : b₀.obj.obj.right = a₀.obj.obj.right) (α : aV ⟶ b₀) (β : aW ⟶ b₀)
    (hα : (cartesianProperFlatProjection B S hS).IsHomLift b α)
    (hβ : (cartesianProperFlatProjection B S hS).IsHomLift a β) (hαβ : u ≫ α = v ≫ β) :
    ∃! φ : a₀ ⟶ b₀, (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 a₀.obj.obj.right) φ ∧
      c ≫ φ = α ∧ d ≫ φ = β := by
  have hV : aV.obj.obj.right = Y := IsHomLift.domain_eq (cartesianProperFlatProjection B S hS) b c
  have hW : aW.obj.obj.right = X' := IsHomLift.domain_eq (cartesianProperFlatProjection B S hS) a d
  have hU : aU.obj.obj.right = X := IsHomLift.domain_eq (cartesianProperFlatProjection B S hS) f u
  have hcsq := isPullback_structureMap hV rfl b c hc
  have hdsq := isPullback_structureMap hW rfl a d hd
  have husq := isPullback_structureMap hU hV f u hu
  have hvw := (isPullback_structureMap hU hW i v hv).w
  have hαsq := isPullback_structureMap hV hb₀ b α hα
  have hβsq := isPullback_structureMap hW hb₀ a β hβ
  have PA := Space.isPushout_of_isFlat_of_isFiniteOrderThickening hiS hnS hfS hE
    (structureMap_props a₀ rfl).2.1 hdsq hcsq husq hvw (congrArg (fun k => k.hom.hom.left) huv)
  have PB := Space.isPushout_of_isFlat_of_isFiniteOrderThickening hiS hnS hfS hE
    (structureMap_props b₀ hb₀).2.1 hβsq hαsq husq hvw (congrArg (fun k => k.hom.hom.left) hαβ)
  let e := PA.isoIsPushout _ _ PB
  have heW : d.hom.hom.left ≫ e.hom = β.hom.hom.left := PA.inl_isoIsPushout_hom _ _ PB
  have heV : c.hom.hom.left ≫ e.hom = α.hom.hom.left := PA.inr_isoIsPushout_hom _ _ PB
  have hes : e.hom ≫ CartesianProperFlatSpaces.structureMap b₀ hb₀ =
      CartesianProperFlatSpaces.structureMap a₀ rfl := by
    refine PA.hom_ext ?_ ?_
    · rw [← Category.assoc, heW, hβsq.w, hdsq.w]
    · rw [← Category.assoc, heV, hαsq.w, hcsq.w]
  have hφ := homOfIso_isHomLift hb₀ e (hes.trans (structureMap_rfl a₀))
  refine ⟨homOfIso hb₀ e (hes.trans (structureMap_rfl a₀)), ⟨hφ,
    hom_ext_of_isHomLift b (IsHomLift.comp_lift_id_right _ b c _) hα heV,
    hom_ext_of_isHomLift a (IsHomLift.comp_lift_id_right _ a d _) hβ heW⟩, ?_⟩
  rintro ψ ⟨hψ, hψc, hψd⟩
  exact hom_ext_of_isHomLift (𝟙 _) hψ hφ (PA.hom_ext
    ((congrArg (fun k => k.hom.hom.left) hψd).trans heW.symm)
    ((congrArg (fun k => k.hom.hom.left) hψc).trans heV.symm))

/-- **Gluing of morphisms across a finite-order thickening pushout**, for a family `a₀` whose base
is the fourth corner of the square on the nose. See `exists_glue_hom_cartesianProperFlatSpaces`.
-/
theorem exists_glue_hom_cartesianProperFlatSpaces_of_base
    (a₀ : CartesianProperFlatSpaces B S hS) {X X' Y : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ a₀.obj.obj.right) (b : Y ⟶ a₀.obj.obj.right)
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) (w : i ≫ a = f ≫ b)
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    ∃ (aV aW aU : CartesianProperFlatSpaces B S hS) (c : aV ⟶ a₀) (d : aW ⟶ a₀) (u : aU ⟶ aV)
      (v : aU ⟶ aW),
      (cartesianProperFlatProjection B S hS).IsHomLift b c ∧
      (cartesianProperFlatProjection B S hS).IsHomLift a d ∧
      (cartesianProperFlatProjection B S hS).IsHomLift f u ∧
      (cartesianProperFlatProjection B S hS).IsHomLift i v ∧ u ≫ c = v ≫ d ∧
      ∀ (b₀ : CartesianProperFlatSpaces B S hS)
        (_hb₀ : b₀.obj.obj.right = a₀.obj.obj.right)
        (α : aV ⟶ b₀) (β : aW ⟶ b₀), (cartesianProperFlatProjection B S hS).IsHomLift b α →
        (cartesianProperFlatProjection B S hS).IsHomLift a β → u ≫ α = v ≫ β →
        ∃! φ : a₀ ⟶ b₀, (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 a₀.obj.obj.right) φ ∧
          c ≫ φ = α ∧ d ≫ φ = β := by
  obtain ⟨hiS, hnS, hfS, hE, -⟩ :=
    spaces_of_isPushout_of_isFiniteOrderThickening i f a b hfin hf hpush
  let s₀ := commaHomAsSpaceMap a₀.obj.obj
  let sa := schemeSpaceMap a
  let sb := schemeSpaceMap b
  have hVsq := IsPullback.of_hasPullback s₀ sb
  have hWsq := IsPullback.of_hasPullback s₀ sa
  let sV := pullback.snd s₀ sb
  let sf := schemeSpaceMap f
  have hUsq := IsPullback.of_hasPullback sV sf
  let aV := baseChange a₀ b
  let aU := baseChange aV f
  let u : aU ⟶ aV := baseChangeHom aV f
  have hℓ : (pullback.fst sV sf ≫ pullback.fst s₀ sb) ≫ s₀ =
      (pullback.snd sV sf ≫ schemeSpaceMap i) ≫ sa := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, ← hE.w]
  let ℓ : pullback sV sf ⟶ pullback s₀ sa :=
    pullback.lift (pullback.fst sV sf ≫ pullback.fst s₀ sb) (pullback.snd sV sf ≫ schemeSpaceMap i)
      hℓ
  have hℓfst : ℓ ≫ pullback.fst s₀ sa = pullback.fst sV sf ≫ pullback.fst s₀ sb :=
    pullback.lift_fst _ _ _
  have hℓsnd : ℓ ≫ pullback.snd s₀ sa = pullback.snd sV sf ≫ schemeSpaceMap i :=
    pullback.lift_snd _ _ _
  have hvsq : IsPullback ℓ (pullback.snd sV sf) (pullback.snd s₀ sa) (schemeSpaceMap i) := by
    have h := hUsq.paste_horiz hVsq
    rw [← hℓfst, ← hE.w] at h
    exact IsPullback.of_right h hℓsnd hWsq
  let v : aU ⟶ baseChange a₀ a := homOfCommaHomIsPullback ⟨ℓ, i, congrArg (fun k => k.hom) hℓsnd⟩
    (AlgebraicSpaces.isPullback_hom B S hS hvsq)
  have hc := IsHomLift.map (cartesianProperFlatProjection B S hS) (baseChangeHom a₀ b)
  have hd := IsHomLift.map (cartesianProperFlatProjection B S hS) (baseChangeHom a₀ a)
  have hu := IsHomLift.map (cartesianProperFlatProjection B S hS) u
  have hv := IsHomLift.map (cartesianProperFlatProjection B S hS) v
  have huvcd : u ≫ baseChangeHom a₀ b = v ≫ baseChangeHom a₀ a := hom_ext hℓfst.symm w.symm
  exact ⟨aV, baseChange a₀ a, aU, baseChangeHom a₀ b, baseChangeHom a₀ a, u, v, hc, hd, hu, hv,
    huvcd, fun b₀ hb₀ α β hα hβ hαβ => existsUnique_hom_of_isHomLift_of_isPushout hiS hnS hfS hE
      _ _ u v hc hd hu hv huvcd hb₀ α β hα hβ hαβ⟩

/-- **Gluing of morphisms across a finite-order thickening pushout.**  For a pushout
`Y' = Y ⨿_X X'` of schemes along a thickening `i` of finite order and an affine `f`, every family
`a₀` over `Y'` has base changes `a_Y`, `a_{X'}`, `a_X` along cartesian morphisms over the square,
and morphisms out of `a_Y` and `a_{X'}` into a family `b₀` over `Y'` which agree on `a_X` glue to
a unique morphism `a₀ ⟶ b₀` over `Y'`: `a₀` is the pushout of its base changes (the counit
assertion of Stacks 07W3), and so is `b₀`. -/
theorem exists_glue_hom_cartesianProperFlatSpaces
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) (w : i ≫ a = f ≫ b)
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (a₀ : (cartesianProperFlatProjection B S hS).Fiber Y') :
    ∃ (aV aW aU : CartesianProperFlatSpaces B S hS) (c : aV ⟶ Fiber.fiberInclusion.obj a₀)
      (d : aW ⟶ Fiber.fiberInclusion.obj a₀) (u : aU ⟶ aV) (v : aU ⟶ aW),
      (cartesianProperFlatProjection B S hS).IsCartesian b c ∧
      (cartesianProperFlatProjection B S hS).IsCartesian a d ∧
      (cartesianProperFlatProjection B S hS).IsHomLift f u ∧
      (cartesianProperFlatProjection B S hS).IsHomLift i v ∧ u ≫ c = v ≫ d ∧
      ∀ (b₀ : (cartesianProperFlatProjection B S hS).Fiber Y')
        (α : aV ⟶ Fiber.fiberInclusion.obj b₀) (β : aW ⟶ Fiber.fiberInclusion.obj b₀),
        (cartesianProperFlatProjection B S hS).IsHomLift b α →
        (cartesianProperFlatProjection B S hS).IsHomLift a β → u ≫ α = v ≫ β →
        ∃! φ : a₀ ⟶ b₀, c ≫ Fiber.fiberInclusion.map φ = α ∧
          d ≫ Fiber.fiberInclusion.map φ = β := by
  obtain ⟨a₀, rfl⟩ := a₀
  obtain ⟨aV, aW, aU, c, d, u, v, hc, hd, hu, hv, huv, hglue⟩ :=
    exists_glue_hom_cartesianProperFlatSpaces_of_base a₀ i f a b hfin hf w hpush
  refine ⟨aV, aW, aU, c, d, u, v, isCartesian_of_isHomLift b c hc,
    isCartesian_of_isHomLift a d hd, hu, hv, huv, ?_⟩
  · intro b₀ α β hα hβ hαβ
    obtain ⟨φ, ⟨hφ, hφc, hφd⟩, huniq⟩ := hglue b₀.1 b₀.2 α β hα hβ hαβ
    refine ⟨⟨φ, hφ⟩, ⟨hφc, hφd⟩, ?_⟩
    rintro ψ ⟨hψc, hψd⟩
    exact Subtype.ext (huniq ψ.1 ⟨ψ.2, hψc, hψd⟩)

/-- **Stacks 0D1J, for a thickening of finite order.**  Let `Y' = Y ⨿_X X'` be a pushout of
schemes of the big fppf site along a thickening `i : X ⟶ X'` of finite order and an affine
morphism `f : X ⟶ Y`.  Then the comparison functor from the fibre of
`Spaces'_{fp, flat, proper}` over `Y'` to the `2`-fibre product of its fibres over `Y` and `X'`
above its fibre over `X` is an equivalence. -/
theorem isEquivalence_fiberSquareComparison_cartesianProperFlatProjection
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (hf : IsAffineHom ((BigFppfOver.toScheme B S hS).map f)) (w : i ≫ a = f ≫ b)
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (cartesianProperFlatProjection B S hS).IsFibered :=
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isFibered
    (Deformation.Artin.fiberSquareComparison (cartesianProperFlatProjection B S hS)
      (chosenPullbacks (cartesianProperFlatProjection B S hS)) f i b a w.symm).IsEquivalence :=
  let : (cartesianProperFlatProjection B S hS).IsFibered :=
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isFibered
  isEquivalence_fiberSquareComparison_of_glue _ f i b a w.symm
    (exists_glue_hom_cartesianProperFlatSpaces i f a b hfin hf w hpush)
    (exists_glue_cartesianProperFlatSpaces i f a b hfin hf w hpush)

end Square

variable (B S hS)

/-- **The stack `Spaces'_{fp, flat, proper}` satisfies (RS*)** (Stacks 07Y8).  Condition (RS*)
asks for the comparison functor of a square of affine schemes along a first order thickening to
be an equivalence; this is Stacks 0D1J, proved here for thickenings of finite order. -/
theorem satisfiesRSStar_cartesianProperFlatProjection :
    Deformation.Artin.SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) :=
  Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine B S hS _ _
    fun i f a b w hX _ hY _ hfirst hpush => by
      have := hX
      have := hY
      exact isEquivalence_fiberSquareComparison_cartesianProperFlatProjection i f a b
        ⟨hfirst.1, 1, by simpa using hfirst.2⟩ inferInstance w hpush

/-- **The stack `Spaces'_{fp, flat, proper}` of Stacks 0D1D satisfies (RS*)** (Stacks 07Y8), read
on `AlgebraicGeometry.Space.properFlatSpacesStack`. -/
theorem Space.satisfiesRSStar_properFlatSpacesStack :
    Deformation.Artin.SatisfiesRSStar B S hS (Space.properFlatSpacesStack B S hS).val.p
      (Space.properFlatSpacesStack B S hS).isFiberedInGroupoids :=
  satisfiesRSStar_cartesianProperFlatProjection B S hS

end AlgebraicGeometry

end
