module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralPushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexesEquivalence

/-!
# The geometric stalk of a derived direct image of a complex supported on a closed subspace

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `Z ⊆ X` be a closed
subspace and let `W ⊆ Y` be a closed subspace lying over it, through a morphism `f' : W ⟶ Z`
which is integral and universally injective — in the source, `W = f^{-1}Z` and `f'` is the base
change of `f`. Let `ȳ` be a geometric point of `Y` lying on `W` and let `x̄ = f(ȳ)`. For an
object `Q` of `D(Y_étale)` all of whose cohomology sheaves are supported on `|W|`, the stalk at
`x̄` of `Rf_*Q` is the stalk at `ȳ` of `Q`. This is **Stacks 0AEQ**.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianStalk`: the geometric stalk of an abelian sheaf on the
  small étale site, as a functor.
* `AlgebraicGeometry.Space.smallEtaleDerivedAbelianStalk`: its degreewise action
  `D(X_étale) ⥤ D(Ab)`.
* `AlgebraicGeometry.Space.DerivedPushforwardSquareData`: for the square and an unbounded derived
  direct image `RF` along `f`, the equivalence `(f')^{-1} : D(Z_étale) ≌ D(W_étale)` of Stacks 0AEH
  part (1) and the composition `RF ∘ Ri'_* ∘ (f')^{-1} ≅ Ri_*` of Stacks 015N.
* `AlgebraicGeometry.Space.derivedStalkIsoOnSupportedComplexes`: the comparison of Stacks 0AEQ as
  an isomorphism of functors on `D_{|W|}(Y_étale)`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkIso` and
  `AlgebraicGeometry.Space.derivedSmallEtaleAbelianPushforwardStalkIso`: **the stalk of a direct
  image along a closed immersion** at the image of a geometric point is the stalk of the sheaf,
  on abelian sheaves and on unbounded derived categories.
* `AlgebraicGeometry.Space.derivedSmallEtaleAbelianInverseImageStalkIso`: Stacks 04K2 part (4)
  on unbounded derived categories.
* `AlgebraicGeometry.Space.stalkDerivedPushforwardIso` is **Stacks 0AEQ**: the identification
  `(Rf_*Q)_{x̄} ≅ Q_ȳ` in `D(Ab)`, and
  `AlgebraicGeometry.Space.stalkDerivedPushforwardIso_naturality` is its naturality in `Q`.

## Implementation notes

Stacks 0AEH part (1) on unbounded derived categories and Stacks 015N for the square are taken as
hypotheses, bundled in `AlgebraicGeometry.Space.DerivedPushforwardSquareData`. `RF` is a total
right derived functor of the direct image of abelian sheaves along `f`, carried with its unit and
the `CategoryTheory.Functor.IsRightDerivedFunctor` property.

The square is not assumed cartesian: `W` is any closed subspace of `Y` over `Z`, and for
`W = f^{-1}Z` this is the source's hypothesis. The geometric point `ȳ` is assumed to lift to `W`.

The coefficient universe is `u + 1`, the universe in which the objects of the small étale site of
an algebraic space over `Scheme.{u}` live; the derived category used throughout is the standard
localization `CategoryTheory.HasDerivedCategory.standard`, installed as a local instance of high
priority.

## References

* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 0AEI](https://stacks.math.columbia.edu/tag/0AEI)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 100000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of geometric points under composition -/

/-- The image of a geometric point under a composite of morphisms of presheaves is the image of
its image. -/
theorem geometricPointMap_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    (z : GeometricPoint B S hS F) :
    geometricPointMap (α ≫ β) z = geometricPointMap β (geometricPointMap α z) :=
  rfl

/-! ### The geometric stalk of an abelian sheaf as an exact functor -/

variable {X Y Z W : AlgebraicSpaces B S hS}

/-- **The geometric stalk of an abelian sheaf on the small étale site**, as a functor
`abelianSheaves B S hS X ⥤ AddCommGrpCat`: the geometric stalk of Stacks 04JY of the underlying
presheaf. -/
abbrev smallEtaleAbelianStalk (x : GeometricPoint B S hS X.1) :
    abelianSheaves.{u + 1} B S hS X ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⋙
    stalkFunctor AddCommGrpCat.{u + 1} x

/-- **Stacks 04K1 part (3).** The geometric stalk of an abelian sheaf is left exact. -/
instance preservesFiniteLimits_smallEtaleAbelianStalk (x : GeometricPoint B S hS X.1) :
    PreservesFiniteLimits (smallEtaleAbelianStalk B S hS x) :=
  sheafAbelianStalk_preservesFiniteLimits.{u, u} B S hS X.1 X.property x

/-- **Stacks 04K1 part (3).** The geometric stalk of an abelian sheaf is right exact. -/
instance preservesFiniteColimits_smallEtaleAbelianStalk (x : GeometricPoint B S hS X.1) :
    PreservesFiniteColimits (smallEtaleAbelianStalk B S hS x) :=
  sheafAbelianStalk_preservesFiniteColimits.{u, u} B S hS X.1 X.property x

/-- The geometric stalk of an abelian sheaf is additive, preserving binary products. -/
instance additive_smallEtaleAbelianStalk (x : GeometricPoint B S hS X.1) :
    (smallEtaleAbelianStalk B S hS x).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The geometric stalk on unbounded derived categories**, `D(X_étale) ⥤ D(Ab)`: the
degreewise action of the exact functor `AlgebraicGeometry.Space.smallEtaleAbelianStalk`. -/
abbrev smallEtaleDerivedAbelianStalk (x : GeometricPoint B S hS X.1) :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (smallEtaleAbelianStalk B S hS x).mapDerivedCategory

/-! ### The stalk of a direct image along a closed immersion -/

/-- **The geometric stalk of a direct image along a closed immersion.** For a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S` and a geometric point `z` of `Z` whose image in `X`
is `x`, the stalk at `x` of `i_*G` is the stalk at `z` of `G`, naturally in the abelian sheaf
`G`. -/
def smallEtaleAbelianPushforwardStalkIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (z : GeometricPoint B S hS Z.1) (x : GeometricPoint B S hS X.1)
    (hx : geometricPointMap i.hom z = x) :
    smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⋙ smallEtaleAbelianStalk B S hS x ≅
      smallEtaleAbelianStalk B S hS z := by
  subst hx
  haveI := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  haveI :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  exact Functor.isoWhiskerLeft _
      (smallEtaleAbelianInverseImageStalkIso B S hS i hi.rep z).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).counit)
      (smallEtaleAbelianStalk B S hS z) ≪≫
    Functor.leftUnitor _

/-- **The geometric stalk of a derived direct image along a closed immersion.** For a closed
immersion `i : Z ⟶ X` and a geometric point `z` of `Z` with image `x` in `X`, the stalk at `x` of
the degreewise direct image `i_*K` of a complex `K` on `Z_étale` is the stalk at `z` of `K`,
naturally in `K`. -/
def derivedSmallEtaleAbelianPushforwardStalkIso (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (z : GeometricPoint B S hS Z.1)
    (x : GeometricPoint B S hS X.1) (hx : geometricPointMap i.hom z = x) :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory ⋙
        smallEtaleDerivedAbelianStalk B S hS x ≅
      smallEtaleDerivedAbelianStalk B S hS z := by
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact Functor.mapDerivedCategoryCompIsoOfCompIso
    (smallEtaleAbelianPushforwardStalkIso B S hS i hi z x hx)

/-- **Stacks 04K2 part (4) on unbounded derived categories.** The stalk of the degreewise inverse
image `g^{-1}K` at a geometric point `w` of the source is the stalk of `K` at the image of `w`,
naturally in `K`. -/
def derivedSmallEtaleAbelianInverseImageStalkIso (g : W ⟶ Z)
    (hg : yoneda.relativelyRepresentable g.hom) (w : GeometricPoint B S hS W.1)
    (z : GeometricPoint B S hS Z.1) (hz : geometricPointMap g.hom w = z) :
    letI := additive_smallEtaleAbelianInverseImage B S hS g hg
    letI : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS g hg) :=
      preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS g hg
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS g hg
    (smallEtaleAbelianInverseImage B S hS g hg).mapDerivedCategory ⋙
        smallEtaleDerivedAbelianStalk B S hS w ≅
      smallEtaleDerivedAbelianStalk B S hS z := by
  letI := additive_smallEtaleAbelianInverseImage B S hS g hg
  letI : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS g hg) :=
      preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS g hg
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS g hg
  subst hz
  exact Functor.mapDerivedCategoryCompIsoOfCompIso
    (smallEtaleAbelianInverseImageStalkIso B S hS g hg w)

/-! ### The datum which is carried -/

/-- **Stacks 0AEH part (1) and Stacks 015N for a square**, for a commutative square of algebraic
spaces over `S` with closed immersions `i : Z ⟶ X` and `i' : W ⟶ Y`, a morphism `f' : W ⟶ Z`
which is integral and universally injective, and an unbounded derived direct image `RF` along
`f : Y ⟶ X`. -/
structure DerivedPushforwardSquareData (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (i' : W ⟶ Y) (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf' : yoneda.relativelyRepresentable f'.hom) (hf'int : IsIntegralHom B S hS f'.hom)
    (hf'inj : UniversallyInjective B S hS f'.hom)
    (RF : smallEtaleDerivedCategory.{u + 1} B S hS Y ⥤
      smallEtaleDerivedCategory.{u + 1} B S hS X) where
  /-- **Stacks 0AEH part (1) on unbounded derived categories.** The inverse image along an
  integral universally injective morphism `f' : W ⟶ Z` is an equivalence
  `D(Z_étale) ≌ D(W_étale)`. -/
  isEquivalence_derivedInverseImage :
    letI := additive_smallEtaleAbelianInverseImage B S hS f' hf'
    letI : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS f' hf') :=
      preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS f' hf'
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS f' hf'
    (smallEtaleAbelianInverseImage B S hS f' hf').mapDerivedCategory.IsEquivalence
  /-- **Stacks 015N for the square**: `RF ∘ Ri'_* ∘ (f')^{-1} ≅ Ri_*`, the direct images along
  the two closed immersions acting degreewise. -/
  lerayIso :
    letI := additive_smallEtaleAbelianInverseImage B S hS f' hf'
    letI : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS f' hf') :=
      preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS f' hf'
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS f' hf'
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    letI :=
      preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i' hi'
    (smallEtaleAbelianInverseImage B S hS f' hf').mapDerivedCategory ⋙
        (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).mapDerivedCategory ⋙ RF ≅
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory

/-! ### Stacks 0AEQ -/

section Main

variable (f : Y ⟶ X) (hfr : yoneda.relativelyRepresentable f.hom) (i : Z ⟶ X)
  (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
  (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
  (hf' : yoneda.relativelyRepresentable f'.hom) (hf'int : IsIntegralHom B S hS f'.hom)
  (hf'inj : UniversallyInjective B S hS f'.hom) (hsq : i' ≫ f = f' ≫ i)
  (RF : smallEtaleDerivedCategory.{u + 1} B S hS Y ⥤ smallEtaleDerivedCategory.{u + 1} B S hS X)
  (unit : (smallEtaleAbelianPushforward.{u + 1} B S hS f hfr).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)

/-- **The comparison of Stacks 0AEQ as an isomorphism of functors on the supported
complexes.** On the subcategory `D_{|W|}(Y_étale)` of complexes whose cohomology sheaves are all
supported on `|W|`, the geometric stalk at `x̄ = f(ȳ)` of `RF` is the geometric stalk at `ȳ`.
-/
def derivedStalkIsoOnSupportedComplexes
    (d : DerivedPushforwardSquareData B S hS i hi i' hi' f' hf' hf'int hf'inj RF)
    (y : GeometricPoint B S hS Y.1) (w : GeometricPoint B S hS W.1)
    (hw : geometricPointMap i'.hom w = y) :
    (cohomologySupportedOn.{u + 1} B S hS Y (Set.range (pointsMap B S hS W.1 i'.hom))).ι ⋙
          RF ⋙ smallEtaleDerivedAbelianStalk B S hS (geometricPointMap f.hom y) ≅
      (cohomologySupportedOn.{u + 1} B S hS Y
          (Set.range (pointsMap B S hS W.1 i'.hom))).ι ⋙
        smallEtaleDerivedAbelianStalk B S hS y := by
  letI := additive_smallEtaleAbelianInverseImage B S hS f' hf'
  letI : PreservesFiniteLimits (smallEtaleAbelianInverseImage B S hS f' hf') :=
      preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS f' hf'
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS f' hf'
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i' hi'
  letI := d.isEquivalence_derivedInverseImage
  set z : GeometricPoint B S hS Z.1 := geometricPointMap f'.hom w with hz
  have hxz : geometricPointMap i.hom z = geometricPointMap f.hom y := by
    rw [hz, ← hw, ← geometricPointMap_comp, ← geometricPointMap_comp]
    exact congrArg (fun α ↦ geometricPointMap α w) (congrArg (fun m ↦ m.hom) hsq.symm)
  set E := derivedSmallEtalePushforwardSupportedEquivalence B S hS i' hi' with hE
  set G := (smallEtaleAbelianInverseImage B S hS f' hf').mapDerivedCategory.asEquivalence with hG
  have hι : (cohomologySupportedOn.{u + 1} B S hS Y
        (Set.range (pointsMap B S hS W.1 i'.hom))).ι ≅
      E.inverse ⋙ (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).mapDerivedCategory :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse
        (derivedSmallEtalePushforwardSupportedEquivalence_functor B S hS i' hi')
  have hW : (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).mapDerivedCategory ⋙
        smallEtaleDerivedAbelianStalk B S hS y ≅
      G.inverse ⋙ smallEtaleDerivedAbelianStalk B S hS z :=
    derivedSmallEtaleAbelianPushforwardStalkIso B S hS i' hi' w y hw ≪≫
      (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight G.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse
          (derivedSmallEtaleAbelianInverseImageStalkIso B S hS f' hf' w z hz.symm)
  have hX : (smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).mapDerivedCategory ⋙
        RF ⋙ smallEtaleDerivedAbelianStalk B S hS (geometricPointMap f.hom y) ≅
      G.inverse ⋙ smallEtaleDerivedAbelianStalk B S hS z :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight G.counitIso.symm _ ≪≫ Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft G.inverse d.lerayIso) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse
        (derivedSmallEtaleAbelianPushforwardStalkIso B S hS i hi z
          (geometricPointMap f.hom y) hxz)
  exact Functor.isoWhiskerRight hι _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E.inverse hX ≪≫
    (Functor.isoWhiskerRight hι _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E.inverse hW).symm

/-- **Stacks 0AEQ.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let
`i : Z ⟶ X` and `i' : W ⟶ Y` be closed immersions and let `f' : W ⟶ Z` be an integral
universally injective morphism making the square commute — in the source `W = f^{-1}Z` and `f'`
is the base change of `f`. Let `ȳ` be a geometric point of `Y` lying on `W` and let
`x̄ = f(ȳ)`. For an object `Q` of `D(Y_étale)` all of whose cohomology sheaves are supported on
`|W|`, the stalk at `x̄` of `Rf_*Q` is the stalk at `ȳ` of `Q`. -/
@[stacks 0AEQ "the comparison isomorphism, for a commutative (not necessarily cartesian) \
square and a geometric point of Y lifted to the closed subspace, on the two carried inputs \
0AEH part (1) and 015N bundled as DerivedPushforwardSquareData"]
def stalkDerivedPushforwardIso
    [RF.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ))]
    (d : DerivedPushforwardSquareData B S hS i hi i' hi' f' hf' hf'int hf'inj RF)
    (y : GeometricPoint B S hS Y.1) (w : GeometricPoint B S hS W.1)
    (hw : geometricPointMap i'.hom w = y) (Q : smallEtaleDerivedCategory.{u + 1} B S hS Y)
    (hQ : cohomologySupportedOn.{u + 1} B S hS Y
      (Set.range (pointsMap B S hS W.1 i'.hom)) Q) :
    (smallEtaleDerivedAbelianStalk B S hS (geometricPointMap f.hom y)).obj (RF.obj Q) ≅
      (smallEtaleDerivedAbelianStalk B S hS y).obj Q :=
  (derivedStalkIsoOnSupportedComplexes B S hS f i hi i' hi' f' hf' hf'int hf'inj hsq RF d
    y w hw).app ⟨Q, hQ⟩

/-- **Stacks 0AEQ: the comparison is natural.** The identification
`(Rf_*Q)_{x̄} ≅ Q_ȳ` is natural in the complex `Q` supported on `|W|`. -/
@[stacks 0AEQ "naturality of the comparison isomorphism in the supported complex"]
theorem stalkDerivedPushforwardIso_naturality
    [RF.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS Y) (ComplexShape.up ℤ))]
    (d : DerivedPushforwardSquareData B S hS i hi i' hi' f' hf' hf'int hf'inj RF)
    (y : GeometricPoint B S hS Y.1) (w : GeometricPoint B S hS W.1)
    (hw : geometricPointMap i'.hom w = y)
    {Q Q' : smallEtaleDerivedCategory.{u + 1} B S hS Y}
    (hQ : cohomologySupportedOn.{u + 1} B S hS Y
      (Set.range (pointsMap B S hS W.1 i'.hom)) Q)
    (hQ' : cohomologySupportedOn.{u + 1} B S hS Y
      (Set.range (pointsMap B S hS W.1 i'.hom)) Q') (g : Q ⟶ Q') :
    (smallEtaleDerivedAbelianStalk B S hS (geometricPointMap f.hom y)).map (RF.map g) ≫
        (stalkDerivedPushforwardIso B S hS f hfr i hi i' hi' f' hf' hf'int hf'inj hsq RF unit d
          y w hw Q' hQ').hom =
      (stalkDerivedPushforwardIso B S hS f hfr i hi i' hi' f' hf' hf'int hf'inj hsq RF unit d
          y w hw Q hQ).hom ≫
        (smallEtaleDerivedAbelianStalk B S hS y).map g :=
  (derivedStalkIsoOnSupportedComplexes B S hS f i hi i' hi' f' hf' hf'int hf'inj hsq RF d
    y w hw).hom.naturality (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) (ObjectProperty.homMk g)

end Main

end AlgebraicGeometry.Space

end
