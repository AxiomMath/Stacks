module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback

/-!
# The data of the derived Chow lemma for algebraic spaces

Let `X` be an algebraic space over a scheme `S` and `x ∈ |X|`. The derived Chow lemma
(Stacks 0CTR) produces an integer `n`, a closed subspace `Z ⊂ X ×_S ℙⁿ_S`, a point of `Z`, an
open `V ⊂ ℙⁿ_S` and an object `E` of `D(𝒪_{X ×_S ℙⁿ_S})` with five properties. This file bundles
those data and properties as `AlgebraicGeometry.Space.DerivedChowDatum`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedChow.product`: the algebraic space `X ×_S ℙⁿ_S`, with its two
  projections `p` and `q`.
* `AlgebraicGeometry.Space.DerivedChow.productOver`: the open subspace `X ×_S V` over an open
  immersion `v : V ⟶ ℙⁿ_S`.
* `AlgebraicGeometry.Space.DerivedChow.overOpen`: the open subspace `W = c⁻¹(V)` of `Z`, where
  `c : Z ⟶ ℙⁿ_S` is the second projection.
* `AlgebraicGeometry.Space.DerivedChowDatum`: the data and the five properties of Stacks 0CTR.

## Implementation notes

`ℙⁿ_S` is `AlgebraicGeometry.Space.projectiveSpaceSiteObj`, the scheme
`AlgebraicGeometry.projectiveSpaceOver n S` of Stacks 01NF read as an object of the site. That
needs the scheme to lie in the site, so the containment is part of the data of a datum: it is
produced, not assumed.

The closed subspace `Z` is given by a closed immersion `i : Z ⟶ X ×_S ℙⁿ_S`, and the open
subspace `V` by an open immersion `v : V ⟶ ℙⁿ_S`; a subspace is determined by such an immersion
up to unique isomorphism. Restriction of an object of `D(𝒪_{X ×_S ℙⁿ_S})` to the open `X ×_S V`
is the derived pullback along the open immersion. The point `z ∈ |Z|` with `z ∈ W` is recorded as
a point `w ∈ |W|`; its image in `|Z|` is the `z` of the source.

## References

* [Stacks Project, Tag 0CTR](https://stacks.math.columbia.edu/tag/0CTR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_Datum (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_Datum {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace DerivedChow

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an algebraic space over `S`, to the representable algebraic space
of the base. -/
abbrev toBase (X : AlgebraicSpaces B S hS) : X ⟶ schemeSpace (baseSiteObj B S hS) :=
  ObjectProperty.homMk ((isTerminal_yoneda_obj_base B S hS).from X.1)

/-- The algebraic space `X ×_S ℙⁿ_S`. -/
abbrev product (X : AlgebraicSpaces B S hS) (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S)) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (toBase B S hS X)
    (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP))

variable {B S hS}

/-- The first projection `p : X ×_S ℙⁿ_S ⟶ X`. -/
abbrev productFst (X : AlgebraicSpaces B S hS) (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S)) :
    product B S hS X n hP ⟶ X :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The second projection `q : X ×_S ℙⁿ_S ⟶ ℙⁿ_S`. -/
abbrev productSnd (X : AlgebraicSpaces B S hS) (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S)) :
    product B S hS X n hP ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP) :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The open subspace `X ×_S V` of `X ×_S ℙⁿ_S` over an open immersion `v : V ⟶ ℙⁿ_S`. -/
abbrev productOver (X : AlgebraicSpaces B S hS) (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
    {V : AlgebraicSpaces B S hS} (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (productSnd X n hP) v

/-- The open immersion `X ×_S V ⟶ X ×_S ℙⁿ_S`. -/
abbrev productOverι (X : AlgebraicSpaces B S hS) (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
    {V : AlgebraicSpaces B S hS} (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)) :
    productOver X n hP v ⟶ product B S hS X n hP :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The open subspace `W = c⁻¹(V)` of `Z`, for `i : Z ⟶ X ×_S ℙⁿ_S` and `c = q ∘ i`. -/
abbrev overOpen {X Z : AlgebraicSpaces B S hS} {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)}
    (i : Z ⟶ product B S hS X n hP) {V : AlgebraicSpaces B S hS}
    (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (i ≫ productSnd X n hP) v

/-- The inclusion `W ⟶ Z`. -/
abbrev overOpenι {X Z : AlgebraicSpaces B S hS} {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)}
    (i : Z ⟶ product B S hS X n hP) {V : AlgebraicSpaces B S hS}
    (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)) : overOpen i v ⟶ Z :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The restriction `c|_W : W ⟶ V` of the second projection of `Z`. -/
abbrev overOpenToOpen {X Z : AlgebraicSpaces B S hS} {n : ℕ}
    {hP : B.Contains (projectiveSpaceOver n S)} (i : Z ⟶ product B S hS X n hP)
    {V : AlgebraicSpaces B S hS} (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP)) :
    overOpen i v ⟶ V :=
  ObjectProperty.homMk (pullback.snd _ _)

end DerivedChow

open DerivedChow

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The data of the derived Chow lemma (Stacks 0CTR)** at a point `x` of an algebraic space `X`
over `S`: an `n ≥ 0`, a closed subspace `i : Z ⟶ X ×_S ℙⁿ_S`, a point `w` of `W = c⁻¹(V)`, an
open `V ⊂ ℙⁿ_S` and an object `E` of `D(𝒪_{X ×_S ℙⁿ_S})` such that

1. `i` is of finite presentation;
2. `c : Z ⟶ ℙⁿ_S` is a closed immersion over `V`;
3. the restriction of `b = p ∘ i : Z ⟶ X` to `W` is étale and sends `w` to `x`;
4. `E|_{X ×_S V} ≅ (b, c)_*𝒪_Z|_{X ×_S V}`;
5. `E` is pseudo-coherent and supported on `Z`. -/
structure DerivedChowDatum (X : AlgebraicSpaces B S hS) (x : points B S hS X.1) where
  /-- The dimension of the projective space. -/
  n : ℕ
  /-- `ℙⁿ_S` lies in the site. -/
  contains : B.Contains (projectiveSpaceOver n S)
  /-- The closed subspace `Z`. -/
  Z : AlgebraicSpaces B S hS
  /-- The closed immersion `(b, c) : Z ⟶ X ×_S ℙⁿ_S`. -/
  i : Z ⟶ product B S hS X n contains
  isClosedImmersion_i : IsClosedImmersion B S hS i.hom
  isFinitePresentation_i : IsFinitePresentation B S hS i.hom
  /-- The open `V ⊂ ℙⁿ_S`, given by an open immersion `v : V ⟶ ℙⁿ_S`. -/
  V : AlgebraicSpaces B S hS
  /-- The open immersion `v : V ⟶ ℙⁿ_S`. -/
  v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n contains)
  isOpenImmersion_v : IsOpenImmersion B S hS v.hom
  isClosedImmersion_overOpenToOpen : IsClosedImmersion B S hS (overOpenToOpen i v).hom
  isEtale_overOpen : IsEtale B S hS (overOpenι i v ≫ i ≫ productFst X n contains).hom
  /-- The point `w ∈ W`. -/
  w : points B S hS (overOpen i v).1
  pointsMap_w : pointsMap B S hS _ (overOpenι i v ≫ i ≫ productFst X n contains).hom w = x
  /-- The object `E` of `D(𝒪_{X ×_S ℙⁿ_S})`. -/
  E : DerivedCategory (Modules.{u, u} B S hS (product B S hS X n contains).1
    (product B S hS X n contains).2)
  restrictIso : Nonempty
    ((smallEtaleDerivedModulePullback B S hS (productOverι X n contains v)).obj E ≅
      (smallEtaleDerivedModulePullback B S hS (productOverι X n contains v)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureSheafPushforward B S hS i)))
  /-- `E` is pseudo-coherent. -/
  isPseudoCoherent_E :
    (smallEtaleRingedSite B S hS (product B S hS X n contains).1
      (product B S hS X n contains).2).IsPseudoCoherent E
  /-- The cohomology sheaves of `E` are supported on the image of `Z`. -/
  cohomologySupportedOn_E : CohomologySupportedOn B S hS (product B S hS X n contains).1
    (product B S hS X n contains).2 (Set.range (pointsMap B S hS Z.1 i.hom)) E

end AlgebraicGeometry.Space

end
