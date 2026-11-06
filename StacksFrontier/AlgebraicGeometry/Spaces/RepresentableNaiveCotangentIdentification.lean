module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentEtaleLocalisation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SheafificationOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCocontinuousRestriction

/-!
# Stacks 0D0X for algebraic spaces representable by schemes

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S`, and assume that `X`
and `Y` are representable by schemes `X₀` and `Y₀`: there are objects `U`, `V` of the big fppf
site of `S` with underlying schemes `X₀`, `Y₀` and isomorphisms `α : h_U ≅ X`, `β : h_V ≅ Y` of
algebraic spaces.  Let `f₀ : U ⟶ V` be the morphism corresponding to `f`
(`AlgebraicGeometry.Space.representingMorphism`, by the Yoneda lemma).  Stacks 0D0X identifies
`NL_{X/Y}` with `ε^*NL_{X₀/Y₀}` in `D(𝒪_X)`, for `ε` the comparison morphism of Stacks 08H7
(Derived Categories of Spaces, Section 071P) from the small étale site of the scheme `X₀` to its
Zariski site.

`AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentIdentification` proves this when
`X = h_U` and `Y = h_V` on the nose.  The morphism `ε` of Section 071P is a morphism out of the
small étale site of the *scheme* `X₀`, which is the small étale site of `h_U`, so for an arbitrary
representable `X` the comparison takes place after identifying `X_étale` with `(X₀)_étale`
along `α`: postcomposition of étale charts with `α`
(`AlgebraicGeometry.Space.representingChartFunctor`, the functor of Stacks 03LP for the
isomorphism `α`) is an equivalence of sites `(X₀)_étale ≌ X_étale`, and restriction along it
carries `𝒪_X`-modules to `𝒪_{X₀}`-modules once the scalars are changed along the identification
`𝒪_{X₀} ≅ α⁻¹𝒪_X` of Stacks 03LV.  This file proves the statement in that form.

The identification of the restriction of `NL_{X/Y}` with `NL_{h_U/h_V}` is the composite of

* `Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso`: the naive cotangent complex
  commutes with restriction along a continuous and cocontinuous functor of sites, so the
  restriction of `NL_{X/Y} = NL_{𝒪_X / f⁻¹𝒪_Y}` is the naive cotangent complex of the restricted
  structure map;
* `Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare`: the restricted structure map is
  identified with the structure map `h_{f₀}⁻¹𝒪_{h_V} ⟶ 𝒪_{h_U}` of `h_{f₀}` by two isomorphisms of
  sheaves of rings, restriction along `α` being the inverse image along `α` (Stacks 03LQ), the
  composition law of Stacks 03G8 for `α ≫ f = h_{f₀} ≫ β` and Stacks 03LV for `α` and `β`.

## Main definitions

* `AlgebraicGeometry.Space.representingChartFunctor`: the identification of the small étale site
  of `h_U` with that of `X`.
* `AlgebraicGeometry.Space.representingMorphism`: the morphism `f₀ : U ⟶ V` corresponding to `f`.
* `AlgebraicGeometry.Space.representingNaiveCotangentComplexIso`: `NL_{h_U/h_V}` is the
  restriction of `NL_{X/Y}` to the small étale site of `X₀`.

## Main results

* `AlgebraicGeometry.Space.quasiIso_representableEpsilonNaiveCotangentIdentification`:
  **Stacks 0D0X**.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 071P](https://stacks.math.columbia.edu/tag/071P)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasWeakSheafify_commRingCat_smallEtale

section

variable {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
  (α : representedAlgebraicSpace B S hS U ≅ X)

/-- **The identification `(X₀)_étale ≌ X_étale`** for an algebraic space `X` represented by `U`
through `α : h_U ≅ X`: postcomposition of étale charts of `h_U` with `α`, the functor of
Stacks 03LP for the isomorphism `α`. -/
def representingChartFunctor :
    SmallEtale B S hS (representedAlgebraicSpace B S hS U).1 ⥤ SmallEtale B S hS X.1 :=
  smallEtalePostcomp B S hS α.hom (isEtale_hom_of_iso B S hS α)

/-- The identification of small étale sites is continuous (Stacks 03LP). -/
instance representingChartFunctor_isContinuous :
    (representingChartFunctor B S hS α).IsContinuous
      (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
      (SmallEtale.topology B S hS X.1) :=
  smallEtalePostcomp_isContinuous B S hS α.hom (isEtale_hom_of_iso B S hS α)

/-- The identification of small étale sites is cocontinuous (Stacks 03LP). -/
instance representingChartFunctor_isCocontinuous :
    (representingChartFunctor B S hS α).IsCocontinuous
      (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
      (SmallEtale.topology B S hS X.1) :=
  smallEtalePostcomp_isCocontinuous B S hS α.hom (isEtale_hom_of_iso B S hS α)

/-- The identification of small étale sites is a left adjoint, the right adjoint being base
change along `α`. -/
instance representingChartFunctor_isLeftAdjoint :
    (representingChartFunctor B S hS α).IsLeftAdjoint :=
  have : IsIso α.hom.hom := (ObjectProperty.ι _).map_isIso α.hom
  smallEtalePostcomp_isLeftAdjoint B S hS α.hom (isEtale_hom_of_iso B S hS α)
    (Functor.relativelyRepresentable.of_isIso (F := yoneda) α.hom.hom)

/-- Restriction of presheaves of commutative rings along the identification of small étale sites
has a right adjoint: the right Kan extension along it exists pointwise, the categories of
structured arrows having initial objects since the identification is a left adjoint. -/
instance representingChartFunctor_hasPointwiseRightKanExtension
    (F : (SmallEtale B S hS (representedAlgebraicSpace B S hS U).1)ᵒᵖ ⥤ CommRingCat.{u}) :
    (representingChartFunctor B S hS α).op.HasPointwiseRightKanExtension F := fun Y ↦
  have := isRightAdjoint_iff_hasInitial_structuredArrow.mp
    (inferInstance : (representingChartFunctor B S hS α).op.IsRightAdjoint) Y
  hasLimit_of_domain_hasInitial

/-- **Stacks 03LQ for sheaves of commutative rings along `α`.**  The inverse image along the
morphism of small étale topoi of `α` is restriction along the identification of small étale
sites: the comparison of Stacks 03LQ on sheaves of sets, transported to sheaves of commutative
rings, followed by the identification of that transport with restriction. -/
def representingInverseImageCommRingIso :
    smallEtaleInverseImageRing B S hS α.hom ≅
      (representingChartFunctor B S hS α).sheafPushforwardContinuous
        CommRingCat.{u} (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
        (SmallEtale.topology B S hS X.1) :=
  -- the instance `restrictionCommRingNatIso` uses; instance search for it times out here
  letI : PreservesFiniteProducts ((representingChartFunctor B S hS α).sheafPushforwardContinuous
      (Type u) (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
      (SmallEtale.topology B S hS X.1)) :=
    instPreservesFiniteProductsOfPreservesFiniteLimits _
  letI : PreservesFiniteProducts (smallEtaleRingedToposHom B S hS α.hom).toToposHom.inverseImage :=
    letI := (smallEtaleRingedToposHom B S hS α.hom).toToposHom.preservesFiniteLimits
    instPreservesFiniteProductsOfPreservesFiniteLimits _
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1} _
      (Φ' := (representingChartFunctor B S hS α).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
        (SmallEtale.topology B S hS X.1))
      (smallToposMorphismTypeU_inverseImageIso B S hS α.hom (isEtale_hom_of_iso B S hS α)) ≪≫
    restrictionCommRingNatIso.{u, u, u + 1, u, u + 1} _ _ _

/-- `𝒪_X` restricted to the small étale site of `X₀` is `𝒪_{X₀}`: restriction is inverse image
along `α`, and `α⁻¹𝒪_X = 𝒪_{h_U}` by Stacks 03LV. -/
def representingStructureSheafIso :
    ((representingChartFunctor B S hS α).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
        (SmallEtale.topology B S hS X.1)).obj (smallEtaleRingedTopos B S hS X).O ≅
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O :=
  ((representingInverseImageCommRingIso B S hS α).app _).symm ≪≫
    etaleInverseImageStructureSheafIso B S hS α.hom (isEtale_hom_of_iso B S hS α)

variable {Y : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
  (β : representedAlgebraicSpace B S hS V ≅ Y)

/-- **The morphism `f₀ : U ⟶ V` corresponding to `f`**, for `X` and `Y` represented by `U` and
`V` through `α` and `β`: the preimage under the Yoneda embedding of `h_U ≅ X ⟶ Y ≅ h_V`. -/
def representingMorphism (f : X ⟶ Y) : U ⟶ V :=
  yoneda.preimage (α.hom.hom ≫ f.hom ≫ β.inv.hom)

/-- `f₀` corresponds to `f`: the square `α ≫ f = h_{f₀} ≫ β` commutes. -/
theorem comp_eq_representedSpaceMap_representingMorphism (f : X ⟶ Y) :
    α.hom ≫ f = representedSpaceMap B S hS (representingMorphism B S hS α β f) ≫ β.hom := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, representingMorphism, schemeSpaceMap_hom,
    Functor.map_preimage, Category.assoc, ObjectProperty.isoInv_hom_id_hom, Category.comp_id]

variable {f : X ⟶ Y} {φ : U ⟶ V}

/-- The base ring `f⁻¹𝒪_Y` restricted to the small étale site of `X₀` is `h_φ⁻¹𝒪_{h_V}`, for a
morphism `φ : U ⟶ V` making `α ≫ f = h_φ ≫ β` commute: restriction is inverse image along `α`,
and `α⁻¹f⁻¹𝒪_Y = h_φ⁻¹𝒪_{h_V}` by the composition law of Stacks 03G8 and Stacks 03LV for `β`
(`AlgebraicGeometry.Space.etaleSquareBaseRingIso`). -/
def representingBaseRingIso (h : α.hom ≫ f = representedSpaceMap B S hS φ ≫ β.hom) :
    ((representingChartFunctor B S hS α).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
        (SmallEtale.topology B S hS X.1)).obj
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O) ≅
      (smallEtaleInverseImageRing B S hS (representedSpaceMap B S hS φ)).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O :=
  ((representingInverseImageCommRingIso B S hS α).app _).symm ≪≫
    etaleSquareBaseRingIso B S hS h (isEtale_hom_of_iso B S hS β)

/-- The two identifications of sheaves of rings carry the structure map of `h_φ` to the
restriction of the structure map of `f`. -/
theorem fSharpInverseImage_comp_representingStructureSheafIso_inv
    (h : α.hom ≫ f = representedSpaceMap B S hS φ ≫ β.hom) :
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage ≫
        (representingStructureSheafIso B S hS α).inv =
      (representingBaseRingIso B S hS α β h).inv ≫
        ((representingChartFunctor B S hS α).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
          (SmallEtale.topology B S hS X.1)).map
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  simp only [representingBaseRingIso, representingStructureSheafIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc, etaleInverseImageStructureSheafIso_hom]
  rw [← etaleSquareBaseRingIso_fSharpInverseImage B S hS h (isEtale_hom_of_iso B S hS β),
    ← Category.assoc, ← NatTrans.naturality, Category.assoc]

attribute [local instance] abelianRepresentedSmallEtaleModules'

/-- **`NL_{h_U/h_V}` is `NL_{X/Y}` read on the small étale site of `X₀`**, for `α ≫ f = h_φ ≫ β`:
the restriction of `NL_{X/Y}` along the identification of small étale sites, with its scalars
changed along `𝒪_{X₀} ≅ α⁻¹𝒪_X`.  It is the canonical chain map of Stacks 08TX for the square
of the two identifications of sheaves of rings, followed by the inverse of the identification of
the restriction of a naive cotangent complex with the naive cotangent complex of the
restriction. -/
def representingNaiveCotangentComplexIso
    (h : α.hom ≫ f = representedSpaceMap B S hS φ ≫ β.hom) :
    representedSpaceNaiveCotangentComplex B S hS φ ≅
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
          (underlyingRingHomOfSite.{u, u + 1, u}
            (representingStructureSheafIso B S hS α).inv)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((Stacks.Sites.Conormal.moduleSheafRestriction.{u + 1}
            (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
            (SmallEtale.topology B S hS X.1) (representingChartFunctor B S hS α)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentComplex B S hS f)) :=
  Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare.{u, u + 1, u, u}
      (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1) _ _ _ _ _ _
      (representingBaseRingIso B S hS α β h).symm (representingStructureSheafIso B S hS α).symm
      (fSharpInverseImage_comp_representingStructureSheafIso_inv B S hS α β h) ≪≫
    ((_root_.SheafOfModules.restrictScalars.{u + 1}
          (underlyingRingHomOfSite.{u, u + 1, u}
            (representingStructureSheafIso B S hS α).inv)).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso.{u, u, u + 1, u, u + 1, u}
        (SmallEtale.topology B S hS (representedAlgebraicSpace B S hS U).1)
        (SmallEtale.topology B S hS X.1) (representingChartFunctor B S hS α)
        ((smallEtaleInverseImageRing B S hS f).obj (smallEtaleRingedTopos B S hS Y).O)
        (smallEtaleRingedTopos B S hS X).O
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).symm

/-- **Stacks 0D0X.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `X` and `Y`
representable by schemes `X₀` and `Y₀`, through `α : h_U ≅ X` and `β : h_V ≅ Y` for objects `U`,
`V` of the big fppf site of `S` with underlying schemes `X₀`, `Y₀`, and let `f₀ : X₀ ⟶ Y₀` be the
morphism of schemes corresponding to `f` (`AlgebraicGeometry.Space.representingMorphism`).  Let
`ε : ((X₀)_étale, 𝒪) ⟶ ((X₀)_Zar, 𝒪_{X₀})` be the comparison morphism of Stacks 08H7.  Then the
canonical map

`ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}`

— the termwise pullback along `ε` of (the universe lift of) `NL_{X₀/Y₀}` of Stacks 0D0H,
followed by the map of Stacks 08TX of the square of Stacks 08GH into `NL_{h_U/h_V}`, followed by
the identification of `NL_{h_U/h_V}` with `NL_{X/Y}` of Stacks 0D0V read on `(X₀)_étale` through
the identification `(X₀)_étale ≌ X_étale` given by `α`
(`AlgebraicGeometry.Space.representingNaiveCotangentComplexIso`) — is a quasi-isomorphism, so
it identifies `NL_{X/Y}` with `ε^*NL_{X₀/Y₀}` in `D(𝒪_X)`. -/
@[stacks 0D0X "the canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` is a quasi-isomorphism, i.e. the \
canonical identification `NL_{X/Y} = ε^*NL_{X₀/Y₀}` in `D(O_X)`, for an arbitrary morphism \
`f : X ⟶ Y` of algebraic spaces with `X ≅ h_U`, `Y ≅ h_V` representable by schemes, `NL_{X/Y}` \
read on the small étale site of `X₀` through the identification `(X₀)_étale ≌ X_étale` that \
the representing isomorphism gives"]
theorem quasiIso_representableEpsilonNaiveCotangentIdentification (f : X ⟶ Y) :
    QuasiIso ((((representedEpsilonModulePullback B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (representedZariskiNaiveCotangentComplexIso B S hS
          (representingMorphism B S hS α β f)).inv ≫
      representedEpsilonNaiveCotangentMap B S hS (representingMorphism B S hS α β f)) ≫
        (representingNaiveCotangentComplexIso B S hS α β
          (comp_eq_representedSpaceMap_representingMorphism B S hS α β f)).hom) := by
  have := quasiIso_representedEpsilonNaiveCotangentMap B S hS (representingMorphism B S hS α β f)
  infer_instance

end

end AlgebraicGeometry.Space

end
