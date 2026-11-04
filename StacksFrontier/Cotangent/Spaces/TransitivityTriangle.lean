module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageULift
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangleDerived
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilon

/-!
# The transitivity triangle of the cotangent complex for morphisms of algebraic spaces

Let `p : W ⟶ X` and `f : X ⟶ Z` be morphisms of algebraic spaces over a scheme `S`. The
cotangent complex of a morphism of algebraic spaces (Stacks 08VD) is the cotangent complex of
the associated morphism of small étale ringed topoi, so Stacks 08V1 gives a distinguished
triangle

`Lp^* L_{X/Z} ⟶ L_{W/Z} ⟶ L_{W/X} ⟶ Lp^* L_{X/Z}[1]`

in `D(𝒪_W)`. This file produces it.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedToposHomULift`: the morphism of small étale ringed
  topoi `(W_étale, 𝒪_W) ⟶ (X_étale, 𝒪_X)` of `p` (Stacks 03G8) with both structure sheaves
  presented in the universe of the small étale sites, the universe in which `L_{W/X}` lives.
* `AlgebraicGeometry.Space.derivedPullbackULift`: the derived pullback `Lp^*` along it
  (Stacks 06YY).
* `AlgebraicGeometry.Space.transitivityUnit` and `AlgebraicGeometry.Space.transitivityCounit`:
  the two canonical arrows `Lp^* L_{X/Z} ⟶ L_{W/Z} ⟶ L_{W/X}`.
* `AlgebraicGeometry.Space.derivedPullbackCotangentComplexIso`: `Lp^* L_{X/Z}` is the base
  change `L_{p⁻¹𝒪_X/p⁻¹f⁻¹𝒪_Z} ⊗_{p⁻¹𝒪_X} 𝒪_W`.

## Main results

* `AlgebraicGeometry.Space.exists_distTriang_transitivity`: the triangle is distinguished.

## Implementation notes

The structure sheaf of `AlgebraicGeometry.Space.smallEtaleRingedTopos` has its sections in the
universe `u` of the schemes, one below the universe `u + 1` of the small étale sites, while the
cotangent complex is formed from the lift of the structure map,
`AlgebraicGeometry.Space.cotangentComplex`. The lifted morphism of ringed topoi has as underlying
morphism of topoi `AlgebraicGeometry.Space.smallToposMorphism`, the morphism of small étale topoi
of Stacks 03G2, part (3) at the universe of the sites, and as structure map the lift of that of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, read through the comparison
`AlgebraicGeometry.Space.smallEtaleInverseImageRingULiftIso` of the inverse images at the two
universes. Its cotangent complex is therefore `L_{W/X}` up to the square functoriality of the
cotangent complex (`CategoryTheory.Sheaf.squareCotangentComplexIso`), and Stacks 08V1 for
morphisms of ringed topoi, `AlgebraicGeometry.RingedToposHom.exists_distTriang_transitivity`,
applies to the lifted morphisms. The middle vertex is identified with `L_{W/Z}` through the
composition law of Stacks 03G8 at the universe of the structure rings,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`.

The derived categories are the standard models `HasDerivedCategory.standard`, the models the
derived pullback of Stacks 06YY is stated for.

## References

* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section LiftedHom

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of `f_small`, with both
structure sheaves presented in the universe of the small étale sites: the lift of the structure
map of `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, read through the comparison of the
inverse images at the two universes. -/
noncomputable def smallEtaleFSharpInverseImageULift :
    (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS f)).obj (smallEtaleStructureSheafULift B S hS Y) ⟶
      smallEtaleStructureSheafULift B S hS X :=
  (smallEtaleInverseImageRingULiftIso f).inv.app (smallEtaleRingedTopos B S hS Y).O ≫
    (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1)).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- **The morphism of small étale ringed topoi of a morphism of algebraic spaces, at the
universe of the sites** (Stacks 03G8). Its underlying morphism of topoi is the morphism of small
étale topoi of Stacks 03G2, part (3) for sheaves of sets valued in `Type (u + 1)`, and its
structure map is that of `AlgebraicGeometry.Space.smallEtaleRingedToposHom` with its sections
lifted. -/
noncomputable def smallEtaleRingedToposHomULift :
    RingedToposHom (smallEtaleRingedToposULift B S hS X) (smallEtaleRingedToposULift B S hS Y)
    where
  toToposHom := smallToposMorphism B S hS f
  fSharp := (commRingImageAdjunction (smallToposMorphism B S hS f)).homEquiv _ _
    (smallEtaleFSharpInverseImageULift f)

/-- The inverse-image form of the structure map of the lifted morphism of ringed topoi is the
lift of the structure map, read through the comparison of the inverse images. -/
theorem smallEtaleRingedToposHomULift_fSharpInverseImage :
    (smallEtaleRingedToposHomULift f).fSharpInverseImage =
      smallEtaleFSharpInverseImageULift f :=
  Equiv.symm_apply_apply _ _

/-- The cotangent complex of the lifted morphism of ringed topoi is the cotangent complex
`L_{X/Y}` of Stacks 08VD: their structure maps differ by the comparison of the inverse images
at the two universes, an isomorphism of the base rings. -/
noncomputable def smallEtaleRingedToposHomULift_cotangentComplexIso :
    (smallEtaleRingedToposHomULift f).cotangentComplex ≅ cotangentComplex B S hS f :=
  Sheaf.squareCotangentComplexIso.{u + 1, u, u} (J := SmallEtale.topology B S hS X.1)
      (a := (smallEtaleInverseImageRingULiftIso f).inv.app (smallEtaleRingedTopos B S hS Y).O)
      (b := 𝟙 _)
      (by rw [smallEtaleRingedToposHomULift_fSharpInverseImage, Category.comp_id]; rfl) ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

end LiftedHom

section Transitivity

variable {W X Z : AlgebraicSpaces B S hS} (p : W ⟶ X) (f : X ⟶ Z)

/-- The base ring of the tower of the composite `p ≫ f` is the lift of `(p ≫ f)⁻¹𝒪_Z`: the
iterated inverse image at the universe of the sites is compared with the iterated inverse image
at the universe of the structure rings, and the latter with the inverse image along the composite
by Stacks 03G8. -/
noncomputable def towerBaseULiftIso :
    (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS p)).obj
        ((inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS f)).obj (smallEtaleStructureSheafULift B S hS Z)) ≅
      (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).obj
        ((smallEtaleInverseImageRing B S hS (p ≫ f)).obj (smallEtaleRingedTopos B S hS Z).O) :=
  (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
      (smallToposMorphism B S hS p)).mapIso
      ((smallEtaleInverseImageRingULiftIso f).app (smallEtaleRingedTopos B S hS Z).O).symm ≪≫
    ((smallEtaleInverseImageRingULiftIso p).app _).symm ≪≫
    (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).mapIso
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p f).app
        (smallEtaleRingedTopos B S hS Z).O)

/-- The composite structure map of the tower of the lifted morphisms is the lift of the structure
map of `p ≫ f`, across `AlgebraicGeometry.Space.towerBaseULiftIso`. -/
theorem towerBaseMap_comp_fSharpInverseImage_ulift :
    (inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
        (smallToposMorphism B S hS p)).map (smallEtaleFSharpInverseImageULift f) ≫
        smallEtaleFSharpInverseImageULift p =
      (towerBaseULiftIso p f).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS W.1)).map
          (smallEtaleRingedToposHom B S hS (p ≫ f)).fSharpInverseImage := by
  have hnat := (smallEtaleInverseImageRingULiftIso p).inv.naturality
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage
  have hcomp := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS p f
  simp only [Functor.comp_map] at hnat
  simp only [smallEtaleFSharpInverseImageULift, towerBaseULiftIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hnat, ← Functor.map_comp, ← Functor.map_comp, ← hcomp]
  rfl

/-- The cotangent complex of the composite of the lifted morphisms of ringed topoi is
`L_{W/Z}`, the cotangent complex of `p ≫ f` of Stacks 08VD. -/
noncomputable def compCotangentComplexULiftIso :
    ((smallEtaleRingedToposHomULift f).comp (smallEtaleRingedToposHomULift p)).cotangentComplex ≅
      cotangentComplex B S hS (p ≫ f) :=
  RingedToposHom.compCotangentComplexIso.{u, u + 1, u, u, u + 1} _ _ ≪≫
    Sheaf.squareCotangentComplexIso.{u + 1, u, u} (J := SmallEtale.topology B S hS W.1)
      (a := (towerBaseULiftIso p f).hom) (b := 𝟙 _)
      (by
        refine (Category.comp_id _).trans ?_
        rw [← towerBaseMap_comp_fSharpInverseImage_ulift,
          ← smallEtaleRingedToposHomULift_fSharpInverseImage,
          ← smallEtaleRingedToposHomULift_fSharpInverseImage]
        rfl) ≪≫
    SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
  CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

/-- Sheafification of abelian groups on the small étale site of an algebraic space at the
universe of the site, in the spelling of the lifted small étale ringed topos. -/
local instance (priority := high) hasSheafify_smallEtaleRingedToposULift
    (Y : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleRingedToposULift B S hS Y).J AddCommGrpCat.{u + 1} :=
  hasSheafify_smallEtaleRingedTopos B S hS Y

/-- The local isomorphisms of presheaves of abelian groups on the small étale site of an
algebraic space are the locally bijective maps, in the spelling of the lifted small étale ringed
topos. -/
local instance (priority := high) wEqualsLocallyBijective_smallEtaleRingedToposULift
    (Y : AlgebraicSpaces B S hS) :
    (smallEtaleRingedToposULift B S hS Y).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  wEqualsLocallyBijective_smallEtaleRingedTopos B S hS Y

/-- The derived pullback `Lp^* : D(𝒪_X) ⥤ D(𝒪_W)` along a morphism of algebraic spaces
(Stacks 06YY), on modules over the structure sheaves presented in the universe of the small
étale sites. -/
noncomputable abbrev derivedPullbackULift :
    DerivedCategory (smallEtaleModulesULift B S hS X) ⥤
      DerivedCategory (smallEtaleModulesULift B S hS W) :=
  RingedToposHom.derivedPullback.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHomULift p)

/-- The first arrow `Lp^* L_{X/Z} ⟶ L_{W/Z}` of the transitivity triangle of Stacks 08V1 for the
morphisms `W ⟶ X ⟶ Z` of algebraic spaces. -/
noncomputable def transitivityUnit :
    (derivedPullbackULift p).obj (cotangentComplexDerived B S hS f) ⟶
      cotangentComplexDerived B S hS (p ≫ f) :=
  (derivedPullbackULift p).map
      (DerivedCategory.Q.map (smallEtaleRingedToposHomULift_cotangentComplexIso f).inv) ≫
    RingedToposHom.transitivityUnit.{u, u + 1, u, u, u + 1} (smallEtaleRingedToposHomULift f)
      (smallEtaleRingedToposHomULift p) ≫
    DerivedCategory.Q.map (compCotangentComplexULiftIso p f).hom

/-- The second arrow `L_{W/Z} ⟶ L_{W/X}` of the transitivity triangle of Stacks 08V1 for the
morphisms `W ⟶ X ⟶ Z` of algebraic spaces. -/
noncomputable def transitivityCounit :
    cotangentComplexDerived B S hS (p ≫ f) ⟶ cotangentComplexDerived B S hS p :=
  DerivedCategory.Q.map (compCotangentComplexULiftIso p f).inv ≫
    RingedToposHom.transitivityCounit.{u, u + 1, u, u, u + 1} (smallEtaleRingedToposHomULift f)
      (smallEtaleRingedToposHomULift p) ≫
    DerivedCategory.Q.map (smallEtaleRingedToposHomULift_cotangentComplexIso p).hom

/-- **Stacks 08V1 for morphisms of algebraic spaces.** For morphisms `p : W ⟶ X` and
`f : X ⟶ Z` of algebraic spaces over `S`, the canonical triangle

`Lp^* L_{X/Z} ⟶ L_{W/Z} ⟶ L_{W/X} ⟶ Lp^* L_{X/Z}[1]`

is distinguished in `D(𝒪_W)`. It is the transitivity triangle of the morphisms of small étale
ringed topoi of `p` and `f`, read through the identifications of their cotangent complexes with
those of Stacks 08VD. -/
theorem exists_distTriang_transitivity :
    ∃ δ : cotangentComplexDerived B S hS p ⟶
        ((derivedPullbackULift p).obj (cotangentComplexDerived B S hS f))⟦(1 : ℤ)⟧,
      Triangle.mk (transitivityUnit p f) (transitivityCounit p f) δ ∈
        distTriang (DerivedCategory (smallEtaleModulesULift B S hS W)) := by
  obtain ⟨δ, hT⟩ := RingedToposHom.exists_distTriang_transitivity.{u, u + 1, u, u, u + 1}
    (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p)
  let e₁ := (derivedPullbackULift p).mapIso
    (DerivedCategory.Q.mapIso (smallEtaleRingedToposHomULift_cotangentComplexIso f))
  let e₂ := DerivedCategory.Q.mapIso (compCotangentComplexULiftIso p f)
  let e₃ := DerivedCategory.Q.mapIso (smallEtaleRingedToposHomULift_cotangentComplexIso p)
  refine ⟨e₃.inv ≫ δ ≫ e₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_
  · simp [e₁, e₂, transitivityUnit]
  · simp [e₂, e₃, transitivityCounit]
  · simp [e₁, e₃, ← Functor.map_comp]

/-- `Lp^* L_{X/Z}` is the base change `L_{p⁻¹𝒪_X/p⁻¹f⁻¹𝒪_Z} ⊗_{p⁻¹𝒪_X} 𝒪_W` of the cotangent
complex of the inverse image of the structure map of `f`, the inverse images being those of the
morphism of small étale topoi at the universe of the sites: `L_{X/Z}` is a bounded above complex
of flat modules, so `Lp^*` is computed on it degreewise (Stacks 06YY), and the degreewise
pullback is that base change by Stacks 08SV. -/
noncomputable def derivedPullbackCotangentComplexIso :
    (derivedPullbackULift p).obj (cotangentComplexDerived B S hS f) ≅
      DerivedCategory.Q.obj (Sheaf.baseChangedCotangentComplex.{u + 1, u, u}
        (SmallEtale.topology B S hS W.1)
        (RingedToposHom.towerBaseMap.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
          (smallEtaleRingedToposHomULift f) (smallEtaleRingedToposHomULift p))
        (smallEtaleRingedToposHomULift p).fSharpInverseImage) :=
  (derivedPullbackULift p).mapIso
      (DerivedCategory.Q.mapIso (smallEtaleRingedToposHomULift_cotangentComplexIso f)).symm ≪≫
    RingedToposHom.derivedPullbackCotangentComplexIso.{u, u + 1, u, u, u + 1, u, u, u + 1, u + 1}
      _ _

end Transitivity

end AlgebraicGeometry.Space

end
