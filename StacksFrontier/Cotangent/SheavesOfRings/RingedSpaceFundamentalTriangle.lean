module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# The fundamental triangle of the cotangent complex of morphisms of ringed spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. On the site of open subsets of
`X` the three structure maps of `f`, of `g ∘ f` and of `g` assemble into a tower
`(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings, whose two cotangent complexes
over the ends are `L_{X/Z}` and `L_{X/Y}`. The fundamental triangle of the tower is therefore
the triangle of Tag 08T4.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap` is the canonical homomorphism
  `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y` of sheaves of rings on `X` filling in the middle of the tower.
* `Stacks.Sheaves.RingedSpaceCotangent.baseChangedCotangentComplex` is the first vertex
  `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X` of the triangle of the tower.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange` and
  `Stacks.Sheaves.RingedSpaceCotangent.cotangentChangeOfBase` are the two displayed arrows
  `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z}` and `L_{X/Z} ⟶ L_{X/Y}`.
* `Stacks.Sheaves.RingedSpaceCotangent.degreewisePullbackCotangentComplex` is the degreewise
  pullback `f^*L_{Y/Z}` of the cotangent complex of `g`.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap_comp`: the structure map of `g ∘ f`
  is the composite of `baseStructureMap` with the structure map of `f`, so the tower is a
  tower over `L_{X/Z}`.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_comp_eq`: consequently the cotangent
  complex of the tower's composite is `L_{X/Z}` on the nose.
* `Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_of_shortExact`: the triangle
  `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ ⋯` on the two canonical
  arrows is distinguished in `D(𝒪_X)`, under the one hypothesis Tag 08SZ carries.
* `Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_degreewisePullback_of_shortExact`:
  **Tag 08T4** with the first vertex the degreewise pullback `f^*L_{Y/Z}`, under two
  hypotheses: the short exact sequence Tag 08SZ carries, and the identification of
  `f^*L_{Y/Z}` with the first vertex of the tower's triangle supplied by Tag 08SV.
* `Stacks.Sheaves.RingedSpaceCotangent.isIso_derivedPullbackComparison_cotangentComplex`: if
  `L_{Y/Z}` is K-flat then the canonical comparison `Lf^*L_{Y/Z} ⟶ f^*L_{Y/Z}` of Tag 06YJ is
  invertible, so the first vertex of that triangle is then `Lf^*L_{Y/Z}`.

## What is proved and what is not

Tag 08T4 asserts the existence of a canonical distinguished triangle

`Lf^*L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ Lf^*L_{Y/Z}[1]`

in `D(𝒪_X)`. The tower and its two displayed arrows are constructed here unconditionally: the
second arrow is the change-of-base-ring map of Tag 08SZ between `L_{X/Z}` and `L_{X/Y}` with no
identification intervening, and the first is the base-change arrow of Tag 08SZ read on `L_{X/Z}`
through the proved equality `cotangentComplex_comp_eq`. Nothing is chosen in either: the tower
itself is canonical, `baseStructureMap` being the adjunct of `g^♯` followed by the unit of
`f⁻¹ ⊣ f_*`, and `eqToHom` of an equality of objects does not depend on its proof.

**Distinguishedness is not proved unconditionally**, and the identification of the first vertex
with the pullback of `L_{Y/Z}` is not proved at all. Two hypotheses are carried, and a third
input — K-flatness — is what separates the degreewise pullback from the derived one.

* The short exact sequence of Tag 08SD at the level of sheaves of rings, in exactly the shape
  `CategoryTheory.Sheaf.exists_distTriang_cotangentComplexDerived_of_shortExact` carries it;
  see the "What is proved and what is not" section of
  `StacksFrontier/Cotangent/SheavesOfRings/FundamentalTriangle.lean` for why none of the three
  inputs of the source's proof of Tag 08SZ (Tags 08SD, 08SE and the isomorphism of 08SY) is
  available for sheaves of rings in this library.
* The identification `f^*L_{Y/Z} ≅ L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X` of Tag 08SV. The
  library's Tag 08SV, `CategoryTheory.Sheaf.inverseImageCotangentComplexIso`, is stated for a
  `CategoryTheory.MorphismOfTopoi`, and this library has no construction of a morphism of topoi
  out of a morphism of ringed spaces, nor a comparison of `(g ∘ f)⁻¹𝒪_Z` with `f⁻¹g⁻¹𝒪_Z`
  through which that Tag 08SV could be read on the tower used here.

The gap between the degreewise pullback `f^*L_{Y/Z}`, which is the first vertex of the triangle
proved here, and the derived pullback `Lf^*L_{Y/Z}` of the source is exactly one flatness
hypothesis, and it is a hypothesis this library can state: K-flatness of `L_{Y/Z}`, the named
predicate `Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex`. Under it the canonical comparison
`Lf^*L_{Y/Z} ⟶ f^*L_{Y/Z}` of Tag 06YJ is invertible, by
`isIso_derivedPullbackComparison_cotangentComplex` below, which is an instance of the unconditional
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`. That
K-flatness is the sheaf-level form of the source's observation that the terms of the cotangent
complex are locally free, and it is not proved for `L_{Y/Z}` in this library.

The first vertex of the triangle of Tag 08SZ carries the degreewise, not the derived, tensor
product, which is the same deviation seen from the other side.

## Implementation notes

The tower is taken in the composite spelling `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` rather than the
iterated spelling `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/NaiveCotangentCompositionTriangle.lean`. In the
composite spelling the second and third vertices of the triangle of Tag 08SZ are `L_{X/Z}` and
`L_{X/Y}` with no comparison of inverse images intervening, which is what Tag 08T4 asserts;
the price is that the identification of the first vertex, which is carried anyway, also absorbs
that comparison.

A sheaf of `𝒪_X`-modules has two definitionally equal spellings of its ring sheaf, that of
`AlgebraicGeometry.structureSheafRing` and that of
`CategoryTheory.Sheaf.targetModules`; as in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpace.lean` the declarations below are stated in the
first, and `HasDerivedCategory.standard` is a local instance so that both spellings carry the
same derived category.

Everything is at `AlgebraicGeometry.RingedSpace.{u, u}`; see the module docstring of
`StacksFrontier/Topology/Sheaves/Functors/Module/RingedSpace.lean` for why that is forced.

## References

* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the triangle for a
  tower of sheaves of rings.
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV), the inverse image of
  the cotangent complex.
* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), the cotangent complex
  of a morphism of ringed spaces.
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials
  (sheafAdjunction structureSheafMap structureSheafMap_comp inverseImageSheaf
    inverseImageStructureMap homEquiv_inverseImageStructureMap)

universe u t

namespace Stacks.Sheaves.RingedSpaceCotangent

/-- `𝒪_X`, typed as a sheaf of commutative rings on the site of open subsets of `X` rather than
as a sheaf on the space `X`. The two types are definitionally equal; only in this one is the
site, and with it every universe, written out. -/
def structureSheafOfSite (X : RingedSpace.{u, u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  X.sheaf

/-- The category of sheaves of `𝒪_X`-modules, spelled as the target modules of a homomorphism
of sheaves of rings on the site of open subsets of `X`. This is the same category as
`SheafOfModules (structureSheafRing X)`, in the spelling in which the
triangulated structure of the derived category of the triangle of Tag 08SZ is stated. -/
abbrev structureModules (X : RingedSpace.{u, u}) :=
  CategoryTheory.Sheaf.targetModules.{u, u, u} (Opens.grothendieckTopology X.carrier)
    (structureSheafOfSite X)

variable {X Y Z : RingedSpace.{u, u}}

/-! ## The tower of inverse images -/

/-- The canonical homomorphism `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y` of sheaves of commutative rings on `X`:
the adjunct, under `(g ∘ f)⁻¹ ⊣ (g ∘ f)_*`, of `g^♯ : 𝒪_Z ⟶ g_*𝒪_Y` followed by `g_*` of the
unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y`. -/
def baseStructureMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseImageSheaf (f ≫ g) ⟶ inverseImageSheaf f :=
  ((sheafAdjunction (f ≫ g)).homEquiv Z.sheaf (inverseImageSheaf f)).symm
    (structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      ((sheafAdjunction f).unit.app Y.sheaf))

/-- **Stacks Project, Tag 08T4**, the tower. The structure map of `g ∘ f` factors through the
structure map of `f` by `baseStructureMap`, so that `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` is a tower
of sheaves of commutative rings on `X` whose composite is the structure map of `g ∘ f`. -/
@[stacks 08T4 "the canonical tower of inverse images, whose fundamental triangle is the \
  triangle of this tag"]
theorem baseStructureMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseStructureMap f g ≫ inverseImageStructureMap f = inverseImageStructureMap (f ≫ g) := by
  have hunit := homEquiv_inverseImageStructureMap f
  rw [Adjunction.homEquiv_unit] at hunit
  have key : (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((sheafAdjunction f).unit.app Y.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ g).hom.base).map
        (inverseImageStructureMap f) =
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (structureSheafMap f) :=
    (Functor.map_comp _ _ _).symm.trans (congrArg _ hunit)
  have key₂ : (structureSheafMap g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        ((sheafAdjunction f).unit.app Y.sheaf)) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ g).hom.base).map
        (inverseImageStructureMap f) =
      structureSheafMap (f ≫ g) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => structureSheafMap g ≫ m) key).trans (structureSheafMap_comp f g).symm)
  exact ((sheafAdjunction (f ≫ g)).homEquiv_naturality_right_symm _
    (inverseImageStructureMap f)).symm.trans
      (congrArg (fun m => ((sheafAdjunction (f ≫ g)).homEquiv Z.sheaf X.sheaf).symm m) key₂)

/-- The cotangent complex of the composite of the tower is `L_{X/Z}`. -/
theorem cotangentComplex_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.Sheaf.cotangentComplex (Opens.grothendieckTopology X.carrier)
        (baseStructureMap f g ≫ inverseImageStructureMap f) :
      CochainComplex (structureModules X) ℤ) = cotangentComplex (f ≫ g) :=
  congrArg (fun k => CategoryTheory.Sheaf.cotangentComplex
    (Opens.grothendieckTopology X.carrier) k) (baseStructureMap_comp f g)

/-- The cotangent complex of the composite of the tower is `L_{X/Z}`. -/
def cotangentComplexCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.Sheaf.cotangentComplex (Opens.grothendieckTopology X.carrier)
        (baseStructureMap f g ≫ inverseImageStructureMap f) :
      CochainComplex (structureModules X) ℤ) ≅ cotangentComplex (f ≫ g) :=
  eqToIso (cotangentComplex_comp_eq f g)

/-! ## The first vertex and the two displayed arrows -/

/-- The first vertex `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X` of the fundamental triangle of
the tower, with the degreewise tensor product. -/
def baseChangedCotangentComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex (structureModules X) ℤ :=
  CategoryTheory.Sheaf.baseChangedCotangentComplex (Opens.grothendieckTopology X.carrier)
    (baseStructureMap f g) (inverseImageStructureMap f)

/-- The first displayed arrow `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z}`: the
base-change arrow of Tag 08SZ for the tower, read on `L_{X/Z}`. -/
def cotangentBaseChange (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChangedCotangentComplex f g ⟶ cotangentComplex (f ≫ g) :=
  CategoryTheory.Sheaf.towerCotangentBaseChange (Opens.grothendieckTopology X.carrier)
      (baseStructureMap f g) (inverseImageStructureMap f) ≫ (cotangentComplexCompIso f g).hom

/-- **Stacks Project, Tag 08T4**, the second displayed arrow `L_{X/Z} ⟶ L_{X/Y}`: the
change-of-base-ring map of Tag 08SZ for the tower `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 08T4 "the second displayed arrow L_{X/Z} ⟶ L_{X/Y}, unconditionally. \
  Distinguishedness of the triangle is not claimed by this declaration"]
def cotangentChangeOfBase (f : X ⟶ Y) (g : Y ⟶ Z) :
    (cotangentComplex (f ≫ g) : CochainComplex (structureModules X) ℤ) ⟶
      cotangentComplex f :=
  (cotangentComplexCompIso f g).inv ≫
    CategoryTheory.Sheaf.towerCotangentChangeOfBase (Opens.grothendieckTopology X.carrier)
      (baseStructureMap f g) (inverseImageStructureMap f)

/-- The degreewise pullback `f^*L_{Y/Z}` of the cotangent complex of `g`. -/
def degreewisePullbackCotangentComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex (structureModules X) ℤ :=
  ((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex g)

/-! ## The distinguished triangle -/

section Derived

/-- Reading the second vertex of a distinguished triangle of a derived category through an
equality of complexes leaves it distinguished. -/
private lemma exists_mem_distTriang_of_eq {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{t} C] {A B B' D : CochainComplex C ℤ} (e : B = B') (α : A ⟶ B)
    (β : B ⟶ D) (δ : DerivedCategory.Q.obj D ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧)
    (h : Triangle.mk (DerivedCategory.Q.map α) (DerivedCategory.Q.map β) δ ∈
      distTriang (DerivedCategory C)) :
    ∃ δ' : DerivedCategory.Q.obj D ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (α ≫ eqToHom e))
          (DerivedCategory.Q.map (eqToHom e.symm ≫ β)) δ' ∈ distTriang (DerivedCategory C) := by
  subst e
  exact ⟨δ, by simpa using h⟩

/-- Reading the first vertex of a distinguished triangle of a derived category through an
isomorphism of complexes leaves it distinguished. -/
private lemma exists_mem_distTriang_of_iso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{t} C] {A A' B D : CochainComplex C ℤ} (e : A' ≅ A) (α : A ⟶ B)
    (β : B ⟶ D) (δ : DerivedCategory.Q.obj D ⟶ (DerivedCategory.Q.obj A)⟦(1 : ℤ)⟧)
    (h : Triangle.mk (DerivedCategory.Q.map α) (DerivedCategory.Q.map β) δ ∈
      distTriang (DerivedCategory C)) :
    ∃ δ' : DerivedCategory.Q.obj D ⟶ (DerivedCategory.Q.obj A')⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (e.hom ≫ α)) (DerivedCategory.Q.map β) δ' ∈
        distTriang (DerivedCategory C) := by
  refine ⟨δ ≫ (DerivedCategory.Q.mapIso e).inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (DerivedCategory.Q.mapIso e) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simp
  · simp
  · simp [← Functor.map_comp]

variable [HasDerivedCategory.{t} (structureModules X)]

/-- **Stacks Project, Tag 08T4, under one carried hypothesis.** For morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the triangle

`L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ ⋯`

on the two canonical arrows `cotangentBaseChange` and `cotangentChangeOfBase` is distinguished
in `D(𝒪_X)`.

The hypothesis carried is the one carried by Tag 08SZ, in the same shape: a short complex `S`
of complexes of sheaves of `𝒪_X`-modules that is short exact (`hS`), whose three terms are the
three vertices (`e₁`, `e₂`, `e₃`) and whose two maps are the two canonical arrows (`hf`, `hg`).
See the "What is proved and what is not" section of the module documentation. -/
@[stacks 08T4 "the triangle with FIRST VERTEX THE DEGREEWISE base change \
  L_{f⁻¹O_Y/(g∘f)⁻¹O_Z} ⊗_{f⁻¹O_Y} O_X, not Lf^* L_{Y/Z}, and under the ONE carried \
  hypothesis of Tag 08SZ: the short exact sequence `S`/`hS`, the sheaf-level analogue of \
  Tag 08SD, absent from this library. See the docstring above"]
theorem exists_distTriang_of_shortExact (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : ShortComplex (CochainComplex (structureModules X) ℤ))
    (hS : S.ShortExact) (e₁ : S.X₁ ≅ baseChangedCotangentComplex f g)
    (e₂ : S.X₂ ≅ cotangentComplex (f ≫ g)) (e₃ : S.X₃ ≅ cotangentComplex f)
    (hf : S.f = e₁.hom ≫ cotangentBaseChange f g ≫ e₂.inv)
    (hg : S.g = e₂.hom ≫ cotangentChangeOfBase f g ≫ e₃.inv) :
    ∃ δ : (DerivedCategory.Q (C := structureModules X)).obj (cotangentComplex f) ⟶
        ((DerivedCategory.Q (C := structureModules X)).obj
          (baseChangedCotangentComplex f g))⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.Q (C := structureModules X)).map (cotangentBaseChange f g))
          ((DerivedCategory.Q (C := structureModules X)).map (cotangentChangeOfBase f g)) δ ∈
        distTriang (DerivedCategory (structureModules X)) := by
  obtain ⟨δ, hδ⟩ :=
    CategoryTheory.Sheaf.exists_distTriang_cotangentComplexDerived_of_shortExact.{u, u, u, t}
    (D := structureSheafOfSite X)
    (Opens.grothendieckTopology X.carrier) (baseStructureMap f g) (inverseImageStructureMap f)
    S hS e₁ (e₂ ≪≫ (cotangentComplexCompIso f g).symm) e₃
    (hf.trans (congrArg (fun m => e₁.hom ≫ m) (Category.assoc _ _ _)))
    (hg.trans ((congrArg (fun m => e₂.hom ≫ m) (Category.assoc _ _ _)).trans
      (Category.assoc _ _ _).symm))
  exact exists_mem_distTriang_of_eq (cotangentComplex_comp_eq f g) _ _ δ hδ

/-- **Stacks Project, Tag 08T4, under two carried hypotheses.** For morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the triangle

`f^*L_{Y/Z} ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ f^*L_{Y/Z}[1]`

is distinguished in `D(𝒪_X)`, its first arrow being the base-change arrow of Tag 08SZ for the
tower read on `f^*L_{Y/Z}` and its second the canonical map `cotangentChangeOfBase`.

Two hypotheses are carried. `e` is Tag 08SV for the tower: the degreewise pullback of `L_{Y/Z}`
is the first vertex `L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X` of the triangle of Tag 08SZ. The
short exact sequence `S`, `hS` is the hypothesis Tag 08SZ itself carries. The first vertex is
the degreewise pullback `f^*L_{Y/Z}`; it is `Lf^*L_{Y/Z}` as soon as `L_{Y/Z}` is K-flat, by
`isIso_derivedPullbackComparison_cotangentComplex`. See the "What is proved and what is not"
section of the module documentation. -/
@[stacks 08T4 "the triangle with first vertex the DEGREEWISE pullback f^* L_{Y/Z}, not \
  Lf^* L_{Y/Z}; the two agree in D(O_X) exactly when L_{Y/Z} is K-flat, which is NOT proved \
  here. TWO carried hypotheses: `e` is Tag 08SV for this tower, `S`/`hS` is what Tag 08SZ \
  carries. See the docstring above and the module documentation"]
theorem exists_distTriang_degreewisePullback_of_shortExact (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : degreewisePullbackCotangentComplex f g ≅ baseChangedCotangentComplex f g)
    (S : ShortComplex (CochainComplex (structureModules X) ℤ))
    (hS : S.ShortExact) (e₁ : S.X₁ ≅ baseChangedCotangentComplex f g)
    (e₂ : S.X₂ ≅ cotangentComplex (f ≫ g)) (e₃ : S.X₃ ≅ cotangentComplex f)
    (hf : S.f = e₁.hom ≫ cotangentBaseChange f g ≫ e₂.inv)
    (hg : S.g = e₂.hom ≫ cotangentChangeOfBase f g ≫ e₃.inv) :
    ∃ δ : (DerivedCategory.Q (C := structureModules X)).obj (cotangentComplex f) ⟶
        ((DerivedCategory.Q (C := structureModules X)).obj
          (degreewisePullbackCotangentComplex f g))⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.Q (C := structureModules X)).map
            (e.hom ≫ cotangentBaseChange f g))
          ((DerivedCategory.Q (C := structureModules X)).map (cotangentChangeOfBase f g)) δ ∈
        distTriang (DerivedCategory (structureModules X)) := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_of_shortExact f g S hS e₁ e₂ e₃ hf hg
  exact exists_mem_distTriang_of_iso e _ _ δ hδ

end Derived

/-! ## The derived pullback of the cotangent complex of `g` -/

section DerivedPullback

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 06YJ** for the cotangent complex of `g`. If `L_{Y/Z}` is K-flat then
the canonical comparison `Lf^*L_{Y/Z} ⟶ f^*L_{Y/Z}` from the derived to the degreewise pullback
is invertible: the derived pullback of `L_{Y/Z}` is computed degreewise. This is the flatness
half of the source's proof of Tag 08T4, which there reads that the terms of the cotangent
complex are locally free. -/
theorem isIso_derivedPullbackComparison_cotangentComplex (f : X ⟶ Y) (g : Y ⟶ Z)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y
      (cotangentComplex g : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) ℤ)) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient
          (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj (cotangentComplex g))) :=
  Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f
    (cotangentComplex g) hK

end DerivedPullback

end Stacks.Sheaves.RingedSpaceCotangent

end
