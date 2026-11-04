module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions

/-!
# Quasi-coherent objects in the derived category of the small affine site

Let `S` be a scheme. Write `S_{affine, Zar}` for its small affine Zariski site — the affine
opens of `S` with the standard Zariski coverings — and `S_affine` for the same category with the
chaotic topology, both carrying the sheaf of global functions `T ↦ Γ(T, 𝒪_T)` as structure
sheaf. Stacks 0GZZ asserts canonical exact equivalences between the five triangulated categories
`D_QCoh(𝒪_S)`, `D_QCoh(S_Zar, 𝒪)`, `D_QCoh(S_{affine, Zar}, 𝒪)`, `D_QCoh(S_affine, 𝒪)` and
`QC(S_affine, 𝒪)`.

This file proves the comparison of the last two. For an arbitrary morphism `U ⟶ V` of affine
opens the restriction homomorphism `Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)` is flat, because such a morphism is
an open immersion of affine schemes; so the criterion of Stacks 0GZR applies on the chaotic
site and identifies the two subcategories of `D(S_affine, 𝒪)` on the nose.

## Main definitions

* `CategoryTheory.ObjectProperty.equivOfEq`: equal object properties cut out equivalent full
  subcategories.
* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.derivedQuasiCoherentEquivQC`: the
  equivalence `D_QCoh(𝒪) ≌ QC(𝒪)` on a ringed site with the chaotic topology and flat
  restriction homomorphisms.
* `AlgebraicGeometry.smallAffineChaoticRingedSite`: the small affine Zariski site of a scheme
  read with the chaotic topology, i.e. the ringed site `(S_affine, 𝒪)`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_smallZariski_toScheme_map`: every morphism of the small
  Zariski site of a scheme is an open immersion of schemes.
* `AlgebraicGeometry.flat_smallAffineZariskiRingedSite_O_map`: the restriction homomorphisms of
  the structure sheaf of the small affine Zariski site are flat.
* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.isQC_eq_hasQuasicoherentCohomology`:
  Stacks 0GZR read as an equality of object properties of `D(𝒪)` rather than as a pointwise
  `iff`.
* `AlgebraicGeometry.smallAffineChaoticDerivedQuasiCoherentEquivQC`: **the equivalence of (4)
  and (5) of Stacks 0GZZ**, together with
  `AlgebraicGeometry.smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι`, which
  identifies it with the canonical comparison inside `D(S_affine, 𝒪)`, and
  `AlgebraicGeometry.smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology`, which states that
  the two subcategories are in fact equal.
* `AlgebraicGeometry.smallAffineChaotic_qcohCohomologyProperty_isTriangulated`: for a scheme in
  `Scheme.{0}`, both sides are triangulated subcategories of `D(S_affine, 𝒪)`, so the
  comparison is an exact equivalence of triangulated categories.

## Implementation notes

On the chaotic site the two subcategories of `D(𝒪)` are *equal*, not merely equivalent, so the
comparison functor is the one induced by the inclusion of object properties and the exactness
of the equivalence needs no separate argument: the statement
`smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι` exhibits the equivalence as a
commuting triangle over the ambient `D(S_affine, 𝒪)`, which is what "canonical exact
equivalence" amounts to here, since the two inclusion functors are the same functor.

The comparison quantifies over a `BaseChangeData` on the structure sheaf, as `IsQC` itself does;
`smallAffineChaoticBaseChangeData` exhibits one, so the quantification is not empty. It is only
exhibited for a scheme in `Scheme.{0}`, because derived base change is constructed in this
library only over a structure sheaf with values in `RingCat.{0}`, and the sections of the
structure sheaf of the small affine site of a scheme in `Scheme.{u}` lie in `Type u`. The
triangulatedness of the two subcategories has the same provenance, through Stacks 0GYW, and so
carries the same restriction.

Flatness of the restriction homomorphisms is where the geometry enters. A morphism of the small
Zariski site of `S` is a morphism over `S` between two schemes whose structure morphisms to `S`
are open immersions, so it is an open immersion by
`CategoryTheory.MorphismProperty.of_postcomp`; between affine objects it is therefore a flat
morphism of affine schemes, and `AlgebraicGeometry.Scheme.Hom.flat_appTop` turns that into
flatness of the map on global sections. The structure sheaf of the small affine Zariski site is
literally `(S_{affine, Zar})ᵒᵖ ⥤ CommRingCat`, `T ↦ Γ(T, 𝒪_T)`, so the identification of its
restriction maps with `Scheme.Hom.appTop` holds by definition.

## Coverage limits

Only the comparison of (4) and (5) is proved. Of the five categories of Stacks 0GZZ, four have
library counterparts: `D_QCoh(𝒪_S)` and `D_QCoh(S_Zar, 𝒪)` as
`DerivedCategoryB.derivedCategoryB` of `SheafOfModules.isQuasicoherentOnSite` over
`Scheme.ringCatSheaf` and over `AlgebraicGeometry.SmallZariski.structureSheaf`, the latter also
as `(smallZariskiRingedSite B S hS).ringSheaf`; `D_QCoh(S_{affine, Zar}, 𝒪)` over
`AlgebraicGeometry.smallAffineZariskiRingedSite`; and `D_QCoh(S_affine, 𝒪)` and
`QC(S_affine, 𝒪)` as the two object properties compared here.

The three remaining comparisons are not proved and nothing here is stated about them.

* (1) and (2) rest on Descent, Remark 03FG — available as
  `AlgebraicGeometry.smallZariskiModuleEquiv` — together with Descent, Proposition 03DX, which
  this development does not have; see the coverage note of
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentModulesAndAffines.lean`.
* (2) and (3) need clause (6) of Stacks 03DM, that quasi-coherence of a sheaf of modules is
  intrinsic to the ringed topos. Only clauses (4), (5) and (7) are proved, in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleTypesUnderEquivalence.lean`; the
  equivalence of ringed topoi itself is available, as
  `AlgebraicGeometry.SmallAffineZariski.ringedToposHom`.
* (3) and (4) need Stacks 07A8, the comparison of a weak Serre subcategory across a change of
  topology, which this development does not have.

The triangulated structure is supplied for (4) and (5) only, and only for a scheme in
`Scheme.{0}`, through Stacks 0GYW. For (1), (2) and (3) it rests on quasi-coherent modules
forming a weak Serre subcategory, Stacks 01LA, which this development does not have, and
nothing is claimed about it here.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GZW](https://stacks.math.columbia.edu/tag/0GZW)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

namespace CategoryTheory.ObjectProperty

/-- Two equal object properties cut out the same full subcategory: both functors are the
inclusion of object properties, which is the identity on the underlying objects and
morphisms. -/
def equivOfEq {C : Type u} [Category.{v} C] {P Q : ObjectProperty C} (h : P = Q) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := ιOfLE (le_of_eq h)
  inverse := ιOfLE (le_of_eq h.symm)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The forward functor of `ObjectProperty.equivOfEq` commutes with the two inclusions into the
ambient category. -/
def equivOfEqFunctorCompιIso {C : Type u} [Category.{v} C] {P Q : ObjectProperty C}
    (h : P = Q) : (equivOfEq h).functor ⋙ Q.ι ≅ P.ι :=
  ιOfLECompιIso (le_of_eq h)

end CategoryTheory.ObjectProperty

namespace Stacks.ModulesOnACategory.QuasiCoherentCohomology

open AlgebraicGeometry

/-- `D_QCoh(𝒪) ⊆ D(𝒪)`, the objects of the derived category all of whose cohomology sheaves are
quasi-coherent, read as an object property rather than as a predicate. -/
abbrev qcohCohomologyProperty (X : RingedSite.{u, v, r}) :
    ObjectProperty (DMod.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  hasQuasicoherentCohomology.{w} X

/-- `QC(𝒪) ⊆ D(𝒪)` of Stacks 0GYV, read as an object property rather than as a predicate. -/
abbrev isQCProperty {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}
    (bc : BaseChangeData.{w} O) : ObjectProperty (DMod.{w} O) :=
  fun K ↦ IsQC.{w} bc K

/-- **Stacks 0GZR as an equality of subcategories.** On a ringed site with the chaotic topology
whose restriction homomorphisms are flat, the object property cutting out `QC(𝒪) ⊆ D(𝒪)` and the
object property cutting out `D_QCoh(𝒪) ⊆ D(𝒪)` are the same property. -/
theorem isQC_eq_hasQuasicoherentCohomology (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (hflat : ∀ {U V : X.Cᵒᵖ} (a : V ⟶ U), RingHom.Flat (X.O.obj.map a).hom)
    (bc : BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    isQCProperty.{w} bc = qcohCohomologyProperty.{w} X :=
  funext fun K ↦ propext (isQC_iff_hasQuasicoherentCohomology.{w} X hX hflat bc K)

/-- **The comparison `D_QCoh(𝒪) ≌ QC(𝒪)`.** On a ringed site with the chaotic topology whose
restriction homomorphisms are flat, the derived category with quasi-coherent cohomology is
equivalent to the category of quasi-coherent objects of Stacks 0GYV. -/
def derivedQuasiCoherentEquivQC (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (hflat : ∀ {U V : X.Cᵒᵖ} (a : V ⟶ U), RingHom.Flat (X.O.obj.map a).hom)
    (bc : BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    (qcohCohomologyProperty.{w} X).FullSubcategory ≌ QC.{w} bc :=
  ObjectProperty.equivOfEq (isQC_eq_hasQuasicoherentCohomology.{w} X hX hflat bc).symm

/-- The comparison `D_QCoh(𝒪) ≌ QC(𝒪)` commutes with the inclusions of both sides into
`D(𝒪)`. -/
def derivedQuasiCoherentEquivQCFunctorCompι (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (hflat : ∀ {U V : X.Cᵒᵖ} (a : V ⟶ U), RingHom.Flat (X.O.obj.map a).hom)
    (bc : BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    (derivedQuasiCoherentEquivQC.{w} X hX hflat bc).functor ⋙ QCι.{w} bc ≅
      (qcohCohomologyProperty.{w} X).ι :=
  ObjectProperty.equivOfEqFunctorCompιIso
    (isQC_eq_hasQuasicoherentCohomology.{w} X hX hflat bc).symm

end Stacks.ModulesOnACategory.QuasiCoherentCohomology

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every morphism of the small Zariski site of a scheme is an open immersion of schemes: it is
a morphism over `S` between two objects whose structure morphisms to `S` are open immersions. -/
theorem isOpenImmersion_smallZariski_toScheme_map {U V : SmallZariski B S hS} (f : U ⟶ V) :
    IsOpenImmersion ((SmallZariski.toScheme B S hS).map f) := by
  have hV : IsOpenImmersion (B.inclusion.map V.obj.hom) := V.property
  have hU : IsOpenImmersion (B.inclusion.map U.obj.hom) := U.property
  have hw := congrArg B.inclusion.map (Over.w ((SmallZariski.inclusion B S hS).map f))
  rw [Functor.map_comp] at hw
  have hU' : IsOpenImmersion ((SmallZariski.toScheme B S hS).map f ≫
      B.inclusion.map V.obj.hom) := hw ▸ hU
  exact MorphismProperty.of_postcomp @IsOpenImmersion _ _ hV hU'

/-- The restriction homomorphisms of the structure sheaf of the small affine Zariski site of a
scheme are flat: they are the maps on global functions of open immersions of affine schemes. -/
theorem flat_smallAffineZariskiRingedSite_O_map
    {U V : (SmallAffineZariski B S hS)ᵒᵖ} (a : V ⟶ U) :
    RingHom.Flat ((smallAffineZariskiRingedSite B S hS).O.obj.map a).hom := by
  have himm : IsOpenImmersion ((SmallAffineZariski.toScheme B S hS).map a.unop) :=
    isOpenImmersion_smallZariski_toScheme_map B S hS
      ((SmallAffineZariski.inclusion B S hS).map a.unop)
  have : Flat ((SmallAffineZariski.toScheme B S hS).map a.unop) := inferInstance
  exact Scheme.Hom.flat_appTop ((SmallAffineZariski.toScheme B S hS).map a.unop)

/-- The ringed site `(S_affine, 𝒪)` of Stacks 0GZZ: the affine opens of `S` with the chaotic
topology, for which sheaves agree with presheaves, carrying the sheaf of global functions
`T ↦ Γ(T, 𝒪_T)` as structure sheaf. -/
abbrev smallAffineChaoticRingedSite : RingedSite.{u + 1, u, u} :=
  (smallAffineZariskiRingedSite B S hS).chaotic

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **Stacks 0GZZ, the equivalence of (4) and (5).** For a scheme `S`, the derived category of
modules on the small affine site `S_affine` with quasi-coherent cohomology sheaves is
canonically equivalent to the category `QC(S_affine, 𝒪)` of quasi-coherent objects of the
derived category.

The equivalence is realized inside `D(S_affine, 𝒪)`, by
`smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι`; the two subcategories are in
fact equal, by `smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology`.

For a scheme in `Scheme.{0}` both sides are triangulated subcategories of `D(S_affine, 𝒪)`, by
`smallAffineChaotic_qcohCohomologyProperty_isTriangulated`, so the comparison is then an exact
equivalence of triangulated categories. None of the other four comparisons of Stacks 0GZZ is
proved; see the coverage note of this file. -/
@[stacks 0GZZ "the equivalence (4) ≃ (5)"]
def smallAffineChaoticDerivedQuasiCoherentEquivQC
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B S hS).O).obj) :
    (qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS)).FullSubcategory ≌
      QC.{w} bc :=
  derivedQuasiCoherentEquivQC.{w} (smallAffineChaoticRingedSite B S hS) rfl
    (fun a ↦ flat_smallAffineZariskiRingedSite_O_map B S hS a) bc

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- The two subcategories compared by `smallAffineChaoticDerivedQuasiCoherentEquivQC` are equal
as object properties of `D(S_affine, 𝒪)`. -/
theorem smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B S hS).O).obj) :
    isQCProperty.{w} bc =
      qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS) :=
  isQC_eq_hasQuasicoherentCohomology.{w} (smallAffineChaoticRingedSite B S hS) rfl
    (fun a ↦ flat_smallAffineZariskiRingedSite_O_map B S hS a) bc

open Stacks.ModulesOnACategory.QuasiCoherentCohomology in
/-- **Stacks 0GZZ, the equivalence of (4) and (5), as a commuting triangle.** The comparison
`D_QCoh(S_affine, 𝒪) ≌ QC(S_affine, 𝒪)` is the canonical one: it commutes with the inclusions
of both sides into `D(S_affine, 𝒪)`. -/
@[stacks 0GZZ "the equivalence (4) ≃ (5) is the canonical one"]
def smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι
    (bc : BaseChangeData.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B S hS).O).obj) :
    (smallAffineChaoticDerivedQuasiCoherentEquivQC.{w} B S hS bc).functor ⋙ QCι.{w} bc ≅
      (qcohCohomologyProperty.{w} (smallAffineChaoticRingedSite B S hS)).ι :=
  derivedQuasiCoherentEquivQCFunctorCompι.{w} (smallAffineChaoticRingedSite B S hS) rfl
    (fun a ↦ flat_smallAffineZariskiRingedSite_O_map B S hS a) bc

section Universe0

open Stacks.ModulesOnACategory.QuasiCoherentCohomology
open Stacks.ModulesOnACategory.CartesianObjects

variable (B₀ : BigZariskiSite.{0}) (S₀ : Scheme.{0}) (hS₀ : B₀.Contains S₀)

/-- A base-change datum on the small affine site `S_affine` of a scheme in `Scheme.{0}`: the
derived extension-of-scalars functors along the restriction homomorphisms of the structure
sheaf, with their adjunctions to derived restriction of scalars.

This is what makes the comparison of (4) and (5) non-vacuous: the statements above quantify
over a `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData`, and this
declaration exhibits one. The library builds derived base change only for a structure sheaf
with values in `RingCat.{0}` and for the module universe `0`
(`Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData`), which for the small
affine site of a scheme forces that scheme into `Scheme.{0}`; the comparison itself is proved
for an arbitrary universe above. -/
def smallAffineChaoticBaseChangeData :
    BaseChangeData.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B₀ S₀ hS₀).O).obj :=
  canonicalBaseChangeData
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B₀ S₀ hS₀).O).obj
    (fun U x y ↦ by
      let _ : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineChaoticRingedSite B₀ S₀ hS₀).O).obj.obj U) :=
        ((smallAffineChaoticRingedSite B₀ S₀ hS₀).O.obj.obj U).commRing
      exact mul_comm x y)

/-- `QC(S_affine, 𝒪)` is a triangulated subcategory of `D(S_affine, 𝒪)`, by Stacks 0GYW. -/
theorem smallAffineChaotic_isQCProperty_isTriangulated :
    ObjectProperty.IsTriangulated
      (isQCProperty.{0} (smallAffineChaoticBaseChangeData B₀ S₀ hS₀)) :=
  Stacks.ModulesOnACategory.CartesianSubcategory.isCartesian_isTriangulated
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineChaoticRingedSite B₀ S₀ hS₀).O).obj _

/-- **Stacks 0GZZ, triangulatedness of (4) and (5).** For a scheme in `Scheme.{0}`,
`D_QCoh(S_affine, 𝒪)` is a triangulated subcategory of `D(S_affine, 𝒪)`: it is the same
subcategory as `QC(S_affine, 𝒪)`, which is triangulated by Stacks 0GYW.

Together with `smallAffineChaoticDerivedQuasiCoherentEquivQC` and
`smallAffineChaoticDerivedQuasiCoherentEquivQC_functor_comp_ι` this makes the comparison of (4)
and (5) an exact equivalence of triangulated categories, both sides being triangulated
subcategories of `D(S_affine, 𝒪)` and the comparison commuting with the two inclusions.

The restriction to `Scheme.{0}` comes from the input: the library constructs derived base
change only over a structure sheaf with values in `RingCat.{0}`; see
`smallAffineChaoticBaseChangeData`. -/
@[stacks 0GZZ "(4) and (5) are triangulated, for a scheme in `Scheme.{0}`"]
theorem smallAffineChaotic_qcohCohomologyProperty_isTriangulated :
    ObjectProperty.IsTriangulated
      (qcohCohomologyProperty.{0} (smallAffineChaoticRingedSite B₀ S₀ hS₀)) := by
  rw [← smallAffineChaotic_isQC_eq_hasQuasicoherentCohomology.{0} B₀ S₀ hS₀
    (smallAffineChaoticBaseChangeData B₀ S₀ hS₀)]
  exact smallAffineChaotic_isQCProperty_isTriangulated B₀ S₀ hS₀

end Universe0

end AlgebraicGeometry

end
