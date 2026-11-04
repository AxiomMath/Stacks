module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermSequence
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquareIso
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
public import StacksCore.Tactic.StacksAttribute

/-!
# The six term exact sequence of naive cotangent complexes

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` the six term exact sequence of
[Stacks Project, Tag 0E44] reads

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ f^*Ω_{Y/Z} ⟶`
`Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`.

This file proves it, as one sequence: the two canonical chain maps
`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y}` and the connecting map
`H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z})`, exactness at the four interior nodes, and the final
`⟶ 0`.  Its last three terms are the degree `0` cohomology sheaves of the three complexes,
which are `f^*Ω_{Y/Z}`, `Ω_{X/Z}` and `Ω_{X/Y}` by `pullbackHomologyZeroIso` and by
[Stacks Project, Tag 0D0J]
(`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`).

All of this is available for a pair of composable morphisms of **ringed spaces** as the
cohomological content of [Stacks Project, Tag 0E1Z], in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSixTerm` and
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves`, and a morphism of
schemes has an underlying morphism of ringed spaces; two comparisons have to be supplied.

The first is here.  That development writes `NL_{X/Z}` as the naive cotangent complex of `𝒪_X`
over the **iterated** inverse image `f⁻¹g⁻¹𝒪_Z`, because that is the spelling in which the
inverse-image theorem of [Stacks Project, Tag 08TM] identifies the first term of the sequence
with `f^*NL_{Y/Z}`, while `AlgebraicGeometry.Scheme.naiveCotangentComplex (f ≫ g)` is the naive
cotangent complex of `𝒪_X` over `(g ∘ f)⁻¹𝒪_Z`.  The two base rings are canonically isomorphic
over `𝒪_X`, and `Stacks.SheafOfModules.naiveCotangentComplexCompIso` is the resulting
identification of the two complexes; the statements below are the ringed-space ones transported
along it, so that `NL_{X/Z}` and `NL_{X/Y}` in them are the naive cotangent complexes of
`f ≫ g` and of `f`.

The second is the identification of the two models of the pullback `f^*`: the development above
uses the inverse image with scalars extended to `𝒪_X`, while the sheaf of relative differentials
and its canonical maps are stated over Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`.
`RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` identifies the two — both are left
adjoint to `f_*` — and `pullbackComplexIso` applies it termwise.  It is this that makes the
fourth term of the sequence `f^*Ω_{Y/Z}` and so makes the six terms one sequence rather than
two ends.

## Main definitions

* `Stacks.SheafOfModules.inverseImageCompIso`: the comparison
  `(g ∘ f)⁻¹𝒪_Z ≅ f⁻¹g⁻¹𝒪_Z` of sheaves of rings on `X` attached to a pair of composable
  morphisms of ringed spaces, the mate of the equality `(g ∘ f)_* = g_* ∘ f_*`.
* `Stacks.SheafOfModules.naiveCotangentComplexCompIso` and
  `Stacks.SheafOfModules.naiveCotangentComplexCompIsoOfEq`: the identification of `NL_{X/Z}`
  with the naive cotangent complex of `𝒪_X` over the iterated inverse image `f⁻¹g⁻¹𝒪_Z`, the
  second taking the composite as an argument together with an equation.
* `Stacks.NaiveCotangentSixTermSequence.pullbackToTotalMap` and
  `Stacks.NaiveCotangentSixTermSequence.totalToRelativeMap`: the two canonical chain maps
  `f^*NL_{Y/Z} ⟶ NL_{X/Z}` and `NL_{X/Z} ⟶ NL_{X/Y}` of a pair of composable morphisms of
  schemes, which induce four of the five arrows of the sequence.
* `Stacks.NaiveCotangentSixTermSequence.jacobiZariskiConnecting`: **the connecting map**
  `H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z})` of the six term sequence, and
  `connectingDifferentials`, the same map with its target written as `f^*Ω_{Y/Z}`.
* `Stacks.NaiveCotangentSixTermSequence.pullbackComplexIso` and
  `Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso`: the identification of the two
  models of `f^*NL_{Y/Z}`, and **the fourth term** `H^0(f^*NL_{Y/Z}) ≅ f^*Ω_{Y/Z}`.

## Main results

* `Stacks.SheafOfModules.inverseImageCompIso_hom_comp`: the comparison of base rings is
  compatible with the two structure maps to `𝒪_X`, which is what makes it a map of
  presentations and hence induces the identification of complexes.
* `Stacks.NaiveCotangentSixTermSequence.exact_sixTerm_negOne_total`: **exactness at
  `H^{-1}(NL_{X/Z})`.**
* `Stacks.NaiveCotangentSixTermSequence.exact_sixTerm_negOne_relative`: **exactness at
  `H^{-1}(NL_{X/Y})`.**
* `Stacks.NaiveCotangentSixTermSequence.exact_sixTerm_zero_pullback`: **exactness at
  `H^0(f^*NL_{Y/Z}) = f^*Ω_{Y/Z}`.**
* `Stacks.NaiveCotangentSixTermSequence.exact_sixTerm_zero_total`: **exactness at
  `H^0(NL_{X/Z}) = Ω_{X/Z}`.**
* `Stacks.NaiveCotangentSixTermSequence.epi_homologyMap_totalToRelativeMap_zero`: **the final
  `⟶ 0`**, that is, exactness at `H^0(NL_{X/Y}) = Ω_{X/Y}`.

## Implementation notes

`Stacks.SheafOfModules.naiveCotangentComplexCompIso` is the canonical chain map of
[Stacks Project, Tag 08TX] attached to the square with the comparison of base rings below and
the identity of `𝒪_X` on top, which is invertible because both horizontal maps are
(`Stacks.SheafOfModules.naiveCotangentComplexIsoOfSquare`).  Restriction of scalars along the
identity is the identity functor, so no transport of the target is left in the statements; the
`eqToIso` that removes it is `mapHomologicalComplex_restrictScalars_id`.

The five arrows of the sequence are the ones induced by the two canonical chain maps and the
connecting map, which is how the source proves the lemma: it is the special case for schemes of
Stacks 0E1Z.  The last three terms also carry the canonical maps of relative differentials of
[Stacks Project, Tag 01UX], and
`Stacks.NaiveCotangentSixTermSequence.differentialsSequence_exact` is the exactness of the last
three terms for *those* arrows.  That the two descriptions of the arrow `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}`
agree — that the map induced on `H^0` by `pullbackToTotalMap` is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` — is not proved here, and nothing here
uses it: the sequence below is complete with its own arrows throughout.

## References

* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the same sequence for a
  pair of composable morphisms of ringed spaces.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of
  the naive cotangent complex for a square of sheaves of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  sheafAdjunction structureSheafMap homEquiv_inverseImageStructureMap structureSheafMap_comp)

universe u

noncomputable section

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

/-! ### Restriction of scalars along an identity -/

/-- Restriction of scalars along the identity carries a complex of sheaves of modules to
itself: restriction of scalars along the identity is the identity functor. -/
theorem mapHomologicalComplex_restrictScalars_id {T : TopCat.{u}}
    (B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B)) ℤ) :
    ((_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite.{u, u, u} (𝟙 B))
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K = K :=
  congrArg (fun α : Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B ⟶
        Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B ↦
      ((_root_.SheafOfModules.restrictScalars α).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
    (CategoryTheory.Functor.map_id
      (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})) B)

/-! ### The comparison of the two inverse images of the base structure sheaf -/

/-- The structure map of a morphism of ringed spaces, in the two spellings the naive cotangent
complex and the Stacks 0E1Z development use, is the same morphism. -/
theorem ringedSpaceStructureMap_eq {S T : RingedSpace.{u, u}} (h : S ⟶ T) :
    ringedSpaceStructureMap h = inverseImageStructureMap h :=
  rfl

/-- **The structure map of a morphism of ringed spaces is adjoint to its comparison map of
structure sheaves**: the unit of `h⁻¹ ⊣ h_*` followed by the pushforward of `h⁻¹𝒪_T ⟶ 𝒪_S` is
`h^♯`. -/
theorem unit_comp_map_ringedSpaceStructureMap {S T : RingedSpace.{u, u}} (h : S ⟶ T) :
    (sheafAdjunction h).unit.app T.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map
          (ringedSpaceStructureMap h) =
      structureSheafMap h := by
  have hh := homEquiv_inverseImageStructureMap h
  rw [Adjunction.homEquiv_unit] at hh
  exact hh

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The comparison `(g ∘ f)⁻¹𝒪_Z ≅ f⁻¹g⁻¹𝒪_Z`** of sheaves of commutative rings on `X`
attached to a pair of composable morphisms of ringed spaces: the inverse image along `g ∘ f` and
the iterated inverse image are both left adjoint to `g_* ∘ f_* = (g ∘ f)_*`, so they are
canonically isomorphic. -/
noncomputable def inverseImageCompIso :
    inverseImageSheaf (f ≫ g) ≅ inverseImageBaseRing f g :=
  ((((sheafAdjunction g).comp (sheafAdjunction f)).leftAdjointUniq
    (sheafAdjunction (f ≫ g))).app Z.sheaf).symm

/-- The unit of `f⁻¹ ⊣ f_*` carried along the structure map of `g`: the naturality square of
that unit at `g⁻¹𝒪_Z ⟶ 𝒪_Y`. -/
private theorem unit_comp_map_inverseImageFirstRingMap :
    (sheafAdjunction f).unit.app (inverseImageBaseRingOnMiddle g) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (inverseImageFirstRingMap f g) =
      ringedSpaceStructureMap g ≫ (sheafAdjunction f).unit.app Y.sheaf :=
  ((sheafAdjunction f).unit.naturality (ringedSpaceStructureMap g)).symm

/-- The unit of `f⁻¹ ⊣ f_*` followed by the pushforward of the structure map
`f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the iterated spelling. -/
private theorem unit_comp_map_towerStructureMap :
    (sheafAdjunction f).unit.app (inverseImageBaseRingOnMiddle g) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) =
      ringedSpaceStructureMap g ≫ structureSheafMap f := by
  rw [Functor.map_comp, ← Category.assoc, unit_comp_map_inverseImageFirstRingMap,
    Category.assoc, unit_comp_map_ringedSpaceStructureMap]

/-- The structure map of the iterated spelling is adjoint, across the composite adjunction, to
the comparison map of structure sheaves of `g ∘ f`. -/
private theorem homEquiv_towerStructureMap :
    ((sheafAdjunction g).comp (sheafAdjunction f)).homEquiv Z.sheaf X.sheaf
        (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) =
      structureSheafMap (f ≫ g) := by
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc,
    ← Functor.map_comp, unit_comp_map_towerStructureMap, Functor.map_comp, ← Category.assoc,
    unit_comp_map_ringedSpaceStructureMap]
  exact (structureSheafMap_comp f g).symm

/-- The defining property of the comparison of base rings: it carries the unit of the composite
adjunction to the unit of the adjunction of `g ∘ f`. -/
private theorem unit_comp_map_inverseImageCompIso_inv :
    ((sheafAdjunction g).comp (sheafAdjunction f)).unit.app Z.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base ⋙
          TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
            (inverseImageCompIso f g).inv =
      (sheafAdjunction (f ≫ g)).unit.app Z.sheaf :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ Z.sheaf

/-- The structure map of the iterated spelling factors through the comparison of base rings. -/
private theorem inverseImageCompIso_inv_comp :
    inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f =
      (inverseImageCompIso f g).inv ≫ inverseImageStructureMap (f ≫ g) := by
  apply (((sheafAdjunction g).comp (sheafAdjunction f)).homEquiv Z.sheaf X.sheaf).injective
  rw [homEquiv_towerStructureMap, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    unit_comp_map_inverseImageCompIso_inv]
  exact (unit_comp_map_ringedSpaceStructureMap (f ≫ g)).symm

/-- **The comparison of base rings is a map of presentations of `𝒪_X`.**  Composed with the
structure map `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the iterated spelling it is the structure map
`(g ∘ f)⁻¹𝒪_Z ⟶ 𝒪_X` of `g ∘ f`. -/
theorem inverseImageCompIso_hom_comp :
    (inverseImageCompIso f g).hom ≫
        inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f =
      inverseImageStructureMap (f ≫ g) := by
  rw [inverseImageCompIso_inv_comp, Iso.hom_inv_id_assoc]

/-- **The identification of `NL_{X/Z}` with its iterated spelling.**  The naive cotangent
complex of `𝒪_X` over `(g ∘ f)⁻¹𝒪_Z` is the naive cotangent complex of `𝒪_X` over the iterated
inverse image `f⁻¹g⁻¹𝒪_Z`: the comparison of base rings is an isomorphism compatible with the
two structure maps, so Stacks 08TX for a square of isomorphisms applies. -/
noncomputable def naiveCotangentComplexCompIso :
    RingedSpace.naiveCotangentComplex (f ≫ g) ≅
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f g) X.sheaf
        (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) :=
  naiveCotangentComplexIsoOfSquare.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (inverseImageSheaf (f ≫ g)) X.sheaf (inverseImageStructureMap (f ≫ g))
      (inverseImageBaseRing f g) X.sheaf
      (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f)
      (inverseImageCompIso f g) (Iso.refl X.sheaf)
      ((Category.comp_id _).trans (inverseImageCompIso_hom_comp f g).symm) ≪≫
    eqToIso (mapHomologicalComplex_restrictScalars_id X.sheaf _)

/-- The identification of `NL_{X/Z}` with its iterated spelling, for a morphism `H : X ⟶ Z`
presented as the composite of `F` and `G`.  Taking the composite as an argument together with an
equation is what lets the identification be used on the naive cotangent complex of a morphism of
schemes without unfolding the composition of schemes at every occurrence. -/
noncomputable def naiveCotangentComplexCompIsoOfEq (h : X ⟶ Z) (hh : h = f ≫ g) :
    RingedSpace.naiveCotangentComplex h ≅
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f g) X.sheaf
        (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) :=
  eqToIso (congrArg RingedSpace.naiveCotangentComplex hh) ≪≫ naiveCotangentComplexCompIso f g

end RingedSpace

end Stacks.SheafOfModules

namespace Stacks.NaiveCotangentSixTermSequence

open Stacks.SheafOfModules

/-! ### Cohomology of a comparison of complexes -/

section General

variable {C : Type*} [Category C] [HasZeroMorphisms C] [CategoryWithHomology C]

/-- An isomorphism of cochain complexes induces an isomorphism of cohomology objects in every
degree. -/
noncomputable def homologyIsoOfComplexIso {K L : CochainComplex C ℤ} (e : K ≅ L) (i : ℤ) :
    K.homology i ≅ L.homology i where
  hom := HomologicalComplex.homologyMap e.hom i
  inv := HomologicalComplex.homologyMap e.inv i
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, e.hom_inv_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, e.inv_hom_id, HomologicalComplex.homologyMap_id]

end General

/-! ### The three complexes and the two chain maps -/

/-- The underlying morphism of ringed spaces of a morphism of schemes. -/
noncomputable abbrev ringedSpaceHom {S T : Scheme.{u}} (h : S ⟶ T) :
    S.toRingedSpace ⟶ T.toRingedSpace :=
  h.toLRSHom.toShHom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- `f^*NL_{Y/Z}`, in the model of the Stacks 08TM/0E1Z development: the inverse image of
`NL_{Y/Z}` along `f` with scalars extended to `𝒪_X`. -/
noncomputable abbrev pullbackNaiveCotangentComplex :=
  pulledNaiveCotangentComplex (ringedSpaceHom f) (ringedSpaceHom g)

/-- The canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of Stacks 0E1Z, whose target is `NL_{X/Z}` in
the iterated spelling: the identification of Stacks 08TM followed by the base change map of the
tower `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
noncomputable abbrev iteratedPullbackMap :=
  (pulledNaiveCotangentComparison (ringedSpaceHom f) (ringedSpaceHom g)).hom ≫
    spaceBaseChangeNaiveCotangentMap
      (inverseImageBaseRing (ringedSpaceHom f) (ringedSpaceHom g))
      (inverseImageMiddleRing (ringedSpaceHom f)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom f) (ringedSpaceHom g))
      (ringedSpaceStructureMap (ringedSpaceHom f))

/-- The canonical map `NL_{X/Z} ⟶ NL_{X/Y}` of Stacks 0E1Z, whose source is `NL_{X/Z}` in the
iterated spelling: the relative map of the tower `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
noncomputable abbrev iteratedRelativeMap :=
  spaceRelativeNaiveCotangentComplexMap
    (inverseImageBaseRing (ringedSpaceHom f) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom f)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom f) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom f))

/-- **The identification of `NL_{X/Z}` with its iterated spelling**, for a pair of composable
morphisms of schemes: `Stacks.SheafOfModules.naiveCotangentComplexCompIso` of the underlying
morphisms of ringed spaces, read on the naive cotangent complex of `f ≫ g`. -/
noncomputable def totalCompIso :
    Scheme.naiveCotangentComplex (f ≫ g) ≅
      naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom f) (ringedSpaceHom g)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom f) (ringedSpaceHom g) ≫
          ringedSpaceStructureMap (ringedSpaceHom f)) :=
  naiveCotangentComplexCompIsoOfEq (ringedSpaceHom f) (ringedSpaceHom g)
    (ringedSpaceHom (f ≫ g)) rfl

/-- **Stacks 0E44, the second arrow.**  The canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of a pair of
composable morphisms of schemes: the canonical map of Stacks 0E1Z of the underlying morphisms of
ringed spaces, read on `NL_{X/Z} = NL_{f ≫ g}` through `totalCompIso`. -/
@[stacks 0E44 "the canonical map f^*NL_{Y/Z} -> NL_{X/Z}, the chain map inducing the first \
and fourth arrows of the six term sequence"]
noncomputable def pullbackToTotalMap :
    pullbackNaiveCotangentComplex f g ⟶ Scheme.naiveCotangentComplex (f ≫ g) :=
  iteratedPullbackMap f g ≫ (totalCompIso f g).inv

/-- **Stacks 0E44, the third arrow.**  The canonical map `NL_{X/Z} ⟶ NL_{X/Y}` of a pair of
composable morphisms of schemes. -/
@[stacks 0E44 "the canonical map NL_{X/Z} -> NL_{X/Y}, the chain map inducing the second \
and fifth arrows of the six term sequence"]
noncomputable def totalToRelativeMap :
    Scheme.naiveCotangentComplex (f ≫ g) ⟶ Scheme.naiveCotangentComplex f :=
  (totalCompIso f g).hom ≫ iteratedRelativeMap f g

/-- The identification of the cohomology sheaves of `NL_{X/Z}` with those of its iterated
spelling. -/
noncomputable abbrev totalHomologyIso (i : ℤ) :=
  homologyIsoOfComplexIso (totalCompIso f g) i

/-- On cohomology sheaves the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` is the one of
Stacks 0E1Z followed by the comparison with the iterated spelling. -/
theorem homologyMap_pullbackToTotalMap (i : ℤ) :
    HomologicalComplex.homologyMap (pullbackToTotalMap f g) i =
      HomologicalComplex.homologyMap (iteratedPullbackMap f g) i ≫
        (totalHomologyIso f g i).inv :=
  HomologicalComplex.homologyMap_comp _ _ i

/-- On cohomology sheaves the canonical map `NL_{X/Z} ⟶ NL_{X/Y}` is the comparison with the
iterated spelling followed by the one of Stacks 0E1Z. -/
theorem homologyMap_totalToRelativeMap (i : ℤ) :
    HomologicalComplex.homologyMap (totalToRelativeMap f g) i =
      (totalHomologyIso f g i).hom ≫
        HomologicalComplex.homologyMap (iteratedRelativeMap f g) i :=
  HomologicalComplex.homologyMap_comp _ _ i

/-- The comparison of `H^i(NL_{X/Z})` with its iterated spelling turns the canonical map
`NL_{X/Z} ⟶ NL_{X/Y}` into the one of Stacks 0E1Z. -/
theorem totalHomologyIso_inv_comp_homologyMap_totalToRelativeMap (i : ℤ) :
    (totalHomologyIso f g i).inv ≫
        HomologicalComplex.homologyMap (totalToRelativeMap f g) i =
      HomologicalComplex.homologyMap (iteratedRelativeMap f g) i :=
  by rw [homologyMap_totalToRelativeMap]; exact Iso.inv_hom_id_assoc _ _

/-! ### The first three terms -/

/-- The composite of the two canonical maps is the composite of the two canonical maps of
Stacks 0E1Z, the comparison with the iterated spelling cancelling. -/
theorem pullbackToTotalMap_comp_totalToRelativeMap :
    pullbackToTotalMap f g ≫ totalToRelativeMap f g =
      iteratedPullbackMap f g ≫ iteratedRelativeMap f g :=
  (Category.assoc _ _ _).trans
    (congrArg (fun t => iteratedPullbackMap f g ≫ t)
      (Iso.inv_hom_id_assoc (totalCompIso f g) (iteratedRelativeMap f g)))

/-- On cohomology sheaves the composite of the two canonical maps is zero. -/
theorem homologyMap_pullbackToTotalMap_comp_totalToRelativeMap (i : ℤ) :
    HomologicalComplex.homologyMap (pullbackToTotalMap f g) i ≫
      HomologicalComplex.homologyMap (totalToRelativeMap f g) i = 0 :=
  (HomologicalComplex.homologyMap_comp (pullbackToTotalMap f g)
        (totalToRelativeMap f g) i).symm.trans
    ((congrArg (fun φ => HomologicalComplex.homologyMap φ i)
        (pullbackToTotalMap_comp_totalToRelativeMap f g)).trans
      ((HomologicalComplex.homologyMap_comp (iteratedPullbackMap f g)
          (iteratedRelativeMap f g) i).trans
        (homologyMap_ringedSpaceBaseChange_comp_relative (ringedSpaceHom f)
          (ringedSpaceHom g) i)))

/-- The sequence `H^i(f^*NL_{Y/Z}) ⟶ H^i(NL_{X/Z}) ⟶ H^i(NL_{X/Y})` is the corresponding
sequence of Stacks 0E1Z of the underlying morphisms of ringed spaces, with its middle term read
on `NL_{f ≫ g}`. -/
noncomputable def homologySequenceIso (i : ℤ) :
    ringedSpaceJacobiZariskiHomologySequence (ringedSpaceHom f) (ringedSpaceHom g) i ≅
      ShortComplex.mk (HomologicalComplex.homologyMap (pullbackToTotalMap f g) i)
        (HomologicalComplex.homologyMap (totalToRelativeMap f g) i)
        (homologyMap_pullbackToTotalMap_comp_totalToRelativeMap f g i) :=
  ShortComplex.isoMk (Iso.refl _) (totalHomologyIso f g i).symm (Iso.refl _)
    ((Category.id_comp _).trans (homologyMap_pullbackToTotalMap f g i))
    ((totalHomologyIso_inv_comp_homologyMap_totalToRelativeMap f g i).trans
      (Category.comp_id _).symm)

/-- **Stacks 0E44, exactness at `H^{-1}(NL_{X/Z})`.**  For morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` the sequence

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y})`

of cohomology sheaves is exact at the middle term.  This is the corresponding assertion of
Stacks 0E1Z for the underlying morphisms of ringed spaces. -/
@[stacks 0E44 "exactness of the six term sequence at its second term, H^{-1}(NL_{X/Z})"]
theorem exact_sixTerm_negOne_total :
    (ShortComplex.mk (HomologicalComplex.homologyMap (pullbackToTotalMap f g) (-1))
      (HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1))
      (homologyMap_pullbackToTotalMap_comp_totalToRelativeMap f g (-1))).Exact :=
  ShortComplex.exact_of_iso (homologySequenceIso f g (-1))
    (exact_ringedSpaceJacobiZariskiHomologySequence_negOne (ringedSpaceHom f) (ringedSpaceHom g))

/-- **Stacks 0E44, the connecting map** `∂ : H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z})` of the six
term sequence, for morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`: the connecting map of
Stacks 0E1Z of the underlying morphisms of ringed spaces. -/
@[stacks 0E44 "the connecting map H^{-1}(NL_{X/Y}) -> H^0(f^*NL_{Y/Z}), the third arrow of \
the six term sequence"]
noncomputable def jacobiZariskiConnecting :
    (Scheme.naiveCotangentComplex f).homology (-1) ⟶
      (pullbackNaiveCotangentComplex f g).homology 0 :=
  ringedSpaceJacobiZariskiConnecting (ringedSpaceHom f) (ringedSpaceHom g)

/-- The composite `H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z})` vanishes. -/
theorem homologyMap_totalToRelativeMap_comp_connecting :
    HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1) ≫
      jacobiZariskiConnecting f g = 0 := by
  have h : HomologicalComplex.homologyMap (iteratedRelativeMap f g) (-1) ≫
      jacobiZariskiConnecting f g = 0 :=
    homologyMap_comp_ringedSpaceJacobiZariskiConnecting (ringedSpaceHom f) (ringedSpaceHom g)
  rw [homologyMap_totalToRelativeMap]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (totalHomologyIso f g (-1)).hom ≫ t) h).trans Limits.comp_zero)

/-- The sequence `H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z})` is the
corresponding segment of the sequence of Stacks 0E1Z, with its first term read on
`NL_{f ≫ g}`. -/
noncomputable def sixTermNegOneIso :
    ShortComplex.mk
        (HomologicalComplex.homologyMap (iteratedRelativeMap f g) (-1))
        (ringedSpaceJacobiZariskiConnecting (ringedSpaceHom f) (ringedSpaceHom g))
        (homologyMap_comp_ringedSpaceJacobiZariskiConnecting (ringedSpaceHom f)
          (ringedSpaceHom g)) ≅
      ShortComplex.mk (HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1))
        (jacobiZariskiConnecting f g)
        (homologyMap_totalToRelativeMap_comp_connecting f g) :=
  ShortComplex.isoMk (totalHomologyIso f g (-1)).symm (Iso.refl _) (Iso.refl _)
    ((totalHomologyIso_inv_comp_homologyMap_totalToRelativeMap f g (-1)).trans
      (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Stacks 0E44, exactness at `H^{-1}(NL_{X/Y})`.**  For morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` the sequence

`H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E44 "exactness of the six term sequence at its third term, H^{-1}(NL_{X/Y})"]
theorem exact_sixTerm_negOne_relative :
    (ShortComplex.mk (HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1))
      (jacobiZariskiConnecting f g)
      (homologyMap_totalToRelativeMap_comp_connecting f g)).Exact :=
  ShortComplex.exact_of_iso (sixTermNegOneIso f g)
    (exact_ringedSpaceJacobiZariskiSixTerm_negOne (ringedSpaceHom f) (ringedSpaceHom g))

/-- The composite `H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z}) ⟶ H^0(NL_{X/Z})` vanishes. -/
theorem connecting_comp_homologyMap_pullbackToTotalMap :
    jacobiZariskiConnecting f g ≫
      HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0 = 0 := by
  have h : jacobiZariskiConnecting f g ≫
      HomologicalComplex.homologyMap (iteratedPullbackMap f g) 0 = 0 :=
    ringedSpaceJacobiZariskiConnecting_comp_homologyMap (ringedSpaceHom f) (ringedSpaceHom g)
  rw [homologyMap_pullbackToTotalMap, ← Category.assoc, h, zero_comp]

/-- The sequence `H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z}) ⟶ H^0(NL_{X/Z})` is the
corresponding segment of the sequence of Stacks 0E1Z, with its last term read on
`NL_{f ≫ g}`. -/
noncomputable def sixTermZeroIso :
    ShortComplex.mk
        (ringedSpaceJacobiZariskiConnecting (ringedSpaceHom f) (ringedSpaceHom g))
        (HomologicalComplex.homologyMap (iteratedPullbackMap f g) 0)
        (ringedSpaceJacobiZariskiConnecting_comp_homologyMap (ringedSpaceHom f)
          (ringedSpaceHom g)) ≅
      ShortComplex.mk (jacobiZariskiConnecting f g)
        (HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0)
        (connecting_comp_homologyMap_pullbackToTotalMap f g) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (totalHomologyIso f g 0).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (homologyMap_pullbackToTotalMap f g 0))

/-! ### The fourth term, and the two models of `f^*NL_{Y/Z}` -/

/-- **The two models of `f^*NL_{Y/Z}` agree.**  The termwise pullback of `NL_{Y/Z}` under
Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback` is the inverse image of `NL_{Y/Z}` with
scalars extended to `𝒪_X`, which is the model of Stacks 08TM and 0E1Z the first four terms of
the sequence are written over.

This is `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep`, the identification of Mathlib's
abstract left adjoint with the two-step model, applied termwise. -/
noncomputable def pullbackComplexIso :
    pullbackNaiveCotangentComplex f g ≅ modulePullbackNaiveCotangentComplex f g :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep (ringedSpaceHom f)).app
      ((Scheme.naiveCotangentComplex g).X i)).symm)
    (fun i j _ => ((RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep
      (ringedSpaceHom f)).inv.naturality ((Scheme.naiveCotangentComplex g).d i j)).symm)

/-- **Stacks 0E44, the fourth term.**  The degree `0` cohomology sheaf of `f^*NL_{Y/Z}` is
`f^*Ω_{Y/Z}`.

The pullback is the one of Stacks 08TM and 0E1Z, the inverse image with scalars extended, which
is the model the first four terms of the sequence are written over; `pullbackComplexIso`
identifies it with Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`, for which the degree
`0` identification is
`Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso`.  It is
this identification that makes the connecting map land in `f^*Ω_{Y/Z}`, so that the three terms
proved here and the three degree `0` terms are one sequence. -/
@[stacks 0E44 "the fourth term: the identification H^0(f^*NL_{Y/Z}) = f^*Omega_{Y/Z} for the \
inverse-image-then-extend-scalars model of the pullback, the model the first four terms are \
written over"]
noncomputable def pullbackHomologyZeroIso :
    (pullbackNaiveCotangentComplex f g).homology 0 ≅
      (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g) :=
  homologyIsoOfComplexIso (pullbackComplexIso f g) 0 ≪≫
    modulePullbackNaiveCotangentComplexHomologyZeroIso f g

/-- **Stacks 0E44, the third arrow with its target written as `f^*Ω_{Y/Z}`.**  The connecting
map of the six term sequence, read through the identification of its target `H^0(f^*NL_{Y/Z})`
with `f^*Ω_{Y/Z}`. -/
@[stacks 0E44 "the connecting map with its target written as f^*Omega_{Y/Z}"]
noncomputable def connectingDifferentials :
    (Scheme.naiveCotangentComplex f).homology (-1) ⟶
      (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g) :=
  jacobiZariskiConnecting f g ≫ (pullbackHomologyZeroIso f g).hom

/-- **Stacks 0E44, exactness at `H^0(f^*NL_{Y/Z})`.**  For morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` the sequence

`H^{-1}(NL_{X/Y}) --∂--> H^0(f^*NL_{Y/Z}) ⟶ H^0(NL_{X/Z})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E44 "exactness of the six term sequence at its fourth term, \
H^0(f^*NL_{Y/Z}) = f^*Omega_{Y/Z}"]
theorem exact_sixTerm_zero_pullback :
    (ShortComplex.mk (jacobiZariskiConnecting f g)
      (HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0)
      (connecting_comp_homologyMap_pullbackToTotalMap f g)).Exact :=
  ShortComplex.exact_of_iso (sixTermZeroIso f g)
    (exact_ringedSpaceJacobiZariskiSixTerm_zero (ringedSpaceHom f) (ringedSpaceHom g))

/-! ### The last two nodes, in the same coordinates -/

/-- **Stacks 0E44, exactness at `H^0(NL_{X/Z})`.**  For morphisms of schemes `f : X ⟶ Y` and
`g : Y ⟶ Z` the sequence

`H^0(f^*NL_{Y/Z}) ⟶ H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`

of cohomology sheaves is exact at the middle term.  With the degree `0` identifications of
Stacks 0D0J and `pullbackHomologyZeroIso` this is exactness at `Ω_{X/Z}`; it is stated on the
cohomology sheaves so that it is the same sequence as the three nodes above. -/
@[stacks 0E44 "exactness of the six term sequence at its fifth term, \
H^0(NL_{X/Z}) = Omega_{X/Z}"]
theorem exact_sixTerm_zero_total :
    (ShortComplex.mk (HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0)
      (HomologicalComplex.homologyMap (totalToRelativeMap f g) 0)
      (homologyMap_pullbackToTotalMap_comp_totalToRelativeMap f g 0)).Exact :=
  ShortComplex.exact_of_iso (homologySequenceIso f g 0)
    (exact_ringedSpaceJacobiZariskiHomologySequence_zero (ringedSpaceHom f) (ringedSpaceHom g))

/-- **Stacks 0E44, the final `⟶ 0`.**  The canonical map `NL_{X/Z} ⟶ NL_{X/Y}` is surjective on
degree `0` cohomology sheaves, that is, the six term sequence is exact at `H^0(NL_{X/Y})`.  With
the degree `0` identification of Stacks 0D0J this is exactness at `Ω_{X/Y}`. -/
@[stacks 0E44 "the final `-> 0` of the six term sequence, its exactness at \
H^0(NL_{X/Y}) = Omega_{X/Y}"]
theorem epi_homologyMap_totalToRelativeMap_zero :
    Epi (HomologicalComplex.homologyMap (totalToRelativeMap f g) 0) := by
  have he : Epi (HomologicalComplex.homologyMap (iteratedRelativeMap f g) 0) :=
    epi_homologyMap_ringedSpaceRelativeNaiveCotangentComplexMap_zero
      (ringedSpaceHom f) (ringedSpaceHom g)
  rw [homologyMap_totalToRelativeMap]
  exact (epi_comp_iff_of_epi _ _).2 he

end Stacks.NaiveCotangentSixTermSequence

end

end
