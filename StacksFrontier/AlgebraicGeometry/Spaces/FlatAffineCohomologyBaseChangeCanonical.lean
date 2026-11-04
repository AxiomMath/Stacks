module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeIso
import StacksCore.Tactic.StacksAttribute

/-!
# Towards Stacks 073K, part (2) for the *canonical* comparison map

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine and `g` flat, **Stacks 073K, part (2)** asserts
that `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`.  Two forms of that assertion are available, and they are
not interchangeable:

* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase` — a *chosen*
  `B`-linear isomorphism between the two sides, which is what carries the `@[stacks 073K]`
  attribute for part (2);
* `IsIso (AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap …)` — that the
  *canonical* comparison map is invertible.  This is what part (1) needs: after étale
  localisation part (1) has to identify the base-change map of **Stacks 0736** with the affine
  case, and a chosen isomorphism with the right endpoints does not plug in.  **It is proved** —
  `AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`).

This file is the reduction of the second form to one equation of morphisms of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap`: the canonical `s ↦ s ⊗ 1`,
  `𝓕 ⟶ 𝓕 ⊗_A B`, as a morphism of `𝒪_X`-modules.

## Main results

* `Stacks.FlatDevissage.tensorComparisonUniv_map_spanHom` and
  `Stacks.FlatDevissage.tensorLeftObjIso_map_spanHom_comp_tensorComparisonUniv`: **the transpose
  of the dévissage comparison along `x ↦ x ⊗ m`.**  A morphism out of the free module of rank
  one is `Stacks.FlatDevissage.spanHom`, the comparison is natural, and at the free module of
  rank one it is the right unitor; so precomposing the comparison with `x ↦ x ⊗ m` gives the
  unitor followed by the functor applied to `spanHom m`.  Nothing here is geometric.
* `AlgebraicGeometry.Space.BaseChangeDiagram.spanHom_comp_affineCohomologyBaseChangeIso_hom`:
  **the transpose of the `A`-linear isomorphism of part (2) along `x ↦ x ⊗ 1`** is `H^i(X, −)`
  of `s ↦ s ⊗ 1` followed by the sheaf identification `𝓕 ⊗_A B = g'_*𝓕'` and then by the
  collapse.  This is the whole formal half of the identification of the chosen isomorphism with
  the canonical map.
* `Stacks.TensorByBaseModule.tensorOneSheafify`: **`s ↦ s ⊗ m` followed by a glued comparison is
  computed on presheaves.**  The gluing step of
  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom` is a transposition across
  the sheafification adjunction, so an identification of such a composite with a morphism of
  sheaves follows from the corresponding equation of presheaves — which is checkable on sections.
  This is what takes the sheafification out of the remaining step; see the implementation notes.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap_of_homEquiv_eq`:
  **the criterion.**  To know that the canonical map is invertible it suffices to exhibit *any*
  isomorphism between the two sides whose transpose across the adjunction between extension and
  restriction of scalars is
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase`; the transposition
  is a bijection and
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint` says the
  canonical map has the same transpose.

## Implementation notes

*That equation is proved.*  It is

```
tensorOneMap ≫ (pushforwardTensorChartIso).hom
  = (modulePullbackAdjunction g').unit.app 𝓕 ≫ (modulePushforwardChartIso.app pulledBack).hom
```

— that the sheaf identification `𝓕 ⊗_A B ≅ g'_*𝓕'` of
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso` carries `s ⊗ 1` to the
unit of `(g')^* ⊣ g'_*` at `s` — and it is
`AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap_comp_pushforwardTensorChartIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeUnitEquation.lean`), whose
module docstring records how.  The three steps the rest of this section describes were all
affordable: step 1 is
`Stacks.TensorByBaseModule.unitIso_inv_comp_map_spanHom_app`, step 2 is
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_one_tmul_one`, and step 3
is `AlgebraicGeometry.Space.BaseChangeDiagram.modulePushforwardChartIso_unit_val_app`, where the
two chart indices turn out to be the *same* structured arrow, so that
`AlgebraicGeometry.Space.chartSetProj_eq_moduleChartProjection` closes it after a `rfl` and the
general-index lemma named below is not needed.

*How `IsIso (affineCohomologyBaseChangeMap …)` is proved.*
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`)
reaches the conclusion **without** going through the criterion
below.  Item 1 is `ModuleCat.extendRestrictScalarsAdj_homEquiv_hom_apply`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeTranspose.lean`).  Item 3
needs nothing, `IsAffineSpace` being a proposition.  Item 2 — the chart-versus-global passage —
is `AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalPartTwo.lean`),
and it is *not* an isomorphism of the two seatings: the two sides are tensor products over
different rings, so it is only a surjection, which is why the criterion — which asks for an
isomorphism between the *global* seatings — is not used and bijectivity is proved
directly instead.

Feeding that equation into
`AlgebraicGeometry.Space.BaseChangeDiagram.spanHom_comp_affineCohomologyBaseChangeIso_hom`
turns `H^i` of `s ↦ s ⊗ 1` followed by the sheaf identification and then by
`(modulePushforwardChartIso.app pulledBack).inv` into `H^i` of the unit of `(g')^* ⊣ g'_*`; and
`AlgebraicGeometry.Space.cohomologyPullbackMap` *is* `H^i` of that unit followed by the inverse
of the collapse, so the transpose of the chosen isomorphism acquires the shape of
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase`.  Three things are
then left before
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap_of_homEquiv_eq`
can be applied, none of them about the square:

1. that the transpose across `ModuleCat.extendRestrictScalarsAdj` of a map out of an extension
   of scalars is precomposition with `x ↦ x ⊗ 1`, which is the shape
   `spanHom_comp_affineCohomologyBaseChangeIso_hom` computes;
2. the passage from the *chart* spellings the chosen isomorphism is stated in —
   `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBaseChart` and
   `AlgebraicGeometry.Space.baseChartRestrictScalars` — to the global ones that
   `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologySource` and
   `affineCohomologyPullbackOverBase` use, which is
   `AlgebraicGeometry.Space.globalSectionsChartRingEquiv` at a terminal chart;
3. the reconciliation of the hypotheses: the criterion takes `IsAffineSpace` of the two bases
   while the chosen isomorphism takes the charts `V₀`, `V₀'` with `IsAffine (chartScheme …)`.

**The sheafification was never in the way.**
`Stacks.TensorByBaseModule.tensorOneSheafify` reduces an identification of that shape to an
equation of morphisms of *presheaves* of modules, which `PresheafOfModules.hom_ext` reduces in
turn to sections over each object of the site: the gluing step
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom` transposes the presheaf-level
comparison across the sheafification adjunction, and the transpose of a composite that factors
through the underlying presheaf of a sheaf cancels against the counit by the triangle identity.

The resulting chartwise equation, over a chart `W` of `X` and a section `s` of `𝓕` over `W`, took
three steps, all of them carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeUnitEquation.lean`:

1. that the presheaf-level `s ↦ s ⊗ 1` is `s ↦ s ⊗ₜ (1 ⊗ₜ 1)`, i.e. the inverse of
   `Stacks.TensorByBaseModule.tensorByBaseModulePresheafOfHomUnitIso` on sections — now
   `Stacks.TensorByBaseModule.unitIso_inv_comp_map_spanHom_app`;
2. that `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorComparison` sends
   `s ⊗ₜ (1 ⊗ₜ 1)` to the chart component of the unit — now
   `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_one_tmul_one`, which is
   `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_tmul` followed by
   `AlgebraicGeometry.Space.modulePullbackChartBaseChange_tmul` at the unit scalar, the scalar
   being `1` because `AlgebraicGeometry.Space.BaseChangeDiagram.chartRingTensorHom` is a ring
   map;
3. that `AlgebraicGeometry.Space.modulePushforwardChartIso` carries the unit's section to that
   same section — now
   `AlgebraicGeometry.Space.BaseChangeDiagram.modulePushforwardChartIso_unit_val_app`.

*The step-1 inverse, and why it was not a wall.*  Unfolding
`tensorByBaseModulePresheafOfHomUnitIso`, `tensorByBaseModulePresheafOfHom`,
`changeOfRingsUnitIso`, `constantModuleUnitIso` and `spanHom` turns step 1 into a
monoidal-coherence computation in `PMod O.val`: the right unitor's inverse followed by three
`whiskerLeft`s acting on the second tensor factor.  The first of those three is the inverse of

```
PresheafOfModules.ChangeOfRings.unitComparison
  (Functor.whiskerRight θ (forget₂ CommRingCat RingCat))
  (PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction θ)
```

which has no formula: `unitComparison α adj`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BaseChangeUnitor.lean`) is the adjoint transpose
`(adj.homEquiv _ _).symm (unitToRestrictScalarsUnit α)` and
`PresheafOfModules.ChangeOfRings.isIso_unitComparison` is proved by
`isIso_iff_coyoneda_map_bijective`, abstractly through Yoneda, so the inverse is never
constructed and no `inv …_app` lemma can be expected to exist.  No formula is needed, because the
inverse is only ever applied to `1`: `Stacks.TensorByBaseModule.changeOfRingsUnitIso_inv_app_one`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorByBaseModuleUnitSection.lean`) computes it
there as the image of `1` under the change-of-rings adjunction unit — which
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply` reads as
`1 ⊗ₜ 1` — out of the forward statement
`Stacks.TensorByBaseModule.changeOfRingsUnitIso_hom_app_unit_app_one` and
`CategoryTheory.Iso.hom_inv_id`.  The rest of step 1 is the right unitor of `PMod O.val` on
sections, which is `TensorProduct.rid` and holds by `rfl`, `constantModuleUnitIso` acting as the
identity, which also holds by `rfl`, and
`Stacks.PresheafOfModules.ChangeOfRings.cofHom_app_tmul` twice.

*Why the `A`-linear isomorphism and not the `B`-linear one.*
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso` takes the collapse in
the form `AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyPushforwardIso`, which is
*literally the isomorphism whose inverse appears in*
`AlgebraicGeometry.Space.cohomologyPullbackMap`; so no comparison of two collapses is needed.
The `B`-linear `affineCohomologyBaseChangeIsoBase` takes it in the form
`AlgebraicGeometry.Space.BaseChangeDiagram.naturalCohomologyPushforwardIso` instead — through
`Stacks.RightDerivedComp.objIso` rather than `Stacks.RightDerivedComp.objIsoOfAcyclicImage`,
because only that form carries naturality — and using it would additionally require those two
collapses to be identified.  Restriction of scalars reflects isomorphisms — a morphism of modules
is invertible exactly when its underlying map is bijective — so the `A`-linear form is enough
for an `IsIso` statement over `B` and that extra comparison is avoided.

**Both inputs of that last step exist** — the reflection step and the chart-ring passage — but
neither is used below.

* Reflection is Mathlib's, the anonymous instance
  `(ModuleCat.restrictScalars f).ReflectsIsomorphisms` of
  `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, applied through
  `CategoryTheory.isIso_of_reflects_iso`; the same file has the `Faithful` instance, and
  `CategoryTheory.ConcreteCategory.isIso_iff_bijective` is the bijectivity reading, already used
  in this development at
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompUnit.lean`.
* The passage between the coordinate ring of a chart and `Γ(Y, 𝒪_Y)` is
  `AlgebraicGeometry.Space.globalSectionsChartRingEquiv`
  (`StacksFrontier/AlgebraicGeometry/Spaces/GlobalSectionsTerminalChart.lean`), a ring equivalence
  at a terminal chart, and it is already composed with
  `AlgebraicGeometry.Space.globalSectionsRingHomSite` in
  `AlgebraicGeometry.Space.baseChartRingHom`
  (`StacksFrontier/AlgebraicGeometry/Spaces/BaseChartTensorByBaseModule.lean`).  What the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean` record as out of reach is
  a different statement — the compatibility of `AlgebraicGeometry.Space.baseRingHom` with
  `globalSectionsRingHomSite`, which would need a description of
  `Stacks.Cohomology.SiteModules.globalSectionsRingHom` on an actual family of sections — and
  that one is not needed here.

*Nothing here carries a `@[stacks 073K]` attribute.*  The tag asserts that a base change map is
an isomorphism, which no declaration below states; part (2) stays registered on
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.TensorByBaseModule

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u w v₂ u₂ w₂

namespace Stacks.FlatDevissage

variable {A : Type u} [CommRing A]
  (Φ : ModuleCat.{u} A ⥤ ModuleCat.{max u w} A) [Φ.Additive] [Functor.Linear A Φ]

/-- **The dévissage comparison, precomposed with the functor applied to a morphism out of the
free module of rank one, is the right unitor followed by the functor.**  The comparison is
natural, and `Stacks.FlatDevissage.tensorComparisonUniv_app_unit` computes it at the free module
of rank one. -/
theorem tensorComparisonUniv_map_spanHom {M : ModuleCat.{u} A} (m : M) :
    (tensorLeftFunctor.{u, max u w, u} (Φ.obj (unitModule A))).map (spanHom m) ≫
        (tensorComparisonUniv Φ).app M =
      (tensorComparisonUnivUnitIso Φ).hom ≫ Φ.map (spanHom m) := by
  rw [(tensorComparisonUniv Φ).naturality, tensorComparisonUniv_app_unit]

/-- **The transpose of the dévissage comparison along `x ↦ x ⊗ m`.**  Here `Φ(A)` is identified
with some other module `H` by `e`, which is the shape the geometric consumer has it in: `H` is
`H^i(X, 𝓕)` and `Φ(A)` is `H^i(X, 𝓕 ⊗_A A)`.  The two steps are the naturality of
`Stacks.FlatDevissage.tensorLeftObjIso` in the second factor and the previous lemma. -/
@[reassoc]
theorem tensorLeftObjIso_map_spanHom_comp_tensorComparisonUniv {H : ModuleCat.{max u w} A}
    (e : H ≅ Φ.obj (unitModule A)) {M : ModuleCat.{u} A} (m : M) :
    (tensorLeftFunctor.{u, max u w, u} H).map (spanHom m) ≫
        ((tensorLeftObjIso e M).hom ≫ (tensorComparisonUniv Φ).app M) =
      (TensorProduct.rid A H).toModuleIso.hom ≫ e.hom ≫ Φ.map (spanHom m) := by
  have hnat : (tensorLeftFunctor.{u, max u w, u} H).map (spanHom m) ≫ (tensorLeftObjIso e M).hom =
      (tensorLeftObjIso e (unitModule A)).hom ≫
        (tensorLeftFunctor.{u, max u w, u} (Φ.obj (unitModule A))).map (spanHom m) :=
    ModuleCat.hom_ext (TensorProduct.ext' fun _ _ ↦ rfl)
  have hunit : (tensorLeftObjIso e (unitModule A)).hom ≫ (tensorComparisonUnivUnitIso Φ).hom =
      (TensorProduct.rid A H).toModuleIso.hom ≫ e.hom :=
    ModuleCat.hom_ext (TensorProduct.ext' fun x a ↦ (map_smul e.hom.hom a x).symm)
  rw [← Category.assoc, hnat, Category.assoc, tensorComparisonUniv_map_spanHom,
    ← Category.assoc, hunit]
  exact Category.assoc _ _ _

end Stacks.FlatDevissage

namespace Stacks.TensorByBaseModule

open Stacks.FlatDevissage

variable {C : Type u₂} [CategoryTheory.Category.{v₂} C] (R : Type w₂) [CommRing R]
  (J : CategoryTheory.GrothendieckTopology C)
  [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (O : CategoryTheory.Sheaf J CommRingCat.{w₂})
  (𝓕 : SheafOfModules.{w₂} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.val)
  [J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{w₂}]

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{w₂} RingCat.{w₂})] in
/-- **The transposition `Stacks.TensorByBaseModule.sheafify` uses is the one of its
adjunction.**  `PresheafOfModules.sheafificationHomEquiv` and the `homEquiv` of
`PresheafOfModules.sheafificationAdjunction` are the same bijection — pointwise by definition —
so the adjunction's naturality and triangle identities apply to the transposes that
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfHom` is built from. -/
theorem sheafificationAdjunction_homEquiv_eq (P : PresheafOfModules (ringSheaf J O).obj)
    (F : SheafOfModules.{w₂} (ringSheaf J O)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).homEquiv P F =
      PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj) :=
  Equiv.ext fun _ ↦ rfl

omit [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{w₂} RingCat.{w₂})] in
/-- **The transpose of a presheaf morphism that factors through the underlying presheaf of a
sheaf.**  If `u` lands in `𝓕` read as a presheaf and is then followed by a morphism `ψ` of
sheaves, its transpose is the sheafification of `u` followed by the sheafification counit and
`ψ`.  The counit cancels the unit by the triangle identity, which is why no trace of the
transposition is left on `ψ`. -/
theorem comp_symm_map_of_sheaf (P : PresheafOfModules (ringSheaf J O).obj)
    (F : SheafOfModules.{w₂} (ringSheaf J O))
    (ψ : 𝓕 ⟶ F)
    (u : P ⟶ (SheafOfModules.forget (ringSheaf J O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj 𝓕) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).homEquiv P F).symm
        (u ≫ (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map u ≫
        (PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf J O).obj)).counit.app 𝓕 ≫ ψ := by
  rw [Adjunction.homEquiv_naturality_left_symm]
  refine congrArg ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map u ≫ ·) ?_
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]

/-- **`s ↦ s ⊗ m` followed by a glued comparison is computed on presheaves.**

`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfHom` glues a locally bijective comparison `Φ`
out of the *presheaf*-level tensor product into an isomorphism `𝓕 ⊗_R M ≅ G` of sheaves, and it
does so by transposing `Φ` across the sheafification adjunction.  Consequently a composite
`𝓕 ⟶ 𝓕 ⊗_R M ⟶ G` whose first leg is `s ↦ s ⊗ m` is determined by the corresponding composite
of *presheaves*: if that composite is a morphism `ψ` of sheaves read on underlying presheaves,
then the sheaf-level composite is `ψ`.

This is what removes the sheafification from such an identification: the hypothesis `h` is an
equation of morphisms of presheaves of modules, which `PresheafOfModules.hom_ext` reduces to
sections over each object of the site. -/
theorem tensorOneSheafify (M : ModuleCat.{w₂} R) (m : M)
    (G : SheafOfModules.{w₂} (ringSheaf J O))
    (Φ : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
        ((SheafOfModules.forget (ringSheaf J O)).obj G))
    [CategoryTheory.Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)]
    [CategoryTheory.Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map Φ)]
    (ψ : 𝓕 ⟶ G)
    (h : (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).inv ≫
          (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m) ≫ Φ =
        (SheafOfModules.forget (ringSheaf J O) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).map ψ) :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).map (spanHom m) ≫
        (tensorByBaseModuleIsoOfHom R J O 𝓕 θ M G Φ).hom =
      (tensorByBaseModuleOfHomUnitIso R J O 𝓕 θ).hom ≫ ψ := by
  show (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
          ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).map (spanHom m)) ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O).obj)).symm Φ =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
          (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit.app 𝓕 ≫ ψ
  rw [← sheafificationAdjunction_homEquiv_eq, ← Adjunction.homEquiv_naturality_left_symm]
  exact (congrArg (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O).obj)).homEquiv
        ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj (unitModule R)) G).symm)
    ((Iso.inv_comp_eq _).mp h)).trans
    (comp_symm_map_of_sheaf J O 𝓕 _ G ψ
      (tensorByBaseModulePresheafOfHomUnitIso R J O 𝓕 θ).hom)

end Stacks.TensorByBaseModule

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace BaseChangeDiagram

variable {B S hS} (D : BaseChangeDiagram B S hS)
  (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- **The canonical map `𝓕 ⟶ 𝓕 ⊗_A B`, `s ↦ s ⊗ 1`**: the inverse of `𝓕 ⊗_A A ≅ 𝓕` followed by
tensoring with the `A`-linear `a ↦ a • 1 : A ⟶ B`.

This is the sheaf-level morphism whose cohomology the transpose of part (2)'s comparison is,
by `AlgebraicGeometry.Space.BaseChangeDiagram.spanHom_comp_affineCohomologyBaseChangeIso_hom`.
Its identification, across `𝓕 ⊗_A B ≅ g'_*𝓕'`, with the unit of `(g')^* ⊣ g'_*` — described by
this file's implementation notes as the only mathematical content left, and recorded here as
missing — is
`AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap_comp_pushforwardTensorChartIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeUnitEquation.lean`). -/
def tensorOneMap (hV₀ : IsTerminal V₀) :
    D.F ⟶ (tensorByBaseChartModule B S hS D.f hV₀ D.F).obj (D.baseModule V₀ V₀') :=
  (tensorByBaseChartModuleUnitIso B S hS D.f hV₀ D.F).inv ≫
    (tensorByBaseChartModule B S hS D.f hV₀ D.F).map
      (spanHom (M := D.baseModule V₀ V₀') (1 : baseChartRing B S hS D.Y' V₀'))

/-- **The `A`-linear isomorphism of part (2), written out as a composite of morphisms.**  It is
its own definition unfolded: the dévissage, the two sheaf identifications, the collapse and the
reassociation of the two restrictions of scalars.  It is stated separately, and used as a rewrite
rule, because asking the reduction below to unfold the definition on its own is expensive. -/
theorem affineCohomologyBaseChangeIso_hom (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ) :
    have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
    letI hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
    letI hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
    letI hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
    letI hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
    letI hXqc : IsQuasiCompactSpace B S hS D.X.1 :=
      isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS D.f.hom hY hqc
    letI hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1 :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ D.f.hom
        D.X.property hY hqs
    (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom =
      (tensorLeftObjIso (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm
          (D.baseModule V₀ V₀')).hom ≫
        (cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).app
          (D.baseModule V₀ V₀') ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv ≫
        (globalSectionsRestrictScalars B S hS D.f ⋙
            baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.cohomologyPushforwardIso hg hY hY' i).inv ≫
        (baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.restrictScalarsSquareIso.hom.app
            (((globalSectionsFunctor.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
                i).obj D.pulledBack)) :=
  rfl

/-- **The first two steps of the reduction, gathered under `H^i(X, −)`**: the inverse of
`𝓕 ⊗_A A ≅ 𝓕`, the scalar extension `a ↦ a • 1` and the sheaf identification `𝓕 ⊗_A B = g'_*𝓕'`
are the cohomology of the single morphism
`AlgebraicGeometry.Space.BaseChangeDiagram.tensorOneMap` followed by that identification. -/
theorem cohomologyFunctorOverBaseChart_tensorOneMap_assoc
    (hg' : yoneda.relativelyRepresentable D.g'.hom) (hV₀ : IsTerminal V₀)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    {T : ModuleCat.{u + 1} (baseChartRing B S hS D.Y V₀)}
    (r : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).obj (D.pushforwardPulledBack hg') ⟶ T) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm.hom ≫
        (cohomologyTensorFunctor B S hS D.f hV₀ D.F i).map
          (spanHom (M := D.baseModule V₀ V₀') (1 : baseChartRing B S hS D.Y' V₀')) ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom ≫ r =
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.tensorOneMap V₀ V₀' hV₀ ≫ (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom) ≫ r := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  rw [tensorOneMap, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  rfl

/-- **The transpose of the `A`-linear isomorphism of part (2) along `x ↦ x ⊗ 1`.**  It is
`H^i(X, −)` of `s ↦ s ⊗ 1` followed by the sheaf identification `𝓕 ⊗_A B = g'_*𝓕'`, then by the
collapse `H^i(X, g'_*𝓕') = H^i(X', 𝓕')` and the reassociation of the restrictions of scalars.

Since a morphism out of an extension of scalars is determined by its transpose, this is the
formal half of the identification of the chosen isomorphism of part (2) with the canonical
comparison map: what remains is to recognise `s ↦ s ⊗ 1` followed by the sheaf identification as
the unit of `(g')^* ⊣ g'_*`, after which the right hand side becomes
`AlgebraicGeometry.Space.cohomologyPullbackMap` for `g'` read over `A`, that is
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase`.

*The statement is pinned to one spelling of the cohomology module.*  It writes that
module as `(cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).obj D.F` throughout, the
spelling of the preceding
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom`, rather
than mixing it with `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBaseChart`,
whose body inlines `isTerminal_of_isIso_chart` where this statement binds `hV₀`.  The two
denote the same module, but `IsTerminal` is data and not a `Prop`, so proof irrelevance
cannot identify the two terminality witnesses: a statement that mixed the spellings would
be checked against the finished proof term only by unfolding the whole cohomology tower.
-/
theorem spanHom_comp_affineCohomologyBaseChangeIso_hom (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ) :
    have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
    letI hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
    letI hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
    letI hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
    letI hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
    (tensorLeftFunctor.{u, u + 1, u}
        ((cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).obj D.F)).map
          (spanHom (M := D.baseModule V₀ V₀') (1 : baseChartRing B S hS D.Y' V₀')) ≫
        (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom =
      (TensorProduct.rid (baseChartRing B S hS D.Y V₀)
            ((cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).obj D.F)).toModuleIso.hom ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          (D.tensorOneMap V₀ V₀' hV₀ ≫ (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom) ≫
        (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map
          ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv ≫
        (globalSectionsRestrictScalars B S hS D.f ⋙
            baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.cohomologyPushforwardIso hg hY hY' i).inv ≫
        (baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.restrictScalarsSquareIso.hom.app
            (((globalSectionsFunctor.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
                i).obj D.pulledBack)) := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  have : Functor.Linear (baseChartRing B S hS D.Y V₀)
      (cohomologyTensorFunctor B S hS D.f
        (isTerminal_of_isIso_chart B S hS D.Y V₀) D.F i) :=
    linear_cohomologyTensorFunctor B S hS D.f
      (isTerminal_of_isIso_chart B S hS D.Y V₀) D.F i
  rw [affineCohomologyBaseChangeIso_hom]
  refine (tensorLeftObjIso_map_spanHom_comp_tensorComparisonUniv_assoc
    (cohomologyTensorFunctor B S hS D.f (isTerminal_of_isIso_chart B S hS D.Y V₀) D.F i)
    (cohomologyTensorFunctorUnitIso B S hS D.f
      (isTerminal_of_isIso_chart B S hS D.Y V₀) D.F i).symm
    (M := D.baseModule V₀ V₀') (1 : baseChartRing B S hS D.Y' V₀') _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg ((TensorProduct.rid (baseChartRing B S hS D.Y V₀)
      ((cohomologyFunctorOverBaseChart B S hS D.f
          (isTerminal_of_isIso_chart B S hS D.Y V₀) i).obj D.F)).toModuleIso.hom ≫ ·)
    ((Category.assoc _ _ _).trans
      (D.cohomologyFunctorOverBaseChart_tensorOneMap_assoc V₀ V₀'
        (D.relativelyRepresentable_g' (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
          (isAffineSpace_of_isIso_chart B S hS D.Y' V₀'))
        (isTerminal_of_isIso_chart B S hS D.Y V₀) i _))

/-- **A criterion for part (2) in canonical form: the canonical comparison map of part (2) is
an isomorphism as soon as some isomorphism between its two sides has the pullback map on
cohomology as its transpose.**

The transposition across the adjunction between extension and restriction of scalars along
`A ⟶ B` is a bijection, and
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_adjoint` says that the
canonical map's transpose is exactly
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase`; so a competitor
with the same transpose *is* the canonical map, and invertibility transfers.

It carries no `@[stacks 073K]` attribute: it asserts nothing about the square, only that one
hypothesis implies another.

*It is not how part (2) in canonical form was finally proved.*  Its hypothesis is an isomorphism
between the two *global* seatings, and what the chart-level work produces is a surjection and
not an isomorphism — the two seatings being tensor products over different rings.
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`)
therefore proves bijectivity of the canonical map directly.  This declaration is kept because it
is the cheapest route for any *future* consumer that does hold such an isomorphism. -/
theorem isIso_affineCohomologyBaseChangeMap_of_homEquiv_eq (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ)
    (e : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
      (D.affineCohomologySource i ≅ D.affineCohomologyTarget i))
    (he : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
      have := enoughInjectives_modules B S hS D.X.1 D.X.2
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          (globalSectionsRingHomSite B S hS D.g)).homEquiv _ _) e.hom =
        D.affineCohomologyPullbackOverBase hg hY hY' i) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    IsIso (D.affineCohomologyBaseChangeMap hg hY hY' i) := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  have key : D.affineCohomologyBaseChangeMap hg hY hY' i = e.hom :=
    ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (globalSectionsRingHomSite B S hS D.g)).homEquiv _ _).injective
      ((D.affineCohomologyBaseChangeMap_adjoint hg hY hY' i).trans he.symm)
  rw [key]
  exact e.isIso_hom

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
