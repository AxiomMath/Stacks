module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs

/-!
# Relative pseudo-coherence on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `E` be an object of `D_QCoh(𝒪_X)` and let `m` be an integer. Then `E` is
*`m`-pseudo-coherent relative to `Y`* when, for every commuting square of étale scheme charts

```
U ⟶ V
↓    ↓
X ⟶ Y
```

with `U` and `V` affine, the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent
relative to the ring `𝒪_Y(V)`; and *pseudo-coherent relative to `Y`* when that holds for every
`m`. A quasi-coherent `𝒪_X`-module is called relatively `m`-pseudo-coherent, resp. relatively
pseudo-coherent, when the complex it determines in degree zero is.

## Main definitions

* `AlgebraicGeometry.Space.chartDerivedSections` is `RΓ(U, E)`, the derived sections of a
  complex of `𝒪_X`-modules over an étale scheme chart, as a complex of modules over the ring
  of regular functions on the chart.
* `AlgebraicGeometry.Space.IsRelativelyPseudoCoherentFrom` and
  `AlgebraicGeometry.Space.IsRelativelyPseudoCoherent` are parts (1) and (2) of Stacks 0CSY,
  for an object of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.IsModuleRelativelyPseudoCoherentFrom` and
  `AlgebraicGeometry.Space.IsModuleRelativelyPseudoCoherent` are parts (3) and (4) of
  Stacks 0CSY, for a quasi-coherent `𝒪_X`-module.

## Main results

* `AlgebraicGeometry.Space.hasRightDerivedFunctor_chartSections`: sections over an étale chart
  have an unbounded right derived functor, so `RΓ(U, -)` exists with no hypothesis.
* `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_forall` and
  `AlgebraicGeometry.Space.isModuleRelativelyPseudoCoherent_iff_forall` expose parts (2) and
  (4) as the conjunction over all `m` of parts (1) and (3), by definition.

## Which of the equivalent conditions of Tag 0CSX is taken as the definition

Stacks 0CSY defines relative `m`-pseudo-coherence by "the equivalent conditions of Lemma
0CSX are satisfied", so any one of the three conditions of that lemma defines the notion.
**Condition (3) is taken here**: the affine one, on the derived sections `RΓ(U, E)` over the
affine étale charts.

Condition (3) is the only one of the three that is a statement of this development. Conditions
(1) and (2) are about `E|_U`, an object of the derived category of the *scheme* `U`, and that
restriction does not exist here. The obstruction is located, and it is not an artefact of the
formalization:

* On all `𝒪_X`-modules there is no restriction to the Zariski site of a chart inducing a
  functor of derived categories. `AlgebraicGeometry.Space.restrictToChartSchemeFunctor`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`) restricts the sections
  of a module to the Zariski opens of the chart's scheme and sheafifies, and it is only *left*
  exact: an epimorphism of modules on the small étale site is a surjection of sections only
  after étale refinement, which Zariski sheafification on the chart does not see.
  `CategoryTheory.Functor.mapDerivedCategory` asks for
  `CategoryTheory.Limits.PreservesFiniteColimits` as well, so the abuse of notation `E|_U` of
  the source is not that functor.

* On `D_QCoh` the restriction does exist — that is why the source confines itself to `D_QCoh`
  in Tag 0CSV and passes through Tag 071Q in Remark 0CSW. The comparison
  `D_QCoh(𝒪_T) ≌ D_QCoh(T_étale, 𝒪)` of Tag 071Q is
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`),
  for the small étale site of a scheme. What is missing here is the identification of `D_QCoh`
  of the small étale site of the representable algebraic space `U^a` with `D_QCoh` of the small
  étale site of the scheme `U`: `AlgebraicGeometry.Space.representedModuleRestriction`
  (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleComparison.lean`) transports
  *modules* across `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` and is known
  only to be additive, with no exactness and no derived form.

Condition (3) needs none of that. `RΓ(U, -)` is the unbounded right derived functor of
evaluation at the chart, which exists for every algebraic space by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_chartSections` below, and "`m`-pseudo-coherent
relative to a ring" is `StacksDraft.PseudoCoherence.IsRelativelyPseudoCoherentFrom`, Tag
065I (1), formalized unconditionally.

**Tag 0CSX itself is not available here and nothing below claims it.** Its proof turns
conditions (2) and (3) into condition (1) using More on Morphisms, Lemmas 0CSN, 0CSP, 09US and
0695, none of which is formalized, and its Remark 0CSW rests on Tag 071Q as above. So the three
conditions are not known to be equivalent in this development; what is defined below is the
notion of Stacks 0CSY, read through the condition of Tag 0CSX the source itself offers for
affine charts.

## Implementation notes

An étale scheme chart is an object of `AlgebraicGeometry.Space.SmallEtale`, the small étale
site of Tag 03ED, rather than a pair of an object of the big fppf site and a proof of the
chart condition: the scheme of the chart is then `AlgebraicGeometry.Space.chartScheme`, its
ring of regular functions is `AlgebraicGeometry.Space.structurePresheaf` at the chart — the two
being `Scheme.Γ` of the same scheme, definitionally — and the morphism of charts is a morphism
`g` of the big fppf site together with the commutation of its triangle over `f`. The defining
chart condition of `AlgebraicGeometry.Space.IsLocallyOfFiniteType` is applied at exactly that
square, which is what makes `g` locally of finite type on schemes; with the two charts affine,
`AlgebraicGeometry.HasRingHomProperty.appTop` turns that into `RingHom.FiniteType` of the map
of section rings, which is by definition the `Algebra.FiniteType` instance that Tag 065I
consumes. No finiteness hypothesis is therefore imposed beyond the source's own "`f` is
locally of finite type".

The `𝒪_X(U)`-module structure on `RΓ(U, E)` is not imposed either: evaluation of a sheaf of
modules at an object of a ringed site takes values in modules over the ring of sections there,
so `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections` already lands in
`D(𝒪_X(U))`.

The module universe is `u`, the universe of the structure rings. This is forced twice over:
`AlgebraicGeometry.Space.derivedCategoryB_singleFunctor_obj` — which places the degree-zero
complex of a quasi-coherent module in `D_QCoh(𝒪_X)`, and so is what parts (3) and (4) are
stated through — is available only there, and Tag 065I is stated for a ring and an algebra
in one universe.

The derived categories are the ones of `CategoryTheory.HasDerivedCategory.standard`, made a
local instance as in `StacksFrontier/AlgebraicGeometry/PseudoCoherent/Relative.lean`.

## References

* [Stacks Project, Tag 0CSY](https://stacks.math.columbia.edu/tag/0CSY)
* [Stacks Project, Tag 0CSX](https://stacks.math.columbia.edu/tag/0CSX)
* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
* [Stacks Project, Tag 0CSV](https://stacks.math.columbia.edu/tag/0CSV)
* [Stacks Project, Tag 065I](https://stacks.math.columbia.edu/tag/065I)
* [Stacks Project, Tag 09UI](https://stacks.math.columbia.edu/tag/09UI)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### Derived sections over an étale chart -/

/-- **`RΓ(U, -)` exists on an algebraic space**: sections of `𝒪_X`-modules over an étale chart
`U`, followed by localization, have an unbounded right derived functor, with no hypothesis
beyond `X` being an algebraic space.

Sections at an object of a ringed site are left exact and additive, and every complex of
`𝒪_X`-modules admits a quasi-isomorphism to a K-injective complex
(`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`), which is what the derived
functor is computed by. -/
theorem hasRightDerivedFunctor_chartSections (U : SmallEtale B S hS X) :
    Functor.HasRightDerivedFunctor
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)) U)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)) U)
    (exists_quasiIso_isKInjective_modules B S hS X hX)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_chartSections

variable [HasSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `RΓ(U, E)`, the derived sections of an object of `D_QCoh(𝒪_X)` over an étale scheme chart
`U` of `X`, as an object of the derived category of modules over the ring `𝒪_X(U)` of regular
functions on the chart.

This is the complex the affine condition of Tag 0CSX, condition (3), is about. -/
abbrev chartDerivedSections (U : SmallEtale B S hS X)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    DerivedCategory (ModuleCat.{u} ((structurePresheaf B S hS X).obj (op U))) :=
  (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)) U).obj E.obj

/-! ### Stacks 0CSY, parts (1) and (2) -/

/-- **Stacks 0CSY, part (1).** An object `E` of `D_QCoh(𝒪_X)` is *`m`-pseudo-coherent relative
to `Y`* when, for every commuting square of étale scheme charts `U` of `X` and `V` of `Y` over
`f` with `U` and `V` affine, the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent
relative to the ring `𝒪_Y(V)` in the sense of Tag 065I.

This is condition (3) of Tag 0CSX; see "Which of the equivalent conditions of Tag 0CSX
is taken as the definition" in the module docstring. -/
@[stacks 0CSY "part (1): m-pseudo-coherence relative to Y of an object of D_QCoh, \
through condition (3) of Tag 0CSX"]
def IsRelativelyPseudoCoherentFrom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ) : Prop :=
  ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
      (hc : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f)
      (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)),
    letI := hU
    letI := hV
    letI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
      hf _ _ U.obj.hom V.obj.hom g U.property V.property hc
    letI : Algebra ((structurePresheaf B S hS Y).obj (op V))
        ((structurePresheaf B S hS X).obj (op U)) :=
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom).toAlgebra
    letI : Algebra.FiniteType ((structurePresheaf B S hS Y).obj (op V))
        ((structurePresheaf B S hS X).obj (op U)) :=
      HasRingHomProperty.appTop (@LocallyOfFiniteType) ((BigFppfOver.toScheme B S hS).map g)
        inferInstance
    PseudoCoherence.IsRelativelyPseudoCoherentFrom
      (R := (structurePresheaf B S hS Y).obj (op V))
      (chartDerivedSections B S hS X hX U E) m

/-- **Stacks 0CSY, part (2).** An object of `D_QCoh(𝒪_X)` is *pseudo-coherent relative to `Y`*
when it is `m`-pseudo-coherent relative to `Y` for every integer `m`. -/
@[stacks 0CSY "part (2): pseudo-coherence relative to Y of an object of D_QCoh"]
def IsRelativelyPseudoCoherent {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) : Prop :=
  ∀ m : ℤ, IsRelativelyPseudoCoherentFrom B S hS X hX f hf E m

/-! ### Stacks 0CSY, parts (3) and (4) -/

/-- **Stacks 0CSY, part (3).** A quasi-coherent `𝒪_X`-module is *`m`-pseudo-coherent relative
to `Y`* when the complex it determines in degree zero, an object of `D_QCoh(𝒪_X)` by
`AlgebraicGeometry.Space.derivedCategoryB_singleFunctor_obj`, is. -/
@[stacks 0CSY "part (3): m-pseudo-coherence relative to Y of a quasi-coherent module"]
def IsModuleRelativelyPseudoCoherentFrom {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) (m : ℤ) : Prop :=
  IsRelativelyPseudoCoherentFrom B S hS X hX f hf
    ⟨(DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj F,
      derivedCategoryB_singleFunctor_obj B S hS X hX F hF⟩ m

/-- **Stacks 0CSY, part (4).** A quasi-coherent `𝒪_X`-module is *pseudo-coherent relative to
`Y`* when the complex it determines in degree zero is. -/
@[stacks 0CSY "part (4): pseudo-coherence relative to Y of a quasi-coherent module"]
def IsModuleRelativelyPseudoCoherent {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) : Prop :=
  IsRelativelyPseudoCoherent B S hS X hX f hf
    ⟨(DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj F,
      derivedCategoryB_singleFunctor_obj B S hS X hX F hF⟩

/-! ### The degreewise form of parts (2) and (4) -/

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)

/-- Relative pseudo-coherence of an object of `D_QCoh(𝒪_X)` is relative `m`-pseudo-coherence
for every `m`, by definition. -/
theorem isRelativelyPseudoCoherent_iff_forall
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    IsRelativelyPseudoCoherent B S hS X hX f hf E ↔
      ∀ m : ℤ, IsRelativelyPseudoCoherentFrom B S hS X hX f hf E m :=
  Iff.rfl

/-- Relative pseudo-coherence of a quasi-coherent `𝒪_X`-module is relative
`m`-pseudo-coherence for every `m`, by definition. -/
theorem isModuleRelativelyPseudoCoherent_iff_forall
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) :
    IsModuleRelativelyPseudoCoherent B S hS X hX f hf F hF ↔
      ∀ m : ℤ, IsModuleRelativelyPseudoCoherentFrom B S hS X hX f hf F hF m :=
  Iff.rfl

end AlgebraicGeometry.Space

end
