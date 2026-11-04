module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.ModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# The conormal module of a first-order thickening of algebraic spaces is its defining ideal

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace with inclusion `i : Z ⟶ X` and defining ideal sheaf
`𝓘 ⊆ 𝒪_X`, and let `𝒞_{Z/X} = i^*𝓘` be the conormal module of
`AlgebraicGeometry.Space.conormalModule`.  The adjunction `i^* ⊣ i_*` has a unit
`𝓘 ⟶ i_*i^*𝓘 = i_*𝒞_{Z/X}`, which is the map `𝓘 ⟶ 𝓘/𝓘²` of the source.

When `Z ⊆ X` is a **first-order thickening**, that is when `𝓘² = 0` on every object of the
small étale site, that unit is an isomorphism, so `i_*𝒞_{Z/X}` *is* the ideal `𝓘` and
therefore sits inside `𝒪_X`.  This file proves the invertibility and constructs the resulting
inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X`.

The invertibility is the essential-image half of Stacks 04CJ, part (3): the direct image
along a closed immersion is fully faithful, so the unit at `𝓘` is invertible exactly when `𝓘`
lies in the essential image of `i_*`, and that essential image is the modules annihilated by
`𝓘`.  A square-zero ideal annihilates itself, so the only thing to supply is the
essential-image characterization itself, which
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` carries as the hypothesis
that every sheaf of `i_*𝒪_Z`-modules be a Stacks 03D1 direct image.  For a *thickening* that
hypothesis is free: chart base change along the inclusion is a dense subsite inclusion
(`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`), so the direct image of
sheaves of sets is an equivalence, and a sheaf of modules whose underlying sheaf of sets is a
direct image is itself one.

## Main definitions

* `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage`: for a closed immersion `f : W ⟶ X` and a
  submodule `N ⊆ 𝒪_X` lying in the essential image of the direct image, the unit
  `N ⟶ f_*f^*N`, as an isomorphism.
* `AlgebraicGeometry.Space.submoduleιOfEssImage`: the resulting inclusion `f_*f^*N ⟶ 𝒪_X`.
* `AlgebraicGeometry.Space.firstOrderConormalModuleIso`: the unit `𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order
  thickening, as an isomorphism.
* `AlgebraicGeometry.Space.firstOrderConormalModuleι`: the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of the
  conormal module of a first-order thickening into the structure sheaf of the ambient space.

## Main results

* `AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_smallBaseChange_op`: the comma
  categories indexing the right Kan extension along chart base change have limits of sets at the
  universe of the structure rings.
* `AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening`: the direct image of
  sheaves of sets along the inclusion of a thickening is essentially surjective.
* `AlgebraicGeometry.Space.essImage_moduleDirectImage_of_isThickening`: every sheaf of
  `i_*𝒪_Z`-modules is a Stacks 03D1 direct image along the inclusion of a thickening.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_definingIdealSheaf_of_isFirstOrderThickening`:
  the defining ideal of a first-order thickening annihilates itself.
* `Space.essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening`:
  the defining ideal of a first-order thickening is a direct image along the inclusion.
* `AlgebraicGeometry.Space.isIso_unit_definingIdealSheaf_of_isFirstOrderThickening`: the unit
  `𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order thickening is an isomorphism.
* `AlgebraicGeometry.Space.modulePushforward_conormalModule_eq`: the target of that unit is the
  direct image of `AlgebraicGeometry.Space.conormalModule`.
* `AlgebraicGeometry.Space.unit_comp_submoduleιOfEssImage` and
  `AlgebraicGeometry.Space.firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι`:
  the characterising property of the two inclusions — composed with the unit each is the
  inclusion `N ⟶ 𝒪_X`,
  respectively `𝓘 ⟶ 𝒪_X`, of the submodule.  A bundled morphism whose type does not mention its
  characterisation asserts nothing by itself.
* `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage_hom`: the underlying morphism of the
  isomorphism is the unit, so the characterisation really is about the unit.

## Implementation notes

**Why the dense-subsite equivalence has to be re-read at `Type u`.**
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` is the same equivalence taken on
sheaves of sets in `Type (u + 1)`, which is not the universe of the structure rings, and
modules on the small étale site have their sections in `Type u`.  The dense-subsite instance
itself is universe-independent; what has to be supplied at `Type u` is that the comma
categories indexing the right Kan extension have limits of sets there, and that is
`AlgebraicGeometry.Space.hasLimitsOfShape_structuredArrow_smallBaseChange_op`, proved from
essential smallness of the small étale site exactly as the two analogous instances of
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleEssentiallySmall.lean` are.  It is stated as a
theorem rather than an instance because its chart-base-change argument carries the
representability proof as an explicit argument, which instance resolution does not recover from
the goal; it is introduced with `let` where it is needed.

**The square-zero condition is used in the one place it can be.**  `𝓘² = 0` enters only
through
`AlgebraicGeometry.Space.annihilatedByKerIdeal_definingIdealSheaf_of_isFirstOrderThickening`,
the statement that `𝓘` is one of the modules the essential image of `i_*` consists of.  The
power in `AlgebraicGeometry.Space.IsNthOrderThickening` is the power of submodules, so it is
`Submodule.pow_succ` and `Submodule.pow_one` that unfold it, not the monoid `pow_succ`.

**Why the inversion is done in a statement general in the submodule.**  Inverting the unit at
the *concrete* defining ideal sheaf does not elaborate within the default budget: the terms
`AlgebraicGeometry.Space.modulePullbackAdjunction` and
`AlgebraicGeometry.Space.modulePushforward` are definitions over the small étale ringed site, and
every restatement of the type of one of their components costs a definitional unfolding of that
site.  `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` and
`AlgebraicGeometry.Space.submoduleιOfEssImage` therefore take the closed immersion and the
submodule as variables, where the terms are small, and the two first-order constructions are
their instances — an application whose arguments are checked without any unfolding.  For the same
reason the objects of the isomorphism are written in the spelling the unit itself carries, the
identity functor on the left and the composite of the two inverse-image functors on the right,
and `AlgebraicGeometry.Space.modulePushforward_conormalModule_eq` is what relates the right-hand
one to `AlgebraicGeometry.Space.conormalModule`.

**Why `i_*𝒞_{Z/X} ⟶ 𝒪_X` and not `𝒞_{Z/X} ⟶ i^{-1}𝒪_X`.**  The conormal module is an
`𝒪_Z`-module and `𝒪_X` is not one, so the inclusion cannot be a morphism of `𝒪_Z`-modules; it
is a morphism of `𝒪_X`-modules after direct image, which for a thickening loses nothing since
the two small étale topoi are equivalent.  This is the shape of the scheme-level
`Stacks.Thickenings.firstOrderConormalSheafι` of
`StacksFrontier/AlgebraicGeometry/Thickenings/FirstOrderConormalInclusion.lean`, built there from
the same unit and pinned by the same equation.

## Partial coverage

**No `@[stacks]` attribute is placed by this file.**  The invertibility of the unit is the
identification of `i_*𝒞_{Z/X}` with `𝓘/𝓘²` of [Stacks Project, Tag 04CN] in the special case
`𝓘² = 0`, where that quotient is `𝓘` itself; the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` asks for the identification for an
arbitrary closed subspace, which is *not* proved here and does not follow: for a closed
immersion that is not first order the unit is the quotient map onto `𝓘/𝓘²` and `i_*𝒞_{Z/X}`
admits no map to `𝒪_X` at all.  The square-zero hypothesis is not removable.

Likewise the essential-image characterization is obtained here only for a *thickening*, where
the direct image of sheaves of sets is an equivalence.  For a closed immersion that is not a
thickening the hypothesis `hsurj` of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj` is still open; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean` record what it
needs, namely the essential-image assertion of [Stacks Project, Tag 04E5].

**That the two inclusions are monomorphisms is not asserted.**  Both are an isomorphism followed
by `CategoryTheory.SheafOfModules.Submodule.ι`, which is a monomorphism in Mathlib; but that
`Mono` instance does not fire for a submodule of
`CategoryTheory.SheafOfModules.unit (AlgebraicGeometry.Space.structureRingSheaf …)` on this site,
and no monomorphism statement is claimed instead of it.  The characterising equations above are
what the inclusions are to be used through.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The direct image of sheaves of sets along a thickening is an equivalence -/

/-- **The comma categories indexing the right Kan extension along chart base change have limits
of sets in universe `u`.**  Base change of étale scheme charts along a representable morphism
is a functor between small étale sites, which are essentially small at `u`, so the comma
categories over it are too.

This is what makes the dense-subsite comparison lemma available at the universe of the
structure rings; see the implementation notes of this file. -/
theorem hasLimitsOfShape_structuredArrow_smallBaseChange_op
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (smallBaseChange B S hS f hf).op) (Type u) :=
  have : EssentiallySmall.{u} (StructuredArrow W (smallBaseChange B S hS f hf).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The direct image of sheaves of sets along the inclusion of a thickening is essentially
surjective.**  Base change of étale scheme charts along the inclusion exhibits the small étale
site of `X` as a dense subsite of that of `Z`
(`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`), so restriction along it
is an equivalence of sheaf categories; and by Stacks 03G8 that restriction is the direct image
of the morphism of small étale topoi. -/
theorem essSurj_smallEtalePushforward_of_isThickening (hZ : IsThickening B S hS X Z.1) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.EssSurj := by
  let := isContinuous_smallBaseChange B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep
  let : (smallBaseChange B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep).IsDenseSubsite
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) :=
    thickeningChartBaseChange_isDenseSubsite B S hS hZ
  let : ∀ W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W
        (smallBaseChange B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep).op) (Type u) :=
    fun W => hasLimitsOfShape_structuredArrow_smallBaseChange_op B S hS
      (subspaceInclusion B S hS X Z) Z.2.2.rep W
  have hE : ((smallBaseChange B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep
      ).sheafPushforwardContinuous (Type u) (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)).IsEquivalence := inferInstance
  exact Functor.essSurj_of_iso
    (smallEtaleRingedToposHom_representable B S hS (subspaceInclusion B S hS X Z) Z.2.2.rep).symm

/-- **Every sheaf of `i_*𝒪_Z`-modules is a direct image along the inclusion of a thickening.**
This is the hypothesis `hsurj` of
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_of_essSurj`, discharged for a
thickening: the underlying sheaf of sets lies in the essential image of the direct image of
sheaves of sets by
`AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening`, and a sheaf of modules
over a direct-image sheaf of rings whose underlying sheaf of sets is a direct image is itself
one (Stacks 08M3). -/
theorem essImage_moduleDirectImage_of_isThickening (hZ : IsThickening B S hS X Z.1)
    (M : SheafOfModules.{u}
      (structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z))) :
    (moduleDirectImage B S hS (subspaceInclusion B S hS X Z)).essImage M := by
  have := essSurj_smallEtalePushforward_of_isThickening B S hS Z hZ
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2
  have := hff.full
  have := hff.faithful
  exact Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModuleFunctor
    (f := smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
    (O := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Z.1.toFunctor Z.2.1).O)) M
    (Functor.EssSurj.mem_essImage _ _)

/-! ### The defining ideal of a first-order thickening annihilates itself -/

/-- **The defining ideal of a first-order thickening annihilates itself.**  A section of
`𝓘 = ker(i♯)` multiplies a section of `𝓘` into `𝓘²`, which vanishes.

This is the form in which the square-zero condition of
`AlgebraicGeometry.Space.IsFirstOrderThickening` enters the essential-image characterization of
Stacks 04CJ, part (3). -/
theorem annihilatedByKerIdeal_definingIdealSheaf_of_isFirstOrderThickening
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    AnnihilatedByKerIdeal B S hS (subspaceInclusion B S hS X Z)
      (definingIdealSheaf B S hS X Z).toSheafOfModules := by
  obtain ⟨hT, hpow⟩ := hZ
  intro U a ha m
  have ha' : a ∈ definingIdealAt B S hS X Z U := (SheafOfModules.mem_kerIdeal _ U a).1 ha
  have hb : (m.1 : ToType ((structureRingSheaf B S hS X).obj.obj U)) ∈
      definingIdealAt B S hS X Z U := m.2
  have hpow2 := hpow U.unop
  rw [Submodule.pow_succ, Submodule.pow_one] at hpow2
  have hmul : definingIdealAt B S hS X Z U * definingIdealAt B S hS X Z U = ⊥ := hpow2
  exact Subtype.ext ((Submodule.eq_bot_iff _).mp hmul _ (Ideal.mul_mem_mul ha' hb))

/-! ### The conormal module of a first-order thickening is the defining ideal -/

/-- **The defining ideal of a first-order thickening is a direct image.**  It is annihilated by
itself, and for a thickening the essential image of the direct image of modules along the
inclusion is exactly the annihilated modules. -/
theorem essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).essImage
      (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  (essImage_modulePushforward_iff_of_essSurj B S hS (subspaceInclusion B S hS X Z) Z.2.2
      (essImage_moduleDirectImage_of_isThickening B S hS Z hZ.1) _).2
    (annihilatedByKerIdeal_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)

/-- The direct image of the conormal module of a closed subspace is the direct image of the
inverse image of its defining ideal sheaf: the conormal module is by definition that inverse
image. -/
theorem modulePushforward_conormalModule_eq :
    (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalModule B S hS X Z) =
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  congrArg (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
    (conormalModule_eq B S hS X Z)

/-- **The unit `𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order thickening is an isomorphism.**  The direct
image of modules along a closed immersion is fully faithful (Stacks 04CJ, part (2)), so the
unit of `i^* ⊣ i_*` is invertible at a module exactly when that module lies in the essential
image of the direct image; the defining ideal does by
`AlgebraicGeometry.Space.essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening`.

For a square-zero ideal this is the identification `𝓘/𝓘² = 𝓘` of the source; see the "Partial
coverage" section of this file for what is *not* claimed. -/
theorem isIso_unit_definingIdealSheaf_of_isFirstOrderThickening
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    IsIso ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (definingIdealSheaf B S hS X Z).toSheafOfModules) := by
  have hff := fullyFaithfulModulePushforward B S hS (subspaceInclusion B S hS X Z) Z.2.2
  have := hff.full
  have := hff.faithful
  exact (modulePullbackAdjunction B S hS
      (subspaceInclusion B S hS X Z)).isIso_unit_app_iff_mem_essImage.2
    (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)

/-! ### The inclusion of a submodule in the essential image of the direct image -/

/-- **The unit at a submodule of `𝒪_X` lying in the essential image of the direct image, as an
isomorphism.**  For a closed immersion `f : W ⟶ X` of algebraic spaces the direct image of
modules is fully faithful (Stacks 04CJ, part (2)), so the unit of `f^* ⊣ f_*` is invertible at
any module in the essential image of `f_*`.

The statement is general in the submodule `N` and the closed immersion, and the two objects are
written in the spelling the unit itself carries, so that no restatement of the type is needed;
see the implementation notes of this file. -/
def submoduleUnitIsoOfEssImage {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : (modulePushforward B S hS f).essImage N.toSheafOfModules) :
    (𝟭 (Modules.{u, u} B S hS X.1 X.2)).obj N.toSheafOfModules ≅
      (modulePullback B S hS f ⋙ modulePushforward B S hS f).obj N.toSheafOfModules :=
  have hff := fullyFaithfulModulePushforward B S hS f hf
  have := hff.full
  have := hff.faithful
  @asIso _ _ _ _ _ ((modulePullbackAdjunction B S hS f).isIso_unit_app_iff_mem_essImage.2 h)

/-- The underlying morphism of `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` is the unit
of `f^* ⊣ f_*` at the submodule. -/
theorem submoduleUnitIsoOfEssImage_hom {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : (modulePushforward B S hS f).essImage N.toSheafOfModules) :
    (submoduleUnitIsoOfEssImage B S hS f hf N h).hom =
      (modulePullbackAdjunction B S hS f).unit.app N.toSheafOfModules :=
  rfl

/-- **The inclusion `f_*f^*N ⟶ 𝒪_X` of a submodule of `𝒪_X` lying in the essential image of the
direct image.**  The unit `N ⟶ f_*f^*N` is invertible there, so `f_*f^*N` is `N` itself and
therefore sits inside `𝒪_X`: the morphism is
`AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage` inverted, followed by the inclusion of the
submodule.

It is pinned by `AlgebraicGeometry.Space.unit_comp_submoduleιOfEssImage`. -/
def submoduleιOfEssImage {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : (modulePushforward B S hS f).essImage N.toSheafOfModules) :
    (modulePullback B S hS f ⋙ modulePushforward B S hS f).obj N.toSheafOfModules ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  (submoduleUnitIsoOfEssImage B S hS f hf N h).inv ≫ N.ι

/-- **The characterising property of `AlgebraicGeometry.Space.submoduleιOfEssImage`.**
Precomposed with the unit `N ⟶ f_*f^*N` it is the inclusion `N ⟶ 𝒪_X` of the submodule.  Since
that unit is an isomorphism, this determines the morphism uniquely. -/
theorem unit_comp_submoduleιOfEssImage {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : (modulePushforward B S hS f).essImage N.toSheafOfModules) :
    (modulePullbackAdjunction B S hS f).unit.app N.toSheafOfModules ≫
        submoduleιOfEssImage B S hS f hf N h =
      N.ι :=
  (submoduleUnitIsoOfEssImage B S hS f hf N h).hom_inv_id_assoc _

/-! ### The conormal module of a first-order thickening as a submodule of the structure sheaf -/

/-- **The defining ideal sheaf of a first-order thickening is its pushed-forward conormal
module**, `𝓘 ≅ i_*i^*𝓘`.  The underlying morphism is the unit of `i^* ⊣ i_*` at `𝓘`, the map
`𝓘 ⟶ 𝓘/𝓘²` of the source.

`AlgebraicGeometry.Space.modulePushforward_conormalModule_eq` identifies the right-hand object
with the direct image of `AlgebraicGeometry.Space.conormalModule`. -/
def firstOrderConormalModuleIso (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (𝟭 (Modules.{u, u} B S hS X.1 X.2)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
          modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  submoduleUnitIsoOfEssImage B S hS (subspaceInclusion B S hS X Z) Z.2.2
    (definingIdealSheaf B S hS X Z)
    (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)

/-- **The inclusion `𝒞_{Z/X} ⟶ 𝒪_X` of the conormal module of a first-order thickening into the
structure sheaf of the ambient space**, read on `X` — that is, the conormal module pushed
forward along the inclusion, which for a thickening is no loss of information since the two
small étale topoi are equivalent.  Its source is the direct image of
`AlgebraicGeometry.Space.conormalModule` by
`AlgebraicGeometry.Space.modulePushforward_conormalModule_eq`.

It is pinned by `AlgebraicGeometry.Space.unit_comp_firstOrderConormalModuleι`. -/
def firstOrderConormalModuleι (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (modulePullback B S hS (subspaceInclusion B S hS X Z) ⋙
          modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  submoduleιOfEssImage B S hS (subspaceInclusion B S hS X Z) Z.2.2
    (definingIdealSheaf B S hS X Z)
    (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)

/-- **The characterising property of `AlgebraicGeometry.Space.firstOrderConormalModuleι`.**
Precomposed with `AlgebraicGeometry.Space.firstOrderConormalModuleIso` — the unit `𝓘 ⟶ i_*𝒞_{Z/X}`,
by `AlgebraicGeometry.Space.submoduleUnitIsoOfEssImage_hom` — it is the inclusion `𝓘 ⟶ 𝒪_X` of
the defining ideal sheaf.  Since that map is an isomorphism, this determines the inclusion
uniquely. -/
theorem firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (firstOrderConormalModuleIso B S hS Z hZ).hom ≫ firstOrderConormalModuleι B S hS Z hZ =
      (definingIdealSheaf B S hS X Z).ι :=
  (firstOrderConormalModuleIso B S hS Z hZ).hom_inv_id_assoc _

end AlgebraicGeometry.Space

end
