module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Fpqc descent of morphisms of quasi-coherent modules, localized at a represented base

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let
`(f i : X i ⟶ X)` be an fpqc covering of `X` in the sense of Stacks 03MQ.  This file proves the
faithfulness of the canonical descent functor of Stacks 04W5 for that family — the faithfulness
half of the full-faithfulness clause of Stacks 04W8 — reducing it to the same statement for an
fpqc covering of a *represented* algebraic space by represented algebraic spaces, that is to the
faithfulness half of Stacks 023T, and then proving that represented case.

The represented case, `AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective`, does
not go through the Zariski modules on the scheme and the equivalence clause of Descent,
Proposition 03DX (2).  It is a consequence of flatness alone: every member of an fpqc covering
is flat by definition, such a covering is jointly surjective on points
(`AlgebraicGeometry.Space.isJointlySurjective_of_isFpqcCovering`), and along a jointly
surjective family of flat morphisms a morphism of modules is determined by its inverse images,
because the inverse image along a flat morphism commutes with the formation of kernels and of
supports (`AlgebraicGeometry.Space.eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat`).
Nothing about the base enters, so the same argument proves the general case directly; the
reduction is kept because it is what the file's geometry is about.

The reduction itself has two steps, both unconditional.

The first step is geometric.  Pulling the family back along a morphism `v` out of a
represented algebraic space and refining the pullbacks by scheme atlases produces an fpqc
covering of that represented space by represented spaces, each member of which maps to the
corresponding member of the original family over `v`; this is
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_represented_fpqc_refinement`.  Neither
flatness nor étaleness of `v` is used: the inputs are Stacks 03MR (3), the base change of an
fpqc covering, and its composition with the atlas coverings of the pullbacks.

The second step is the comparison of inverse images around the resulting square.  The square
is not cartesian — the atlas of the pullback is chosen independently — so what carries a
statement across it is `AlgebraicGeometry.Space.modulePullbackCommSquareIso`, the comparison
of the two composites of inverse images around a merely *commuting* square, which is the
composition comparison of Stacks 03LU and nothing else.  It is a natural isomorphism of
functors, so it transports an equality of *morphisms*, which is what faithfulness is about.

The last step is the appeal to the represented case.  Taking `v` to be a scheme atlas of `X`,
which is a one-member étale covering of it, the conclusion is carried back to `X` by
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.

## Main definitions

* `representedAlgebraicSpace` and `.reprSpaceMap` are the
  algebraic space represented by an object of the site and the morphism represented by a
  morphism of the site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.ReprFpqcHomInjective` is the faithfulness half
  of Stacks 023T, read on represented algebraic spaces: a morphism of `𝒪`-modules on the
  algebraic space represented by an object of the site is determined by its inverse images
  along an fpqc covering of that object by objects of the site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum'` and
  `.canonicalDescentFunctor'` are the canonical descent datum and the canonical descent functor
  of Stacks 04W5 for an arbitrary family of algebraic spaces over `X`, formed with no
  hypothesis.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_eq_of_comm_square`: **two
  morphisms of modules with equal inverse images along one side of a commuting square have
  equal inverse images along the other way round it.**  Unconditional.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_represented_fpqc_refinement`: **an fpqc
  covering of an algebraic space, pulled back along a morphism out of a represented algebraic
  space, is refined by an fpqc covering of that represented space by represented spaces**,
  compatibly with the original family.  Unconditional.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFlat`: **a
  morphism of `𝒪_X`-modules is determined by its inverse images along a jointly surjective
  family of flat morphisms.**  Unconditional.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective`: **the faithfulness half
  of Stacks 023T, read on represented algebraic spaces.**  Unconditional, so
  `ReprFpqcHomInjective` is a theorem of this development and not a gap.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering`:
  a morphism of `𝒪_X`-modules is determined by its inverse images along an fpqc covering,
  stated over the represented case, which `reprFpqcHomInjective` supplies.
* `…faithful_canonicalDescentFunctor_of_isFpqcCovering`: **the canonical descent functor of an
  fpqc covering of algebraic spaces is faithful.**  The covering is its only input.

## Implementation notes

The canonical descent functor is formed here as
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor'` rather than as
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor`, which takes the
associativity coherence of Stacks 03LU and the quasi-coherence of the inverse images as
arguments.  Both are available: the coherence is
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, and quasi-coherence of the inverse image
along an *arbitrary* morphism of algebraic spaces is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`,
Stacks 03GA.  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum'_eq` records
that the two descent data are the same term, so every statement about the one applies to the
other; the primed forms exist only so that the statements need no argument.

`ReprFpqcHomInjective` is kept as a named predicate even though
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective` proves it: it is the
interface of the reduction, and the statements that consume it elsewhere take it as an argument.
It is no longer a gap — it is a theorem, discharged by flatness and joint surjectivity rather
than by the equivalence clause of Descent, Proposition 03DX (2), which that route would have
needed.  Note that the predicate quantifies over *arbitrary* `𝒪`-modules, with no
quasi-coherence, so it is strictly stronger than the faithfulness half of Stacks 023T as the
source states it; the flatness argument gives the stronger form.

`representedAlgebraicSpace` and `.reprSpaceMap` are the object and
the morphism parts of `AlgebraicGeometry.schemeSpaceFunctor` on the nose, as
`reprSpace_eq_yonedaSpace_obj` and `reprSpaceMap_eq_yonedaSpace_map` record.  They are
abbreviations, hence reducible, and the functor is not.  That is the reason for them: the
represented case is instantiated at the *underlying presheaf* of a represented space, and the
covering condition is read on the Yoneda images of the morphisms of the site, so the rewriting
steps below must see through the construction, which they do for a reducible abbreviation and
do not for an opaque definition.

The reduction is stated at an arbitrary morphism `v` out of a represented space, and the étale
atlas is one instance of it: nothing in the first two steps uses any property of `v`, and
étaleness enters only in the last step, where the atlas is used as a one-member covering.

`AlgebraicGeometry.Space.ChartRestrictionBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/ModuleFiniteness.lean` is *not* used.  It compares
the Zariski reading of the chart restriction with pullback inside the schemes, and it is a family
of isomorphisms with no naturality in the module, so it cannot move a morphism of modules across
a square at all — that is so whether it is assumed, as it once was, or proved, as it now is in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`.  The comparison used here
is natural by construction.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of inverse images around a commuting square, on morphisms.**  Two
morphisms of `𝒪_Z`-modules whose inverse images along `a : X₀ ⟶ Z` agree have agreeing inverse
images along `γ` of their restrictions along `cZ`, for any commuting square
`γ ≫ cZ = cX ≫ a`.

The square is not assumed cartesian.  The comparison is
`AlgebraicGeometry.Space.modulePullbackCommSquareIso`, a natural isomorphism of functors, which
is why an equality of morphisms crosses it. -/
theorem modulePullback_map_eq_of_comm_square {X' X₀ Z' Z : AlgebraicSpaces B S hS}
    {γ : X' ⟶ Z'} {cZ : Z' ⟶ Z} {cX : X' ⟶ X₀} {a : X₀ ⟶ Z} (hsq : γ ≫ cZ = cX ≫ a)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS a).map φ = (modulePullback B S hS a).map ψ) :
    (modulePullback B S hS γ).map ((modulePullback B S hS cZ).map φ) =
      (modulePullback B S hS γ).map ((modulePullback B S hS cZ).map ψ) :=
  Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
    (modulePullbackCommSquareIso B S hS hsq).symm
    (congrArg (fun b => (modulePullback B S hS cX).map b) h)

/-- The morphism of represented algebraic spaces attached to a morphism of the big fppf site
of `S`: an abbreviation of `AlgebraicGeometry.schemeSpaceMap`. -/
abbrev reprSpaceMap {U U' : BigFppfOver B S hS} (g : U ⟶ U') :
    representedAlgebraicSpace B S hS U ⟶ representedAlgebraicSpace B S hS U' :=
  schemeSpaceMap g

/-- The represented algebraic space is the value of `AlgebraicGeometry.schemeSpaceFunctor`. -/
theorem reprSpace_eq_yonedaSpace_obj (U : BigFppfOver B S hS) :
    representedAlgebraicSpace B S hS U = (schemeSpaceFunctor B S hS).obj U :=
  rfl

/-- The represented morphism is the image under `AlgebraicGeometry.schemeSpaceFunctor`. -/
theorem reprSpaceMap_eq_yonedaSpace_map {U U' : BigFppfOver B S hS} (g : U ⟶ U') :
    reprSpaceMap B S hS g = (schemeSpaceFunctor B S hS).map g :=
  rfl

/-- **The faithfulness half of Stacks 023T, read on represented algebraic spaces.**  A
morphism of `𝒪`-modules on the algebraic space represented by an object `U` of the big fppf
site is determined by its inverse images along an fpqc covering of `U` by objects of the site.

For the Zariski modules on a scheme this is the `moreover` clause of Stacks 023T; the statement
below is the same assertion for the `𝒪`-modules of Stacks 03LU on the small étale site, and
passing between the two is the equivalence clause of Descent, Proposition 03DX (2). -/
abbrev ReprFpqcHomInjective : Prop :=
  ∀ {J : Type v} (U : BigFppfOver B S hS) (T : J → BigFppfOver B S hS) (g : ∀ j, T j ⟶ U),
    IsFpqcCovering B S hS (fun j => yoneda.map (g j)) →
    ∀ {M N : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
        (representedAlgebraicSpace B S hS U).2}
      (φ ψ : M ⟶ N),
      (∀ j, (modulePullback B S hS (reprSpaceMap B S hS (g j))).map φ =
          (modulePullback B S hS (reprSpaceMap B S hS (g j))).map ψ) →
      φ = ψ

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **A morphism of `𝒪_X`-modules is determined by its inverse images along a jointly surjective
family of flat morphisms of algebraic spaces.**

The inverse image along a flat morphism commutes with the formation of kernels and of supports,
so a morphism of modules whose inverse image along every member of such a family vanishes has
empty support and is itself zero; that is
`AlgebraicGeometry.Space.eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat`.  The inverse
image is additive, being a left adjoint between abelian categories, so the difference of two
morphisms with equal inverse images is such a morphism.

No quasi-coherence is assumed, and no property of the base. -/
theorem modulePullback_map_injective_of_isFlat (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (hflat : ∀ i, IsFlat B S hS (f i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Xi i).1) fun i => (f i).hom)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ ψ : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS (f i)).map φ = (modulePullback B S hS (f i)).map ψ) :
    φ = ψ := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := SheafOfModules.instAbelian _
  have key : ∀ i, (modulePullback B S hS (f i)).map (φ - ψ) = 0 := by
    intro i
    let _ : Abelian (Modules.{u, u} B S hS (Xi i).1 (Xi i).2) :=
      SheafOfModules.instAbelian _
    have hleft := (modulePullbackAdjunction B S hS (f i)).isLeftAdjoint
    have hbip : PreservesBinaryBiproducts (modulePullback B S hS (f i)) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have hadd : (modulePullback B S hS (f i)).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    rw [Functor.map_sub, h i, sub_self]
  exact sub_eq_zero.1
    (eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat B S hS f hflat hsurj (φ - ψ) key)

/-- **The faithfulness half of Stacks 023T, read on represented algebraic spaces.**  A morphism
of `𝒪`-modules on the algebraic space represented by an object of the big fppf site is
determined by its inverse images along an fpqc covering of that object by objects of the site.

The route is not the one through the Zariski modules on the scheme and the equivalence clause of
Descent, Proposition 03DX (2).  The members of an fpqc covering of Stacks 03MQ are flat by
definition, and such a covering is jointly surjective on points by
`AlgebraicGeometry.Space.isJointlySurjective_of_isFpqcCovering`, so
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isFlat` applies
with nothing further. -/
theorem reprFpqcHomInjective : ReprFpqcHomInjective.{u, v} B S hS := by
  intro J U T g hcov M N φ ψ h
  exact modulePullback_map_injective_of_isFlat B S hS
    (fun j => representedAlgebraicSpace B S hS (T j)) (fun j => reprSpaceMap B S hS (g j)) hcov.1
    (isJointlySurjective_of_isFpqcCovering B S hS (fun j => yoneda.map (g j)) hcov) φ ψ h

/-- A surjective étale chart of an algebraic space is a one-member étale covering of it. -/
private theorem isEtaleCovering_singleton_of_atlas (Y : AlgebraicSpaces B S hS)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ Y.1)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U) (fun _ => a) := by
  refine ⟨Y.property, fun _ => isAlgebraicSpace_yoneda B S hS U,
    fun _ => (isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale, ?_⟩
  rw [Set.iUnion_const, Set.range_eq_univ]
  exact (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 U a).1 hsurj

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasLimit_cospan_presheaf_FpqcChartLocalization
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **An fpqc covering of an algebraic space is refined, over any morphism out of a represented
algebraic space, by an fpqc covering of that represented space by represented spaces.**

Given an fpqc covering `(f i : X i ⟶ X)` and a morphism `v` out of the algebraic space
represented by an object `U` of the site, there are objects `T i` of the site, morphisms
`g i : T i ⟶ U`, and morphisms `c i` of the space represented by `T i` to `X i`, such that each
square `g i`, `v`, `c i`, `f i` commutes and the `g i` represent an fpqc covering of `U`.

The members are the atlases of the fibre products `X i ×_X U`, so the squares are *not*
cartesian.  Neither flatness nor étaleness of `v` is used: the two inputs are the base change
of an fpqc covering, Stacks 03MR (3), and its composition with the one-member étale coverings
given by the atlases. -/
theorem exists_represented_fpqc_refinement (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    (U : BigFppfOver B S hS) (v : representedAlgebraicSpace B S hS U ⟶ X) :
    ∃ (T : I → BigFppfOver B S hS) (g : ∀ i, T i ⟶ U)
      (c : ∀ i, representedAlgebraicSpace B S hS (T i) ⟶ Xi i),
      (∀ i, reprSpaceMap B S hS (g i) ≫ v = c i ≫ f i) ∧
        IsFpqcCovering B S hS fun i => yoneda.map (g i) := by
  classical
  choose T e hsurj hetale using
    fun i => (AlgebraicSpaces.fiberProduct B S hS (f i) v).property.exists_atlas
  have hEtaleCovering (i : I) :
      IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) :=
    isEtaleCovering_singleton_of_atlas B S hS _ (T i) (e i) (hsurj i) (hetale i)
  have hcomp : IsFpqcCovering B S hS fun i => e i ≫ pullback.snd (f i).hom v.hom :=
    isFpqcCovering_reindex B S hS
      (isFpqcCovering_comp B S hS (X := (representedAlgebraicSpace B S hS U).1)
        (Xi := fun i => (AlgebraicSpaces.fiberProduct B S hS (f i) v).1)
        (Xij := fun ij : Σ _ : I, Unit => yoneda.obj (T ij.1))
        (representedAlgebraicSpace B S hS U).2
        (fun i => (AlgebraicSpaces.fiberProduct B S hS (f i) v).2)
        (fun i _ => isAlgebraicSpace_yoneda B S hS (T i))
        (fun i => pullback.snd (f i).hom v.hom) (fun i _ => e i)
        (isFpqcCovering_pullback B S hS f v hf)
        (fun i => isFpqcCovering_of_isEtaleCovering B S hS
          (fun _ : Unit => yoneda.obj (T i)) (fun _ => e i) (hEtaleCovering i)))
      (σ := fun i : I => (⟨i, ()⟩ : Σ _ : I, Unit)) (fun r => ⟨r.1, by cases r.2; rfl⟩)
  refine ⟨T, fun i => Yoneda.fullyFaithful.preimage (e i ≫ pullback.snd (f i).hom v.hom),
    fun i => ObjectProperty.homMk (e i ≫ pullback.fst (f i).hom v.hom), fun i => ?_, ?_⟩
  · refine ObjectProperty.hom_ext _ ?_
    exact (congrArg (fun k => k ≫ v.hom)
        (Yoneda.fullyFaithful.map_preimage
          (e i ≫ pullback.snd (f i).hom v.hom))).trans
      ((Category.assoc (e i) (pullback.snd (f i).hom v.hom) v.hom).trans
        ((congrArg (fun k => e i ≫ k)
            (pullback.condition (f := (f i).hom) (g := v.hom)).symm).trans
          (Category.assoc (e i) (pullback.fst (f i).hom v.hom) (f i).hom).symm))
  · simpa only [Yoneda.fullyFaithful.map_preimage] using hcomp

/-- **A morphism of `𝒪_X`-modules is determined by its inverse images along an fpqc covering of
algebraic spaces.**  The represented case is taken as an argument, and
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective` is a term of its type, so
the statement is unconditional in substance.

The reduction is: restrict to a scheme atlas `v` of `X`, where
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_represented_fpqc_refinement` turns the
given covering into an fpqc covering of the atlas by represented spaces and
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_eq_of_comm_square` carries the
hypothesis to it; the represented case then gives equality after restriction to the atlas, and
the atlas is a one-member étale covering of `X`, so
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`
concludes.

No quasi-coherence is assumed: as for an étale covering, this is a statement about arbitrary
sheaves of modules on the small étale site of `X`. -/
theorem modulePullback_map_injective_of_isFpqcCovering
    (hrepr : ReprFpqcHomInjective.{u, v} B S hS) (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ ψ : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS (f i)).map φ = (modulePullback B S hS (f i)).map ψ) :
    φ = ψ := by
  classical
  obtain ⟨U, a, hsurj, hetale⟩ := X.property.exists_atlas
  obtain ⟨T, g, c, hsq, hcov⟩ := exists_represented_fpqc_refinement B S hS Xi f hf U
    (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X)
  have hatlas : (modulePullback B S hS
        (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X)).map φ =
      (modulePullback B S hS
        (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X)).map ψ :=
    hrepr U T g hcov _ _ fun i =>
      modulePullback_map_eq_of_comm_square B S hS (hsq i) φ ψ (h i)
  have hEtaleCovering := isEtaleCovering_singleton_of_atlas B S hS X U a hsurj hetale
  exact modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : Unit => representedAlgebraicSpace B S hS U)
    (fun _ => (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X)) hEtaleCovering
    φ ψ fun _ => hatlas

/-! ### The canonical descent functor of an arbitrary family, with no hypothesis -/

variable (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)

/-- The canonical descent datum `(M|_{X i}, can)` of Stacks 04W5 of a quasi-coherent
`𝒪_X`-module `M` relative to an arbitrary family `(f i : X i ⟶ X)` of algebraic spaces over
`X`, formed with no hypothesis.

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` spelled out here,
and `canonicalDescentDatum'_eq` records that the two agree.  Both draw quasi-coherence of the
inverse images from Stacks 03GA for an arbitrary morphism of algebraic spaces,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, and the
cocycle condition from the associativity coherence of the comparison of inverse images of
Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`. -/
def canonicalDescentDatum' (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) : DescentDatum B S hS Xi f where
  F i := (modulePullback B S hS (f i)).obj M
  quasicoherent i :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) M hM
  transition i j := canonicalComparison (pairFst B S hS Xi f i j) (pairSnd B S hS Xi f i j)
    (f i) (f j) (pair_condition B S hS Xi f i j) M
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    rw [transitionOn_canonicalComparison B S hS Xi f M
        i j vij vi vj hij₀ hij₁,
      transitionOn_canonicalComparison B S hS Xi f M
        j k vjk vj vk hjk₀ hjk₁,
      transitionOn_canonicalComparison B S hS Xi f M
        i k vik vi vk hik₀ hik₁]
    exact canonicalComparison_trans B S hS vi vj vk (f i) (f j) (f k) _ _ M

/-- The `i`-th component module of the canonical descent datum of an arbitrary family is the
inverse image of `M` along `f i`. -/
@[simp]
theorem canonicalDescentDatum'_F (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i : I) :
    (canonicalDescentDatum' B S hS Xi f M hM).F i = (modulePullback B S hS (f i)).obj M :=
  rfl

/-- The pairwise isomorphism of the canonical descent datum of an arbitrary family is the
canonical comparison of the two inverse images of `M` to the pairwise fibre product. -/
@[simp]
theorem canonicalDescentDatum'_transition (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i j : I) :
    (canonicalDescentDatum' B S hS Xi f M hM).transition i j =
      canonicalComparison (pairFst B S hS Xi f i j) (pairSnd B S hS Xi f i j) (f i) (f j)
        (pair_condition B S hS Xi f i j) M :=
  rfl

/-- The canonical descent datum formed with no hypothesis is the canonical descent datum of
Stacks 04W5: the two differ only in the proofs filling their `Prop`-valued fields. -/
theorem canonicalDescentDatum'_eq
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    canonicalDescentDatum' B S hS Xi f M hM =
      canonicalDescentDatum B S hS Xi f M hM :=
  rfl

/-- A family of morphisms of the component modules of two canonical descent data of an arbitrary
family which is the family of inverse images of one morphism `φ` of quasi-coherent `𝒪_X`-modules
commutes with the pairwise isomorphisms of those data. -/
theorem canonicalDescentDatum'_naturality (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (a : ∀ i, (canonicalDescentDatum' B S hS Xi f M hM).F i ⟶
      (canonicalDescentDatum' B S hS Xi f N hN).F i)
    (ha : ∀ i, a i = (modulePullback B S hS (f i)).map φ) (i j : I) :
    (modulePullback B S hS (pairFst B S hS Xi f i j)).map (a i) ≫
        ((canonicalDescentDatum' B S hS Xi f N hN).transition i j).hom =
      ((canonicalDescentDatum' B S hS Xi f M hM).transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Xi f i j)).map (a j) := by
  rw [ha i, ha j, canonicalDescentDatum'_transition, canonicalDescentDatum'_transition]
  exact canonicalComparison_naturality B S hS (pairFst B S hS Xi f i j)
    (pairSnd B S hS Xi f i j) (f i) (f j) (pair_condition B S hS Xi f i j) φ

/-- The morphism of canonical descent data of an arbitrary family induced by a morphism of
quasi-coherent `𝒪_X`-modules: the inverse image of that morphism along each member of the
family. -/
def canonicalDescentHom' (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    canonicalDescentDatum' B S hS Xi f M hM ⟶ canonicalDescentDatum' B S hS Xi f N hN :=
  DescentDatum.Hom.mk (fun i => (modulePullback B S hS (f i)).map φ)
    (canonicalDescentDatum'_naturality B S hS Xi f M N hM hN φ
      (fun i => (modulePullback B S hS (f i)).map φ) (fun _ => rfl))

/-- The `i`-th component of the morphism of canonical descent data induced by a morphism of
quasi-coherent modules is the inverse image of that morphism along `f i`. -/
@[simp]
theorem canonicalDescentHom'_app (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) (i : I) :
    (canonicalDescentHom' B S hS Xi f M N hM hN φ).app i =
      (modulePullback B S hS (f i)).map φ :=
  rfl

/-- The morphism of canonical descent data induced by an identity is an identity. -/
theorem canonicalDescentHom'_id (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    canonicalDescentHom' B S hS Xi f M M hM hM (𝟙 M) =
      𝟙 (canonicalDescentDatum' B S hS Xi f M hM) :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_id M

/-- The morphism of canonical descent data induced by a composite is the composite of the
induced morphisms. -/
theorem canonicalDescentHom'_comp (M N P : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (φ : M ⟶ N) (ψ : N ⟶ P) :
    canonicalDescentHom' B S hS Xi f M P hM hP (φ ≫ ψ) =
      canonicalDescentHom' B S hS Xi f M N hM hN φ ≫
        canonicalDescentHom' B S hS Xi f N P hN hP ψ :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_comp φ ψ

/-- **The canonical descent functor of Stacks 04W5 for an arbitrary family
`(f i : X i ⟶ X)` of algebraic spaces over `X`, formed with no hypothesis.**  It sends a
quasi-coherent `𝒪_X`-module to its canonical descent datum `(M|_{X i}, can)` and a morphism of
modules to its inverse images along the members of the family.

`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum'_eq` records that this is
the functor of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor` on the nose whenever the
latter can be formed. -/
def canonicalDescentFunctor' :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ DescentDatum B S hS Xi f where
  obj M := canonicalDescentDatum' B S hS Xi f M.obj M.property
  map {M N} φ := canonicalDescentHom' B S hS Xi f M.obj N.obj M.property N.property φ.hom
  map_id M := canonicalDescentHom'_id B S hS Xi f M.obj M.property
  map_comp {M N P} φ ψ :=
    canonicalDescentHom'_comp B S hS Xi f M.obj N.obj P.obj M.property N.property
      P.property φ.hom ψ.hom

/-- The canonical descent functor sends a quasi-coherent module to its canonical descent
datum. -/
@[simp]
theorem canonicalDescentFunctor'_obj (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (canonicalDescentFunctor' B S hS Xi f).obj M =
      canonicalDescentDatum' B S hS Xi f M.obj M.property :=
  rfl

/-- The `i`-th component of the image of a morphism of quasi-coherent modules under the
canonical descent functor. -/
@[simp]
theorem canonicalDescentFunctor'_map_app
    {M N : QuasicoherentSheaves.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (i : I) :
    ((canonicalDescentFunctor' B S hS Xi f).map φ).app i =
      (modulePullback B S hS (f i)).map φ.hom :=
  rfl

/-- **The faithfulness half of the full-faithfulness clause of Stacks 04W8.**  The canonical
descent functor of Stacks 04W5, from the quasi-coherent `𝒪_X`-modules of Stacks 03G9 to the
descent data of Stacks 04W3 relative to an fpqc covering `(f i : X i ⟶ X)` of algebraic spaces
in the sense of Stacks 03MQ, is faithful.

The covering is the only input.  Its members are flat and it is jointly surjective on points, so
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprFpqcHomInjective` supplies the represented case
of the reduction above.  The two data needed to form the functor are supplied, not assumed: the
associativity coherence of the comparison of inverse images of Stacks 03LU is
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, and quasi-coherence of the inverse images
is Stacks 03GA for an arbitrary morphism of algebraic spaces.

This is the faithfulness half only.  The fullness half of the full-faithfulness clause, and the
effectivity clause of the same tag, are not proved here. -/
@[stacks 04W8 "the faithfulness half of the full-faithfulness clause, for an fpqc covering of \
algebraic spaces: the members of an fpqc covering are flat and the covering is jointly \
surjective on points, so a morphism of quasi-coherent modules is determined by its inverse \
images along it and the canonical descent functor of Stacks 04W5 is faithful.  The fullness \
half of that clause and the effectivity clause are separate assertions of the tag and are not \
proved here"]
theorem faithful_canonicalDescentFunctor_of_isFpqcCovering
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) :
    (canonicalDescentFunctor' B S hS Xi f).Faithful where
  map_injective {M N} φ ψ h := by
    refine ObjectProperty.hom_ext _ (modulePullback_map_injective_of_isFpqcCovering B S hS
      (reprFpqcHomInjective B S hS) Xi f hf φ.hom ψ.hom fun i => ?_)
    have hi := congrArg
      (fun b : (canonicalDescentFunctor' B S hS Xi f).obj M ⟶
        (canonicalDescentFunctor' B S hS Xi f).obj N => b.app i) h
    rwa [canonicalDescentFunctor'_map_app, canonicalDescentFunctor'_map_app] at hi

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
