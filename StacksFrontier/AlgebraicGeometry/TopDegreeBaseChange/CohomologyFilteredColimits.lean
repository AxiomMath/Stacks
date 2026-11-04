module

public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendUnconditional
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses

/-!
# Cohomology commutes with filtered colimits, as a functor valued in modules

[Stacks, Tag 01FF] says that on a space with a basis of quasi-compact opens whose pairwise
intersections are quasi-compact, cohomology over a quasi-compact open commutes with filtered
colimits of sheaves of modules. It is proved for the `AddCommGrpCat`-valued cohomology functor
as `Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`.

This file states it for the **module-valued** cohomology functor
`(SheafOfModules.evaluation R (op U)).rightDerived q`, which is the functor every statement in
this directory is written in — and in both indexings, Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` and the `ℤ`-indexed `Functor.rightDerivedPlus` that
[Stacks, Tag 0E7D] and [Stacks, Tag 0EX3] are stated in here.

**The module-valued statement needs no new mathematics.** Colimits of modules are computed on
underlying abelian groups, so `forget₂ (ModuleCat R) AddCommGrpCat` reflects them; and
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` says that deriving
module-valued sections and then forgetting *is* deriving the abelian-group-valued sections
functor. The module-valued statement is therefore the `AddCommGrpCat`-valued one reflected
along the forgetful functor, with the same hypotheses and no extra input.

## Main results

* `Stacks.Cohomology.ModuleColimit.isIso_colimit_post_rightDerived_evaluation_of_isCompact`:
  **[Stacks, Tag 01FF] at the module-valued spelling**, in the tag's own shape — the canonical
  map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` of `Γ(U, O_X)`-modules is an isomorphism.
* `Stacks.Cohomology.ModuleColimit.preservesColimitsOfShape_rightDerived_evaluation_of_isCompact`:
  the same as preservation of filtered colimits, which is the form consumers use.
* `Stacks.Cohomology.ModuleColimit`'s
  `preservesColimitsOfShape_rightDerivedPlus_evaluation_of_isCompact`:
  the same for the `ℤ`-indexed `Functor.rightDerivedPlus`, crossed with
  `Stacks.DerivedIndexing.rightDerivedIso`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
  `isZero_rightDerivedPlus_moduleGlobalSections_colimit_of_forall_isZero`:
  **vanishing passes to a filtered colimit.** On a quasi-compact quasi-separated scheme, if
  `Hᑫ(X, Fᵢ)` vanishes for every member of a filtered system then it vanishes on the colimit.
  This is the step by which a vanishing statement proved for coherent modules extends to the
  quasi-coherent modules that are filtered colimits of them.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
  `isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation`:
  **the coherent → quasi-coherent step of [Stacks, Tag 0E7D]**, assembled from the previous
  statement and [Stacks, Tag 01PK].

## Implementation notes

**The scheme-level statements are at `U = ⊤` only**, because
`Stacks.Cohomology.AffineBase.moduleGlobalSections` is evaluation at `⊤`; the general
ringed-space statements above them carry an arbitrary quasi-compact open.

*The `@[stacks 01FF]` attribute is placed on the canonical-map form alone.* That declaration
states the tag verbatim at the module spelling, with the tag's hypotheses and no others, so it
is a member of a covering set for the tag; the preservation forms and the `rightDerivedPlus`
form are restatements of it and carry no attribute. The `AddCommGrpCat`-valued carrier
`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact` keeps its attribute.

*"The tag's hypotheses and no others" is now literal.* The tagged declaration writes its own
signature out instead of reading the section variables, because the three typeclass hypotheses
those variables carry — `HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}`, its
`WEqualsLocallyBijective` companion and `EnoughInjectives (SheafOfModules.{u} R)` — are all
plain instances when the space, the ring sheaf and the modules share a universe: the site of
opens of a space in `Type u` is `u`-small, so Mathlib's
`SheafOfModules.instIsGrothendieckAbelian` applies and
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` is a global instance. `omit` cannot be
used for this: the conclusion mentions `Functor.rightDerived`, so the variables are referenced
and Lean refuses to omit them. The preservation forms keep them as binders, which costs nothing
and keeps instance search cheap inside their proofs.

*`isZero_colimit_of_isZero` is pure category theory and exists three times already as a
`private` declaration* — `Stacks.Homology.Perfect`'s copy in `StacksFrontier/Homology/Perfect/ProjectiveAmplitude.lean`, which
is already at this generality, and a `ModuleCat`-specific one in
`AlgebraicGeometry/CoherentSubquotients/NowhereDense.lean`. Neither can be repointed at this
file without reversing the import order, so the public form is stated here and those two are
left for a dedup pass that can move it down into the category-theory tree.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.Cohomology.ModuleColimit

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **A colimit of zero objects is a zero object.** The identity of the colimit agrees with the
zero map after every injection, because each injection has a zero object as its source. -/
theorem isZero_colimit_of_isZero {J C : Type*} [Category* J] [Category* C]
    [HasZeroMorphisms C] (F : J ⥤ C) [HasColimit F] (h : ∀ j, IsZero (F.obj j)) :
    IsZero (colimit F) := by
  rw [IsZero.iff_id_eq_zero]
  refine colimit.hom_ext fun j => ?_
  rw [Category.comp_id, comp_zero]
  exact (h j).eq_of_src _ _

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **[Stacks, Tag 01FF] for the module-valued cohomology functor**, as preservation of
filtered colimits. The hypotheses are the tag's: a basis of quasi-compact opens with
quasi-compact pairwise intersections, and a quasi-compact open `U`.

The proof is reflection along `forget₂ (ModuleCat (R(U))) AddCommGrpCat`, which reflects
colimits because colimits of modules are computed on underlying abelian groups:
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` identifies the composite
with the `AddCommGrpCat`-valued cohomology functor, for which the statement is
`Stacks.Cohomology.DirectSum.preservesColimitsOfShape_Hfunctor_of_isFiltered`. -/
theorem preservesColimitsOfShape_rightDerived_evaluation_of_isCompact
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ)
    (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((_root_.SheafOfModules.evaluation R (op U)).rightDerived q) := by
  have h1 : PreservesColimitsOfShape I (Hfunctor R U q) :=
    Stacks.Cohomology.DirectSum.preservesColimitsOfShape_Hfunctor_of_isFiltered
      R hBasis hInter U hU q I
  have h2 : PreservesColimitsOfShape I
      ((_root_.SheafOfModules.evaluation R (op U)).rightDerived q ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) :=
    @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
      (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R U q).symm h1
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})

/-- **[Stacks, Tag 01FF] at the module-valued spelling, in the tag's own shape.** Let `X` be a
space with a basis of quasi-compact opens whose pairwise intersections are quasi-compact, let
`O_X` be a sheaf of rings on `X` and let `U` be a quasi-compact open. Then for every filtered
system `F` of `O_X`-modules and every degree `q` the canonical map
`colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` of `Γ(U, O_X)`-modules is an isomorphism.

`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact` is the same statement
for cohomology valued in abelian groups. -/
@[stacks 01FF]
theorem isIso_colimit_post_rightDerived_evaluation_of_isCompact
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ)
    {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ SheafOfModules.{u} R) :
    IsIso (colimit.post F ((_root_.SheafOfModules.evaluation R (op U)).rightDerived q)) := by
  have := preservesColimitsOfShape_rightDerived_evaluation_of_isCompact R hBasis hInter U hU q I
  infer_instance

/-- **[Stacks, Tag 01FF] in the `ℤ`-indexed derived-category spelling.** The two indexings of
the right derived functors agree in a degree that is a natural number
(`Stacks.DerivedIndexing.rightDerivedIso`), so the preservation statement transports. This is
the indexing [Stacks, Tag 0E7D] and [Stacks, Tag 0EX3] are stated in in this directory. -/
theorem preservesColimitsOfShape_rightDerivedPlus_evaluation_of_isCompact
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ)
    (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      ((_root_.SheafOfModules.evaluation R (op U)).rightDerivedPlus (q : ℤ)) := by
  have h := preservesColimitsOfShape_rightDerived_evaluation_of_isCompact R hBasis hInter U hU q I
  exact @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _
    (Stacks.DerivedIndexing.rightDerivedIso (_root_.SheafOfModules.evaluation R (op U)) q) h

end

end Stacks.Cohomology.ModuleColimit

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (X : Scheme.{u}) [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with filtered colimits**, as
a functor valued in `Γ(X, ⊤)`-modules. The two topological hypotheses of [Stacks, Tag 01FF] are
discharged by `hasBasisOfCompactOpens_scheme` and `interCompactOpenIsCompact_scheme`.

`preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections` is the direct-sum
statement; a coproduct is not a filtered colimit, so neither statement implies the other
directly. -/
theorem preservesColimitsOfShape_rightDerived_moduleGlobalSections_of_isFiltered
    (q : ℕ) (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((moduleGlobalSections X).rightDerived q) :=
  Stacks.Cohomology.ModuleColimit.preservesColimitsOfShape_rightDerived_evaluation_of_isCompact
    X.ringCatSheaf (hasBasisOfCompactOpens_scheme X) (interCompactOpenIsCompact_scheme X) ⊤
    (by simpa using CompactSpace.isCompact_univ) q I

/-- The canonical-map form of the previous statement: on a quasi-compact quasi-separated scheme
the map `colimᵢ Hᑫ(X, Fᵢ) ⟶ Hᑫ(X, colimᵢ Fᵢ)` of `Γ(X, ⊤)`-modules is an isomorphism. -/
theorem isIso_colimit_post_rightDerived_moduleGlobalSections
    (q : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ X.Modules) :
    IsIso (colimit.post F ((moduleGlobalSections X).rightDerived q)) := by
  have := preservesColimitsOfShape_rightDerived_moduleGlobalSections_of_isFiltered X q I
  infer_instance

/-- The same for the `ℤ`-indexed `Functor.rightDerivedPlus`, which is the spelling the
[Stacks, Tag 0E7D] and [Stacks, Tag 0EX3] statements in this directory use. -/
theorem preservesColimitsOfShape_rightDerivedPlus_moduleGlobalSections_of_isFiltered
    (q : ℕ) (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((moduleGlobalSections X).rightDerivedPlus (q : ℤ)) :=
  Stacks.Cohomology.ModuleColimit.preservesColimitsOfShape_rightDerivedPlus_evaluation_of_isCompact
    X.ringCatSheaf (hasBasisOfCompactOpens_scheme X) (interCompactOpenIsCompact_scheme X) ⊤
    (by simpa using CompactSpace.isCompact_univ) q I

/-- **Vanishing of absolute cohomology passes to a filtered colimit.** On a quasi-compact
quasi-separated scheme, if `Hᑫ(X, Fᵢ)` is a zero object for every member of a filtered system
then so is `Hᑫ(X, colimᵢ Fᵢ)`.

This is the shape in which [Stacks, Tag 01FF] is used to pass a vanishing statement from the
coherent modules to the quasi-coherent ones: a quasi-coherent module that is a filtered colimit
of coherent submodules inherits their vanishing. The hypothesis is on
`Functor.rightDerivedPlus`, which is the indexing the `hcoh` residue of [Stacks, Tag 0E7D] is
stated in. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_colimit_of_forall_isZero
    (q : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I] (F : I ⥤ X.Modules)
    (h : ∀ i, IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj (F.obj i))) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj (colimit F)) := by
  have hp := preservesColimitsOfShape_rightDerivedPlus_moduleGlobalSections_of_isFiltered X q I
  exact (Stacks.Cohomology.ModuleColimit.isZero_colimit_of_isZero
      (F ⋙ (moduleGlobalSections X).rightDerivedPlus (q : ℤ)) h).of_iso
    (preservesColimitIso ((moduleGlobalSections X).rightDerivedPlus (q : ℤ)) F)

/-- **Vanishing for modules of finite presentation gives vanishing for all quasi-coherent
modules.** On a quasi-compact quasi-separated scheme, if `Hᑫ(X, G)` vanishes for every module
`G` of finite presentation, then it vanishes for every quasi-coherent module.

This is the *coherent → quasi-coherent* step of the proof of [Stacks, Tag 0E7D]: its two inputs
are [Stacks, Tag 01PK] — a quasi-coherent module on a quasi-compact quasi-separated scheme is
the colimit of a directed system of modules of finite presentation,
`AlgebraicGeometry.exists_directed_system_of_isFinitePresentation` — and
[Stacks, Tag 01FF] in the form above. On a locally Noetherian scheme "finite presentation"
upgrades to "coherent" by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation`, which is where
the source's word "coherent" enters; no Noetherian hypothesis is needed here. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation (q : ℕ)
    (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ G : X.Modules, G.IsFinitePresentation →
      IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj G)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj F) := by
  obtain ⟨I, hPO, hNE, hDir, D, φ, hFP, ⟨hc⟩⟩ :=
    _root_.AlgebraicGeometry.exists_directed_system_of_isFinitePresentation X F
  have : HasColimit D := ⟨⟨_, hc⟩⟩
  exact (isZero_rightDerivedPlus_moduleGlobalSections_colimit_of_forall_isZero X q D
    (fun i => h (D.obj i) (hFP i))).of_iso
    (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).mapIso
      (hc.coconePointUniqueUpToIso (colimit.isColimit D)))

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
