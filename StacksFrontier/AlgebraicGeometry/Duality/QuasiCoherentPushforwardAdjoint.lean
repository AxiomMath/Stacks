module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct image on quasi-coherent derived categories, and its right adjoint

Let `f : X ⟶ Y` be a morphism of schemes. Sheaves of `𝒪_X`-modules form a Grothendieck abelian
category, so every cochain complex of them admits a K-injective resolution and direct image has a
total right derived functor `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` on the *unbounded* derived categories.
Inside `D(𝒪_X)` sits the full subcategory `D_QCoh(𝒪_X)` of the complexes all of whose cohomology
sheaves are quasi-coherent, and `Rf_*` restricts to it once one knows that it preserves
quasi-coherence of cohomology.

The abstract half of Grothendieck duality asks for a right adjoint to that restriction — the
functor written `f^×` in the literature. The Stacks proof of [Stacks, Tag 0A9E] obtains it from
Brown representability: `D_QCoh(𝒪_X)` has direct sums and is compactly generated, and for `f`
quasi-compact and quasi-separated `Rf_*` commutes with direct sums, so the right adjoint exists
by the formal statement [Stacks, Tag 0A8G], available here as
`CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`.

## Main definitions

* `Stacks.Duality.derivedPushforward` — the unbounded derived direct image `Rf_*` of sheaves of
  modules along a morphism of schemes. It needs no hypotheses beyond a choice of derived
  category: its existence is K-injective resolutions in a Grothendieck abelian category.
* `Stacks.Duality.quasiCoherentDerivedCategory` — the full subcategory `D_QCoh(𝒪_X)` of the
  unbounded derived category cut out by quasi-coherence of every cohomology sheaf.
* `Stacks.Duality.quasiCoherentDerivedPushforward` — the restriction of `Rf_*` to
  `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

## Main results

* `Stacks.Duality.hasRightDerivedFunctor_of_isGrothendieckAbelian` — every functor out of the
  homotopy category of cochain complexes in a Grothendieck abelian category has a total right
  derived functor along the quasi-isomorphisms.
* `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` — the restricted derived direct
  image is a left adjoint as soon as `D_QCoh(𝒪_X)` is a triangulated category with direct sums
  which is compactly generated and the restricted functor is exact and preserves direct sums.
  This is the Stacks proof of Tag 0A9E with its geometric inputs left as hypotheses; see the
  implementation notes for which ones and why.

## Implementation notes

`derivedPushforward` is `Functor.totalRightDerived` of the composite
`K(𝒪_X-Mod) ⥤ K(𝒪_Y-Mod) ⥤ D(𝒪_Y)`, and the `HasRightDerivedFunctor` hypothesis it needs is
supplied unconditionally, as an instance, by
`hasRightDerivedFunctor_of_isGrothendieckAbelian`, whose proof is the functorial K-injective
resolution of [Stacks, Tag 079P] fed to [Stacks, Tag 070K]. Statements elsewhere that carry that
hypothesis as a `letI` can therefore drop it.

The morphism universe `w` of the derived categories is left free, rather than fixed by
`HasDerivedCategory.standard`, and this is forced by the adjointness statement rather than a
matter of taste. `HasDerivedCategory.standard` puts the morphisms of `D(𝒪_X)` in
`Type (u + 1)`, and Brown representability asks for coproducts indexed by the types of its own
morphism universe; but a `Type (u + 1)`-indexed family of sheaves of `𝒪_X`-modules has no direct
sum, those being computed from direct sums of `Type u`-sized modules. So with the standard
derived category the hypothesis `HasCoproducts` below is not merely unavailable, it is false, and
the statement would be vacuous. With `w = u` — a locally small derived category, which a
Grothendieck abelian category has, its morphism sets being computed as homotopy classes of maps
into a K-injective resolution — the hypothesis is the direct sums of [Stacks, Tag 08DT] and the
statement has content. That locally small model is available, as the global instances
`SheafOfModules.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, and it is the model in force on
`Stacks.Duality.quasiCoherentDerivedCategory` wherever no file-level attribute pins
`HasDerivedCategory.standard`.

`isLeftAdjoint_quasiCoherentDerivedPushforward` is **not** Tag 0A9E: it carries hypotheses that
the source derives from the geometry of a quasi-compact, quasi-separated morphism. They are, in
the order the source uses them, with their present status at the locally small model:

* `(DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent _)).IsTriangulated` for
  the source and the target — quasi-coherent modules on a scheme form a weak Serre subcategory
  ([Stacks, Tag 01LA], [Stacks, Tag 077P]), which is what makes `D_QCoh` a triangulated
  subcategory ([Stacks, Tag 06VT]). *Available*, as the instance
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`.
* `HasCoproducts.{w} (quasiCoherentDerivedCategory X)` — `D_QCoh(𝒪_X)` has direct sums
  ([Stacks, Tag 08DT]). *Available*, as
  `Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory`.
* exactness of the restricted functor, i.e. a `Functor.CommShift ℤ` structure together with
  `Functor.IsTriangulated` — `Rf_*` is an exact functor of triangulated categories. *Available*,
  model-generically, as `Stacks.Duality.DerivedPushforward.commShift_*` and
  `isTriangulated_quasiCoherentDerivedPushforward`.
* `PreservesColimitsOfShape (Discrete α)` of the restricted functor for every `α : Type w` —
  `Rf_*` commutes with direct sums ([Stacks, Tag 08DZ]), which is where quasi-compactness and
  quasi-separatedness of `f` enter. *Proved only at* `HasDerivedCategory.standard`, by
  `preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward` of
  `Stacks.Duality.DerivedPushforward` — the obstruction to reading it at the locally small model
  is part (2) of [Stacks, Tag 08D5], recorded in
  `StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBound.lean`.
* a compact generating family `E` — `D_QCoh(𝒪_X)` is compactly generated for `X` quasi-compact
  and quasi-separated ([Stacks, Tag 09IS]). *Open*. Tag 09IS rests on
  Tags 08DD, 08EH, 08EI, 08EK, 09IM and 09IQ, and all six are registered: 08DD as
  `Koszul.DerivedSystem.cohomologyComparison_bijective`
  (`…/Perfect/KoszulCohomologyComparisonBijective.lean`, at the standard model), 08EH, 08EI and
  08EK for an affine `X` (`…/DerivedQCoh/OpenLift/AffineLift.lean`,
  `…/OpenLift/AffineSupportedLift.lean`), in the `Spec A` forms the arguments here consume in
  `…/OpenLift/PerfectSourceLift.lean`, `…/OpenLift/ShiftedSummandLift.lean` and
  `…/OpenLift/SupportedPerfectLift.lean`, 09IM for a quasi-compact quasi-separated `X` and a
  *general* closed `T` with retrocompact complement as
  `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift`
  (`…/Perfect/LiftingComplexes/General.lean`), and 09IQ unconditionally at a quasi-compact open of
  a quasi-compact quasi-separated scheme, at the locally small model, as
  `Stacks.DerivedQCoh.AnyModel.exists_isPerfect_retract_derivedRestrict`
  (`…/DerivedQCoh/AnyModel/PerfectSummandOfRestriction.lean`). What is open is the *induction* of
  [Stacks, Tag 08DR] over an affine cover that assembles them; see the coverage note of
  `StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineCompactObject.lean` for the
  inductive step and what it still needs. The compact-generation-free alternative of
  [Stacks, Tag 0GZ0] part (3) needs the comparison of [Stacks, Tag 0GZZ], for which see the
  coverage note of
  `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineSiteQuasiCoherentObjects.lean`.

**This list is not an obstruction to [Stacks, Tag 0A9E] itself.** That tag is proved for a
quasi-compact quasi-separated morphism with quasi-compact target, at the locally small model, as
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`: it runs
the weak Brown representability of [Stacks, Tag 0GYG] on the generating family of
`AlgebraicGeometry.exists_generating_family_quasiCoherentDerivedCategory`, which exists for every
scheme with no hypothesis, in place of a compact generator. The bullets above are the hypotheses
of `isLeftAdjoint_quasiCoherentDerivedPushforward` below, which is the *source's* route to 0A9E
and not the only one in this library.

The hypothesis `hpush` that `Rf_*` preserves quasi-coherent cohomology is an explicit argument
rather than a hypothesis of the adjointness statement, because the restricted functor cannot be
written down without it; it too is a theorem of the source for a quasi-compact, quasi-separated
morphism, part (1) of [Stacks, Tag 08D5], and it is available at the locally small model as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` for a quasi-compact
quasi-separated `f` with quasi-compact target.

Compactness and generation are phrased as the source lemma phrases them: `E i` is compact when
`preadditiveCoyoneda.obj (op (E i))` preserves direct sums, and the family generates when the
only objects right orthogonal to all shifts of all `E i` are the zero objects. The conclusion is
`Functor.IsLeftAdjoint`, the shape in which later results consume the adjoint through
`Functor.rightAdjoint`; exactness of that adjoint, which the source also records, is available
from the same source lemma.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Amnon Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*, Example 4.2][Neeman-Grothendieck]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite

universe w v u v' u'

namespace Stacks.Duality

/-! ### Total right derived functors in a Grothendieck abelian category -/

/-- Every functor out of the homotopy category of cochain complexes in a Grothendieck abelian
category has a total right derived functor along the quasi-isomorphisms: such a category admits
functorial K-injective resolutions ([Stacks, Tag 079P]), and a category in which every complex
receives a quasi-isomorphism into a K-injective complex has pointwise right derived functors
([Stacks, Tag 070K]). -/
theorem hasRightDerivedFunctor_of_isGrothendieckAbelian
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    {H : Type u'} [Category.{v'} H] (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := fun K =>
    ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩
  have :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v, v',
      v, u, u', u} F hA).1
  infer_instance

/-! ### The quasi-coherent derived category of a scheme -/

section

variable (Z : Scheme.{u}) [HasDerivedCategory.{w} Z.Modules]

/-- `D_QCoh(𝒪_Z)`: the full subcategory of the unbounded derived category of `𝒪_Z`-modules
consisting of the objects whose cohomology sheaf is quasi-coherent in every degree. -/
@[sga "6 II 3.7"]
abbrev quasiCoherentDerivedCategory : Type (u + 1) :=
  (DerivedCategoryB.derivedCategoryB
    (A := Z.Modules) (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).FullSubcategory

end

/-! ### Derived direct image of sheaves of modules on schemes -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- Direct image of sheaves of modules on the homotopy categories of cochain complexes, followed
by the localization at the quasi-isomorphisms. Its total right derived functor is
`Stacks.Duality.derivedPushforward`. -/
abbrev homotopyPushforward :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory Y.Modules :=
  (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `homotopyPushforward f` has a right derived functor with respect to the quasi-isomorphisms. -/
instance hasRightDerivedFunctor_homotopyPushforward :
    (homotopyPushforward f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- The unbounded derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of sheaves of modules along a
morphism of schemes, as the total right derived functor of direct image. -/
abbrev derivedPushforward : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  (homotopyPushforward f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-! ### The restriction of `Rf_*` to quasi-coherent cohomology -/

/-- Derived direct image restricted to the complexes with quasi-coherent cohomology, given that
it preserves quasi-coherence of the cohomology sheaves. -/
abbrev quasiCoherentDerivedPushforward
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ derivedPushforward f) hpush

/-! ### The right adjoint, from Brown representability -/

/-- **The Stacks proof of Tag 0A9E, with its geometric inputs as hypotheses.** Let `f : X ⟶ Y`
be a morphism of schemes and suppose derived direct image preserves quasi-coherent cohomology.
If `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_Y)` are triangulated subcategories, if `D_QCoh(𝒪_X)` has direct
sums and is compactly generated by a family `E`, and if the restricted derived direct image is
exact and commutes with direct sums, then it has a right adjoint — the twisted inverse image
`f^×`.

The hypotheses are precisely the inputs the source cites: Tags 06VT, 08DT, 08DZ and 09IS. The
proof is one application of [Stacks, Tag 0A8G]. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward
    [(DerivedCategoryB.derivedCategoryB
      (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated]
    [(DerivedCategoryB.derivedCategoryB
      (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).IsTriangulated]
    [HasCoproducts.{w} (quasiCoherentDerivedCategory X)]
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hpush).CommShift ℤ]
    [(quasiCoherentDerivedPushforward f hpush).IsTriangulated]
    [∀ α : Type w, PreservesColimitsOfShape (Discrete α)
      (quasiCoherentDerivedPushforward f hpush)]
    {ι : Type w} (E : ι → quasiCoherentDerivedCategory X)
    [∀ (i : ι) (α : Type w),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : quasiCoherentDerivedCategory X,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    (quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint := by
  obtain ⟨_, adj, _, _⟩ :=
    Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated
      (quasiCoherentDerivedPushforward f hpush) E hE
  exact adj.isLeftAdjoint

end Stacks.Duality

end
