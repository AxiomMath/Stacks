module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.UnboundedDerivedPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# The derived base-change map: the localization step and the cover step of Stacks 0DJ9

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of ringed spaces or of schemes, and let

`Lg^*(Rf_* K) ⟶ Rf'_*(L(g')^* K)`

be the derived base-change map of Stacks 08HY.  Stacks 0DJ9 asserts that this is an isomorphism
when `f` is quasi-compact and quasi-separated, `K` has quasi-coherent cohomology sheaves and the
chart comparisons of Stacks 0DJ8 (2) are invertible.  Its proof has three steps: localize the base
to an affine open; run an induction over the quasi-compact opens of `X`; settle the affine case
from the chart condition.  This module carries the first step in full and the engine of the second.

**The localization step.**  When the horizontal arrows `g` and `g'` are open immersions the
base-change map is an isomorphism for *every* `K`, with no finiteness or quasi-coherence
hypothesis.  Its content is Stacks 08FE — derived direct image commutes with restriction to an open
of the base — together with the observation that the comparison isomorphism 08FE provides *is* the
canonical map of Stacks 08HY.  The latter is what has to be checked, and the route to it is the
mates calculus: the canonical map is by construction the mate of the comparison of the two
iterated derived pullbacks, and a mate taken across two adjunctions with invertible counits is the
conjugate of that comparison, hence invertible with it.

**The cover step.**  Invertibility of the base-change map at one vertex of a distinguished triangle
in `D(𝒪_X)` follows from invertibility at the other two, and at a binary biproduct from
invertibility at the two summands.  Together with the Mayer–Vietoris triangle of Stacks 08HZ and
the induction of Stacks 08DR — both supplied below in the shape the step consumes — this is the
two-out-of-three mechanism of the induction over quasi-compact opens.

## Main definitions

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `openImmersionDerivedPullbackUnit` — the canonical derived pullback along an open immersion,
  equipped with the unit exhibiting it as a *right* derived functor of degreewise pullback.
* `derivedPushforwardRestrictIsoCanonical` — the isomorphism of Stacks 08FE, instantiated at the
  canonical derived pushforwards and pullbacks of the square.
* `openDerivedPushforward` — the chosen derived pushforward of the restriction of `f` to an open of
  its source, and `openDerivedPushforwardUnit` its canonical comparison.
* `derivedBaseChangeSourceCommShift`, `derivedBaseChangeTargetCommShift` — the shift
  compatibility of the two sides of the base-change two-square.  That of `Rf_*` itself is
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift`, seated below
  as a local instance.
* `derivedBaseChangeNatTrans` — the base-change two-square of Stacks 08HY read as a plain natural
  transformation `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`.

## Main results

* `derivedBaseChangeMap_eq_mateEquiv_app` — the base-change map of Stacks 08HY, written out as the
  mate of the comparison of the two iterated derived pullbacks; and
  `derivedBaseChangeNatTrans_app`, its components read off `derivedBaseChangeNatTrans`.
* `isIso_mateEquiv_app_of_isIso_counit` — the abstract statement: in a square of four adjunctions
  in which the two "horizontal" ones have invertible counit, the mate of an invertible two-square
  of left adjoints is invertible, provided the square of right adjoints commutes up to some
  isomorphism.
* `isIso_derivedAdjunction_counit_of_isOpenImmersion` — the counit of the derived adjunction
  `Lf^* ⊣ Rf_*` of an open immersion of ringed spaces is invertible.
* `isIso_derivedBaseChangeMap_of_isOpenImmersions` — **the localization step**: the derived
  base-change map of Stacks 08HY on a Cartesian square of ringed spaces whose horizontal arrows are
  open immersions; and `isIso_derivedBaseChangeMap_of_isOpenImmersion`, the same for a Cartesian
  square of schemes whose bottom arrow is an open immersion.
* `compact_open_immersion_induction_on` — the induction of Stacks 08DR, reindexed by the schemes
  carrying an open immersion into `Y` rather than by the opens of `Y`.
* `exists_canonicalRelativeMayerVietorisTriangle` — the Mayer–Vietoris triangle of Stacks 08HZ at
  the canonical derived pushforwards.
* `isIso_app_first_of_all_shifts`, `isIso_app_of_biprod`, `isIso_app_shift_biprod` — the generic
  transports of invertibility of a natural transformation along a distinguished triangle and across
  a binary biproduct.
* `isIso_derivedBaseChangeNatTrans_app_of_distTriang` and
  `isIso_derivedBaseChangeNatTrans_app_shift_biprod` — **the cover step**, those transports applied
  to the base-change map.

## Implementation notes

*Scope.*  No declaration below carries the tag 0DJ9; Stacks 0DJ9 is
`AlgebraicGeometry.isIso_derivedBaseChangeComp_of_pointwiseBaseChange`.

*Why Stacks 08HZ is not restated over an open.*  Stacks 08HZ,
`Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris`, is stated for a cover
`U ⊔ V = ⊤` of the whole source, while the induction of Stacks 08DR ranges over the opens of one
scheme.  Rather than restate 08HZ over an open subspace, `compact_open_immersion_induction_on`
reindexes the induction by an arbitrary quasi-compact quasi-separated scheme carrying an open
immersion into `Y`; at every stage the cover is then a cover of the whole source and 08HZ applies
as it stands.

*What the existential of Stacks 08HZ does not give.*  Its five natural transformations come with no
characterization, so `exists_canonicalRelativeMayerVietorisTriangle` says that *some* triangle
exists on the canonical vertices, not that the canonical restriction maps are its legs.  This is
why the cover step below is formulated as a transport along *one* distinguished triangle in the
source category rather than as a comparison of the triangles of `f` and of `f'`: comparing two
triangles would need their legs pinned down by the universal property of the right derived functor,
and strengthening 08HZ to expose that is a separate piece of work.

*Why the open-immersion case may not be deduced from Stacks 08IB.*  In this development the input
to 08IB, `AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison`, is a statement
about the ring-level comparison on a chart; the chart-level statement 0DJ8 (2) is what 0DJ9
consumes, and the localization step is used in proving it.  The step therefore has to be obtained
from 08FE directly, which is what happens below; no Lean import cycle is involved, but the
mathematical order of the argument matters.

*Derived pullback as a right derived functor.*  Stacks 08FE is stated for arbitrary choices of
right derived functors of the four degreewise functors, so to apply it to the canonical derived
pullback — which this development constructs as a *left* derived functor, by K-flat resolutions —
one must also exhibit the canonical derived pullback as a right derived functor.  That is
`openImmersionDerivedPullback_isRightDerivedFunctor`, and it holds only for an open immersion:
there `pullbackOnHomotopy` inverts the quasi-isomorphisms, by Stacks 08FE's
`Stacks.Cohomology.derivedRestrictionUnit_isIso`, so the canonical comparison
`derivedPullbackComparison` is invertible and may be read backwards as a right-derived unit.
`pullbackOnHomotopy_hasRightDerivedFunctor`, which needs no open immersion, is recorded separately
because it is K-injective resolutions that provide it.

*No shift compatibility of the base-change map is used.*  The base-change map is built as a mate,
and nothing in this repository or in Mathlib derives `CategoryTheory.NatTrans.CommShift` for a
mate, so it does not give a morphism of triangles.  The cover step avoids needing one by going
through `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`, which
asks only that the two functors be exact and pays for the missing shift compatibility with
hypotheses at every shift instead of only at the shift by one.  That is why the statements below
quantify over all shifts.

*Three places where the kernel's reduction budget is the binding constraint.*  First,
`derivedBaseChangeMap_eq_mateEquiv_app` and `derivedBaseChangeMap_eq_derivedBaseChangeSquare_app`
are chains of `rfl` steps joined by `Eq.trans`, each unfolding exactly one definition; the
composite equations are also true by `rfl`, but the kernel does not check them, because it reduces
through the `eqToIso` of `derivedPullbackCompIsoLeft` and so unfolds the derived functors on
objects.  Second, `isIso_mateEquiv_app_of_isIso_counit` takes an arbitrary two-square with an
invertible underlying transformation rather than an isomorphism of functors, so that the two-square
the library already built is handed to it verbatim instead of being rebuilt and matched up to
definitional equality.  Third, the cover step is stated for `derivedBaseChangeNatTrans` rather than
for `derivedBaseChangeSquare`: passing the latter as the natural-transformation argument of
`isIso_app_first_of_all_shifts` exceeds the budget, while a bare type ascription of it to
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` — which is all `derivedBaseChangeNatTrans` is — does not.  The
shift and exactness data of the two functors are likewise passed as named constants rather than
found by instance search at the point of use.  `isIso_derivedBaseChangeNatTrans_app_iff` converts
between the two spellings one component at a time.

*The model of the derived category.*  Everything here is at `HasDerivedCategory.standard`, which
is the model `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` is declared at, installed
as a file-local instance.  Nothing is claimed about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; a statement proved here can be transported
to it by `StacksDraft.DerivedModel.isIso_shrinkComparison_functor_map_iff`, and a morphism taken
at that model can be brought here by `StacksDraft.DerivedModel.derivedPullbackModelIso` followed
by the inverse of `StacksDraft.DerivedModel.shrinkComparison`.

That transport cannot be carried out *in this module*, which is why it is not.  The proofs below
leave the `HasDerivedCategory` argument of `derivedPullback`, `derivedPushforward` and
`pullbackOnHomotopy` to instance search, and rely on search finding at the standard model the
`Functor.IsRightDerivedFunctor` and `Functor.HasLeftDerivedFunctor` instances that the derived
functors need.  Importing `StacksFrontier.Homology.DerivedCategory.LocallySmall`, which the
transport
needs, puts a second global `HasDerivedCategory` instance on
`SheafOfModules.{u} (structureSheafRing X)` in scope, and search then prefers it to the file-local
one: `pullbackOnHomotopy f` is elaborated with morphisms in `Type u` instead of `Type (u + 1)` and
nothing below typechecks.  A module combining the two must therefore spell every instance
explicitly, as `StacksFrontier/Homology/DerivedCategory/ModelComparison.lean` does, and that is
incompatible with leaving the derived-functor instances to search.  The affine case of Stacks 0DJ9,
which needs both, belongs in a module of its own.

## References

* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardAssociativity (derivedPushforwardIdIso
  derivedPullbackIdIso)

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance] HasDerivedCategory.standard

/-! ### The mate of an invertible two-square, across adjunctions with invertible counit -/

section Abstract

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  {H : C ⥤ C'} {I : C' ⥤ C} {J : D ⥤ D'} {V : D' ⥤ D}

/-- **The mate of an invertible two-square is invertible when the two horizontal adjunctions have
invertible counit.**  Consider four adjunctions `a : L ⊣ R`, `b : L' ⊣ R'`, `h : H ⊣ I` and
`j : J ⊣ V` arranged in a square, and suppose `h` and `j` have invertible counits.  Let
`α : H ⋙ L' ⟶ L ⋙ J` be a two-square of the left adjoints whose underlying transformation is
invertible, and suppose that the square of right adjoints commutes up to *some* isomorphism
`e : R ⋙ H ≅ J ⋙ R'`.  Then the mate of `α` is invertible at every object.

The isomorphism `e` is used only to know that `H` sends `R`-images of the unit components of `j`
to isomorphisms; the conclusion is about the mate of `α`, which is a different morphism from `e`.
This is the abstract form of base change along an open immersion: `H` and `J` are the two
restriction functors, whose derived adjunctions have invertible counit because restricting a
direct image back to the open subspace changes nothing, and `e` is the comparison of
Stacks 08FE. -/
theorem isIso_mateEquiv_app_of_isIso_counit (a : L ⊣ R) (b : L' ⊣ R') (h : H ⊣ I) (j : J ⊣ V)
    [IsIso h.counit] [IsIso j.counit] (α : TwoSquare H L L' J) [IsIso α]
    (e : R ⋙ H ≅ J ⋙ R') (A : D) :
    IsIso ((mateEquiv a b α).app A) := by
  set β := mateEquiv a b α with hβ
  have hδ : (mateEquiv j h β) = conjugateEquiv (a.comp j) (h.comp b) α :=
    iterated_mateEquiv_conjugateEquiv a b h j _
  have : IsIso (mateEquiv j h β) := by rw [hδ]; infer_instance
  have hJ : IsIso (J.map (j.unit.app A)) := by
    refine (isIso_comp_right_iff _ (j.counit.app (J.obj A))).mp ?_
    rw [j.left_triangle_components A]
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  have : IsIso (H.map (R.map (j.unit.app A))) :=
    (NatIso.isIso_map_iff e (j.unit.app A)).mpr (R'.map_isIso (J.map (j.unit.app A)))
  have hfac : H.map (R.map (j.unit.app A)) ≫
      H.map ((mateEquiv j h β).app (J.obj A)) ≫ h.counit.app (R'.obj (J.obj A)) =
      β.app A := by
    rw [← H.map_comp_assoc, unit_mateEquiv j h β A, H.map_comp, Category.assoc]
    change H.map (h.unit.app (R.obj A)) ≫ H.map (I.map (β.app A)) ≫
      h.counit.app _ = _
    rw [h.counit_naturality (β.app A), ← Category.assoc]
    exact (congrArg (fun t => t ≫ β.app A)
      (h.left_triangle_components (R.obj A))).trans (Category.id_comp _)
  rw [← hfac]
  infer_instance

end Abstract

/-! ### Derived pullback along an open immersion, read as a right derived functor -/

section OpenImmersion

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Every functor out of the homotopy category of sheaves of modules on a ringed space, with values
in a category of the appropriate size, has a right derived functor, by K-injective resolutions. -/
private theorem hasRightDerivedFunctor_of_exists_kInjective {X : RingedSpace.{u, u}}
    {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} F (exists_quasiIso_isKInjective X)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **Degreewise pullback also has an everywhere-defined right derived functor.**  Unlike the
left derived functor, which this development builds from K-flat resolutions, this one comes from
K-injective resolutions and so needs no hypothesis on `f` at all; it is Stacks 070K applied to
`pullbackOnHomotopy f`. -/
theorem pullbackOnHomotopy_hasRightDerivedFunctor :
    (pullbackOnHomotopy f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :=
  hasRightDerivedFunctor_of_exists_kInjective _

attribute [local instance] pullbackOnHomotopy_hasRightDerivedFunctor

/-- **Derived pullback along an open immersion is ordinary restriction.**  Pullback along an open
immersion is exact, so by Stacks 08FE the unit of any chosen right derived functor of it is
invertible; since `pullbackOnHomotopy f` therefore inverts the quasi-isomorphisms, the canonical
comparison `Lf^* ∘ Q ⟶ f^*` from the chosen left derived functor is invertible as well. -/
theorem isIso_derivedPullbackComparison_of_isOpenImmersion [SheafedSpace.IsOpenImmersion f] :
    IsIso (derivedPullbackComparison f) := by
  set W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ) with hW
  set P := pullbackOnHomotopy f with hP
  have : IsIso (P.totalRightDerivedUnit DerivedCategory.Qh W) :=
    Stacks.Cohomology.derivedRestrictionUnit_isIso f (P.totalRightDerived DerivedCategory.Qh W)
      (P.totalRightDerivedUnit DerivedCategory.Qh W)
  have hinv : W.IsInvertedBy P :=
    (MorphismProperty.IsInvertedBy.iff_of_iso W
        (asIso (P.totalRightDerivedUnit DerivedCategory.Qh W))).mpr
      (MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
        Functor.IsLocalization.inverts (P.totalRightDerived DerivedCategory.Qh W))
  have : (derivedPullback f).IsLeftDerivedFunctor
      (L := DerivedCategory.Qh) (derivedPullbackComparison f) W := by
    dsimp only [derivedPullback, derivedPullbackComparison]
    infer_instance
  exact Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (L := DerivedCategory.Qh) (W := W) (derivedPullback f) (derivedPullbackComparison f) hinv

/-- The canonical derived pullback along an open immersion, equipped with the unit that exhibits
it as a *right* derived functor of degreewise pullback: the inverse of the canonical comparison,
which is invertible by `isIso_derivedPullbackComparison_of_isOpenImmersion`. -/
def openImmersionDerivedPullbackUnit [SheafedSpace.IsOpenImmersion f] :
    pullbackOnHomotopy f ⟶ DerivedCategory.Qh ⋙ derivedPullback f :=
  have := isIso_derivedPullbackComparison_of_isOpenImmersion f
  inv (derivedPullbackComparison f)

/-- The canonical derived pullback along an open immersion is a right derived functor of
degreewise pullback, with unit `openImmersionDerivedPullbackUnit`.  This is the shape in which
Stacks 08FE consumes a restriction functor. -/
theorem openImmersionDerivedPullback_isRightDerivedFunctor [SheafedSpace.IsOpenImmersion f] :
    (derivedPullback f).IsRightDerivedFunctor (openImmersionDerivedPullbackUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ)) :=
  have := isIso_derivedPullbackComparison_of_isOpenImmersion f
  Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (.up ℤ))
    (derivedPullback f) (asIso (derivedPullbackComparison f))

attribute [local instance] openImmersionDerivedPullback_isRightDerivedFunctor

end OpenImmersion

section Localization

attribute [local instance] pullbackOnHomotopy_hasRightDerivedFunctor
  openImmersionDerivedPullback_isRightDerivedFunctor

/-! ### Stacks 08FE for the canonical derived pushforwards and pullbacks -/

/-- **Stacks 08FE for the canonical choices.**  On a Cartesian square of ringed spaces whose
vertical arrows `i` and `j` are open immersions, restricting the canonical derived direct image
along `j` is the canonical derived direct image along `g` of the restriction along `i`.  This is
`Stacks.Cohomology.derivedPushforwardRestrictIso` instantiated at the canonical derived
pushforwards, with their total-right-derived units, and at the canonical derived pullbacks, with
the units of `openImmersionDerivedPullback_isRightDerivedFunctor`. -/
def derivedPushforwardRestrictIsoCanonical {X Y U V : RingedSpace.{u, u}}
    (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]
    (sq : IsPullback i g f j) :
    derivedPushforward f ⋙ derivedPullback j ≅ derivedPullback i ⋙ derivedPushforward g :=
  Stacks.Cohomology.derivedPushforwardRestrictIso f i j g sq
    (derivedPushforward f) (derivedPushforward g) (derivedPullback i) (derivedPullback j)
    (derivedPushforwardUnit f) (derivedPushforwardUnit g)
    (openImmersionDerivedPullbackUnit i) (openImmersionDerivedPullbackUnit j)

/-- **The derived adjunction of an open immersion has invertible counit**: restricting a derived
direct image back to the open subspace changes nothing.  Applying
`derivedPushforwardRestrictIsoCanonical` to the Cartesian square with both other sides the
identity gives `Rf_* ⋙ Lf^* ≅ L(𝟙)^* ⋙ R(𝟙)_*`, which the unit laws of Stacks 0D5S identify with
the identity functor. -/
theorem isIso_derivedAdjunction_counit_of_isOpenImmersion {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    [SheafedSpace.IsOpenImmersion f] : IsIso (derivedAdjunction f).counit :=
  have sq : IsPullback (𝟙 X) (𝟙 X) f f := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  (derivedAdjunction f).isIso_counit_of_iso
    (derivedPushforwardRestrictIsoCanonical f (𝟙 X) f (𝟙 X) sq ≪≫
      Functor.isoWhiskerLeft _ (derivedPushforwardIdIso X) ≪≫
      (derivedPullback (𝟙 X)).rightUnitor ≪≫ derivedPullbackIdIso X)

/-! ### The base-change map of Stacks 08HY as a mate

The four steps below each unfold exactly one definition.  They are chained in
`derivedBaseChangeMap_eq_mateEquiv_app` and
`derivedBaseChangeMap_eq_derivedBaseChangeSquare_app`; see the implementation notes for why they
are not collapsed into a single `rfl`. -/

section Mates

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

private theorem derivedBaseChangeMap_eq_mate_step₁
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K =
      Mate.derivedBaseChangeMap (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) K :=
  rfl

private theorem derivedBaseChangeMap_eq_mate_step₂
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Mate.derivedBaseChangeMap (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) K =
      (Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)).app K :=
  rfl

private theorem derivedBaseChangeMap_eq_mate_step₃ :
    Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) =
      mateEquiv (derivedAdjunction f) (derivedAdjunction f')
        (Mate.derivedPullbackSquare (derivedPullbackCompIsoLeft g' f' f g sq)
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)) :=
  rfl

private theorem derivedBaseChangeSquare_eq_mate_step₀ :
    derivedBaseChangeSquare g' f' f g sq =
      Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f) :=
  rfl

/-- **The derived base-change map of Stacks 08HY is a mate**, written out: it is the mate, under
the two derived adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, of the two-square comparing
the two iterated derived pullbacks around the square, evaluated at `K`.  This is the definition
of the map, recorded as an equation so that a consumer may feed it to
`isIso_mateEquiv_app_of_isIso_counit` without the kernel having to reduce the definition. -/
theorem derivedBaseChangeMap_eq_mateEquiv_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K =
      (mateEquiv (derivedAdjunction f) (derivedAdjunction f')
        (Mate.derivedPullbackSquare (derivedPullbackCompIsoLeft g' f' f g sq)
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f))).app K :=
  ((derivedBaseChangeMap_eq_mate_step₁ g' f' f g sq K).trans
      (derivedBaseChangeMap_eq_mate_step₂ g' f' f g sq K)).trans
    (congrArg (fun α : TwoSquare _ _ _ _ => α.app K)
      (derivedBaseChangeMap_eq_mate_step₃ g' f' f g sq))

/-- **The derived base-change map is a component of the derived base-change two-square.**  This
is the form in which the map is handed to the invertibility transports of the next section, which
are statements about a natural transformation `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` rather than about one
of its components. -/
theorem derivedBaseChangeMap_eq_derivedBaseChangeSquare_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K = (derivedBaseChangeSquare g' f' f g sq).app K :=
  ((derivedBaseChangeMap_eq_mate_step₁ g' f' f g sq K).trans
      (derivedBaseChangeMap_eq_mate_step₂ g' f' f g sq K)).trans
    (congrArg (fun α : TwoSquare _ _ _ _ => α.app K)
      (derivedBaseChangeSquare_eq_mate_step₀ g' f' f g sq)).symm

end Mates

/-! ### The localization step of Stacks 0DJ9 -/

/-- **Base change along an open immersion, for ringed spaces.**  On a Cartesian square of ringed
spaces

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

whose horizontal arrows `g` and `g'` are open immersions, the canonical derived base-change map of
Stacks 08HY is an isomorphism, for every object of the unbounded derived category of
`𝒪_X`-modules.  No quasi-compactness, quasi-separatedness or quasi-coherence hypothesis is used.

The base-change map is the mate of the comparison of the two iterated derived pullbacks, which is
invertible because both composites are derived pullback along the common composite of the square;
the two derived adjunctions of the open immersions have invertible counits by
`isIso_derivedAdjunction_counit_of_isOpenImmersion`; and the square of right adjoints commutes by
Stacks 08FE.  So `isIso_mateEquiv_app_of_isIso_counit` applies.

This is the step of Stacks 0DJ9 that reduces the statement to an affine base.  It does not carry
the tag 0DJ9, which is about a quasi-compact quasi-separated `f` and asks for the chart condition
of Stacks 0DJ8; see the implementation notes. -/
theorem isIso_derivedBaseChangeMap_of_isOpenImmersions {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion g]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (derivedBaseChangeMap g' f' f g sq.w K) := by
  have := isIso_derivedAdjunction_counit_of_isOpenImmersion g
  have := isIso_derivedAdjunction_counit_of_isOpenImmersion g'
  have : IsIso (Mate.derivedPullbackSquare (derivedPullbackCompIsoLeft g' f' f g sq.w)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)) := by
    dsimp only [Mate.derivedPullbackSquare, TwoSquare.mk]
    infer_instance
  rw [derivedBaseChangeMap_eq_mateEquiv_app g' f' f g sq.w K]
  exact isIso_mateEquiv_app_of_isIso_counit (derivedAdjunction f) (derivedAdjunction f')
    (derivedAdjunction g) (derivedAdjunction g') _
    (derivedPushforwardRestrictIsoCanonical f g' g f' sq) K

/-- A Cartesian square of schemes whose bottom arrow is an open immersion stays Cartesian in
ringed spaces: the forgetful functor to locally ringed spaces preserves all fibre products, and
the one to sheafed spaces preserves a fibre product one leg of which is an open immersion. -/
theorem isPullback_toShHom_of_isOpenImmersion {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    IsPullback g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom := by
  have hL : IsPullback g'.toLRSHom f'.toLRSHom f.toLRSHom g.toLRSHom :=
    have : PreservesLimit (cospan f g) Scheme.forgetToLocallyRingedSpace := inferInstance
    sq.map Scheme.forgetToLocallyRingedSpace
  have : PreservesLimit (cospan f.toLRSHom g.toLRSHom) LocallyRingedSpace.forgetToSheafedSpace :=
    LocallyRingedSpace.IsOpenImmersion.forget_preservesPullback_of_right g.toLRSHom f.toLRSHom
  exact hL.map LocallyRingedSpace.forgetToSheafedSpace

/-- **Base change along an open immersion of the base, for schemes.**  For a Cartesian square of
schemes in which `g` is an open immersion, the canonical derived base-change map of Stacks 08HY is
an isomorphism on every object of the unbounded derived category of `𝒪_X`-modules.

The other horizontal arrow `g'` is then an open immersion too, being a base change of `g`, and
the square stays Cartesian in ringed spaces by
`isPullback_toShHom_of_isOpenImmersion`, so `isIso_derivedBaseChangeMap_of_isOpenImmersions`
applies.  This is the form in which the localization step of Stacks 0DJ9 is used: it replaces the
base `S` by an affine open `V ⊆ S` and `S'` by its preimage. -/
theorem isIso_derivedBaseChangeMap_of_isOpenImmersion {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion g] (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom
      (isPullback_toShHom_of_isOpenImmersion g' f' f g sq).w K) :=
  have : AlgebraicGeometry.IsOpenImmersion g' :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion) sq.flip inferInstance
  isIso_derivedBaseChangeMap_of_isOpenImmersions _ _ _ _
    (isPullback_toShHom_of_isOpenImmersion g' f' f g sq) K

end Localization

/-! ### The induction of Stacks 08DR, reindexed so that every cover is a cover of a whole space

The induction principle of Stacks 08DR is indexed by the opens of one scheme, while the relative
Mayer–Vietoris triangle of Stacks 08HZ is formed for a cover `U ⊔ V = ⊤` of the *whole* space it
lives over.  The two are reconciled below by indexing the property not by an open of `Y` but by an
arbitrary quasi-compact quasi-separated scheme carrying an open immersion onto that open: at every
stage of the induction the cover is then a cover of the whole source, and Stacks 08HZ applies as it
stands.  This is why no restatement of Stacks 08HZ over an open subspace is needed. -/

section CoverInduction

/-- **The induction of Stacks 08DR in the shape the cover step of Stacks 0DJ9 consumes.**  Let `Y`
be a quasi-compact quasi-separated scheme and let `P` be a property of the schemes carrying a
morphism to `Y`.  If `P Z jZ` holds whenever `Z` is affine and `jZ` an open immersion, and `P Z jZ`
follows for a quasi-compact quasi-separated `Z` with `jZ` an open immersion from `P` on the two
members of a two-open cover of `Z` and on their intersection, then `P Y (𝟙 Y)` holds.

The property is indexed by a scheme together with an open immersion into `Y` rather than by an
open of `Y`, which is exactly what makes the hypothesis `U ⊔ V = ⊤` of
`Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris` available at every stage
rather than only at the top one.

Stacks 08DR itself, `Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open`,
is what does the work; the content here is the reindexing.  It carries no tag: the source
states 08DR, not this repackaging of it. -/
theorem compact_open_immersion_induction_on {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (P : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop)
    (affine : ∀ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] [IsAffine Z]
      (jZ : Z ⟶ Y) [AlgebraicGeometry.IsOpenImmersion jZ], P Z jZ)
    (cover : ∀ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
      (jZ : Z ⟶ Y) [AlgebraicGeometry.IsOpenImmersion jZ] (U V : Z.Opens), U ⊔ V = ⊤ →
      P U.toScheme (U.ι ≫ jZ) → P V.toScheme (V.ι ≫ jZ) →
      P (U ⊓ V).toScheme ((U ⊓ V).ι ≫ jZ) → P Z jZ) :
    P Y (𝟙 Y) := by
  let property : Y.Opens → Prop := fun O =>
    ∀ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
      (jZ : Z ⟶ Y) [AlgebraicGeometry.IsOpenImmersion jZ], jZ.opensRange = O → P Z jZ
  have htop : property ⊤ := by
    refine Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
      (X := Y) property ?_ ?_ ⊤ isCompact_univ
    · intro O hOaff Z _ _ jZ _ hrange
      have : IsAffine Z := by
        have : IsAffine (⊤ : Z.Opens).toScheme :=
          jZ.isAffineOpen_iff_of_isOpenImmersion.mp
            (by rwa [Scheme.Hom.image_top_eq_opensRange, hrange])
        exact IsAffine.of_isIso Z.topIso.inv
      exact affine Z jZ
    · intro O V hO hVaff hPO hPV hPOV Z _ _ jZ _ hrange
      set first : Z.Opens := jZ ⁻¹ᵁ O with hfirst
      set second : Z.Opens := jZ ⁻¹ᵁ (V : Y.Opens) with hsecond
      have himg₁ : jZ ''ᵁ first = O := by
        simp [hfirst, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
      have himg₂ : jZ ''ᵁ second = (V : Y.Opens) := by
        simp [hsecond, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
      have hc₁ : IsCompact (first : Set Z) := by
        apply jZ.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
        simpa only [← Scheme.Hom.coe_image, himg₁] using hO
      have hc₂ : IsCompact (second : Set Z) := by
        apply jZ.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
        simpa only [← Scheme.Hom.coe_image, himg₂] using hVaff.isCompact
      have hc₁₂ : IsCompact ((first ⊓ second : Z.Opens) : Set Z) :=
        QuasiSeparatedSpace.inter_isCompact _ _ first.isOpen hc₁ second.isOpen hc₂
      have hcov : first ⊔ second = ⊤ := by
        rw [hfirst, hsecond, ← Scheme.Hom.preimage_sup, ← hrange]
        ext z
        simp [Scheme.Hom.opensRange]
      have : CompactSpace first.toScheme := isCompact_iff_compactSpace.mp hc₁
      have : QuasiSeparatedSpace first.toScheme := quasiSeparatedSpace_of_quasiSeparated first.ι
      have : CompactSpace second.toScheme := isCompact_iff_compactSpace.mp hc₂
      have : QuasiSeparatedSpace second.toScheme := quasiSeparatedSpace_of_quasiSeparated second.ι
      have : CompactSpace (first ⊓ second).toScheme := isCompact_iff_compactSpace.mp hc₁₂
      have : QuasiSeparatedSpace (first ⊓ second).toScheme :=
        quasiSeparatedSpace_of_quasiSeparated (first ⊓ second).ι
      refine cover Z jZ first second hcov ?_ ?_ ?_
      · exact hPO _ (first.ι ≫ jZ) (by simpa [Scheme.Hom.opensRange_comp] using himg₁)
      · exact hPV _ (second.ι ≫ jZ) (by simpa [Scheme.Hom.opensRange_comp] using himg₂)
      · refine hPOV _ ((first ⊓ second).ι ≫ jZ) ?_
        rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
        change jZ ''ᵁ (jZ ⁻¹ᵁ (O ⊓ (V : Y.Opens))) = O ⊓ (V : Y.Opens)
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
        exact inf_eq_right.mpr (inf_le_left.trans le_sup_left)
  exact htop Y (𝟙 Y) (by simp [Scheme.Hom.opensRange_of_isIso])

end CoverInduction

/-! ### The relative Mayer–Vietoris triangle at the canonical derived pushforwards -/

section MayerVietoris

open CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.RelativeMayerVietoris

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens X)

/-- **Restriction to an open followed by pushforward has an everywhere-defined right derived
functor**, by K-injective resolutions; this is Stacks 070K applied to
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforward`. -/
theorem restrictedPushforward_hasRightDerivedFunctor :
    (homotopyToDerived (restrictedPushforward f U)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :=
  hasRightDerivedFunctor_of_exists_kInjective _

attribute [local instance] restrictedPushforward_hasRightDerivedFunctor

/-- **The chosen derived pushforward of the restriction of `f` to an open `U` of its source**,
`R(f|_U)_* ∘ (-)|_U : D(𝒪_X) ⥤ D(𝒪_Y)`: the total right derived functor of
`Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforward`.  Taking it rather than an
arbitrary choice is what makes the Mayer–Vietoris triangle below a formula in `f`, `U` and `V`
alone, and hence makes the triangles of two different morphisms comparable. -/
abbrev openDerivedPushforward :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (homotopyToDerived (restrictedPushforward f U)).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))

/-- The canonical comparison exhibiting `openDerivedPushforward` as a right derived functor of
restriction followed by pushforward. -/
abbrev openDerivedPushforwardUnit :
    homotopyToDerived (restrictedPushforward f U) ⟶
      DerivedCategory.Qh ⋙ openDerivedPushforward f U :=
  (homotopyToDerived (restrictedPushforward f U)).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))

/-- **The relative Mayer–Vietoris triangle of Stacks 08HZ at the canonical choices.**  For a
morphism of ringed spaces and a cover of its source by two opens, the chosen derived pushforward
and the three chosen restricted derived pushforwards of `openDerivedPushforward` fit into a
distinguished triangle, naturally in the object of the unbounded derived category.

This is `Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris`, whose four
derived functors are arbitrary, instantiated at the canonical ones.  Carrying no tag of its own,
it is Stacks 08HZ read at the choices the cover step of Stacks 0DJ9 needs.

*What it does not supply.*  The five natural transformations are produced by an existential with
no characterization attached, exactly as in Stacks 08HZ above.  So this statement says that *some*
triangle exists on the canonical vertices, not that the canonical restriction maps are its legs;
relating the triangle of `f` to the triangle of a base change of `f`, which is what the cover step
of Stacks 0DJ9 does, needs the legs pinned down by the universal property of the right derived
functor, and that is not available from the existential. See the implementation notes. -/
theorem exists_canonicalRelativeMayerVietorisTriangle (V : Opens X) (hUV : U ⊔ V = ⊤) :
    ∃ (rU : derivedPushforward f ⟶ openDerivedPushforward f U)
      (rV : derivedPushforward f ⟶ openDerivedPushforward f V)
      (dU : openDerivedPushforward f U ⟶ openDerivedPushforward f (U ⊓ V))
      (dV : openDerivedPushforward f V ⟶ openDerivedPushforward f (U ⊓ V))
      (δ : openDerivedPushforward f (U ⊓ V) ⟶ derivedPushforward f ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (1 : ℤ)),
      ∀ E, Triangle.mk (biprod.lift (rU.app E) (rV.app E))
        (biprod.desc (dU.app E) (dV.app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  unboundedRelativeMayerVietoris f U V hUV (derivedPushforward f)
    (openDerivedPushforward f U) (openDerivedPushforward f V) (openDerivedPushforward f (U ⊓ V))
    (derivedPushforwardUnit f) (openDerivedPushforwardUnit f U) (openDerivedPushforwardUnit f V)
    (openDerivedPushforwardUnit f (U ⊓ V))

end MayerVietoris

/-! ### Transporting invertibility of the base-change map along a distinguished triangle

This is the two-out-of-three step the cover induction is run with: it reduces invertibility of the
base-change map at one vertex of a distinguished triangle to invertibility at the other two.  It
is obtained without any shift compatibility of the base-change map itself; see the implementation
notes. -/

section Transport

open CategoryTheory.Pretriangulated
open Stacks.CategoryTheory.ComponentwiseInvertibility (isIso_app_middle_of_all_shifts)

attribute [local instance] derivedPushforwardCommShift derivedPushforward_isTriangulated

/-- The source of the derived base-change two-square, `Rf_* ⋙ Lg^*`, commutes with the shift.
Recorded as a named declaration rather than left to instance search at the point of use, so that
the kernel checks it once, here. -/
@[instance_reducible]
def derivedBaseChangeSourceCommShift {X S' S : RingedSpace.{u, u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (derivedPushforward f ⋙ derivedPullback g).CommShift ℤ :=
  inferInstance

/-- The source of the derived base-change two-square is exact. -/
theorem derivedBaseChangeSource_isTriangulated {X S' S : RingedSpace.{u, u}} (f : X ⟶ S)
    (g : S' ⟶ S) :
    letI := derivedBaseChangeSourceCommShift f g
    (derivedPushforward f ⋙ derivedPullback g).IsTriangulated :=
  let := derivedBaseChangeSourceCommShift f g
  inferInstance

/-- The target of the derived base-change two-square, `Lg'^* ⋙ Rf'_*`, commutes with the shift. -/
@[instance_reducible]
def derivedBaseChangeTargetCommShift {X' X S' : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') : (derivedPullback g' ⋙ derivedPushforward f').CommShift ℤ :=
  inferInstance

/-- The target of the derived base-change two-square is exact. -/
theorem derivedBaseChangeTarget_isTriangulated {X' X S' : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') :
    letI := derivedBaseChangeTargetCommShift g' f'
    (derivedPullback g' ⋙ derivedPushforward f').IsTriangulated :=
  let := derivedBaseChangeTargetCommShift g' f'
  inferInstance

attribute [local instance] derivedBaseChangeSourceCommShift derivedBaseChangeSource_isTriangulated
  derivedBaseChangeTargetCommShift derivedBaseChangeTarget_isTriangulated

/-- **Invertibility at the first vertex of a distinguished triangle.**  A natural transformation
between exact functors which is invertible at every shift of the second and third vertices of a
distinguished triangle is invertible at every shift of the first.

This is `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts` applied
to the inverse rotation of the triangle, whose middle vertex is the first vertex of the original.
Like that result it asks for no compatibility of the transformation with the shift, which is why
it applies to the derived base-change map; it pays for that with hypotheses at all shifts rather
than only at the shift by one.

The shift and exactness data of the two functors are explicit arguments rather than instances,
following `Stacks.Cohomology.StrictlyPerfectInvertibility.isIso_app_of_isStrictlyPerfect`: the
derived pushforward carries them as a `def` and a `theorem`, not as instances. -/
theorem isIso_app_first_of_all_shifts {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated)
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)) :=
  let := hFs
  let := hGs
  let := hFt
  let := hGt
  isIso_app_middle_of_all_shifts F G α T.invRotate (inv_rot_of_distTriang T hT)
    (fun m => (α.isIso_app_iff_of_iso ((shiftFunctorAdd C (-1) m).app T.obj₃)).1 (h₃ (-1 + m)))
    h₂

/-- **Invertibility at a binary biproduct.**  A natural transformation between additive functors
which is invertible at two objects is invertible at their biproduct.

Only additivity is used, through `CategoryTheory.Limits.biprod.total`: the inverse is written down
as the sum of the two conjugated inverses.  No instance saying that the functors preserve binary
biproducts is needed — Mathlib does not derive one from additivity, and
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_biproduct` asks for it. -/
theorem isIso_app_of_biprod {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (A B : C)
    [HasBinaryBiproduct A B] (hA : IsIso (α.app A)) (hB : IsIso (α.app B)) :
    IsIso (α.app (A ⊞ B)) := by
  have := hA
  have := hB
  have h₁ : α.app (A ⊞ B) ≫ G.map biprod.fst = F.map biprod.fst ≫ α.app A :=
    (α.naturality biprod.fst).symm
  have h₂ : α.app (A ⊞ B) ≫ G.map biprod.snd = F.map biprod.snd ≫ α.app B :=
    (α.naturality biprod.snd).symm
  have h₃ : F.map biprod.inl ≫ α.app (A ⊞ B) = α.app A ≫ G.map biprod.inl :=
    α.naturality biprod.inl
  have h₄ : F.map biprod.inr ≫ α.app (A ⊞ B) = α.app B ≫ G.map biprod.inr :=
    α.naturality biprod.inr
  refine ⟨G.map biprod.fst ≫ inv (α.app A) ≫ F.map biprod.inl +
    G.map biprod.snd ≫ inv (α.app B) ≫ F.map biprod.inr, ?_, ?_⟩
  · rw [Preadditive.comp_add]
    simp only [← Category.assoc, h₁, h₂]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  · rw [Preadditive.add_comp]
    simp only [Category.assoc, h₃, h₄, IsIso.inv_hom_id_assoc]
    rw [← G.map_comp, ← G.map_comp, ← G.map_add, biprod.total, G.map_id]

/-- `isIso_app_of_biprod` at a shift of a binary biproduct: whiskering by the shift functor, which
is additive, presents the shift of the biproduct as the biproduct seen by a different pair of
additive functors. -/
theorem isIso_app_shift_biprod {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (A B : C) [HasBinaryBiproduct A B]
    (n : ℤ) (hA : IsIso (α.app (A⟦n⟧))) (hB : IsIso (α.app (B⟦n⟧))) :
    IsIso (α.app ((A ⊞ B)⟦n⟧)) :=
  isIso_app_of_biprod (Functor.whiskerLeft (shiftFunctor C n) α) A B hA hB

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The derived base-change two-square of Stacks 08HY as a plain natural transformation**
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`.  This is `derivedBaseChangeSquare` with its `TwoSquare` wrapper
removed, by a type ascription; it exists so that the transports below can be stated for a named
constant.  Handing `derivedBaseChangeSquare` itself to them instead exceeds the kernel's reduction
budget — see the implementation notes. -/
def derivedBaseChangeNatTrans :
    (derivedPushforward f ⋙ derivedPullback g) ⟶
      (derivedPullback g' ⋙ derivedPushforward f') :=
  derivedBaseChangeSquare g' f' f g sq

/-- The components of `derivedBaseChangeNatTrans` are the derived base-change maps of
Stacks 08HY. -/
theorem derivedBaseChangeNatTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedBaseChangeNatTrans g' f' f g sq).app K = derivedBaseChangeMap g' f' f g sq K :=
  rfl

/-- `derivedBaseChangeNatTrans_app` read as an equivalence of invertibility statements, which is
the form in which the transports below are consumed. -/
theorem isIso_derivedBaseChangeNatTrans_app_iff
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app K) ↔
      IsIso (derivedBaseChangeMap g' f' f g sq K) :=
  iff_of_eq (congrArg IsIso (derivedBaseChangeNatTrans_app g' f' f g sq K))

private theorem isIso_app_first_of_all_shifts_derived
    (α : (derivedPushforward f ⋙ derivedPullback g) ⟶
      (derivedPullback g' ⋙ derivedPushforward f'))
    (T : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (hT : T ∈ distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)) :=
  isIso_app_first_of_all_shifts _ _ (derivedBaseChangeSourceCommShift f g)
    (derivedBaseChangeTargetCommShift g' f') (derivedBaseChangeSource_isTriangulated f g)
    (derivedBaseChangeTarget_isTriangulated g' f') α T hT h₂ h₃

/-- **The two-out-of-three step of Stacks 0DJ9.**  For a commutative square of ringed spaces and a
distinguished triangle in `D(𝒪_X)`, if the derived base-change map of Stacks 08HY is invertible at
every shift of the second and third vertices then it is invertible at every shift of the first.

This is what the cover step of the induction of Stacks 08DR consumes: the Mayer–Vietoris triangle
of `Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris` has the complex at its
first vertex, the two members of the cover at its second and their intersection at its third, so
the conclusion over an open follows from the conclusion over two smaller opens and their
intersection.

Stated for `derivedBaseChangeNatTrans`; `isIso_derivedBaseChangeNatTrans_app_iff` turns each
hypothesis and the conclusion into a statement about `derivedBaseChangeMap`. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_distTriang
    (T : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (hT : T ∈ distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (h₂ : ∀ n : ℤ, IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app (T.obj₃⟦n⟧))) :
    ∀ n : ℤ, IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app (T.obj₁⟦n⟧)) :=
  isIso_app_first_of_all_shifts_derived g' f' f g (derivedBaseChangeNatTrans g' f' f g sq) T hT
    h₂ h₃

/-- **The base-change map at the middle vertex of a Mayer–Vietoris triangle.**  The second vertex
of the triangle of `Stacks.Cohomology.RelativeMayerVietoris.unboundedRelativeMayerVietoris` is a
binary biproduct, so invertibility of the base-change map there follows from invertibility at the
two summands, by `isIso_app_shift_biprod`. -/
theorem isIso_derivedBaseChangeNatTrans_app_shift_biprod
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ)
    (hA : IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app (A⟦n⟧)))
    (hB : IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app (B⟦n⟧))) :
    IsIso ((derivedBaseChangeNatTrans g' f' f g sq).app ((A ⊞ B)⟦n⟧)) :=
  isIso_app_shift_biprod (derivedBaseChangeNatTrans g' f' f g sq) A B n hA hB

end Transport

end Stacks.Cohomology.DerivedBaseChange

end
