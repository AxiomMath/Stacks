module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Triangulated.LeftDerivedOfInverting
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# `La^*` as an equivalence onto the cartesian bounded below derived category of modules

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it, let `K` be a hypercovering of `C` and let `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the
ringed augmentation of Stacks 0D9W, with `O = a⁻¹O_C`. Let `𝒜 ⊂ Mod(O)` be the cartesian
`O`-modules. Stacks 0DA2 asserts that

`La^* : D⁺(O_C) ⟶ D⁺_𝒜(O)`

is an equivalence of categories, with quasi-inverse `R a_*`.

The proof is the one of Stacks 0D7U, carried out here for the adjunction `La^* ⊣ R a_*` of
sheaves of modules along a morphism of ringed topoi with invertible structure map: the two
derived functors restrict to the bounded below subcategories, the restricted adjunction has both
adjoints fully faithful by Stacks 0D7Q and 0D7R, and an adjunction whose two adjoints are fully
faithful is an equivalence. This is the module counterpart of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringBoundedBelowEquivalence.lean`, which
does the same for the abelian-sheaf adjunction and is this library's Stacks 0D8I.

**The library's own Stacks 0D7U cannot be used instead.**
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalence` is stated for an
`AlgebraicGeometry.RingedToposSiteHom` — a morphism of ringed topoi presented by a *continuous
functor* `u : Y.C ⥤ X.C` between the underlying sites, together with the hypothesis that `u` is
a morphism of sites. The augmentation of a hypercovering admits no such presentation: it is given
by a cocontinuous functor `(C/K)_total ⥤ C` out of the total site, and there is no functor
`C ⥤ (C/K)_total` in the other direction. So its hypotheses are not even expressible for `a`,
and the argument is redone here for the abstract `AlgebraicGeometry.RingedToposHom` that the
ringed augmentation of Stacks 0D9D is.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedPullbackObjIso`: the derived pullback is the functor
  induced on derived categories by the exact degreewise pullback, so `La^*` of a complex is
  computed degreewise.
* `AlgebraicGeometry.RingedToposHom.derivedPullbackHomologyObjIso` and
  `.derivedPullbackSingleFunctorObjIso`: consequently `H^q(La^*E) = a^*H^q(E)`, and `La^*` of a
  module placed in degree zero is `a^*` of it placed in degree zero.
* `AlgebraicGeometry.RingedToposHom.derivedPullbackEquivalenceOfProperty`: **the equivalence
  `D⁺(O_D) ≌ D⁺_𝒫(O_C)`** for a morphism of ringed topoi with invertible structure map and a
  class `𝒫` of sheaves of modules containing the pullbacks, granted that the unit is invertible
  on `D⁺(O_D)` and the counit on `D⁺_𝒫(O_C)`.
* `Stacks.CategoryTheory.Hypercovering.derivedPullbackEquivalenceOfHypercovering`:
  the same for the ringed augmentation of a hypercovering and the cartesian `O`-modules, which is
  **Stacks 0DA2**, together with `.derivedPullbackEquivalenceOfHypercovering_functor` and
  `..._inverse` identifying its two functors with the restrictions of `La^*` and of `R a_*`.

## Main results

* `AlgebraicGeometry.RingedToposHom.isTriangulated_derivedPullback` and
  `.isTriangulated_derivedPushforward`: both derived functors are exact functors of triangulated
  categories. `La^*` because a total left derived functor of a triangulated functor which inverts
  the quasi-isomorphisms is triangulated, and `R a_*` because it is the right adjoint of one.
* `AlgebraicGeometry.RingedToposHom.isGE_derivedPullback_obj`, `.isLE_derivedPullback_obj` and
  `.isGE_derivedPushforward_obj`: both derived functors preserve boundedness below, and `La^*`
  also boundedness above. The statement about `R a_*` is the orthogonality argument: `D^{≥n}` is
  the right orthogonal of `D^{≤n-1}`, and a morphism from `D^{≤n-1}` into `R a_*E` is adjoint to
  one out of `La^*` of it, which stays in `D^{≤n-1}`.
* `AlgebraicGeometry.RingedToposHom.derivedCategoryBPlus_derivedPushforward_obj` and
  `.derivedCategoryBPlus_derivedPullback_obj`: the two functors restrict to the bounded below
  subcategories. Both are unconditional given that `𝒫` contains the pullbacks, which for the
  cartesian modules is Stacks 0D7H (3).
* `AlgebraicGeometry.RingedToposHom.isIso_derivedCounit_app_of_property`: **the module form of
  Stacks 0D7S for this adjunction** — the counit is invertible at every object of `D⁺_𝒫(O_C)` as
  soon as the unit is invertible on `D(O_D)` and every object of `𝒫` is `a^*` of a sheaf of
  modules on the augmentation site.

## What Stacks 0DA2 still lacks here

`Stacks.CategoryTheory.Hypercovering.derivedPullbackEquivalenceOfHypercovering` carries three
named hypotheses, and says so in its clause string.

* `hunit` and `hacyclic` are the two inputs of this library's Stacks 0DA0, inherited unchanged
  from `Stacks.CategoryTheory.Hypercovering`
  `.isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`: the first is Stacks 0D8E in its
  module form, that the underived unit `M ⟶ a_*a^*M` is an isomorphism, and the second is that
  `a^*` of a K-injective complex computes `R a_*`. See the module docstring of
  `HypercoveringModuleCohomologicalDescent.lean`, in this directory, for why neither is
  available.
* `hsurj` is the remaining clause of Stacks 0D9Z: every cartesian `O`-module on the total site
  lies in the essential image of `a^*`. It is carried in exactly the shape in which
  `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.isCartesianModule_of_mem_essImage`
  carries the converse inclusion, and for the same reason: the development has the essential-image
  inclusion and faithfulness of `a^*` and nothing more.

Nothing else is assumed. In particular the exactness of `a^*`, the exactness of both derived
functors, the restriction of both to the bounded below subcategories, and the propagation of the
counit from `𝒜` to all of `D⁺_𝒜` are proved here.

## Implementation notes

**`𝒜` is not known here to be a weak Serre subcategory.** The source introduces the cartesian
`O`-modules as a weak Serre subcategory of `Mod(O)`, citing Stacks 0D7J part (2). This library
has only part (1) of that tag, for cartesian *abelian sheaves*
(`CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_isWeakSerreClass`); the module half,
which the source proves from flatness of the face morphisms, is absent. That is harmless for the
statement: `D⁺_𝒜(O)` is `DerivedCategoryB.derivedCategoryBPlus` of the class of cartesian
modules, the full subcategory of bounded below objects all of whose cohomology modules are
cartesian, and the equivalence below is about exactly that subcategory. The weak Serre property
is what would make it a *triangulated* subcategory, and no step of the argument needs it — which
is also why the abelian Stacks 0D8I in this library does not use the weak Serre instance it has.
All that is used of `𝒜` is that it is closed under isomorphism, which for cartesian modules is
`CategoryTheory.SimplicialSiteSituation.isCartesianModule_of_iso`.

**`D⁺(O_D)` is `D⁺_{Mod(O_D)}(O_D)`**: the bounded below subcategory attached to the class of
*all* sheaves of modules is cohomological boundedness below and nothing more, which is
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff`. Taking the
class downstairs to be everything is what makes the restriction of `R a_*` unconditional here,
since the only condition left on its image is boundedness below.

**The equivalence is the restricted adjunction**, not an isomorphism assembled by hand, so its
two functors are the restrictions of `La^*` and of `R a_*` on the nose. The propagation of the
counit along the truncation triangles is `CategoryTheory.NatTrans.isIso_app_of_isGE`, the generic
dévissage engine, and the propagation of the unit is not needed at all: this library's
Stacks 0DA0 already gives it on the whole unbounded derived category.

**Exactness of the two derived functors is proved, not assumed.** `La^*` is the total left
derived functor of an exact degreewise pullback, so it commutes with the shift
(`StacksDraft.PseudoCoherence.leftDerivedCommShift`) and is triangulated
(`CategoryTheory.Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts`); `R a_*` then
inherits both from the adjunction. This is the module counterpart of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationDerivedInverseImageTriangulated.lean`.

## References

* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0D8I](https://stacks.math.columbia.edu/tag/0D8I)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedToposHom

section ExactPullback

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]

attribute [local instance] pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  pullbackModules_preservesFiniteColimits_of_adjunction

attribute [local instance] LeftDerivedPullback.isLeftDerivedFunctor

/-! ### The derived pullback is an exact functor -/

/-- **`La^*` commutes with the shift.** It is a total left derived functor, and every total left
derived functor does. -/
instance commShift_derivedPullback :
    (leftDerivedPullbackOfIsIsoFSharp f).functor.CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (leftDerivedPullbackOfIsIsoFSharp f).functor
    (leftDerivedPullbackOfIsIsoFSharp f).comparison (targetQuasiIso Y) ℤ

/-- The canonical comparison from `La^*` to the degreewise pullback is compatible with
`commShift_derivedPullback`. -/
instance natTransCommShift_derivedPullbackComparison :
    NatTrans.CommShift (leftDerivedPullbackOfIsIsoFSharp f).comparison ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift
    (leftDerivedPullbackOfIsIsoFSharp f).functor
    (leftDerivedPullbackOfIsIsoFSharp f).comparison (targetQuasiIso Y) ℤ

/-- **`La^*` is a triangulated functor.** The degreewise pullback is exact, so it inverts the
quasi-isomorphisms, and a total left derived functor of a triangulated functor which inverts the
localizing class is triangulated. -/
instance isTriangulated_derivedPullback :
    (leftDerivedPullbackOfIsIsoFSharp f).functor.IsTriangulated :=
  Functor.isTriangulated_of_isLeftDerivedFunctor_of_inverts
    (leftDerivedPullbackOfIsIsoFSharp f).functor
    (leftDerivedPullbackOfIsIsoFSharp f).comparison (targetQuasiIso Y)
    (fun _ _ s hs => pullbackOnHomotopy_inverts_quasiIso f s hs)

/-- `R a_*` commutes with the shift, being the right adjoint of a functor which does. -/
instance commShift_derivedPushforward :
    (derivedPushforward (X := X) (Y := Y) f).CommShift ℤ :=
  (derivedAdjunctionOfIsIsoFSharp f).rightAdjointCommShift ℤ

/-- The derived adjunction is compatible with the shift. -/
instance commShift_derivedAdjunction :
    (derivedAdjunctionOfIsIsoFSharp f).CommShift ℤ :=
  (derivedAdjunctionOfIsIsoFSharp f).commShift_of_leftAdjoint ℤ

/-- The derived adjunction is an adjunction of triangulated functors, its left adjoint being
triangulated. -/
instance isTriangulated_derivedAdjunction :
    (derivedAdjunctionOfIsIsoFSharp f).IsTriangulated :=
  Adjunction.IsTriangulated.mk' (derivedAdjunctionOfIsIsoFSharp f)

/-- `R a_*` is a triangulated functor, being the right adjoint of one. -/
instance isTriangulated_derivedPushforward :
    (derivedPushforward (X := X) (Y := Y) f).IsTriangulated :=
  (derivedAdjunctionOfIsIsoFSharp f).isTriangulated_rightAdjoint

/-! ### The derived pullback is the degreewise pullback -/

/-- The canonical comparison from the derived pullback to the degreewise one is invertible: `a^*`
is exact, so the degreewise functor already inverts the quasi-isomorphisms. -/
theorem isIso_derivedPullbackComparison :
    IsIso (leftDerivedPullbackOfIsIsoFSharp f).comparison :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (leftDerivedPullbackOfIsIsoFSharp f).functor
    (leftDerivedPullbackOfIsIsoFSharp f).comparison
    (fun _ _ s hs => pullbackOnHomotopy_inverts_quasiIso f s hs)

/-- **`La^*E` is computed degreewise.** The derived pullback agrees with the functor induced on
derived categories by the exact functor `a^*` of sheaves of modules. -/
def derivedPullbackObjIso
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (leftDerivedPullbackOfIsIsoFSharp f).functor.obj M ≅
      (f.toModulesHom.pullbackModules).mapDerivedCategory.obj M :=
  have := isIso_derivedPullbackComparison f
  (leftDerivedPullbackOfIsIsoFSharp f).functor.mapIso
      (DerivedCategory.Qh.objObjPreimageIso M).symm ≪≫
    asIso ((leftDerivedPullbackOfIsIsoFSharp f).comparison.app
      (DerivedCategory.Qh.objPreimage M)) ≪≫
    ((f.toModulesHom.pullbackModules).mapDerivedCategoryFactorsh.app
      (DerivedCategory.Qh.objPreimage M)).symm ≪≫
    (f.toModulesHom.pullbackModules).mapDerivedCategory.mapIso
      (DerivedCategory.Qh.objObjPreimageIso M)

/-- **`H^q(La^*E) = a^*H^q(E)`**: the derived pullback is degreewise, and an exact functor
commutes with the cohomology functors. -/
def derivedPullbackHomologyObjIso
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) (q : ℤ) :
    (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) q).obj
        ((leftDerivedPullbackOfIsIsoFSharp f).functor.obj M) ≅
      (f.toModulesHom.pullbackModules).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) q).obj M) :=
  (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) q).mapIso
      (derivedPullbackObjIso f M) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (f.toModulesHom.pullbackModules) q).app M

/-- **`La^*` of a sheaf of modules placed in degree zero is `a^*` of it, placed in degree
zero.** -/
def derivedPullbackSingleFunctorObjIso
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    (leftDerivedPullbackOfIsIsoFSharp f).functor.obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj N) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((f.toModulesHom.pullbackModules).obj N) :=
  derivedPullbackObjIso f _ ≪≫
    ((f.toModulesHom.pullbackModules).mapDerivedCategorySingleFunctor 0).app N

/-! ### Boundedness -/

/-- The cohomology of the degreewise pullback of `M` vanishes where that of `M` does. -/
private theorem isZero_homologyFunctor_obj_mapDerivedCategory_pullback
    (M : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj M)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((f.toModulesHom.pullbackModules).mapDerivedCategory.obj M)) :=
  ((f.toModulesHom.pullbackModules).map_isZero h).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (f.toModulesHom.pullbackModules) i).app M)

/-- **The derived pullback preserves boundedness below.** It is degreewise, and an exact functor
commutes with the cohomology functors. -/
theorem isGE_derivedPullback_obj
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) (n : ℤ)
    (hM : M.IsGE n) :
    ((leftDerivedPullbackOfIsIsoFSharp f).functor.obj M).IsGE n := by
  have := hM
  have hmap : ((f.toModulesHom.pullbackModules).mapDerivedCategory.obj M).IsGE n := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi ↦ isZero_homologyFunctor_obj_mapDerivedCategory_pullback f M i
      (DerivedCategory.isZero_of_isGE M n i hi)
  exact DerivedCategory.TStructure.t.isGE_of_iso (derivedPullbackObjIso f M).symm n

/-- **The derived pullback preserves boundedness above**, by the same argument. -/
theorem isLE_derivedPullback_obj
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) (n : ℤ)
    (hM : M.IsLE n) :
    ((leftDerivedPullbackOfIsIsoFSharp f).functor.obj M).IsLE n := by
  have := hM
  have hmap : ((f.toModulesHom.pullbackModules).mapDerivedCategory.obj M).IsLE n := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi ↦ isZero_homologyFunctor_obj_mapDerivedCategory_pullback f M i
      (DerivedCategory.isZero_of_isLE M n i hi)
  exact DerivedCategory.TStructure.t.isLE_of_iso (derivedPullbackObjIso f M).symm n

/-- **The derived direct image preserves boundedness below.** `D^{≥n}` is the right orthogonal of
`D^{≤n-1}`, and a morphism from an object `L` of `D^{≤n-1}` into `R a_*E` is adjoint to a morphism
`La^*L ⟶ E` with `La^*L` again in `D^{≤n-1}`, hence zero. -/
theorem isGE_derivedPushforward_obj
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) (n : ℤ)
    (hM : M.IsGE n) :
    ((derivedPushforward (X := X) (Y := Y) f).obj M).IsGE n := by
  have := hM
  change DerivedCategory.TStructure.t.IsGE
    ((derivedPushforward (X := X) (Y := Y) f).obj M) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro L g hL
  have := isLE_derivedPullback_obj f L (n - 1) hL
  have hzero := DerivedCategory.TStructure.t.zero
    (((derivedAdjunctionOfIsIsoFSharp f).homEquiv L M).symm g) (n - 1) n (by omega)
  have hz0 : ((derivedAdjunctionOfIsIsoFSharp f).homEquiv L M).symm 0 = 0 := by
    rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact ((derivedAdjunctionOfIsIsoFSharp f).homEquiv L M).symm.injective
    (hzero.trans hz0.symm)

/-! ### The two functors restrict to the bounded below subcategories -/

variable (P : ObjectProperty (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
  [P.IsClosedUnderIsomorphisms]

/-- `D⁺(O_D)`: the bounded below derived category of sheaves of modules on the target, written as
`D⁺_{Mod(O_D)}(O_D)`, the bounded below subcategory attached to the class of *all* sheaves of
modules, which is how the source reads it. The condition on the cohomology modules is vacuous:
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff`. -/
@[sga "4 Vbis 1.3.8", sga "4½ Rapport 4.1" "D⁺(X"]
abbrev derivedPlusTarget :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :=
  DerivedCategoryB.derivedCategoryBPlus ⊤

/-- `D⁺_𝒫(O_C)`: the bounded below objects of the derived category of sheaves of modules on the
source all of whose cohomology modules lie in `𝒫`. -/
@[sga "4 Vbis 1.3.8" "more general"]
abbrev derivedPlusProperty :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :=
  DerivedCategoryB.derivedCategoryBPlus P

/-- **`R a_*` carries `D⁺_𝒫(O_C)` into `D⁺(O_D)`.** Only boundedness below is at stake, the class
downstairs being all of `Mod(O_D)`. -/
theorem derivedCategoryBPlus_derivedPushforward_obj
    (M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
    (hM : DerivedCategoryB.IsBoundedBelow M) :
    derivedPlusTarget (Y := Y) ((derivedPushforward (X := X) (Y := Y) f).obj M) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE M).1 hM
  exact (CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff _).2
    ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
      ⟨n, isGE_derivedPushforward_obj f M n hGE⟩)

/-- **`La^*` carries `D⁺(O_D)` into `D⁺_𝒫(O_C)`.** It preserves boundedness below, and its
cohomology modules are `a^*` of those of its argument, which lie in `𝒫` by hypothesis. -/
theorem derivedCategoryBPlus_derivedPullback_obj
    (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hM : DerivedCategoryB.IsBoundedBelow M) :
    derivedPlusProperty P ((leftDerivedPullbackOfIsIsoFSharp f).functor.obj M) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE M).1 hM
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨n, isGE_derivedPullback_obj f M n hGE⟩, fun q ↦ ?_⟩
  exact ObjectProperty.prop_of_iso (P := P) (derivedPullbackHomologyObjIso f M q).symm (hP _)

/-! ### The counit on the bounded below derived category of `𝒫` -/

omit [P.IsClosedUnderIsomorphisms] in
/-- **The counit is invertible at an object of `𝒫` placed in degree zero**, granted that the
derived unit is invertible and that every object of `𝒫` is `a^*` of a sheaf of modules on the
target. Writing `M = a^*N`, the module `M` in degree zero is `La^*` of `N` in degree zero, and the
counit at `La^*` of an object at which the unit is invertible is invertible. -/
theorem isIso_derivedCounit_app_singleFunctor_obj
    (hunit : ∀ M, IsIso ((derivedAdjunctionOfIsIsoFSharp f).unit.app M))
    (hsurj : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), P M →
      (f.toModulesHom.pullbackModules).essImage M)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : P M) :
    IsIso ((derivedAdjunctionOfIsIsoFSharp f).counit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).obj M)) := by
  obtain ⟨N, ⟨e⟩⟩ := hsurj M hM
  have eL := derivedPullbackSingleFunctorObjIso f N ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).mapIso e
  exact (NatTrans.isIso_app_iff_of_iso
    (derivedAdjunctionOfIsIsoFSharp f).counit eL).mp
      (Adjunction.isIso_counit_app_obj_of_isIso_unit_app
        (derivedAdjunctionOfIsIsoFSharp f) _ (hunit _))

omit [P.IsClosedUnderIsomorphisms] in
/-- **The module form of Stacks 0D7S for the derived augmentation adjunction.** The counit
`La^*R a_*E ⟶ E` is invertible at every object `E` of `D⁺_𝒫(O_C)`, granted the same two inputs:
the cohomology modules of `E` lie in `𝒫`, so the counit is invertible on each of them placed in
degree zero, and the dévissage along the truncation triangles propagates that to `E` itself. Both
`La^* ⋙ R a_*` and the identity are exact, commute with the shift and preserve boundedness
below. -/
theorem isIso_derivedCounit_app_of_property
    (hunit : ∀ M, IsIso ((derivedAdjunctionOfIsIsoFSharp f).unit.app M))
    (hsurj : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), P M →
      (f.toModulesHom.pullbackModules).essImage M)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : derivedPlusProperty P E) :
    IsIso ((derivedAdjunctionOfIsIsoFSharp f).counit.app E) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE E).1 hE.1
  exact NatTrans.isIso_app_of_isGE (derivedAdjunctionOfIsIsoFSharp f).counit
    (fun L m h ↦ isGE_derivedPullback_obj f _ m (isGE_derivedPushforward_obj f L m h))
    (fun _ _ h ↦ h) E n hGE
    (fun q ↦ isIso_derivedCounit_app_singleFunctor_obj f P hunit hsurj _ (hE.2 q))

/-! ### The equivalence -/

/-- **`La^*` restricted to `D⁺(O_D) ⥤ D⁺_𝒫(O_C)`**, the forward functor of the equivalence. -/
abbrev derivedPullbackPlus (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N)) :
    (derivedPlusTarget (Y := Y)).FullSubcategory ⥤ (derivedPlusProperty P).FullSubcategory :=
  (derivedPlusProperty P).lift
    ((derivedPlusTarget (Y := Y)).ι ⋙ (leftDerivedPullbackOfIsIsoFSharp f).functor)
    (fun M ↦ derivedCategoryBPlus_derivedPullback_obj f P hP M.obj
      ((CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff
        M.obj).1 M.property))

/-- **`R a_*` restricted to `D⁺_𝒫(O_C) ⥤ D⁺(O_D)`**, the quasi-inverse of the equivalence. -/
abbrev derivedPushforwardPlus :
    (derivedPlusProperty P).FullSubcategory ⥤ (derivedPlusTarget (Y := Y)).FullSubcategory :=
  (derivedPlusTarget (Y := Y)).lift
    ((derivedPlusProperty P).ι ⋙ derivedPushforward (X := X) (Y := Y) f)
    (fun M ↦ derivedCategoryBPlus_derivedPushforward_obj f M.obj M.property.1)

/-- The restriction of the derived adjunction `La^* ⊣ R a_*` to the bounded below
subcategories. -/
def derivedAdjunctionBoundedBelow (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N)) :
    derivedPullbackPlus f P hP ⊣ derivedPushforwardPlus f P :=
  (derivedAdjunctionOfIsIsoFSharp f).restrictFullyFaithful
    (derivedPlusTarget (Y := Y)).fullyFaithfulι
    (derivedPlusProperty P).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- **`La^*` is an equivalence `D⁺(O_D) ≌ D⁺_𝒫(O_C)` with quasi-inverse `R a_*`**, for a morphism
of ringed topoi with invertible structure map, granted that the unit is invertible on `D⁺(O_D)`
and the counit on `D⁺_𝒫(O_C)`.

The restricted left adjoint is fully faithful because `D⁺(O_D)` lies in the subcategory of
Stacks 0D7Q where the unit is invertible, the restricted right adjoint because `D⁺_𝒫(O_C)` lies
in the subcategory of Stacks 0D7R where the counit is invertible; an adjunction whose two adjoints
are fully faithful is an equivalence. -/
def derivedPullbackEquivalenceOfProperty (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (hunitPlus : derivedPlusTarget (Y := Y) ≤ (derivedAdjunctionOfIsIsoFSharp f).unitIsIso)
    (hcounitPlus : derivedPlusProperty P ≤ (derivedAdjunctionOfIsIsoFSharp f).counitIsIso) :
    (derivedPlusTarget (Y := Y)).FullSubcategory ≌
      (derivedPlusProperty P).FullSubcategory :=
  letI hL := (derivedAdjunctionOfIsIsoFSharp f).fullyFaithfulιCompLeftAdjointOfLE hunitPlus
  letI hR := (derivedAdjunctionOfIsIsoFSharp f).fullyFaithfulιCompRightAdjointOfLE hcounitPlus
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (derivedAdjunctionBoundedBelow f P hP).toEquivalence

/-- **The forward functor of the equivalence is `La^*`.** -/
theorem derivedPullbackEquivalenceOfProperty_functor (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (hunitPlus : derivedPlusTarget (Y := Y) ≤ (derivedAdjunctionOfIsIsoFSharp f).unitIsIso)
    (hcounitPlus : derivedPlusProperty P ≤ (derivedAdjunctionOfIsIsoFSharp f).counitIsIso) :
    (derivedPullbackEquivalenceOfProperty f P hP hunitPlus hcounitPlus).functor =
      derivedPullbackPlus f P hP :=
  rfl

/-- **The quasi-inverse of the equivalence is `R a_*`.** -/
theorem derivedPullbackEquivalenceOfProperty_inverse (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (hunitPlus : derivedPlusTarget (Y := Y) ≤ (derivedAdjunctionOfIsIsoFSharp f).unitIsIso)
    (hcounitPlus : derivedPlusProperty P ≤ (derivedAdjunctionOfIsIsoFSharp f).counitIsIso) :
    (derivedPullbackEquivalenceOfProperty f P hP hunitPlus hcounitPlus).inverse =
      derivedPushforwardPlus f P :=
  rfl

end ExactPullback

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian sheaves on the total site are sheafifiable at the site universe. -/
local instance hasWeakSheafifyTotalBoundedBelow (S : SimplicialSiteSituation.{u}) :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  objectModuleDescentHasWeakSheafifyTotal S

/-- On the total site at the site universe, the maps inverted by sheafification of abelian sheaves
are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalBoundedBelow (S : SimplicialSiteSituation.{u}) :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  objectModuleDescentWEqualsLocallyBijectiveTotal S

/-- **The cartesian `O`-modules are closed under isomorphism**, which is
`CategoryTheory.SimplicialSiteSituation.isCartesianModule_of_iso` read as an instance. It is all
that the equivalence of Stacks 0DA2 uses of the class `𝒜`; the weak Serre property of
Stacks 0D7J (2) is not needed and is not available here. -/
instance isClosedUnderIsomorphisms_isModuleFiberTransitionIso (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (S.IsModuleFiberTransitionIso O) where
  of_iso e h := isCartesianModule_of_iso S O e h

end CategoryTheory.SimplicialSiteSituation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

/-- The cartesian `O`-modules on the total site of a hypercovering, the weak Serre subcategory
`𝒜 ⊂ Mod(O)` of Stacks 0DA2 — read here only as a class of objects closed under isomorphism, the
module half of Stacks 0D7J being unavailable. -/
abbrev hypercoveringCartesianModules :
    ObjectProperty (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := ((hypercoveringSituation J H).totalRingedTopos
        (hypercoveringRingedAugmentation J H OC).O).J))
      ((hypercoveringSituation J H).totalRingedTopos
        (hypercoveringRingedAugmentation J H OC).O).O)) :=
  (hypercoveringSituation J H).IsModuleFiberTransitionIso
    (hypercoveringRingedAugmentation J H OC).O

/-- The cartesian `O`-modules are closed under isomorphism, in the spelling in which the
equivalence below consumes the class. The general statement is
`CategoryTheory.SimplicialSiteSituation.isClosedUnderIsomorphisms_isModuleFiberTransitionIso`;
it is restated here because the ring sheaf of the total *ringed topos* and the ring sheaf of the
total topology are the same only up to unfolding `totalRingedTopos`, which instance search does
not do. -/
local instance isClosedUnderIsomorphisms_hypercoveringCartesianModules :
    ObjectProperty.IsClosedUnderIsomorphisms (hypercoveringCartesianModules J H OC) where
  of_iso e h := CategoryTheory.SimplicialSiteSituation.isCartesianModule_of_iso _ _ e h

/-- **Stacks 0D7H (3) for the ringed augmentation of a hypercovering**: every pullback `a^*N` of a
sheaf of `O_C`-modules is a cartesian `O`-module. -/
theorem isCartesianModule_pullbackModules_hypercovering
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.J))
      (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.O)) :
    hypercoveringCartesianModules J H OC
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom).obj N) :=
  RingedAugmentation.isCartesianModule_pullbackModules
    (hypercoveringRingedAugmentation J H OC) N

/-- **Stacks 0DA2**, granted the inputs the library does not have. For a site `C` with equalizers
and fibre products, a sheaf of commutative rings `O_C` on it, a hypercovering `K` of `C`, the
ringed augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` of Stacks 0D9W with `O = a⁻¹O_C`,
and the class `𝒜 ⊂ Mod(O)` of cartesian `O`-modules, the derived pullback is an equivalence

`La^* : D⁺(O_C) ⟶ D⁺_𝒜(O)`

with quasi-inverse `R a_*`. Both functors of the equivalence are the restrictions of `La^*` and of
`R a_*` on the nose, since the equivalence is the restricted adjunction.

Three hypotheses are carried. `hunit` and `hacyclic` are the two inputs of this library's
Stacks 0DA0, inherited unchanged from
`isIso_derivedPullbackPushforwardUnit_app_of_hypercovering`: the first is Stacks 0D8E in its
module form, that the underived unit `M ⟶ a_*a^*M` is an isomorphism, and the second is that
`a^*` of a K-injective complex computes `R a_*`. `hsurj` is the remaining clause of
Stacks 0D9Z, that every cartesian `O`-module on the total site lies in the essential image of
`a^*`; the development carries the converse inclusion
(`RingedAugmentation.isCartesianModule_of_mem_essImage`) and faithfulness of `a^*`, and the
degree-zero condition on a hypercovering does not supply the rest. The derived content of
Stacks 0D7U is *not* assumed: see the module docstring.

`𝒜` is read as the class of cartesian `O`-modules, closed under isomorphism; that it is a weak
Serre subcategory, which is Stacks 0D7J (2) and which this library has only for abelian sheaves,
is not used anywhere in the argument. -/
@[stacks 0DA2 "granted the two inputs of this library's Tag 0DA0 -- the module form of Tag 0D8E \
as hunit and the Ra_*-acyclicity of a^* of a K-injective complex as hacyclic -- and granted the \
essential-surjectivity clause of Tag 0D9Z as hsurj. The weak Serre property of the cartesian \
O-modules, Tag 0D7J (2), is not available in this library and is not used: D^+_A(O) is read as \
the bounded below objects whose cohomology modules are cartesian",
  sga "4 Vbis 2.2.7" "special case",
  sga "4 Vbis 2.4.12" "special case"]
def derivedPullbackEquivalenceOfHypercovering
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation J H OC).totalRingedHom)
    (hsurj : ∀ M, hypercoveringCartesianModules J H OC M →
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom).essImage M) :
    (AlgebraicGeometry.RingedToposHom.derivedPlusTarget
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)).FullSubcategory ≌
      (AlgebraicGeometry.RingedToposHom.derivedPlusProperty
        (hypercoveringCartesianModules J H OC)).FullSubcategory :=
  have hall : ∀ M, IsIso ((AlgebraicGeometry.RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (X := (hypercoveringSituation J H).totalRingedTopos
        (hypercoveringRingedAugmentation J H OC).O)
      (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit.app M) :=
    isIso_derivedPullbackPushforwardUnit_app_of_hypercovering J H OC hunit hacyclic
  AlgebraicGeometry.RingedToposHom.derivedPullbackEquivalenceOfProperty
    (X := (hypercoveringSituation J H).totalRingedTopos
      (hypercoveringRingedAugmentation J H OC).O)
    (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
    (hypercoveringRingedAugmentation J H OC).totalRingedHom
    (hypercoveringCartesianModules J H OC)
    (isCartesianModule_pullbackModules_hypercovering J H OC)
    (fun M _ ↦ hall M)
    (fun M hM ↦ AlgebraicGeometry.RingedToposHom.isIso_derivedCounit_app_of_property
      (hypercoveringRingedAugmentation J H OC).totalRingedHom
      (hypercoveringCartesianModules J H OC) hall hsurj M hM)

/-- **Stacks 0DA2, the forward functor of the equivalence is `La^*`:** it is the restriction of
the derived pullback to the bounded below subcategories. -/
@[stacks 0DA2 "the forward functor of the equivalence is La^*, under the three hypotheses of \
`derivedPullbackEquivalenceOfHypercovering`"]
theorem derivedPullbackEquivalenceOfHypercovering_functor
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation J H OC).totalRingedHom)
    (hsurj : ∀ M, hypercoveringCartesianModules J H OC M →
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom).essImage M) :
    (derivedPullbackEquivalenceOfHypercovering J H OC hunit hacyclic hsurj).functor =
      AlgebraicGeometry.RingedToposHom.derivedPullbackPlus
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom
        (hypercoveringCartesianModules J H OC)
        (isCartesianModule_pullbackModules_hypercovering J H OC) :=
  rfl

/-- **Stacks 0DA2, the quasi-inverse of the equivalence is `R a_*`:** it is the restriction of the
derived direct image to the bounded below subcategories. -/
@[stacks 0DA2 "the quasi-inverse of the equivalence is Ra_*, under the three hypotheses of \
`derivedPullbackEquivalenceOfHypercovering`"]
theorem derivedPullbackEquivalenceOfHypercovering_inverse
    (hunit : IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringRingedAugmentation J H OC).totalRingedHom).unit)
    (hacyclic : AlgebraicGeometry.RingedToposHom.PullbackComputesDerivedPushforward.{u}
      (hypercoveringRingedAugmentation J H OC).totalRingedHom)
    (hsurj : ∀ M, hypercoveringCartesianModules J H OC M →
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom).essImage M) :
    (derivedPullbackEquivalenceOfHypercovering J H OC hunit hacyclic hsurj).inverse =
      AlgebraicGeometry.RingedToposHom.derivedPushforwardPlus
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom
        (hypercoveringCartesianModules J H OC) :=
  rfl

end Stacks.CategoryTheory.Hypercovering

end
