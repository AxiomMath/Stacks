module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitDegrees
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula for a perfect complex

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.
This file carries the *localization on the base* half of [Stacks, Tag 0B54] — the step that
reduces the projection formula for a perfect complex on `Y` to the projection formula for a
strictly perfect complex on a member of an open covering of `Y` — and, with it, states and proves
the projection formula for a perfect complex, **whose only hypothesis is that `K` is perfect**,
which is the source's only hypothesis too.

## Main results

* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap`:
  **the transport step.**  On a Cartesian square of ringed spaces whose horizontal arrows are
  open immersions, if the projection-formula morphism of [Stacks, Tag 0B53] is invertible for the
  other vertical arrow at the pulled-back objects, then the derived pullback along the bottom
  arrow of the projection-formula morphism for `f` is invertible.
* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_derivedPullback_obj`:
  the projection-formula morphism upstairs at `Lj_U^*K`, from a strictly perfect model of the
  restriction of a representative of `K` to `U`.
* `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect`:
  **[Stacks, Tag 0B54] for a perfect complex, with no hypothesis beyond perfectness of `K`.**

## The dévissage

The source reduces to `K = 𝒪_Y[n]` in three steps: localize on `Y` until `K` is strictly
perfect, pass from a strictly perfect complex to its finite free terms by stupid truncations
and direct summands, and check the case `𝒪_Y[n]`. The last two steps are
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect`
(in `ProjectionFormulaStrictlyPerfect`), whose base case `K = 𝒪_Y[i]⟦n⟧` for all integers `i`,
`n` is `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_singleUnit_degree`
(in `ProjectionFormulaUnitShifts`, Stacks 08EU in every degree), obtained from the abstract
projection formula at a ⊗-invertible object. This file supplies the first step.

## Route

Three things stood between [Stacks, Tag 0B6B] — the compatibility of the projection-formula
morphism with a commutative square, which
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_derivedBaseChangeMap` proves
with no hypothesis beyond commutativity — and the localization on the base.  Two of them are
proved elsewhere in the library:

* **Invertibility of the derived base-change map at the square.**
  `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions` supplies
  it for a Cartesian square both of whose horizontal arrows are open immersions, with no
  boundedness, flatness or quasi-coherence hypothesis.  It asks for a
  `CategoryTheory.IsPullback`, and the square used below *is* one: `RingedSpace` is
  `AlgebraicGeometry.SheafedSpace CommRingCat`, where
  `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_right` gives the
  fibre product of `f` with an open immersion `j` and
  `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right` makes its
  first projection an open immersion again.  So the genuine categorical pullback of `f` along
  the inclusion of an open subspace of `Y` is available, and nothing has to be deduced from the
  mere commutativity of `AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict`.
* **The identification of the derived pullback along an open immersion with restriction.**
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso` and
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso` are it, the second
  in the `ExtensionByZeroModules.jStar` spelling that the locality statement uses.

The third is
`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedLocality/InvertibilityOnAnOpenCover.lean`:
locality of invertibility in `D(𝒪_Y)` over an *arbitrary* open cover of a ringed space.  The
library had it for a two-open cover only, and privately; the indexed statement existed at the
level of the slice site, where the restriction functor is
`CategoryTheory.SheafOfModules.overFunctor` rather than a functor to modules on an open
subspace.

## Implementation notes

*Why the diagram is consumed through `isIso_of_comp_eq` and `refine`.*  Tag 0B6B is the
commutativity of a square of composites.  Reading `IsIso` off it means knowing that five of the
six arrows are invertible, and each of those five is a component of a natural isomorphism, a
functor applied to one, or a base-change map.  Instance search does not find them: the
comparison of [Stacks, Tag 079U] is the `hom` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, and the tensor bifunctors
are indexed by a *product* category, which carries two `CategoryTheory.Category` instances
(`CategoryTheory.prod` and `CategoryTheory.uniformProd`); a hypothesis stated at one of them is
invisible to a goal stated at the other.  Every such obligation is therefore produced as a
`refine` subgoal — so that the goal itself, with whichever instance Tag 0B6B put there, is what
the witness is checked against — and the invertibility of a `CategoryTheory.Prod.mkHom` is given
by its explicit inverse rather than by a lemma whose statement would fix one of the two
instances.  No transparency option is relaxed and no heartbeat is raised.

*Why the reduction is cut into three declarations.*  Written as one proof it does not elaborate
inside the default heartbeat budget, and raising the budget is not an option here.  The three
pieces are the comparison `derivedPullbackRestrictComplexIso`, the per-cover-member step
`isIso_projectionFormulaMap_derivedPullback_obj`, and the locality wrap-up; each is small, and
naming the intermediate isomorphisms is what stops the elaborator from re-deriving them.

*Why the sheafification instances are re-stated.*  `Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective` are stated at `AddCommGrpCat.{max
u v}`, and as local instances at that shape the universe constraint `max u v =?= u` is left
unsolved — elaboration of the statement below dies on it.  `hasSheafifyOpens` and
`wEqualsLocallyBijectiveOpens` are those two theorems with `v := u`, so that the instance has no
universe metavariable in it.  Both classes are `Prop`s inhabited for every ringed space, so
installing them locally is not a hypothesis on anything.

*Why `asIso` is applied explicitly.*  In `derivedQIsoOfQuasiIso` the invertibility of
`DerivedCategory.Q.map q` is passed as the explicit instance argument of
`CategoryTheory.asIso` rather than put in scope and found by search.  Found by search it is not:
the complex `AlgebraicGeometry.RingedSpace.restrictComplex A U` lives in the
`StrictlyPerfect.structureSheafOfRings` spelling of the modules on the open subspace and the
localization functor is reached through the `structureSheafRing` one, and the
two agree only at default transparency.

## References

* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaPerfect

/-- Sheafification of presheaves of abelian groups on the open-cover site of a ringed space, with
the universe of the values pinned to the universe of the space.

This is `Stacks.AssociatedSheaf.hasModuleSheafify` at `v := u`.  That theorem is stated at
`AddCommGrpCat.{max u v}`, and installed as a local instance in that shape it leaves the
constraint `max u v =?= u` for the elaborator, which does not solve it. -/
theorem hasSheafifyOpens (Z : RingedSpace.{u, u}) :
    HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.hasModuleSheafify.{u, u} Z

/-- Weak equivalences of presheaves of abelian groups on the open-cover site of a ringed space
are the locally bijective maps, with the universe of the values pinned to the universe of the
space.  This is `Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective` at `v := u`; see
`hasSheafifyOpens`. -/
theorem wEqualsLocallyBijectiveOpens (Z : RingedSpace.{u, u}) :
    (Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Z

attribute [local instance] HasDerivedCategory.standard

/-- **Invertibility read off a commuting square of composites.**  If `a ≫ b = c ≫ d` with `a`,
`b` and `d` invertible, then `c` is invertible.

The three invertibility hypotheses are explicit arguments rather than instances: at the shape
this is used, each of them lives in a category of pairs whose `CategoryTheory.Category` instance
is not the one instance search would pick, so they have to be handed over. -/
theorem isIso_of_comp_eq {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y}
    {c : W ⟶ Z} {d : Z ⟶ Y} (hab : a ≫ b = c ≫ d)
    (ha : IsIso a) (hb : IsIso b) (hd : IsIso d) : IsIso c := by
  have hcd : IsIso (c ≫ d) := hab ▸ IsIso.comp_isIso
  exact (isIso_comp_right_iff c d).mp hcd

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The projection-formula morphism of [Stacks, Tag 0B53] is invertible after derived pullback
along an open immersion of the base, as soon as it is invertible upstairs.**

Let

```
          g'
   X' ----------→ X
   |              |
f' |              | f
   v      g       v
   Y' ----------→ Y
```

be a Cartesian square of ringed spaces whose horizontal arrows `g` and `g'` are open immersions,
and let `E ∈ D(𝒪_X)`, `K ∈ D(𝒪_Y)`.  If the projection-formula morphism for `f'` at
`L(g')^*E` and `Lg^*K` is invertible, then `Lg^*` of the projection-formula morphism for `f` at
`E` and `K` is invertible.

This is [Stacks, Tag 0B6B] read for invertibility.  Of the six arrows of that square, five are
invertible here — the two comparisons of [Stacks, Tag 079U] because they are components of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, the two derived base-change
maps by
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`, and the
projection-formula morphism for `f'` by hypothesis — so the sixth, `Lg^*` of the
projection-formula morphism for `f`, is invertible too.

There is no boundedness, flatness, quasi-coherence or perfectness hypothesis on `E` or `K`. -/
@[stacks 08EU "the localization step of the source's proof: for a Cartesian square of ringed \
spaces whose horizontal arrows are open immersions, invertibility of the projection-formula map \
for f' at the restricted complexes implies invertibility of the derived pullback along g of the \
map for f; unconditional in both complexes, but only one implication of the source's reduction \
— the affine case and the passage from an open cover back to the base are not proved"]
theorem isIso_derivedPullback_map_projectionFormulaMap
    [SheafedSpace.IsOpenImmersion g'] [SheafedSpace.IsOpenImmersion g]
    (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : IsIso (projectionFormulaMap f' ((derivedPullback g').obj E)
      ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback g).map (projectionFormulaMap f E K)) := by
  have hbc := Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions
    g' f' f g sq
  have key : _ = _ := projectionFormulaMap_derivedBaseChangeMap g' f' f g sq.w E K
  refine isIso_of_comp_eq key
    ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g).app _).isIso_hom ?_ ?_
  · refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ h
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact ⟨⟨Prod.mkHom (inv (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      g' f' f g sq.w E)) (𝟙 _), by ext <;> simp, by ext <;> simp⟩⟩
  · refine @IsIso.comp_isIso _ _ _ _ _ _ _ (hbc _) ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @IsIso.comp_isIso _ _ _ _ _ _ _
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g').app _).isIso_hom ?_
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    exact ⟨⟨Prod.mkHom (𝟙 _) ((derivedPullbackSquareIso g' f' f g sq.w).hom.app K),
      by ext <;> simp, by ext <;> simp⟩⟩

/-! ### The reduction of a perfect complex to a strictly perfect one -/

section Reduction

attribute [local instance] hasSheafifyOpens wEqualsLocallyBijectiveOpens

attribute [local instance 2000] SheafOfModules.instAbelian

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose

/-- A quasi-isomorphism of cochain complexes of `𝒪_Z`-modules becomes invertible in the derived
category: the localization inverts the class of quasi-isomorphisms. -/
theorem isIso_Q_map_of_quasiIso {Z : RingedSpace.{u, u}}
    {P R : CochainComplex (OXMod.{u, u} Z) ℤ} (q : P ⟶ R) (hq : QuasiIso q) :
    IsIso ((DerivedCategory.Q (C := OXMod.{u, u} Z)).map q) :=
  Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (OXMod.{u, u} Z) (ComplexShape.up ℤ)) q
    ((HomologicalComplex.mem_quasiIso_iff q).2 hq)

/-- A quasi-isomorphism read as an isomorphism of the derived category.

`CategoryTheory.asIso` is applied with its invertibility argument explicit; see the
implementation notes for why instance search does not supply it here. -/
def derivedQIsoOfQuasiIso {Z : RingedSpace.{u, u}}
    {P R : CochainComplex (OXMod.{u, u} Z) ℤ} (q : P ⟶ R) (hq : QuasiIso q) :
    (DerivedCategory.Q (C := OXMod.{u, u} Z)).obj P ≅
      (DerivedCategory.Q (C := OXMod.{u, u} Z)).obj R :=
  @asIso _ _ _ _ _ (isIso_Q_map_of_quasiIso q hq)

/-- **`Lj_U^*(Q A) ≅ Q(A|_U)`**: the derived pullback along the inclusion of an open subspace of
the class of a cochain complex is the class of its restriction.

Both halves are already in the library: the derived pullback along `j_U` is the functor
restriction induces on derived categories, by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`, and that functor
takes the class of a complex to the class of the degreewise image, by
`CategoryTheory.Functor.mapDerivedCategoryFactors`.  This is their composite, named so that the
elaborator meets it once. -/
def derivedPullbackRestrictComplexIso (Y : RingedSpace.{u, u}) (U : Opens Y.carrier)
    (A : CochainComplex (OXMod.{u, u} Y) ℤ) :
    (derivedPullback (Y.ofRestrict U.isOpenEmbedding)).obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex A U) :=
  letI : Abelian (SheafOfModules.{u} (structureSheafRing
      (Stacks.Cohomology.HigherDirectImage.restrictToOpen Y U))) :=
    _root_.SheafOfModules.instAbelian _
  (derivedPullbackModuleRestrictionIso Y U).app _ ≪≫
    (Stacks.Cohomology.HigherDirectImage.moduleRestriction Y U).mapDerivedCategoryFactors.app A

/-- **The per-cover-member step of the reduction.**  Let `U` be an open of `Y`, let `A` be a
cochain complex of `𝒪_Y`-modules whose restriction to `U` receives a quasi-isomorphism `q` from a
strictly perfect complex `P`, and let `f_U : X ×_Y U ⟶ U` be the base change of `f` along the
inclusion of `U`.  Then the projection-formula morphism of [Stacks, Tag 0B53] for `f_U` is
invertible at `Lj_U^*(Q A)`, with no hypothesis.

The dévissage
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect`
gives it at `Q P`, and `q` together with `derivedPullbackRestrictComplexIso` identifies `Q P`
with `Lj_U^*(Q A)`; invertibility is transported along that isomorphism by naturality of the
projection-formula morphism in the second variable, which is
`projectionFormulaTransformation`. -/
theorem isIso_projectionFormulaMap_derivedPullback_obj
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens Y.carrier)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (A : CochainComplex (OXMod.{u, u} Y) ℤ)
    (P : CochainComplex (OXMod.{u, u} (Y.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (q : P ⟶ AlgebraicGeometry.RingedSpace.restrictComplex A U) (hq : QuasiIso q) :
    IsIso (projectionFormulaMap (pullback.snd f (Y.ofRestrict U.isOpenEmbedding))
      ((derivedPullback (pullback.fst f (Y.ofRestrict U.isOpenEmbedding))).obj E)
      ((derivedPullback (Y.ofRestrict U.isOpenEmbedding)).obj (DerivedCategory.Q.obj A))) :=
  ((projectionFormulaTransformation _ _).isIso_app_iff_of_iso
      (derivedQIsoOfQuasiIso q hq ≪≫ (derivedPullbackRestrictComplexIso Y U A).symm)).mp
    (isIso_projectionFormulaMap_of_isStrictlyPerfect _ _ P hP)

/-- **The projection formula for a perfect complex** [Stacks, Tag 0B54].  For a morphism of
ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, an arbitrary `E ∈ D(𝒪_X)` and a *perfect*
`K ∈ D(𝒪_Y)`, the projection-formula morphism

`Rf_*E ⊗^L_{𝒪_Y} K ⟶ Rf_*(E ⊗^L_{𝒪_X} Lf^*K)`

of [Stacks, Tag 0B53] is invertible.

The base case `K = 𝒪_Y[i]⟦n⟧` of the source's dévissage is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_singleUnit_degree`
([Stacks, Tag 08EU] at every degree), obtained from the abstract projection formula
`Stacks.ProjectionFormula.isIso_adjunctionTensorMap` at an invertible object, and the dévissage
over strictly perfect complexes is `isIso_projectionFormulaMap_of_isStrictlyPerfect`.

**The proof.**  A perfect `K` is the class of a perfect complex `A`, so there is an open covering
`U` of `Y` on each member of which `A` receives a quasi-isomorphism from a strictly perfect
complex.  Invertibility in `D(𝒪_Y)` is local on that covering
(`Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`), restriction to a member is
derived pullback along its inclusion
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`), and derived
pullback of the projection-formula morphism along that inclusion is invertible as soon as the
projection-formula morphism of the base change is
(`isIso_derivedPullback_map_projectionFormulaMap`, which is [Stacks, Tag 0B6B] together with
invertibility of the derived base-change map at a square of open immersions).  The base change
is taken as the genuine fibre product `X ×_Y U` in ringed spaces, which exists because the
inclusion of an open subspace is an open immersion, so the square is Cartesian on the nose and
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions` applies.
Upstairs the complex is strictly perfect and
`isIso_projectionFormulaMap_derivedPullback_obj` closes it. -/
@[stacks 0B54 "the whole tag: for an arbitrary morphism of ringed spaces f : X ⟶ Y, an arbitrary \
E in D(𝒪_X) and a perfect K in D(𝒪_Y), the projection-formula morphism \
Rf_*E ⊗ᴸ K ⟶ Rf_*(E ⊗ᴸ Lf^*K) of Tag 0B53 is invertible",
  sga "6 III 3.7" "special case",
  sga "6 IV 2.11.1" "more general"]
theorem isIso_projectionFormulaMap_of_isPerfect {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hK : AlgebraicGeometry.RingedSpace.IsPerfect K) :
    IsIso (projectionFormulaMap f E K) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := hK
  refine ((projectionFormulaTransformation f E).isIso_app_iff_of_iso e).mp ?_
  obtain ⟨ι, U, hU, hloc⟩ := hA
  refine Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
    (structureSheafRing Y) U hU _ fun t => ?_
  refine (NatIso.isIso_map_iff (derivedPullbackOpenRestrictionIso Y (U t)) _).mp ?_
  obtain ⟨P, hP, q, hq⟩ := hloc t
  exact isIso_derivedPullback_map_projectionFormulaMap _ _ f _
    (IsPullback.of_hasPullback f (Y.ofRestrict (U t).isOpenEmbedding)) E _
    (isIso_projectionFormulaMap_derivedPullback_obj f (U t) E A P hP q hq)

end Reduction

end Stacks.Cohomology.ProjectionFormulaPerfect

end

end
