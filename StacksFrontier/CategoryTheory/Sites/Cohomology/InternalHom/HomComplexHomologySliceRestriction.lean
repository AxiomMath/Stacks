module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction

/-!
# The cohomology sheaves of an internal Hom complex commute with restriction to a slice site

Let `X` be a ringed site, `U` an object of its underlying category and `K`, `M` complexes of
`O`-modules. Restriction of sheaves of modules to the slice site over `U` is exact, so it
commutes with the cohomology of a complex, and it carries the internal Hom complex to the
internal Hom complex of the restrictions by
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`. Composing the two:

`Hⁿ(SheafHom(K, M))|_U ≅ Hⁿ(SheafHom(K|_U, M|_U))`.

These are the *pieces* of the graded algebra that the composition product of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct` is built on —
the cohomology sheaves of the internal Hom complex itself, not the Ext sheaves of the derived
internal Hom. The two agree when the complex is a suitable resolution, but they are different
objects, and the comparison for the Ext sheaves,
`Stacks.SheafOfModules.derivedSheafExtRestrictionIso`, is not this one.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`: the comparison above.
* `AlgebraicGeometry.RingedSite.sheafHomCyclesOverMap`: the same comparison with cycles in
  place of cohomology.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso_hom`: the comparison written out as the
  composite of the two isomorphisms it is built from.
* `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso_natural`: it is natural in both
  variables, which is what makes it *the* comparison rather than an unspecified isomorphism of
  the two sheaves.
* `AlgebraicGeometry.RingedSite.map_homologyπ_sheafHomHomologyOverIso` and its form on local
  sections `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso_hom_app_homologyπ`: **the
  comparison carries the class of a cocycle to the class of the corresponding cocycle.** Without
  this an isomorphism of cohomology sheaves says nothing about any particular section of either.
* `AlgebraicGeometry.RingedSite.sheafHomCyclesOverMap_iCycles` and
  `AlgebraicGeometry.RingedSite.sheafHomCyclesOverMap_iCycles_app`: that comparison on cycles,
  read inside the complex, where it is the chain-level comparison of Stacks 08JB.

## Implementation notes

Nothing here is proved twice. Exactness of restriction to a slice is
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` together with
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits`; that an exact additive
functor commutes with the cohomology of a complex is `Stacks.Homology.exactHomologyIso`; and the
comparison of the internal Hom complexes is the chain-level form of Stacks 08JB. The naturality
statement is the naturality of each of those two in turn, so it is an identity of composites and
not a computation.

The exactness and additivity of restriction are supplied as local instances. They are theorems
rather than instances in the library because their hypotheses mention the sheafification of
abelian groups on the slice site, which instance search cannot discharge on its own at the
universe-degenerate spelling a ringed site carries.

The statements about a class of a cocycle are proved in term mode. Their proofs pass through
`ShortComplex.mapCyclesIso` of the degree-`n` short complex of a complex, so the identification
of `(K.sc n).cycles` with `K.cycles n` and of `(K.sc n).map F` with the degree-`n` short complex
of the complex of `F`-images occurs in the middle of every chain; `HomologicalComplex.cycles`
and `AlgebraicGeometry.RingedSite.sheafHomComplex` are not unfolded at the transparency a
rewrite uses, so each step is a `congrArg` rather than a `rw`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Restriction to a slice site is additive by the global instance
-- `AlgebraicGeometry.RingedSite.overFunctor_additive`
-- (StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfComplexes.lean:47); left and
-- right exactness are the named theorems of Stacks 04IX, made local instances here.
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- **The cohomology sheaves of an internal Hom complex commute with restriction to a slice
site.** For complexes `K`, `M` of `O`-modules and an integer `n`, restricting the cohomology
sheaf `Hⁿ(SheafHom(K, M))` to the site over `U` gives the cohomology sheaf
`Hⁿ(SheafHom(K|_U, M|_U))` of the internal Hom complex of the restrictions.

It is the comparison of Stacks 08JB at the level of complexes, under the degree-`n` cohomology
functor, preceded by the comparison which identifies the restriction of a cohomology sheaf with
the cohomology sheaf of the restriction, restriction being exact. -/
def sheafHomHomologyOverIso (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).obj
        ((sheafHomComplex X K M).obj.homology n) ≅
      (sheafHomComplex (X.over U)
        (restrictComplex X K U) (restrictComplex X M U)).obj.homology n :=
  ((Stacks.Homology.exactHomologyIso
        (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n).app
      (sheafHomComplex X K M).obj).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (sheafHomRestrictionComplexIso X U K M)

/-- The comparison, spelled out: the inverse of the exactness comparison for the restriction
functor, followed by the degree-`n` cohomology of the chain-level comparison of Stacks 08JB. -/
theorem sheafHomHomologyOverIso_hom
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) :
    (sheafHomHomologyOverIso X U K M n).hom =
      (Stacks.Homology.exactHomologyIso
            (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n).inv.app
          (sheafHomComplex X K M).obj ≫
        HomologicalComplex.homologyMap (sheafHomRestrictionComplexIso X U K M).hom n :=
  rfl

/-- **The comparison is natural in both variables.** Restricting the map of cohomology sheaves
induced by `f : K' ⟶ K` and `g : M ⟶ M'` gives the map induced by the restrictions of `f` and
`g`. -/
theorem sheafHomHomologyOverIso_natural
    {K K' M M' : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ} (f : K' ⟶ K) (g : M ⟶ M')
    (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
          (HomologicalComplex.homologyMap (homMap X f g) n) ≫
        (sheafHomHomologyOverIso X U K' M' n).hom =
      (sheafHomHomologyOverIso X U K M n).hom ≫
        HomologicalComplex.homologyMap
          (homMap (X.over U)
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f)
            (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapHomologicalComplex
              (ComplexShape.up ℤ)).map g)) n := by
  have hnat : (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
          (HomologicalComplex.homologyMap (homMap X f g) n) ≫
        (Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n).inv.app
            (sheafHomComplex X K' M').obj =
      (Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n).inv.app
            (sheafHomComplex X K M).obj ≫
        HomologicalComplex.homologyMap
          (((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (homMap X f g)) n :=
    (Stacks.Homology.exactHomologyIso
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n).inv.naturality (homMap X f g)
  refine (congrArg (_ ≫ ·) (sheafHomHomologyOverIso_hom X U K' M' n)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hnat).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n).symm).trans ?_
  refine (congrArg (_ ≫ HomologicalComplex.homologyMap · n)
    (sheafHomRestrictionComplexIso_natural X U f g)).trans ?_
  refine (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (sheafHomHomologyOverIso_hom X U K M n).symm)

/-! ### The comparison on a class of a cocycle

The comparison is an isomorphism of cohomology sheaves and so says nothing on its own about a
*section* of one of them. What a consumer computing with local sections needs is the value of the
comparison on the class of a cocycle, and that is what follows: the comparison carries the class
of a cocycle to the class of the cocycle obtained by the same comparison on cycles. -/

/-- **The cycles of an internal Hom complex commute with restriction to a slice site.** The
comparison is built exactly as `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`, with
cycles in place of cohomology: the exactness comparison of the restriction functor on the
degree-`n` short complex, followed by the degree-`n` cycles of the chain-level comparison of
Stacks 08JB. -/
def sheafHomCyclesOverMap (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).obj
        ((sheafHomComplex X K M).obj.cycles n) ⟶
      (sheafHomComplex (X.over U)
        (restrictComplex X K U) (restrictComplex X M U)).obj.cycles n :=
  (((sheafHomComplex X K M).obj.sc n).mapCyclesIso
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)).inv ≫
    HomologicalComplex.cyclesMap (sheafHomRestrictionComplexIso X U K M).hom n

/-- **The comparison on cycles, read inside the complex.** A cocycle and the cocycle it is
carried to have the same image in the complex, up to the chain-level comparison of Stacks 08JB.
-/
theorem sheafHomCyclesOverMap_iCycles
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) :
    sheafHomCyclesOverMap X U K M n ≫
        (sheafHomComplex (X.over U)
          (restrictComplex X K U) (restrictComplex X M U)).obj.iCycles n =
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
          ((sheafHomComplex X K M).obj.iCycles n) ≫
        (sheafHomRestrictionComplexIso X U K M).hom.f n := by
  have hi : (((sheafHomComplex X K M).obj.sc n).mapCyclesIso
          (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)).inv ≫
        (restrictComplex X (sheafHomComplex X K M).obj U).iCycles n =
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
        ((sheafHomComplex X K M).obj.iCycles n) :=
    (Iso.inv_comp_eq _).2
      (ShortComplex.mapCyclesIso_hom_iCycles ((sheafHomComplex X K M).obj.sc n)
        (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (((sheafHomComplex X K M).obj.sc n).mapCyclesIso
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)).inv ≫ z)
    (HomologicalComplex.cyclesMap_i (sheafHomRestrictionComplexIso X U K M).hom n)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (sheafHomRestrictionComplexIso X U K M).hom.f n) hi)

/-- **The comparison of cohomology sheaves carries the class of a cocycle to the class of the
corresponding cocycle.** This is the compatibility of
`AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso` with
`HomologicalComplex.homologyπ`, which neither factor of that comparison had: the second factor
has `HomologicalComplex.homologyπ_naturality`, and the first is
`Stacks.Homology.exactHomologyIso`, whose compatibility with the projection from cycles is
`Stacks.Homology.map_homologyπ_exactHomologyIso_inv_app`. -/
theorem map_homologyπ_sheafHomHomologyOverIso
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
          ((sheafHomComplex X K M).obj.homologyπ n) ≫
        (sheafHomHomologyOverIso X U K M n).hom =
      sheafHomCyclesOverMap X U K M n ≫
        (sheafHomComplex (X.over U)
          (restrictComplex X K U) (restrictComplex X M U)).obj.homologyπ n := by
  refine (congrArg (fun z => (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).map
      ((sheafHomComplex X K M).obj.homologyπ n) ≫ z)
    (sheafHomHomologyOverIso_hom X U K M n)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg
    (fun z => z ≫ HomologicalComplex.homologyMap
      (sheafHomRestrictionComplexIso X U K M).hom n)
    (Stacks.Homology.map_homologyπ_exactHomologyIso_inv_app
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U) n
      (sheafHomComplex X K M).obj)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (((sheafHomComplex X K M).obj.sc n).mapCyclesIso
      (SheafOfModules.overFunctor.{u} (ringSheaf X.O) U)).inv ≫ z)
    (HomologicalComplex.homologyπ_naturality
      (sheafHomRestrictionComplexIso X U K M).hom n)).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The comparison on a class of a cocycle, on local sections.** For an object `V` of the
slice site and a degree-`n` cocycle `x` of `SheafHom(K, M)` over `V.left`, the comparison sends
the class of `x` to the class of the cocycle `x` is carried to. -/
theorem sheafHomHomologyOverIso_hom_app_homologyπ
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) (V : Over U)
    (x : ((sheafHomComplex X K M).obj.cycles n).val.obj (op V.left)) :
    ((sheafHomHomologyOverIso X U K M n).hom.val.app (op V))
        (((sheafHomComplex X K M).obj.homologyπ n).val.app (op V.left) x) =
      ((sheafHomComplex (X.over U)
            (restrictComplex X K U) (restrictComplex X M U)).obj.homologyπ n).val.app (op V)
        ((sheafHomCyclesOverMap X U K M n).val.app (op V) x) :=
  congrArg (fun z => (SheafOfModules.Hom.val z).app (op V) x)
    (map_homologyπ_sheafHomHomologyOverIso X U K M n)

/-- **The comparison on cycles, read inside the complex, on local sections.** -/
theorem sheafHomCyclesOverMap_iCycles_app
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf X.O)) ℤ) (n : ℤ) (V : Over U)
    (x : ((sheafHomComplex X K M).obj.cycles n).val.obj (op V.left)) :
    (((sheafHomComplex (X.over U)
            (restrictComplex X K U) (restrictComplex X M U)).obj.iCycles n).val.app (op V))
        ((sheafHomCyclesOverMap X U K M n).val.app (op V) x) =
      ((sheafHomRestrictionComplexIso X U K M).hom.f n).val.app (op V)
        (((sheafHomComplex X K M).obj.iCycles n).val.app (op V.left) x) :=
  congrArg (fun z => (SheafOfModules.Hom.val z).app (op V) x)
    (sheafHomCyclesOverMap_iCycles X U K M n)

end AlgebraicGeometry.RingedSite

end
