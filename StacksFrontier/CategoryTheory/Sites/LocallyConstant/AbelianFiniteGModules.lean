module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Finite locally constant abelian sheaves and finite discrete `G`-modules

Let `(C, J)` be a site and let `G` be a topological group, and suppose given an equivalence
between the finite locally constant sheaves of sets on `C` and the finite continuous `G`-sets.
Then the finite locally constant sheaves of abelian groups on `C` are equivalent to the finite
discrete `G`-modules. This is part (2) of Stacks Tag 0DV5; part (1) supplies the hypothesis when
`C` is the small étale site of a connected scheme and `G` is its fundamental group.

## Main definitions

* `CategoryTheory.ObjectProperty.commGrpEquivalence`: a commutative group object in a full
  subcategory closed under finite products is the same thing as a commutative group object of
  the ambient category whose underlying object lies in the subcategory.
* `AlgebraicGeometry.ContinuousGSet.isFinite` and `CategoryTheory.ContinuousGAddCommGrp.isFinite`:
  finiteness of the underlying set of a continuous `G`-set and of a discrete `G`-module.

## Main results

* `Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence`, the
  site-independent transport that Tag 0DV5 part (2) is an instance of. The tag itself is
  `AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence`.
* `Stacks.ConstantSheaf.finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_forgetAction`:
  the equivalence lifts the given one, so the finite `G`-set underlying the discrete `G`-module
  attached to an abelian sheaf is the one attached to its underlying sheaf of sets.

## Implementation notes

Part (1) of the tag is the composition of Tag 03RV with Fundamental Groups, Tag 0BND, and lives
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Sets`; here it
enters as the argument `e`, an equivalence of the *full subcategory* of finite
locally constant sheaves of sets with the *full subcategory* of finite continuous `G`-sets. It is
emphatically not an equivalence of the whole topos of sheaves of sets with all continuous
`G`-sets — that is false already for a general connected scheme — so the whole-topos transport
`AlgebraicGeometry.abelianEquivalenceOfGSetEquivalence`, whose hypothesis is of that shape and
which is used for the spectrum of a field, does not apply.

Part (2) is the transport of commutative group objects along `e`, which is the argument the
source gives: the equivalence of (1) preserves products, hence carries an addition on a sheaf to
an addition on the corresponding finite `G`-set. Concretely the equivalence is the composite of
five steps. `CategoryTheory.Sites.AbelianSheaf.equivalence` identifies abelian sheaves with
commutative group objects in sheaves of sets, and `isFiniteLocallyConstant_iff_forget` says the
finiteness condition only sees the underlying sheaf of sets, so it restricts to the
subcategories. `commGrpEquivalence` moves the subcategory condition from the ambient category
inside the commutative group object, on both sides. In between,
`CategoryTheory.Equivalence.mapCommGrp` applies `e`. Finally
`CategoryTheory.commGrpContinuousGSetEquivalence` identifies commutative group objects in
continuous `G`-sets with discrete `G`-modules, again compatibly with finiteness.

The content of `commGrpEquivalence` is essential surjectivity: its underlying functor is fully
faithful for free from `CategoryTheory.Functor.FullyFaithful.mapCommGrp`, and a commutative group
object of the ambient category whose underlying object lies in the subcategory has its operations
in the subcategory because the inclusion is full, which is
`CategoryTheory.Sites.AbelianSheaf.pullCommGrp`.

Continuous `G`-sets are `AlgebraicGeometry.ContinuousGSet`, which carries
`commGrpContinuousGSetEquivalence`, the finite-product structure and the braidings. Discrete
`G`-modules are `CategoryTheory.ContinuousGAddCommGrp`, continuous actions
on objects of `AddCommGrpCat`; Tag 04JP spells the same notion as
`Stacks.Injectives.ContinuousModule ℤ G`, continuous actions on `ModuleCat ℤ`.

The sheaf universes are those of Tag 093U: sets in `Type (max u v)` and abelian groups in
`AddCommGrpCat.{max u v}`, obtained from the free third universe of
`isFiniteLocallyConstantSetSheaf` by setting it to `u`. The free universe cannot be kept here
because `isFiniteLocallyConstant_iff_forget` is available only at `max u v`.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u u' w

namespace CategoryTheory

section Pullback

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{w} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

/-- The unit of a commutative group object pulled back along a fully faithful cartesian functor
is, after applying that functor again, the original unit. -/
theorem one_mapCommGrp_pullCommGrp (X : C) [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] :
    MonObj.one (X := (F.mapCommGrp.obj (Sites.AbelianSheaf.pullCommGrp hF X)).X) =
      MonObj.one (X := F.obj X) := by
  let : GrpObj X := hF.grpObj X
  change Functor.LaxMonoidal.ε F ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.η F ≫ MonObj.one (X := F.obj X))) =
    MonObj.one (X := F.obj X)
  rw [hF.map_preimage, ← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

/-- A commutative group object pulled back along a fully faithful cartesian functor is carried by
that functor to the commutative group object one started with. -/
def mapCommGrpPullCommGrpIso (X : C) [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] :
    F.mapCommGrp.obj (Sites.AbelianSheaf.pullCommGrp hF X) ≅ CommGrp.mk (F.obj X) :=
  have h : (𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj X)) ≫ MonObj.mul (X := F.obj X) =
      MonObj.mul (X := F.obj X) := by
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
  CommGrp.mkIso (Iso.refl (F.obj X))
    ((Category.comp_id _).trans (one_mapCommGrp_pullCommGrp hF X))
    ((Category.comp_id _).trans ((mul_mapCommGrp_pullCommGrp hF X).trans h.symm))

end Pullback

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (P : ObjectProperty C) [CartesianMonoidalCategory P.FullSubcategory]
  [BraidedCategory P.FullSubcategory] [P.ι.Braided]

/-- The property of a commutative group object of `C` that its underlying object satisfies `P`. -/
abbrev commGrpProp : ObjectProperty (CommGrp C) := P.inverseImage (CommGrp.forget C)

/-- A commutative group object in the full subcategory on `P` is one in `C` whose underlying
object satisfies `P`. -/
def commGrpι : CommGrp P.FullSubcategory ⥤ P.commGrpProp.FullSubcategory :=
  P.commGrpProp.lift P.ι.mapCommGrp fun A ↦ A.X.property

/-- Pushing a commutative group object out of a full subcategory loses nothing. -/
def commGrpιFullyFaithful : (commGrpι P).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    P.fullyFaithfulι.mapCommGrp

/-- A commutative group object of `C` whose underlying object satisfies `P` is one in the full
subcategory on `P`: the inclusion is full, so its operations are morphisms there. -/
abbrev pullCommGrpSub (A : P.commGrpProp.FullSubcategory) : CommGrp P.FullSubcategory := by
  letI : GrpObj (P.ι.obj (⟨A.obj.X, A.property⟩ : P.FullSubcategory)) := A.obj.grp
  letI : IsCommMonObj (P.ι.obj (⟨A.obj.X, A.property⟩ : P.FullSubcategory)) := A.obj.comm
  exact Sites.AbelianSheaf.pullCommGrp P.fullyFaithfulι ⟨A.obj.X, A.property⟩

/-- Reading the operations of `A` inside the full subcategory on `P` and pushing them back out
recovers `A`. -/
def commGrpιObjIso (A : P.commGrpProp.FullSubcategory) :
    (commGrpι P).obj (pullCommGrpSub P A) ≅ A := by
  letI : GrpObj (P.ι.obj (⟨A.obj.X, A.property⟩ : P.FullSubcategory)) := A.obj.grp
  letI : IsCommMonObj (P.ι.obj (⟨A.obj.X, A.property⟩ : P.FullSubcategory)) := A.obj.comm
  exact ObjectProperty.isoMk _
    (mapCommGrpPullCommGrpIso P.fullyFaithfulι (⟨A.obj.X, A.property⟩ : P.FullSubcategory))

/-- Reading the operations of a commutative group object of `C` inside the full subcategory on
`P` is functorial: a morphism of such objects is one of the subcategory, again by fullness. -/
def pullCommGrpSubFunctor : P.commGrpProp.FullSubcategory ⥤ CommGrp P.FullSubcategory where
  obj := pullCommGrpSub P
  map {A B} f := by
    let X : P.FullSubcategory := ⟨A.obj.X, A.property⟩
    let Y : P.FullSubcategory := ⟨B.obj.X, B.property⟩
    letI : GrpObj (P.ι.obj X) := A.obj.grp
    letI : GrpObj (P.ι.obj Y) := B.obj.grp
    let g : X ⟶ Y := ObjectProperty.homMk f.hom.hom.hom.hom
    haveI : IsMonHom (P.ι.map g) := f.hom.hom.hom.isMonHom_hom
    haveI := Sites.AbelianSheaf.isMonHom_pullGrpObj P.fullyFaithfulι g
    exact InducedCategory.homMk (Grp.homMk g)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Pushing the operations back out recovers the commutative group object, naturally in it. -/
def pullCommGrpSubFunctorCompCommGrpι :
    pullCommGrpSubFunctor P ⋙ commGrpι P ≅ 𝟭 P.commGrpProp.FullSubcategory :=
  NatIso.ofComponents (commGrpιObjIso P) fun f ↦ by
    apply ObjectProperty.hom_ext
    apply CommGrp.hom_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Pushing the operations of a commutative group object out of the full subcategory on `P` is an
equivalence onto the commutative group objects of `C` whose underlying object satisfies `P`. -/
instance isEquivalence_commGrpι : (commGrpι P).IsEquivalence :=
  letI := (commGrpιFullyFaithful P).full
  letI := (commGrpιFullyFaithful P).faithful
  letI : (commGrpι P).EssSurj := ⟨fun A ↦ ⟨pullCommGrpSub P A, ⟨commGrpιObjIso P A⟩⟩⟩
  {}

/-- Reading the operations inside the full subcategory on `P` is a quasi-inverse of pushing them
out. -/
def commGrpιInvIso : (commGrpι P).inv ≅ pullCommGrpSubFunctor P :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (pullCommGrpSubFunctorCompCommGrpι P).symm (commGrpι P).inv ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (commGrpι P).asEquivalence.unitIso.symm ≪≫
          Functor.rightUnitor _

/-- **A commutative group object in a full subcategory closed under finite products is the same
thing as a commutative group object of the ambient category whose underlying object lies in the
subcategory.** Both directions are explicit: `commGrpι` and `pullCommGrpSubFunctor`. -/
@[sga "3 VIA 0.2" "partial"]
def commGrpEquivalence : CommGrp P.FullSubcategory ≌ P.commGrpProp.FullSubcategory :=
  (commGrpι P).asEquivalence.changeInverse (commGrpιInvIso P)

end ObjectProperty

end CategoryTheory

attribute [local instance] cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace CategoryTheory

section Finiteness

/-- Finiteness, as a property of objects of `Type w`. -/
def isFiniteType : ObjectProperty (Type w) := fun X ↦ Finite X

/-- A type isomorphic to a finite type is finite. -/
instance isClosedUnderIsomorphisms_isFiniteType :
    (isFiniteType.{w}).IsClosedUnderIsomorphisms where
  of_iso e hX := @Finite.of_equiv _ _ hX e.toEquiv

/-- A limit of finite types over a finite index category is finite: it is a subtype of the
product of the finitely many values. -/
instance isClosedUnderLimitsOfShape_isFiniteType (K : Type) [SmallCategory K] [FinCategory K] :
    (isFiniteType.{w}).IsClosedUnderLimitsOfShape K :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩
    have : ∀ k, Finite (D.obj k) := hD
    exact Finite.of_equiv _ (Types.limitEquivSections D).symm)

end Finiteness

end CategoryTheory

namespace AlgebraicGeometry

section Finiteness

variable (G : Type u') [Group G] [TopologicalSpace G]

/-- Finiteness of the underlying set, as a property of objects of `ContinuousGSet G`: these are
the finite `G`-sets among all continuous ones. -/
abbrev ContinuousGSet.isFinite : ObjectProperty (ContinuousGSet.{u', w} G) :=
  (isFiniteType.{w}).inverseImage (ContinuousGSet.forget G)

end Finiteness

end AlgebraicGeometry

namespace CategoryTheory

section Finiteness

variable (G : Type u') [Group G] [TopologicalSpace G]

/-- Finiteness of the underlying set, as a property of objects of `ContinuousGAddCommGrp G`:
these are the finite discrete `G`-modules among all of them. -/
abbrev ContinuousGAddCommGrp.isFinite :
    ObjectProperty (ContinuousGAddCommGrp.{u', w} G) :=
  (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).inverseImage
    (ContinuousGAddCommGrp.forgetAction G)

/-- A continuous `G`-set has the finiteness property exactly when its underlying set is
finite. -/
theorem continuousGSet_isFinite_iff (M : AlgebraicGeometry.ContinuousGSet.{u', w} G) :
    AlgebraicGeometry.ContinuousGSet.isFinite G M ↔ Finite M.obj.obj.V := Iff.rfl

/-- A discrete `G`-module has the finiteness property exactly when its underlying abelian group
is finite. -/
theorem continuousGAddCommGrp_isFinite_iff (M : ContinuousGAddCommGrp.{u', w} G) :
    ContinuousGAddCommGrp.isFinite G M ↔ Finite M.obj.obj.V := Iff.rfl

/-- The braiding of the cartesian monoidal structure on finite continuous `G`-sets, which have
finite products because a finite product of finite sets is finite. -/
local instance braidedContinuousGSetIsFinite :
    BraidedCategory (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory :=
  .ofCartesianMonoidalCategory

/-- The inclusion of the finite continuous `G`-sets creates finite products, hence preserves
them. -/
instance preservesFiniteProducts_ι_continuousGSetIsFinite :
    PreservesFiniteProducts (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι where
  preserves _ := inferInstance

/-- The inclusion of the finite continuous `G`-sets preserves finite products, hence is braided
monoidal. -/
local instance braidedι_continuousGSetIsFinite :
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).ι.Braided :=
  .ofChosenFiniteProducts _

/-- The finite continuous `G`-set underlying a finite discrete `G`-module. -/
def ContinuousGAddCommGrp.forgetActionIsFinite :
    (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory ⥤
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).FullSubcategory :=
  (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).lift
    ((ContinuousGAddCommGrp.isFinite.{u', w} G).ι ⋙ ContinuousGAddCommGrp.forgetAction G)
    fun M ↦ M.property

/-- A commutative group object in continuous `G`-sets is finite exactly when the discrete
`G`-module it corresponds to is: the two have the same underlying set. -/
theorem isFinite_inverseImage_commGrpContinuousGSetEquivalence :
    (ContinuousGAddCommGrp.isFinite.{u', w} G).inverseImage
        (commGrpContinuousGSetEquivalence.{u', w} (G := G)).functor =
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).commGrpProp :=
  rfl

end Finiteness

end CategoryTheory

attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  braidedContinuousGSetIsFinite braidedι_continuousGSetIsFinite

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (G : Type u') [Group G] [TopologicalSpace G]

/-- The braiding of the cartesian monoidal structure on finite locally constant sheaves of sets,
which have finite products because the property is closed under finite limits. -/
local instance braidedFiniteLocallyConstantSetSheaf :
    BraidedCategory (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory :=
  .ofCartesianMonoidalCategory

/-- The inclusion of the finite locally constant sheaves of sets preserves finite products, hence
is braided monoidal. -/
local instance braidedι_finiteLocallyConstantSetSheaf :
    (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.Braided :=
  .ofChosenFiniteProducts _

/-- An abelian sheaf is finite locally constant exactly when the sheaf of sets underlying the
commutative group object it corresponds to is. -/
theorem commGrpProp_inverseImage_internalSheaf
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).commGrpProp).inverseImage
        (Sites.AbelianSheaf.equivalence J).functor =
      isFiniteLocallyConstantAbelianSheaf.{v, u, u} J :=
  funext fun F ↦ propext (isFiniteLocallyConstant_iff_forget J F).symm

/-- The sheaf of sets underlying a finite locally constant abelian sheaf, which is again finite
locally constant. -/
def forgetFiniteLocallyConstantAbelianSheaf
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}] :
    (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory ⥤
      (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory :=
  (isFiniteLocallyConstantSetSheaf.{v, u, u} J).lift
    ((isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).ι ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v}))
    fun F ↦ (isFiniteLocallyConstant_iff_forget J F.obj).1 F.property

/-- **The transport of commutative group objects underlying Stacks Tag 0DV5 part (2).** Given an
equivalence `e` of the finite locally constant sheaves of sets on a site with the finite
continuous `G`-sets, the finite locally constant sheaves of abelian groups are equivalent to the
finite discrete `G`-modules. Both sides are commutative group objects in the categories related
by `e`, which preserves products.

This is the site-independent engine of part (2); Tag 0DV5 part (2) itself is
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence`, which instantiates it at the
small étale site of a connected scheme with `e` supplied by part (1),
`AlgebraicGeometry.finiteLocallyConstantSetsEquivalence`. -/
def finiteLocallyConstantAbelianEquivalenceOfSetEquivalence
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory) :
    (isFiniteLocallyConstantAbelianSheaf.{v, u, u} J).FullSubcategory ≌
      (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory :=
  letI : e.functor.Braided := .ofChosenFiniteProducts _
  letI : e.inverse.Braided := .ofChosenFiniteProducts _
  ((Sites.AbelianSheaf.equivalence J).congrFullSubcategory
      (commGrpProp_inverseImage_internalSheaf J)).trans
    (((isFiniteLocallyConstantSetSheaf.{v, u, u} J).commGrpEquivalence.symm.trans
        (e.mapCommGrp.trans
          (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).commGrpEquivalence)).trans
      ((commGrpContinuousGSetEquivalence.{u', max u v} (G := G)).congrFullSubcategory
        (isFinite_inverseImage_commGrpContinuousGSetEquivalence G)))

/-- **The abelian transport lifts the equivalence it is built from.** The finite `G`-set
underlying the discrete `G`-module attached to a finite locally constant abelian sheaf is the one
`e` attaches to its underlying sheaf of sets. -/
theorem finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_forgetAction
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory) :
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).functor ⋙
        ContinuousGAddCommGrp.forgetActionIsFinite.{u', max u v} G =
      forgetFiniteLocallyConstantAbelianSheaf J ⋙ e.functor :=
  rfl

end Stacks.ConstantSheaf

end
