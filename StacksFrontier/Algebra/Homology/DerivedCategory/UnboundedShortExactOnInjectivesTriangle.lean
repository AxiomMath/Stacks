module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle

/-!
# The distinguished triangle of a sequence of functors exact on injectives

Let `A` be a Grothendieck abelian category with a chosen unbounded derived category `D(A)`, and
let `F ⟶ G ⟶ H` be a short complex of additive endofunctors of `A` whose short complex is short
exact at every *injective* object of `A`.  This file produces, for arbitrary right derived
functors `RF`, `RG`, `RH` of `F`, `G`, `H` on `D(A)`, a connecting map
`δ : RH ⟶ RF ⋙ (-)⟦1⟧` and a triangle

`RF(K) ⟶ RG(K) ⟶ RH(K) ⟶ RF(K)⟦1⟧`

which is distinguished for every object `K` of `D(A)`, functorially in `K`.

Exactness at the injective objects only is what a merely *left* exact functor supplies, and it is
exactly the hypothesis the K-injective route consumes: a K-injective resolution chosen
functorially (Tag 079P) has injective terms, so applying the three functors to it degreewise
gives a short exact sequence of cochain complexes, hence a distinguished triangle in `D(A)`,
which is then transported to the chosen right derived functors.

Rather than fixing models for the derived functors, every statement quantifies over arbitrary
functors equipped with their `CategoryTheory.Functor.IsRightDerivedFunctor` data, and
characterizes the maps of the triangle by their composites with the supplied comparison maps.

## Main definitions

* `Stacks.ShortExactOnInjectives.homotopyIdentityIso`: applying the identity functor
  degreewise is the identity on the homotopy category.
* `Stacks.ShortExactOnInjectives.derivedRestrictionMap`: a map from the localization functor
  descends to a map out of the identity of `D(A)` into a chosen right derived functor.
* `Stacks.ShortExactOnInjectives.derivedRestrictionTransition`: the map of chosen right
  derived functors induced by a map of the underlying functors.
* `Stacks.ShortExactOnInjectives.homotopyLocalization`: the localization of cochain complexes
  written as the quotient to the homotopy category followed by `Qh`.
* `Stacks.ShortExactOnInjectives.complexDerivedUnit`: the derived unit of an additive
  endofunctor, read on cochain complexes.
* `Stacks.ShortExactOnInjectives.resolutionDerivedIso`: a chosen right derived functor,
  evaluated on a complex, is computed by the functorial K-injective resolution.

## Main results

* `Stacks.ShortExactOnInjectives.exists_quasiIso_kInjective`: every cochain complex in a
  Grothendieck abelian category admits a quasi-isomorphism into a K-injective complex.
* `Stacks.ShortExactOnInjectives.derivedUnit_isIso_of_isKInjective` and
  `Stacks.ShortExactOnInjectives.complexDerivedUnit_app_isIso_of_isKInjective`: the unit of a
  right derived functor is invertible at a K-injective complex.
* `Stacks.ShortExactOnInjectives.resolutionDerivedIso_fac`: the comparison isomorphisms are
  compatible with a map of the underlying functors.
* `Stacks.ShortExactOnInjectives.derivedTriangleOfShortExactOnInjectives`: the connecting map
  and the distinguished triangle, for any short complex of additive endofunctors of `A` which
  is short exact at every injective object and any choice of comparison isomorphisms.
* `Stacks.ShortExactOnInjectives.exists_derivedTriangle_of_shortExactOnInjectives`: the same
  conclusion from the right-derived-functor data alone, with the maps of the triangle and the
  comparison isomorphisms supplied by this file rather than by the caller.

## Implementation notes

Three elaboration points are worth recording because the obvious spellings fail.

* `CategoryTheory.Functor.IsRightDerivedFunctor`'s localization functor `L` is implicit and
  recovered from the unit `α : F ⟶ L ⋙ RF`.  With `RF` the identity functor and `α = 𝟙 Qh` the
  constraint `L ⋙ 𝟭 =?= Qh` needs structure eta, so the instance argument `[L.IsLocalization W]`
  is searched while `L` is still a metavariable and the search fails.  Writing
  `(L := DerivedCategory.Qh)` out fixes it.
* `DerivedCategory.Q.obj K` and `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`
  are only *definitionally* equal, so composites that mix them are not type-correct at
  `instances` transparency and `rw`/`simp` cannot act on them.  Every such square below is
  therefore closed in term mode, by `calc` steps that are `Category.assoc`, `congrArg`, or a
  named naturality hypothesis.  The purely formal steps are the abstract lemmas
  `Stacks.Cohomology.RestrictionCover.comp_square_chase`,
  `Stacks.Cohomology.RestrictionCover.inv_comp_comm` and
  `Stacks.Cohomology.RestrictionCover.comp_inv_chase`, where no such obstruction exists.
* The morphism property is written out as `HomotopyCategory.quasiIso A (ComplexShape.up ℤ)` at
  every occurrence rather than abbreviated, so that a single spelling reaches every instance.

`Stacks.ShortExactOnInjectives.identityRightDerivedUnit` is a plain theorem made a *local*
instance: as a global instance it would offer itself to every
`CategoryTheory.Functor.IsRightDerivedFunctor` goal in any abelian category with a derived
category, which is a search surface this file has no reason to widen.  Consumers that want it as
an instance declare their own specialization.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe w t v u

namespace Stacks.ShortExactOnInjectives

variable (A : Type u) [Category.{v} A] [Abelian A]

/-! ### The homotopy-category layer -/

/-- Applying the identity functor degreewise is canonically isomorphic to the identity on the
homotopy category. -/
public def homotopyIdentityIso :
    (CategoryTheory.Functor.id A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      CategoryTheory.Functor.id (HomotopyCategory A (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

/-- A natural transformation of additive functors, applied degreewise and then pushed to the
homotopy category, is the quotient of its degreewise application. -/
public lemma mapHomotopyCategory_app_quotient_obj
    {F G : A ⥤ A} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
  rfl

/-! ### K-injective resolutions -/

section

variable [IsGrothendieckAbelian.{w} A]

/-- Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
K-injective complex; this is the functorial resolution of Tag 079P, forgetting functoriality. -/
public lemma exists_quasiIso_kInjective (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

end

section

variable [HasDerivedCategory.{t} A]

/-! ### The identity functor as a right derived functor -/

/-- The identity functor on `D(A)` is the right derived functor of `Qh` along the identity.
The localization functor `L` is written out: it is implicit in `IsRightDerivedFunctor` and
recovered from the unit, and `L ⋙ 𝟭 =?= Qh` leaves it a metavariable when the instance
argument `[L.IsLocalization _]` is searched. -/
public theorem identityRightDerivedUnit :
    (CategoryTheory.Functor.id (DerivedCategory A)).IsRightDerivedFunctor
      (L := DerivedCategory.Qh)
      (𝟙 (DerivedCategory.Qh (C := A)))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (Iso.refl _)

attribute [local instance] identityRightDerivedUnit

/-! ### Descending maps into a chosen right derived functor -/

/-- Descend a map from the localization functor into a chosen right-derived functor. -/
public def derivedRestrictionMap
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (R : DerivedCategory A ⥤ DerivedCategory A)
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    (s : DerivedCategory.Qh (C := A) ⟶ F) :
    (CategoryTheory.Functor.id (DerivedCategory A)) ⟶ R :=
  Functor.rightDerivedDesc
    (CategoryTheory.Functor.id (DerivedCategory A))
    (L := DerivedCategory.Qh)
    (𝟙 (DerivedCategory.Qh (C := A)))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) R (s ≫ a)

/-- The comparison map just defined is characterized by its composite with the derived unit. -/
public lemma derivedRestrictionMap_fac
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (R : DerivedCategory A ⥤ DerivedCategory A)
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    (s : DerivedCategory.Qh (C := A) ⟶ F) :
    s ≫ a = Functor.whiskerLeft DerivedCategory.Qh
      (derivedRestrictionMap A F R a s) := by
  simpa [derivedRestrictionMap] using
    (Functor.rightDerived_fac
      (CategoryTheory.Functor.id (DerivedCategory A))
      (L := DerivedCategory.Qh)
      (𝟙 (DerivedCategory.Qh (C := A)))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      R (s ≫ a)).symm

/-- The map of right derived functors induced by a map of the underlying functors. -/
public def derivedRestrictionTransition
    (F G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (RF RG : DerivedCategory A ⥤ DerivedCategory A)
    (aF : F ⟶ DerivedCategory.Qh ⋙ RF)
    (aG : G ⟶ DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor aF
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor aG
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (q : F ⟶ G) : RF ⟶ RG :=
  RF.rightDerivedNatTrans RG aF aG
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) q

/-- The induced map is characterized by its composite with the two derived units. -/
public lemma derivedRestrictionTransition_fac
    (F G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (RF RG : DerivedCategory A ⥤ DerivedCategory A)
    (aF : F ⟶ DerivedCategory.Qh ⋙ RF)
    (aG : G ⟶ DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor aF
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor aG
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (q : F ⟶ G) :
    q ≫ aG = aF ≫ Functor.whiskerLeft DerivedCategory.Qh
      (derivedRestrictionTransition A F G RF RG aF aG q) := by
  simp [derivedRestrictionTransition]

/-! ### Comparison with the functorial K-injective resolution -/

/-- The composite of the quotient to the homotopy category with the localization `Qh`.  This is
`DerivedCategory.Q` up to the canonical isomorphism `DerivedCategory.quotientCompQhIso`, but it
is the spelling in which the derived unit of a functor on the homotopy category is stated. -/
public abbrev homotopyLocalization : CochainComplex A ℤ ⥤ DerivedCategory A :=
  HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The derived unit of `F`, read on cochain complexes rather than on the homotopy category. -/
public def complexDerivedUnitHomotopy
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ homotopyLocalization A ⟶
      homotopyLocalization A ⋙ RF where
  app K := α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  naturality _ _ f := α.naturality ((HomotopyCategory.quotient _ _).map f)

/-- The derived unit of `F`, transported to the localization `DerivedCategory.Q`. -/
public def complexDerivedUnit
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso A).inv ≫
    complexDerivedUnitHomotopy A F RF α ≫
    Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso A).hom RF

/-- The three factors of `complexDerivedUnit`, spelled out.  Stating this once is what lets the
compatibility lemmas below be proved in term mode: the composite mixes `DerivedCategory.Q.obj K`
with `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`, which are definitionally
but not syntactically equal. -/
public lemma complexDerivedUnit_app
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex A ℤ) :
    (complexDerivedUnit A F RF α).app K =
      (DerivedCategory.quotientCompQhIso A).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
          RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
  rfl

/-- The derived units are compatible with a map of the underlying functors. -/
public lemma complexDerivedUnit_fac
    {F G : A ⥤ A}
    [F.Additive] [G.Additive]
    {RF RG : DerivedCategory A ⥤ DerivedCategory A}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β) :
    complexDerivedUnit A F RF α ≫ Functor.whiskerLeft DerivedCategory.Q r =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
        DerivedCategory.Q ≫ complexDerivedUnit A G RG β := by
  refine NatTrans.ext (funext fun K => ?_)
  have hn : RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        r.app (DerivedCategory.Q.obj K) =
      r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        RG.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
    r.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  have hh : α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
        β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    congr_app h ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hi : DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso A).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) :=
    (DerivedCategory.quotientCompQhIso A).inv.naturality
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)
  exact Stacks.Cohomology.RestrictionCover.comp_square_chase _ _ _ _ _ _ _ _ _ _ hn hh hi

/-! ### The comparison isomorphism on K-injective resolutions -/

section

variable [IsGrothendieckAbelian.{w} A]

/-- The unit of a right derived functor is invertible at a K-injective complex. -/
public lemma derivedUnit_isIso_of_isKInjective
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (R : DerivedCategory A ⥤ DerivedCategory A)
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor a
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (a.app ((HomotopyCategory.quotient _ _).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F (exists_quasiIso_kInjective A)).2
    DerivedCategory.Qh R a I inferInstance

/-- The derived unit of `F` is invertible on a K-injective complex, read at the level of
cochain complexes. -/
public lemma complexDerivedUnit_app_isIso_of_isKInjective
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit A F RF α).app I) := by
  have hα := derivedUnit_isIso_of_isKInjective A
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RF α I
  rw [complexDerivedUnit_app]
  exact IsIso.comp_isIso'
    ((DerivedCategory.quotientCompQhIso A).symm.app _).isIso_hom
    (IsIso.comp_isIso' hα
      (RF.mapIso ((DerivedCategory.quotientCompQhIso A).app I)).isIso_hom)

/-- A chosen right derived functor is computed by the functorial K-injective resolution:
applying `F` degreewise to the resolution and localizing agrees with `RF`. -/
public def resolutionDerivedIso
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF := by
  have ha : ∀ K, IsIso ((Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A F RF α)).app K) := fun K =>
    complexDerivedUnit_app_isIso_of_isKInjective A F RF α _
  have hb : ∀ K, IsIso ((Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF)).app K) := by
    intro K
    exact RF.map_isIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))
  have : IsIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A F RF α)) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF)) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor A)
      (complexDerivedUnit A F RF α)) ≪≫
    (asIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion A)
      (DerivedCategory.Q ⋙ RF))).symm

/-- The two legs of `resolutionDerivedIso`, spelled out. -/
public lemma resolutionDerivedIso_hom_app
    (F : A ⥤ A) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory A)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) :
    (resolutionDerivedIso A F RF α).hom.app K =
      (complexDerivedUnit A F RF α).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K) ≫
        inv (RF.map (DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))) := by
  simp [resolutionDerivedIso, NatIso.isIso_inv_app]

/-- The comparison isomorphisms are compatible with a map of the underlying functors. -/
public lemma resolutionDerivedIso_fac
    {F G : A ⥤ A}
    [F.Additive] [G.Additive]
    {RF RG : DerivedCategory A ⥤ DerivedCategory A}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β)
    (K : CochainComplex A ℤ) :
    (resolutionDerivedIso A F RF α).hom.app K ≫ r.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
        (resolutionDerivedIso A G RG β).hom.app K := by
  rw [resolutionDerivedIso_hom_app, resolutionDerivedIso_hom_app]
  exact Stacks.Cohomology.RestrictionCover.comp_inv_chase _ _ _ _ _ _ _
    (Stacks.Cohomology.RestrictionCover.inv_comp_comm _ _ _ _ (r.naturality (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))))
    (congr_app (complexDerivedUnit_fac A α β τ r h)
      ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))

/-! ### The distinguished triangle of a sequence exact on injectives -/

omit [HasDerivedCategory A] [IsGrothendieckAbelian.{w, v, u} A] in
/-- The maps of complexes induced by natural transformations composing to zero compose to zero. -/
public lemma mapHomologicalComplex_app_comp_eq_zero {F G H : A ⥤ A}
    [F.Additive] [G.Additive] [H.Additive]
    {f : F ⟶ G} {g : G ⟶ H} (hfg : f ≫ g = 0) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app K = 0 := by
  ext n : 1
  exact NatTrans.congr_app hfg (K.X n)

omit [HasDerivedCategory A] in
/-- A sequence of additive endofunctors which is short exact at every injective object is short
exact on the K-injective resolution of every complex. -/
public lemma shortExact_mapHomologicalComplex_kInjectiveResolution
    (F G H : A ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (K : CochainComplex A ℤ) :
    (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))
      ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K))
      (mapHomologicalComplex_app_comp_eq_zero A hfg _)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => hS _

/-- Given three additive endofunctors of `A`, maps `f : F ⟶ G`, `g : G ⟶ H` composing to
zero whose short complex is short exact at every injective object, and chosen right derived
functors identified on K-injective resolutions by `eF`, `eG`, `eH`, there is a connecting map
making the triangle of the derived maps distinguished at every object. -/
public def derivedTriangleOfShortExactOnInjectives
    (F G H : A ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (RF RG RH : DerivedCategory A ⥤ DerivedCategory A)
    (eF : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF)
    (eG : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RG)
    (eH : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RH)
    (rf : RF ⟶ RG) (rg : RG ⟶ RH)
    (hf : ∀ K, eF.hom.app K ≫ rf.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
          eG.hom.app K)
    (hg : ∀ K, eG.hom.app K ≫ rg.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K)) ≫
          eH.hom.app K) :
    {δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ) //
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        distTriang (DerivedCategory A)} := by
  have hs := shortExact_mapHomologicalComplex_kInjectiveResolution A F G H f g hfg hS
  let d : Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      (Stacks.Injectives.kInjectiveResolutionFunctor A ⋙
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        shiftFunctor (DerivedCategory A) (1 : ℤ) :=
    { app := fun K => DerivedCategory.triangleOfSESδ (hs K)
      naturality := fun K L k =>
        (DerivedCategory.triangleOfSESδ_naturality (hs K) (hs L)
          { τ₁ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            τ₂ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            τ₃ := (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            comm₁₂ := (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k)
            comm₂₃ := (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor A).map k) }).symm }
  let b : DerivedCategory.Q ⋙ RH ⟶
      DerivedCategory.Q ⋙ (RF ⋙
        shiftFunctor (DerivedCategory A) (1 : ℤ)) :=
    eH.inv ≫ d ≫ Functor.whiskerRight eF.hom
      (shiftFunctor (DerivedCategory A) (1 : ℤ))
  let E := (Functor.whiskeringLeft (CochainComplex A ℤ)
    (DerivedCategory A)
    (DerivedCategory A)).obj DerivedCategory.Q
  have : E.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _
  let δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ) :=
    E.preimage b
  have hd (K : CochainComplex A ℤ) :
      δ.app (DerivedCategory.Q.obj K) = b.app K :=
    NatTrans.congr_app (E.map_preimage b) K
  have hdist (K : CochainComplex A ℤ) :
      Triangle.mk (rf.app (DerivedCategory.Q.obj K)) (rg.app (DerivedCategory.Q.obj K))
        (δ.app (DerivedCategory.Q.obj K)) ∈
          distTriang (DerivedCategory A) := by
    refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (hs K)) _
      (Iso.symm (Triangle.isoMk _ _ (eF.app K) (eG.app K) (eH.app K) (hf K).symm (hg K).symm ?_))
    dsimp [DerivedCategory.triangleOfSES]
    rw [hd]
    dsimp [b, d]
    simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨δ, fun K => ?_⟩
  exact isomorphic_distinguished _ (hdist (DerivedCategory.Q.objPreimage K)) _
    (Iso.symm (Triangle.isoMk _ _ (RF.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RG.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RH.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (rf.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (rg.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (δ.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm))

/-- **The distinguished triangle of a short complex of endofunctors exact on injectives**, from
the right-derived-functor data alone.  Given additive endofunctors `F ⟶ G ⟶ H` of `A` composing
to zero and short exact at every injective object, and arbitrary right derived functors `RF`,
`RG`, `RH` with units `αF`, `αG`, `αH`, there are maps `rf : RF ⟶ RG` and `rg : RG ⟶ RH` —
pinned down as the derived versions of `f` and `g` by their composites with the units — and a
connecting map `δ : RH ⟶ RF⟦1⟧` making `RF(K) ⟶ RG(K) ⟶ RH(K) ⟶ RF(K)⟦1⟧` distinguished for
every `K`.

This is `derivedTriangleOfShortExactOnInjectives` with the comparison isomorphisms taken to be
`resolutionDerivedIso` and the two maps taken to be `derivedRestrictionTransition`, so that a
consumer supplies only the functors, the short exactness and the derived-functor data. -/
public theorem exists_derivedTriangle_of_shortExactOnInjectives
    (F G H : A ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : A) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (RF RG RH : DerivedCategory A ⥤ DerivedCategory A)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αH : H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RH.IsRightDerivedFunctor αH
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    ∃ (rf : RF ⟶ RG) (rg : RG ⟶ RH)
      (δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ)),
      Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ αG =
        αF ≫ Functor.whiskerLeft DerivedCategory.Qh rf ∧
      Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ αH =
        αG ≫ Functor.whiskerLeft DerivedCategory.Qh rg ∧
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        distTriang (DerivedCategory A) := by
  let rf := derivedRestrictionTransition A
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RF RG αF αG
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
      DerivedCategory.Qh)
  let rg := derivedRestrictionTransition A
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RG RH αG αH
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
      DerivedCategory.Qh)
  have hrf : Functor.whiskerRight (NatTrans.mapHomotopyCategory f (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ αG =
      αF ≫ Functor.whiskerLeft DerivedCategory.Qh rf :=
    derivedRestrictionTransition_fac A _ _ RF RG αF αG _
  have hrg : Functor.whiskerRight (NatTrans.mapHomotopyCategory g (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ αH =
      αG ≫ Functor.whiskerLeft DerivedCategory.Qh rg :=
    derivedRestrictionTransition_fac A _ _ RG RH αG αH _
  obtain ⟨δ, hδ⟩ := derivedTriangleOfShortExactOnInjectives A F G H f g hfg hS RF RG RH
    (resolutionDerivedIso A F RF αF) (resolutionDerivedIso A G RG αG)
    (resolutionDerivedIso A H RH αH) rf rg
    (fun K => resolutionDerivedIso_fac A αF αG f rf hrf.symm K)
    (fun K => resolutionDerivedIso_fac A αG αH g rg hrg.symm K)
  exact ⟨rf, rg, δ, hrf, hrg, hδ⟩

end

end

end Stacks.ShortExactOnInjectives

end
