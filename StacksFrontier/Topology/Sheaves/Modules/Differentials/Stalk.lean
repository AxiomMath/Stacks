module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.RingTheory.Kaehler.Colimit
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of the sheaf of relative differentials

For a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a topological space `X` and a
point `x : X`, this file develops the two presentations of the stalk at `x` of the sheaf of
relative differentials of `φ`, and the sectionwise description of that sheaf which relates them.

The sheaf of relative differentials is the sheafification of the presheaf of sectionwise Kähler
differentials, and sheafification does not change stalks, so the stalk is the filtered colimit of
the sectionwise Kähler differentials over the open neighbourhoods of `x`. That colimit is in turn
the module of Kähler differentials of the colimit algebra, which is the induced map `O₁,ₓ → O₂,ₓ`
of stalk rings. Each half is recorded here: the direct-limit presentations of a stalk, the
transport of a module of Kähler differentials along a commuting pair of ring equivalences, and the
comparison of Kähler differentials with a colimit.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.toSectionwiseDifferentialsSheaf`: the unit of sheafification
  from the presheaf of sectionwise Kähler differentials to its associated sheaf.
* `AlgebraicGeometry.SheafOfModules.presheafStalkRingDirectLimitIso`: the stalk of a presheaf of
  commutative rings as an algebraic direct limit over the open neighbourhoods of the point.
* `AlgebraicGeometry.SheafOfModules.presheafStalkAdditiveDirectLimitIso`: the same for a presheaf
  of abelian groups.
* `AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv`: transport of a module of
  Kähler differentials along a commuting pair of ring equivalences.
* `AlgebraicGeometry.SheafOfModules.presheafModuleStalkLinearMapCommRing`: the stalk map of a
  morphism of presheaves of modules, as a map linear over the stalk of the base ring presheaf.

## Main results

* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise_hom_app_d`: on a local
  section, the sectionwise presentation sends the universal differential to the sheafified
  sectionwise differential.
* `AlgebraicGeometry.SheafOfModules.omegaColimLinearEquiv`: the module of Kähler differentials of
  a colimit algebra is the colimit of the modules of Kähler differentials, linearly over the
  colimit ring.

## Implementation notes

The open neighbourhoods of a point form a filtered category, but the direct-limit constructions
of `Mathlib.Algebra.Colimit` are stated for a directed preorder of indices. The two are matched
by `CategoryTheory.orderDualEquivalence`, which presents the opposite of `OpenNhds x` as the
order dual of `OpenNhds x`, and by the resulting cofinality of that equivalence; the
`stalkDiagram…` and `additiveDiagram…` families below are the colimit cocones that the comparison
needs on each of the two concrete categories involved.

The space and the ring sheaves lie in a single universe, as required by the stalk-module API of
`Mathlib.Algebra.Category.ModuleCat.Stalk`; the sheaf of relative differentials is therefore used
at its sectionwise universe `moduleOfDifferentials.{u, u, u}`.

## References

* [Stacks Project, Tag 08TD](https://stacks.math.columbia.edu/tag/08TD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits PresheafOfModules TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry.SheafOfModules

/-- The canonical map from sectionwise Kähler differentials to their associated sheaf, that is,
the unit of the sheafification adjunction for presheaves of modules. -/
noncomputable def toSectionwiseDifferentialsSheaf {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom ⟶
      (sectionwiseDifferentialsSheaf φ).val := by
  letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u v} _
  exact (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (𝟙 (underlyingRingSheaf O₂).obj)).unit.app
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)

-- The former `@[stacks 08TD]` definition is `moduleOfDifferentialsIsoSectionwise`.
add_to_stacks 08TD AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise

/-- On a local section, the sectionwise presentation of the sheaf of relative differentials sends
the universal differential `d f` to the image of the sectionwise differential of `f` under the
unit of sheafification. -/
@[simp]
theorem moduleOfDifferentialsIsoSectionwise_hom_app_d {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂)
    (U : (Opens X)ᵒᵖ) (f : O₂.obj.obj U) :
    ((moduleOfDifferentialsIsoSectionwise φ).hom.val.app U).hom
        ((universalDerivation φ).d f) =
      ((toSectionwiseDifferentialsSheaf φ).app U).hom
        ((PresheafOfModules.DifferentialsConstruction.derivation' φ.hom).d f) :=
  PresheafOfModules.Derivation.congr_d
    (moduleOfDifferentialsIsoSectionwise_compatible φ) f

/-! ### The stalk of a presheaf of commutative rings as a direct limit -/

/-- The transition map of a diagram of commutative rings indexed by a preorder, as a function. -/
abbrev stalkDiagramMap {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) (i j : I) (h : i ≤ j) :
    ToType (F.obj i) → ToType (F.obj j) :=
  fun x => (F.map (homOfLE h)).hom x

/-- The algebraic direct limit of a diagram of commutative rings indexed by a preorder. -/
abbrev stalkDiagramDirectLimit {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) :=
  Ring.DirectLimit (fun i => ToType (F.obj i)) (fun i j h => stalkDiagramMap F i j h)

/-- The algebraic direct limit of a diagram of commutative rings, as a cocone over that
diagram. -/
noncomputable def stalkDiagramDirectLimitCocone {I : Type u} [Preorder I]
    (F : I ⥤ CommRingCat.{u}) : Cocone F where
  pt := CommRingCat.of (stalkDiagramDirectLimit F)
  ι := NatTrans.mk
    (fun i => CommRingCat.ofHom
      (Ring.DirectLimit.of (G := fun i => ToType (F.obj i))
        (f := fun i j h => stalkDiagramMap F i j h) i))
    (by
      intro i j g
      apply ConcreteCategory.hom_ext
      intro x
      rw [Subsingleton.elim g (homOfLE g.le)]
      exact Ring.DirectLimit.of_f (G := fun i => ToType (F.obj i))
        (f := fun i j h => stalkDiagramMap F i j h) g.le x)

/-- The components of a cocone over a diagram of commutative rings are compatible with the
transition maps of that diagram. -/
theorem stalkDiagramDirectLimit_cocone_compat {I : Type u} [Preorder I]
    (F : I ⥤ CommRingCat.{u}) (s : Cocone F) (i j : I) (h : i ≤ j) (x : ToType (F.obj i)) :
    (s.ι.app j).hom (stalkDiagramMap F i j h x) = (s.ι.app i).hom x := by
  simpa only [ConcreteCategory.comp_apply, stalkDiagramMap] using
    congrArg (fun m => m.hom x) (s.w (homOfLE h))

/-- The ring map out of the algebraic direct limit induced by a cocone over the diagram. -/
noncomputable def stalkDiagramDirectLimitDesc {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ CommRingCat.{u}) (s : Cocone F) :
    stalkDiagramDirectLimit F →+* ToType s.pt :=
  Ring.DirectLimit.lift (fun i => ToType (F.obj i))
    (fun i j h => stalkDiagramMap F i j h) _ (fun i => (s.ι.app i).hom)
    (stalkDiagramDirectLimit_cocone_compat F s)

/-- The induced ring map out of the algebraic direct limit agrees with the cocone on each
summand. -/
theorem stalkDiagramDirectLimitDesc_of {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [DecidableEq I] (F : I ⥤ CommRingCat.{u}) (s : Cocone F) (i : I) (x : ToType (F.obj i)) :
    stalkDiagramDirectLimitDesc F s (Ring.DirectLimit.of _ _ i x) = (s.ι.app i).hom x :=
  Ring.DirectLimit.lift_of (P := ToType s.pt) (g := fun i => (s.ι.app i).hom)
    (Hg := stalkDiagramDirectLimit_cocone_compat F s) i x

/-- The algebraic direct limit of a diagram of commutative rings over a directed preorder is its
colimit. -/
noncomputable def stalkDiagramDirectLimitIsColimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ CommRingCat.{u}) :
    IsColimit (stalkDiagramDirectLimitCocone F) where
  desc s := CommRingCat.ofHom (stalkDiagramDirectLimitDesc F s)
  fac s i := by
    ext x
    exact stalkDiagramDirectLimitDesc_of F s i x
  uniq s m hm := by
    apply CommRingCat.hom_ext
    change m.hom = stalkDiagramDirectLimitDesc F s
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    exact (congrArg (fun n => n.hom x) (hm i)).trans (stalkDiagramDirectLimitDesc_of F s i x).symm

/-- The algebraic direct limit of a diagram of commutative rings over a directed preorder,
identified with the categorical colimit. -/
noncomputable def stalkDiagramDirectLimitIso {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ CommRingCat.{u}) :
    CommRingCat.of (stalkDiagramDirectLimit F) ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (stalkDiagramDirectLimitIsColimit F) (colimit.isColimit F)

/-- The stalk of a presheaf of commutative rings at a point, identified with the algebraic direct
limit of its sections over the open neighbourhoods of that point. -/
noncomputable def presheafStalkRingDirectLimitIso {X : TopCat.{u}} (O : X.Presheaf CommRingCat.{u})
    (x : X) :
    CommRingCat.of
        (stalkDiagramDirectLimit ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
          (OpenNhds.inclusion x).op ⋙ O)) ≅
      CommRingCat.of (O.stalk x) := by
  let e := CategoryTheory.orderDualEquivalence (OpenNhds x)
  let D := (OpenNhds.inclusion x).op ⋙ O
  let F := e.functor ⋙ D
  letI : DecidableEq (OrderDual (OpenNhds x)) := Classical.decEq _
  exact (stalkDiagramDirectLimitIso F) ≪≫ Functor.Final.colimitIso e.functor D

/-- The canonical iso from a colimit cocone over `e ⋙ D` to `colimit D` sends `ι i z` to the
colimit inclusion of `z`. -/
private theorem coconePointUniqueUpToIso_colimitIso_apply {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] {I J : Type*} [Category I] [Category J] (e : I ⥤ J)
    [e.Final] (D : J ⥤ C) [HasColimit D] [HasColimit (e ⋙ D)] {c : Cocone (e ⋙ D)}
    (hc : IsColimit c) (i : I) (z : ToType ((e ⋙ D).obj i)) (q : ToType c.pt)
    (hq : q = c.ι.app i z) :
    (hc.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫ Functor.Final.colimitIso e D).hom q =
      colimit.ι D (e.obj i) z := by
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply, hq]
  rw [← ConcreteCategory.comp_apply (c.ι.app i), IsColimit.comp_coconePointUniqueUpToIso_hom,
    ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (Functor.Final.ι_colimitIso_hom e D i) z

/-- The identification of the stalk of a presheaf of commutative rings with an algebraic direct
limit sends the image of a section over an open neighbourhood to its germ. -/
theorem presheafStalkRingDirectLimitIso_apply_of {X : TopCat.{u}} (F : X.Presheaf CommRingCat.{u})
    (x : X) (i : OrderDual (OpenNhds x))
    (z : ToType (((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
      (OpenNhds.inclusion x).op ⋙ F).obj i)) :
    (presheafStalkRingDirectLimitIso F x).hom.hom (Ring.DirectLimit.of _ _ i z) =
      F.germ ((OpenNhds.inclusion x).obj
          ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor.obj i).unop) x
        ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor.obj i).unop.2 z := by
  classical
  let e := CategoryTheory.orderDualEquivalence (OpenNhds x)
  exact coconePointUniqueUpToIso_colimitIso_apply e.functor ((OpenNhds.inclusion x).op ⋙ F)
    (stalkDiagramDirectLimitIsColimit _) i z _ rfl

/-! ### The stalk of a presheaf of abelian groups as a direct limit -/

/-- The direct limit of a diagram of abelian groups indexed by a preorder, taken as a direct limit
of modules over `ℤ`. -/
abbrev additiveDiagramDirectLimit {I : Type u} [Preorder I] [DecidableEq I]
    (F : I ⥤ AddCommGrpCat.{u}) :=
  Module.DirectLimit (R := ℤ) (fun i => ToType (F.obj i))
    (fun _ _ h => ((F.map (homOfLE h)).hom).toIntLinearMap)

/-- The direct limit of a diagram of abelian groups, as a cocone over that diagram. -/
noncomputable def additiveDiagramDirectLimitCocone {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) : Cocone F where
  pt := AddCommGrpCat.of (additiveDiagramDirectLimit F)
  ι := NatTrans.mk
    (fun i => AddCommGrpCat.ofHom
      (Module.DirectLimit.of ℤ I (fun i => ToType (F.obj i))
        (fun _ _ h => ((F.map (homOfLE h)).hom).toIntLinearMap) i).toAddMonoidHom)
    (by
      intro i j g
      ext x
      rw [Subsingleton.elim g (homOfLE g.le)]
      exact Module.DirectLimit.of_f)

/-- The components of a cocone over a diagram of abelian groups are compatible with the transition
maps of that diagram, viewed as maps of `ℤ`-modules. -/
theorem additiveDiagramDirectLimit_cocone_compat {I : Type u} [Preorder I]
    (F : I ⥤ AddCommGrpCat.{u}) (s : Cocone F) (i j : I) (hij : i ≤ j) (x : ToType (F.obj i)) :
    (s.ι.app j).hom.toIntLinearMap (((F.map (homOfLE hij)).hom).toIntLinearMap x) =
      (s.ι.app i).hom.toIntLinearMap x :=
  congrArg (fun f : F.obj i ⟶ s.pt => f.hom x) (s.w (homOfLE hij))

/-- The map out of the direct limit of a diagram of abelian groups induced by a cocone over the
diagram.

It is recorded as a map of additive groups rather than of `ℤ`-modules because the two `ℤ`-module
structures available on the direct limit of a diagram of abelian groups — the one carried by the
direct limit and the one coming from its additive group — are equal but not syntactically so, and
identifying them is expensive on a quotient of a direct sum. -/
noncomputable def additiveDiagramDirectLimitDesc {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) (s : Cocone F) :
    additiveDiagramDirectLimit F →+ ToType s.pt :=
  (Module.DirectLimit.lift ℤ I (fun i => ToType (F.obj i))
    (fun _ _ h => ((F.map (homOfLE h)).hom).toIntLinearMap)
    (fun i => (s.ι.app i).hom.toIntLinearMap)
    (additiveDiagramDirectLimit_cocone_compat F s)).toAddMonoidHom

/-- The defining equation of `additiveDiagramDirectLimitDesc`, at an unspecified element of the
direct limit. Stating it separately keeps every use of it a rewrite along a syntactic equation:
the direct limit is a quotient of a direct sum, so asking the elaborator to evaluate the induced
map on a single summand by unfolding is far more expensive than rewriting with
`Module.DirectLimit.lift_of`. -/
theorem additiveDiagramDirectLimitDesc_apply {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) (s : Cocone F)
    (z : additiveDiagramDirectLimit F) :
    additiveDiagramDirectLimitDesc F s z =
      Module.DirectLimit.lift ℤ I (fun i => ToType (F.obj i))
        (fun _ _ h => ((F.map (homOfLE h)).hom).toIntLinearMap)
        (fun i => (s.ι.app i).hom.toIntLinearMap)
        (additiveDiagramDirectLimit_cocone_compat F s) z :=
  rfl

/-- The induced map out of the direct limit of a diagram of abelian groups agrees with the cocone
on each summand. -/
theorem additiveDiagramDirectLimitDesc_of {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) (s : Cocone F) (i : I)
    (x : ToType (F.obj i)) :
    additiveDiagramDirectLimitDesc F s
        (Module.DirectLimit.of ℤ I (fun i => ToType (F.obj i))
          (fun _ _ h => ((F.map (homOfLE h)).hom).toIntLinearMap) i x) =
      (s.ι.app i).hom x := by
  rw [additiveDiagramDirectLimitDesc_apply, Module.DirectLimit.lift_of]
  rfl

/-- The direct limit of a diagram of abelian groups over a directed preorder is its colimit. -/
noncomputable def additiveDiagramDirectLimitIsColimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) :
    IsColimit (additiveDiagramDirectLimitCocone F) where
  desc s := AddCommGrpCat.ofHom (additiveDiagramDirectLimitDesc F s)
  fac s i := by
    ext x
    exact additiveDiagramDirectLimitDesc_of F s i x
  uniq s m hm := by
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        exact (congrArg (fun f => f.hom x) (hm i)).trans
          (additiveDiagramDirectLimitDesc_of F s i x).symm

/-- The direct limit of a diagram of abelian groups over a directed preorder, identified with the
categorical colimit. -/
noncomputable def additiveDiagramDirectLimitIso {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] [DecidableEq I] (F : I ⥤ AddCommGrpCat.{u}) :
    AddCommGrpCat.of (additiveDiagramDirectLimit F) ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (additiveDiagramDirectLimitIsColimit F)
    (colimit.isColimit F)

/-- The stalk of a presheaf of abelian groups at a point, identified with the direct limit of its
sections over the open neighbourhoods of that point. -/
noncomputable def presheafStalkAdditiveDirectLimitIso {X : TopCat.{u}}
    (F : X.Presheaf AddCommGrpCat.{u}) (x : X) [DecidableEq (OrderDual (OpenNhds x))] :
    AddCommGrpCat.of
        (additiveDiagramDirectLimit ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
          (OpenNhds.inclusion x).op ⋙ F)) ≅
      AddCommGrpCat.of (F.stalk x) := by
  let e := CategoryTheory.orderDualEquivalence (OpenNhds x)
  let D := (OpenNhds.inclusion x).op ⋙ F
  let G := e.functor ⋙ D
  exact (additiveDiagramDirectLimitIso G) ≪≫ Functor.Final.colimitIso e.functor D

/-- The identification of the stalk of a presheaf of abelian groups with a direct limit sends the
image of a section over an open neighbourhood to its germ. -/
theorem presheafStalkAdditiveDirectLimitIso_apply_of {X : TopCat.{u}}
    (F : X.Presheaf AddCommGrpCat.{u}) (x : X) [DecidableEq (OrderDual (OpenNhds x))]
    (i : OrderDual (OpenNhds x))
    (z : ToType (((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
      (OpenNhds.inclusion x).op ⋙ F).obj i)) :
    (presheafStalkAdditiveDirectLimitIso F x).hom.hom
        (Module.DirectLimit.of ℤ (OrderDual (OpenNhds x))
          (fun i => ToType (((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
            (OpenNhds.inclusion x).op ⋙ F).obj i))
          (fun _ _ h => ((((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor ⋙
            (OpenNhds.inclusion x).op ⋙ F).map (homOfLE h)).hom).toIntLinearMap) i z) =
      TopCat.Presheaf.germ F
        ((OpenNhds.inclusion x).obj
          ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor.obj i).unop) x
        ((CategoryTheory.orderDualEquivalence (OpenNhds x)).functor.obj i).unop.2 z := by
  classical
  let e := CategoryTheory.orderDualEquivalence (OpenNhds x)
  exact coconePointUniqueUpToIso_colimitIso_apply e.functor ((OpenNhds.inclusion x).op ⋙ F)
    (additiveDiagramDirectLimitIsColimit _) i z _ rfl

/-! ### The module of differentials of a colimit algebra -/

/-- The maps from the modules of Kähler differentials of a directed system of algebras to the
module of Kähler differentials of the colimit algebra are compatible with the transition maps of
the system. -/
theorem omegaToColim_omegaTrans {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {R S : I → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j)
    (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j) (hsq : Stacks.KaehlerDifferential.Colimit.IsCompatible fR
      fS)
    (l k : I) (hlk : l ≤ k) (z : Ω[S l⁄R l]) :
    Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq k
      (Stacks.KaehlerDifferential.Colimit.omegaTrans fR fS hsq l k hlk z) =
      Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq l z := by
  have hz : z ∈ Submodule.span (S l) (Set.range (KaehlerDifferential.D (R l) (S l))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      simp only [Stacks.KaehlerDifferential.Colimit.omegaTrans,
        Stacks.KaehlerDifferential.Colimit.omegaToColim, Stacks.KaehlerDifferential.Colimit.sqMap_D]
      congr 1
      exact Ring.DirectLimit.of_f hlk _
  | zero => simp
  | add p q _ _ hp hq => rw [map_add, map_add, map_add, hp, hq]
  | smul d p _ hp =>
      simp only [Stacks.KaehlerDifferential.Colimit.omegaTrans,
        Stacks.KaehlerDifferential.Colimit.omegaToColim,
        Stacks.KaehlerDifferential.Colimit.sqMap_smul] at hp ⊢
      rw [hp]
      congr 1
      exact Ring.DirectLimit.of_f hlk _

/-- The defining equation of the comparison map `Stacks.KaehlerDifferential.Colimit.Theta`, at an
  unspecified element
of the colimit. Stating it separately keeps every use of it a rewrite along a syntactic equation:
the two `ℤ`-module structures on the colimit — the one carried by the direct limit and the one
coming from its additive group — are equal but not syntactically so, which blocks the direct use
of `Module.DirectLimit.lift_of` on an element of the colimit. -/
theorem omegaColimTheta_apply {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    [DecidableEq I] {R S : I → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j)
    (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j) (hsq : Stacks.KaehlerDifferential.Colimit.IsCompatible fR
      fS)
    (z : Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq) :
    Stacks.KaehlerDifferential.Colimit.Theta fR fS hsq z =
      Module.DirectLimit.lift ℤ I (fun i => Ω[S i⁄R i])
        (Stacks.KaehlerDifferential.Colimit.omegaTrans fR fS hsq)
        (Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq)
        (fun l k hlk z => omegaToColim_omegaTrans fR fS hsq l k hlk z) z :=
  rfl

/-- The comparison map sends the image of a module of Kähler differentials of the system to the
differentials of the colimit algebra by the map of that stage. -/
theorem omegaColimTheta_ofΩ {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    [DecidableEq I] {R S : I → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j)
    (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j) (hsq : Stacks.KaehlerDifferential.Colimit.IsCompatible fR
      fS) (i : I)
    (y : Ω[S i⁄R i]) :
    Stacks.KaehlerDifferential.Colimit.Theta fR fS hsq (Stacks.KaehlerDifferential.Colimit.ofΩ fR fS
      hsq i y) =
      Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq i y := by
  rw [show Stacks.KaehlerDifferential.Colimit.ofΩ fR fS hsq i y =
      Module.DirectLimit.of ℤ I (fun i => Ω[S i⁄R i]) (Stacks.KaehlerDifferential.Colimit.omegaTrans
        fR fS hsq) i y
      from rfl, omegaColimTheta_apply, Module.DirectLimit.lift_of]

/-- The comparison map from the colimit of the modules of Kähler differentials of a directed
system of algebras to the module of Kähler differentials of the colimit algebra, as a map linear
over the colimit ring. -/
noncomputable def omegaColimLinearMap {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    [DecidableEq I] {R S : I → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j)
    (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j) (hsq : Stacks.KaehlerDifferential.Colimit.IsCompatible fR
      fS)
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    letI := Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq
    letI : Module (Stacks.KaehlerDifferential.Colimit.Sinf fS)
      (Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq) :=
      Stacks.KaehlerDifferential.Colimit.omegaColimModule fR fS hsq hdirS
    Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq
      →ₗ[Stacks.KaehlerDifferential.Colimit.Sinf fS]
      @KaehlerDifferential (Stacks.KaehlerDifferential.Colimit.Rinf fR)
        (Stacks.KaehlerDifferential.Colimit.Sinf fS) _ _
        (Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq) := by
  classical
  letI := Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq
  letI : Module (Stacks.KaehlerDifferential.Colimit.Sinf fS)
    (Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq) :=
    Stacks.KaehlerDifferential.Colimit.omegaColimModule fR fS hsq hdirS
  let T := Stacks.KaehlerDifferential.Colimit.Theta fR fS hsq
  have hT : ∀ (i : I) (y : Ω[S i⁄R i]),
      T (Stacks.KaehlerDifferential.Colimit.ofΩ fR fS hsq i y) =
        Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq i y :=
    omegaColimTheta_ofΩ fR fS hsq
  have hint : ∀ (i : I) (c : S i) (ξ : Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq),
      T (Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i c • ξ) =
        Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) i c • T ξ := by
    intro i c ξ
    refine ξ.induction_on fun j x => ?_
    change T (Stacks.KaehlerDifferential.Colimit.actFun fR fS hsq hdirS _
      (Stacks.KaehlerDifferential.Colimit.ofΩ fR fS hsq j x)) = _
    rw [Stacks.KaehlerDifferential.Colimit.actFun_of]
    obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    rw [Stacks.KaehlerDifferential.Colimit.actLevel_ofΩ_eq fR fS hsq hdirS i c j x him hjm, hT]
    have h1 : Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq m
          (fS him c • Stacks.KaehlerDifferential.Colimit.omegaTrans fR fS hsq j m hjm x) =
        Ring.DirectLimit.of S (fun _ _ h => (fS h : S _ → S _)) m (fS him c) •
          Stacks.KaehlerDifferential.Colimit.omegaToColim fR fS hsq m
            (Stacks.KaehlerDifferential.Colimit.omegaTrans fR fS hsq j m hjm x) :=
      Stacks.KaehlerDifferential.Colimit.sqMap_smul (R m) (S m)
        (Stacks.KaehlerDifferential.Colimit.Rinf fR) (Stacks.KaehlerDifferential.Colimit.Sinf fS) _
          _ _
        (fS him c) _
    rw [h1, omegaToColim_omegaTrans fR fS hsq j m hjm x, Ring.DirectLimit.of_f him]
    change _ = _ • T (Stacks.KaehlerDifferential.Colimit.ofΩ fR fS hsq j x)
    rw [hT]
  exact
    { toFun := T
      map_add' := T.map_add
      map_smul' s ξ := s.induction_on fun i c => hint i c ξ }

/-- **Stacks Project, Tag 031G.** The module of Kähler differentials of a colimit of a directed
system of algebras is the colimit of the modules of Kähler differentials, linearly over the
colimit ring. -/
noncomputable def omegaColimLinearEquiv {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    [DecidableEq I] {R S : I → Type u} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (fR : ∀ ⦃i j⦄, i ≤ j → R i →+* R j)
    (fS : ∀ ⦃i j⦄, i ≤ j → S i →+* S j) (hsq : Stacks.KaehlerDifferential.Colimit.IsCompatible fR
      fS)
    (hdirS : DirectedSystem S (fun _ _ h => (fS h : S _ → S _))) :
    letI := Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq
    letI : Module (Stacks.KaehlerDifferential.Colimit.Sinf fS)
      (Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq) :=
      Stacks.KaehlerDifferential.Colimit.omegaColimModule fR fS hsq hdirS
    Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq
      ≃ₗ[Stacks.KaehlerDifferential.Colimit.Sinf fS]
      @KaehlerDifferential (Stacks.KaehlerDifferential.Colimit.Rinf fR)
        (Stacks.KaehlerDifferential.Colimit.Sinf fS) _ _
        (Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq) := by
  letI := Stacks.KaehlerDifferential.Colimit.alginf fR fS hsq
  letI : Module (Stacks.KaehlerDifferential.Colimit.Sinf fS)
    (Stacks.KaehlerDifferential.Colimit.OmegaColim fR fS hsq) :=
    Stacks.KaehlerDifferential.Colimit.omegaColimModule fR fS hsq hdirS
  exact LinearEquiv.ofBijective (omegaColimLinearMap fR fS hsq hdirS)
    (Stacks.KaehlerDifferential.Colimit.main_theorem_031g fR fS hsq hdirS)

/-! ### Transport of Kähler differentials along ring equivalences -/

/-- If the algebra maps `A → A'` and `A' → A` are mutually inverse, then the maps of Kähler
differentials `Ω[A⁄R] → Ω[A'⁄R'] → Ω[A⁄R]` compose to the identity. -/
theorem kaehlerDifferential_map_map_of_comp_eq_id {R R' A A' : Type u} [CommRing R] [CommRing R']
    [CommRing A] [CommRing A'] [Algebra R A] [Algebra R' A'] [Algebra R R'] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] [SMulCommClass R' A A']
    [Algebra R' R] [Algebra A' A] [Algebra R' A] [IsScalarTower R' A' A] [IsScalarTower R' R A]
    [SMulCommClass R A' A] (hA : ∀ a : A, algebraMap A' A (algebraMap A A' a) = a)
    (z : Ω[A⁄R]) :
    KaehlerDifferential.map R' R A' A (KaehlerDifferential.map R R' A A' z) = z := by
  have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, hA]
  | zero => simp
  | add z w _ _ hz hw => simp [hz, hw]
  | smul c z _ hz =>
      rw [LinearMap.map_smul, ← algebraMap_smul A' c (KaehlerDifferential.map R R' A A' z),
        LinearMap.map_smul, hz, ← algebraMap_smul A (algebraMap A A' c) z, hA]

/-- A pair of ring equivalences `R ≃+* R'` and `A ≃+* A'` commuting with the algebra maps
transports the module of Kähler differentials of `A` over `R` to that of `A'` over `R'`. -/
noncomputable def kaehlerDifferentialRingEquiv {R R' A A' : Type u} [CommRing R] [CommRing R']
    [CommRing A] [CommRing A'] [Algebra R A] [Algebra R' A'] (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    letI : Algebra A A' := eA.toRingHom.toAlgebra
    letI : Module A (Ω[A'⁄R']) := Module.compHom _ eA.toRingHom
    Ω[A⁄R] ≃ₗ[A] Ω[A'⁄R'] := by
  letI : Algebra A A' := eA.toRingHom.toAlgebra
  letI : Algebra R R' := eR.toRingHom.toAlgebra
  letI : Algebra R A' := (eA.toRingHom.comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq h
  have : SMulCommClass R' A A' := by
    constructor
    intro r a z
    simp only [Algebra.smul_def]
    ring
  letI : Module A (Ω[A'⁄R']) := Module.compHom _ eA.toRingHom
  let f : Ω[A⁄R] →ₗ[A] Ω[A'⁄R'] := KaehlerDifferential.map R R' A A'
  letI : Algebra A' A := eA.symm.toRingHom.toAlgebra
  letI : Algebra R' R := eR.symm.toRingHom.toAlgebra
  letI : Algebra R' A := ((algebraMap R A).comp eR.symm.toRingHom).toAlgebra
  have : IsScalarTower R' A' A := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    apply eA.injective
    change eA ((algebraMap R A) (eR.symm r)) = eA (eA.symm ((algebraMap R' A') r))
    rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]
  have : IsScalarTower R' R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : SMulCommClass R A' A := by
    constructor
    intro r a z
    simp only [Algebra.smul_def]
    ring
  letI : Module A' (Ω[A⁄R]) := Module.compHom _ eA.symm.toRingHom
  let g : Ω[A'⁄R'] →ₗ[A'] Ω[A⁄R] := KaehlerDifferential.map R' R A' A
  exact { f with
    invFun := g
    left_inv := kaehlerDifferential_map_map_of_comp_eq_id fun a => eA.symm_apply_apply a
    right_inv := kaehlerDifferential_map_map_of_comp_eq_id fun a => eA.apply_symm_apply a }

/-- Transport of Kähler differentials along a commuting pair of ring equivalences sends the
differential of an element to the differential of its image. -/
theorem kaehlerDifferentialRingEquiv_D {R R' A A' : Type u} [CommRing R] [CommRing R']
    [CommRing A] [CommRing A'] [Algebra R A] [Algebra R' A'] (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r)) (a : A) :
    kaehlerDifferentialRingEquiv eR eA h (KaehlerDifferential.D R A a) =
      KaehlerDifferential.D R' A' (eA a) := by
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let : Algebra R R' := eR.toRingHom.toAlgebra
  let : Algebra R A' := (eA.toRingHom.comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq h
  simp only [kaehlerDifferentialRingEquiv]
  exact KaehlerDifferential.map_D R R' A A' a

/-! ### Stalks of morphisms of presheaves of modules -/

/-- The stalk map of a morphism of presheaves of modules over a presheaf of commutative rings, as
a map linear over the stalk of that presheaf of rings. -/
noncomputable def presheafModuleStalkLinearMapCommRing {X : TopCat.{u}}
    {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (f : M ⟶ N) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x →ₗ[R.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)
  map_add' _ _ := map_add _ _ _
  map_smul' := by
    intro r m
    obtain ⟨Ur, hUr, sr, hsr⟩ := TopCat.Presheaf.exists_germ_eq R r
    obtain ⟨Um, hUm, sm, hsm⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) M.presheaf m
    let U : Opens X := Ur ⊓ Um
    have hxU : x ∈ U := ⟨hUr, hUm⟩
    let iUr : U ⟶ Ur := homOfLE inf_le_left
    let iUm : U ⟶ Um := homOfLE inf_le_right
    let rU : R.obj (op U) := (R.map iUr.op).hom sr
    let mU : M.obj (op U) := (M.map iUm.op).hom sm
    have hgr : R.germ U x hxU rU = r := by
      rw [show rU = (R.map iUr.op).hom sr from rfl,
        TopCat.Presheaf.germ_res_apply R iUr x hxU sr, hsr]
    have hgm : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hxU mU = m := by
      change (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hxU).hom mU = m
      rw [show mU = (M.presheaf.map iUm.op).hom sm from rfl,
        TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.presheaf iUm x hxU sm]
      exact hsm
    have hnat : ∀ s : M.obj (op U),
        ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
            ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f))
          (TopCat.Presheaf.germ (C := Ab.{u}) M.presheaf U x hxU s) =
        TopCat.Presheaf.germ (C := Ab.{u}) N.presheaf U x hxU ((f.app (op U)).hom s) :=
      fun s => TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hxU
        ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f) s
    rw [← hgr, ← hgm, ← PresheafOfModules.germ_smul M x U hxU rU mU, hnat (rU • mU), hnat mU,
      (f.app (op U)).hom.map_smul rU mU]
    exact PresheafOfModules.germ_smul N x U hxU rU ((f.app (op U)).hom mU)

/-- The stalk map of a morphism of presheaves of modules carries the germ of a section to the germ
of its image. -/
theorem presheafModuleStalkLinearMapCommRing_germ {X : TopCat.{u}}
    {R : X.Presheaf CommRingCat.{u}}
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (f : M ⟶ N) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    presheafModuleStalkLinearMapCommRing M N f x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) N.presheaf U x hx ((f.app (op U)).hom m) := by
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx m) = _
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f) m

/-! ### Transfer of linearity along a ring equivalence of the scalars -/

/-- A linear equivalence is linear over either of two isomorphic rings of scalars: if `M` and `N`
are modules over both `R` and `S`, and in each case the `R`-action is the `S`-action read through a
ring equivalence `eRS : R ≃+* S`, then an `R`-linear equivalence between them is an `S`-linear
equivalence. The hypotheses `hM` and `hN` say that the two actions correspond; for an `R`-module
structure obtained as `Module.compHom _ eRS.toRingHom` they hold by definition. -/
noncomputable def linearEquivOfRingEquivScalars {R S : Type u} [CommRing R] [CommRing S]
    (eRS : R ≃+* S) {M N : Type u} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Module S M] [Module S N] (hM : ∀ (r : R) (m : M), r • m = eRS r • m)
    (hN : ∀ (r : R) (n : N), r • n = eRS r • n) (f : M ≃ₗ[R] N) :
    M ≃ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by
    have h1 : s • m = (eRS.symm s : R) • m := by rw [hM, RingEquiv.apply_symm_apply]
    have h2 : (eRS.symm s : R) • f m = s • f m := by rw [hN, RingEquiv.apply_symm_apply]
    rw [RingHom.id_apply, h1, f.map_smul, h2]
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

/-- The `S`-linear equivalence `linearEquivOfRingEquivScalars eRS hM hN f` agrees with `f` as a
function. -/
@[simp]
theorem linearEquivOfRingEquivScalars_apply {R S : Type u} [CommRing R] [CommRing S]
    (eRS : R ≃+* S) {M N : Type u} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Module S M] [Module S N] (hM : ∀ (r : R) (m : M), r • m = eRS r • m)
    (hN : ∀ (r : R) (n : N), r • n = eRS r • n) (f : M ≃ₗ[R] N) (m : M) :
    linearEquivOfRingEquivScalars eRS hM hN f m = f m :=
  rfl

/-! ### The stalk of the sheaf of relative differentials -/

/-- The stalk of the sheaf of relative differentials is a module over the stalk of the structure
sheaf. This is the module structure of `Mathlib.Algebra.Category.ModuleCat.Stalk`, recorded at the
spelling of the ring sheaf that the sheaf of relative differentials carries: instance search does
not identify `underlyingRingSheaf O₂` with the composition of `O₂` with the forgetful functor to
rings on its own. -/
noncomputable instance moduleStalkModuleOfDifferentials {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X} (phi : O₁ ⟶ O₂) (x : X) :
    Module (ToType (O₂.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (moduleOfDifferentials.{u, u, u} phi).val.presheaf x)) :=
  inferInstanceAs (Module (ToType (O₂.presheaf.stalk x))
    (ToType (TopCat.Presheaf.stalk
      (show PresheafOfModules.{u} (O₂.presheaf ⋙ forget₂ CommRingCat RingCat) from
        (moduleOfDifferentials.{u, u, u} phi).val).presheaf x)))

end AlgebraicGeometry.SheafOfModules
