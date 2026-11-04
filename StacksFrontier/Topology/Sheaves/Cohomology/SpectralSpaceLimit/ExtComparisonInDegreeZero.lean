module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.DegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.PullbackAsAMorphismOfDeltaFunctors

/-!
# The `Ext`-side comparison map is the map prescribed by Tag 0A37

`Stacks.Cohomology.AbelianColimit.H'spacePullback` is the comparison arrow of Stacks 0A37 on the
`Ext` side, and `Stacks.Cohomology.AbelianColimit.H'spacePullback_comp_H'δ` proves that those
arrows commute with the connecting morphism, so that they are the components of a morphism of
δ-functors.  What is left open there is the identification of those arrows with the arrows
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` prescribes, which are built from a lift of
injective resolutions.  **This file supplies the
degree-zero case of that identification, for the canonical identifications of cohomology with
right-derived sections.**

Two points about the shape of the statement.

First, the identifications `Sheaf.H' F p U ≅ ((sections X U).rightDerived p).obj F` that
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` takes as parameters are *arbitrary*; an
arbitrary one satisfies no relation to anything, so the identification cannot be proved for it.
The ones used here are the components of
`ModuleSheafCohomology.extFunctorObjIsoRightDerived`, which is canonical, carries a
formula in every degree, and -- being the transporting isomorphism of
`Stacks.Cohomology.AbelianColimit.rightDerivedSectionsDeltaFunctor` -- is by construction an
isomorphism of δ-functors (`CategoryTheory.DeltaFunctor.ofIsoIso`).  This is a strictly better
normalization than the `CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` form used in
`Stacks.Cohomology.AbelianColimit.H'isoRightDerivedDelta`, which is pinned only by its
degree-zero component and gives no formula at all in positive degree.

Second, `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` compares cohomology of a sheaf `G` on
the target with
cohomology of a sheaf `F` on the source along an `f`-map `φ : G ⟶ f_* F`, whereas
`H'spacePullback` lands in the cohomology of the inverse image `f⁻¹ G`.  The arrow to compare is
therefore `H'spacePullback` followed by the map induced by the adjoint `f⁻¹ G ⟶ F` of `φ`; that
composite is `extSpacePullbackMap` below.

## Main definitions

* `coyonedaMapComp`: for `b : XA ⟶ F.obj XB` with `F` additive, the natural transformation
  `Hom(XB, -) ⟶ Hom(XA, F -)` given by `t ↦ b ≫ F.map t`.  It is the degree-zero shadow of
  `Stacks.Cohomology.ModuleComparison.extMapComp`.
* `derivedSectionsMap`: the same transformation read through two corepresentations, as a map
  `HB ⟶ F ⋙ HA` of the corepresented functors.  For sections of abelian sheaves and the inverse
  image along a continuous map this is the pullback map on sections.
* `sheafPushforward` and `sheafAdjunction`: the direct image and the inverse-image/direct-image
  adjunction, at the spelling of the site of opens.
* `H'isoRightDerivedSections`: the canonical identification of native cohomology over an open
  with the right-derived functors of sections, in every degree.
* `extSpacePullbackMap`: the `Ext`-side comparison arrow of Stacks 0A37 attached to an `f`-map,
  namely `H'spacePullback` followed by the map induced by the adjoint of the `f`-map.

## Main results

* `extMapComp_conj_zero`: **in degree zero the `Ext`-side comparison map is the map on the
  corepresented functors.**  This is
  `Stacks.Cohomology.ModuleComparison.extZeroIsoCoyoneda_inv_comp_extMapComp` conjugated by the
  degree-zero value of `ModuleSheafCohomology.extFunctorObjIsoRightDerived`.
* `repU_inv_freeOfOpenPullbackMap`: the defining property of
  `Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap`, read through the corepresentation of
  sections: it is the tautological section carried across the adjunction unit and restricted.
* `derivedSectionsMap_comp_eq_sectionsRestrictMap`: **the pullback map on sections, followed by
  an `f`-map read through the adjunction, is the `f`-map on sections followed by restriction.**
  This is the one computation that connects the `Ext`-side description of the comparison arrows
  to the `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` description, and it is what the
  degree-zero identification runs on.
* `extSpacePullbackMap_zero_eq`: **in degree zero the `Ext`-side comparison arrow is the arrow
  prescribed by Tag 0A37**, for the canonical identifications.
* `isCohomologyMap_extSpacePullbackMap_zero`: the same statement in the form
  `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` asks for.

## Implementation notes

The spelling crossing between `TopCat.Sheaf C X` and `Sheaf (Opens.grothendieckTopology X) C`
costs real heartbeats and not merely elegance.  Concretely: the naturality
of the corepresentation of sections at the direct image of a morphism, *stated* with
`TopCat.Sheaf.pushforward`, exhausts the default `whnf` budget, while the same term with the
functor ascribed to the site spelling by the `sheafPushforward` abbreviation elaborates at once.
So the direct image and the adjunction are given abbreviations here exactly as
`Stacks.Cohomology.AbelianColimit.sheafPullback` gives one to the inverse image, and every
statement below is at the site spelling.  For the same reason the proof of
`derivedSectionsMap_comp_eq_sectionsRestrictMap` lets Lean infer the types of its naturality
steps instead of ascribing them: an ascribed naturality square is what exhausted the budget.

What is *not* here is positive degree, and it is **no longer open**: it is
`Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap` in
`StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInPositiveDegree`, which
is `isCohomologyMap_extSpacePullbackMap_zero` below with `0` replaced by an arbitrary `p`.  Its
homological-algebra input is the resolution-level reading of
`Stacks.Cohomology.ModuleComparison.extMapComp` in degree `n + 1`, read through a corepresentation
of the *source* functor rather than through
`Stacks.Cohomology.ModuleComparison.compCorepresentation` (which does not exist here, because
`Hom(freeOfOpen V, -)` is not `Hom(freeOfOpen U, f⁻¹ -)`), namely
`Stacks.Cohomology.ExtComparison.extMapComp_conj_succ`; the instantiation that turns it into the
statement above is in that same module.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ModuleSheafCohomology
open Stacks.Cohomology.ModuleComparison

namespace Stacks.Cohomology.ExtComparison

/-! ### Two reassociation helpers

`Mathlib.Tactic.Reassoc`'s `reassoc_of%` would do this, but it runs a `simp` over the
hypothesis, and that mints congruence lemmas in the namespaces of every constant the hypothesis
mentions -- here `Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap` and
`Stacks.Cohomology.SpectralLimit.sectionsRestrictMap`, i.e. two other modules'.  These two
helpers are stated in an abstract category, so no foreign constant is traversed. -/

section Reassoc

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- Composing an equality of morphisms on the right. -/
theorem whiskerRightEq {A B W : C} {p q : A ⟶ B} (hpq : p = q) (k : B ⟶ W) :
    p ≫ k = q ≫ k := by
  rw [hpq]

/-- Reassociating a two-fold composite against a further morphism. -/
theorem assoc₂ {A B D W : C} (a : A ⟶ B) (b : B ⟶ D) (k : D ⟶ W) :
    (a ≫ b) ≫ k = a ≫ b ≫ k :=
  Category.assoc a b k

/-- Reassociating a three-fold composite against a further morphism. -/
theorem assoc₃ {A B D E W : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (k : E ⟶ W) :
    (a ≫ b ≫ c) ≫ k = a ≫ b ≫ c ≫ k := by
  rw [Category.assoc, Category.assoc]

end Reassoc

/-! ### The degree-zero shadow of the `Ext`-side comparison map -/

section Coyoneda

universe w uA uB

variable {A : Type uA} [Category.{w} A] [Abelian A]
  {B : Type uB} [Category.{w} B] [Abelian B]
  (F : B ⥤ A) [F.Additive] (XA : A) (XB : B) (b : XA ⟶ F.obj XB)

/-- **The degree-zero shadow of `Stacks.Cohomology.ModuleComparison.extMapComp`**: for
`b : XA ⟶ F.obj XB` and an additive `F`, the natural transformation
`Hom(XB, -) ⟶ Hom(XA, F -)` sending `t` to `b ≫ F.map t`.  Naturality is associativity. -/
def coyonedaMapComp :
    preadditiveCoyoneda.obj (op XB) ⟶ F ⋙ preadditiveCoyoneda.obj (op XA) where
  app Z := AddCommGrpCat.ofHom
    { toFun := fun t => b ≫ F.map (t : XB ⟶ Z)
      map_zero' :=
        (congrArg (fun g => b ≫ g) (CategoryTheory.Functor.map_zero F XB Z)).trans
          Limits.comp_zero
      map_add' := fun t t' =>
        (congrArg (fun g => b ≫ g)
            (CategoryTheory.Functor.map_add (F := F) (f := (t : XB ⟶ Z))
              (g := (t' : XB ⟶ Z)))).trans
          (Preadditive.comp_add _ _ _ b (F.map (t : XB ⟶ Z)) (F.map (t' : XB ⟶ Z))) }
  naturality Z Z' g := by
    ext t
    exact (congrArg (fun u => b ≫ u) (F.map_comp (t : XB ⟶ Z) g)).trans
      (Category.assoc b (F.map (t : XB ⟶ Z)) (F.map g)).symm

/-- `coyonedaMapComp` on a morphism. -/
theorem coyonedaMapComp_app_apply (Z : B) (t : XB ⟶ Z) :
    (coyonedaMapComp F XA XB b).app Z t = b ≫ F.map t :=
  rfl

/-- `coyonedaMapComp` recovers `b` from the identity, which is what identifies it with the
degree-zero component of `Stacks.Cohomology.ModuleComparison.extMapComp`. -/
theorem coyonedaMapComp_app_id : (coyonedaMapComp F XA XB b).app XB (𝟙 XB) = b :=
  (congrArg (fun u => b ≫ u) (F.map_id XB)).trans (Category.comp_id b)

end Coyoneda

/-! ### The degree-zero reading of the `Ext`-side comparison map -/

section DegreeZero

universe w uA uB

variable {A : Type uA} [Category.{w} A] [Abelian A] [HasExt.{w} A] [HasInjectiveResolutions A]
  {B : Type uB} [Category.{w} B] [Abelian B] [HasExt.{w} B] [HasInjectiveResolutions B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (HA : A ⥤ Ab.{w}) [HA.Additive] [PreservesFiniteLimits HA]
  (XA : A) (αA : HA ≅ preadditiveCoyoneda.obj (op XA))
  (HB : B ⥤ Ab.{w}) [HB.Additive] [PreservesFiniteLimits HB]
  (XB : B) (αB : HB ≅ preadditiveCoyoneda.obj (op XB))
  (b : XA ⟶ F.obj XB)

/-- **The map on the corepresented functors attached to `b`**: `coyonedaMapComp` read through
the two corepresentations.  For sections of abelian sheaves over two opens and the inverse image
along a continuous map, this is the pullback map on sections. -/
def derivedSectionsMap : HB ⟶ F ⋙ HA :=
  αB.hom ≫ coyonedaMapComp F XA XB b ≫ Functor.whiskerLeft F αA.inv

/-- **In degree zero the `Ext`-side comparison map is the map on the corepresented functors.**
Both identifications of `Ext` with right-derived functors are, in degree zero, the
corepresentation followed by left exactness, so after cancelling those the claim is
`Stacks.Cohomology.ModuleComparison.extZeroIsoCoyoneda_inv_comp_extMapComp`. -/
theorem extMapComp_conj_zero :
    (extFunctorObjIsoRightDerived HB XB αB 0).inv ≫ extMapComp F b 0 ≫
        Functor.whiskerLeft F (extFunctorObjIsoRightDerived HA XA αA 0).hom =
      HB.rightDerivedZeroIsoSelf.hom ≫ derivedSectionsMap F HA XA αA HB XB αB b ≫
        Functor.whiskerLeft F HA.toRightDerivedZero := by
  have hb := extZeroIsoCoyoneda_inv_comp_extMapComp_assoc F (coyonedaMapComp F XA XB b)
    (Functor.whiskerLeft F αA.inv ≫ Functor.whiskerLeft F HA.rightDerivedZeroIsoSelf.inv)
  rw [coyonedaMapComp_app_id] at hb
  rw [extFunctorObjIsoRightDerived_zero, extFunctorObjIsoRightDerived_zero, derivedSectionsMap,
    ← Functor.rightDerivedZeroIsoSelf_inv HA]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [hb]

end DegreeZero

/-! ### The direct image and the adjunction at the spelling of the site of opens -/

namespace Spaces

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **The direct image of abelian sheaves along a continuous map**, read at the spelling of the
site of opens, which is the one `H'functor` and `abSections` are stated in.  The ascription is
what keeps the naturality squares below inside one spelling; see the implementation notes. -/
abbrev sheafPushforward :
    Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

/-- **The inverse-image/direct-image adjunction**, at the spelling of the site of opens. -/
def sheafAdjunction :
    Stacks.Cohomology.AbelianColimit.sheafPullback f ⊣ sheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f

end Spaces

section Bridge

universe u

/-- **The `Ext`-side pullback map on native cohomology is
`Stacks.Cohomology.ModuleComparison.extMapComp`**, read at a sheaf.  Both are "act with the
exact functor on `Ext`-classes, then precompose with the map of corepresenting objects", and they
agree by unfolding.  Stated at a sheaf rather than as an equality of natural transformations
because the latter is an equality of *functors* in its type and exhausts the `whnf` budget at the
`TopCat` spelling, while this one is immediate. -/
theorem H'spacePullback_app_eq_extMapComp {X Y : TopCat.{u}} (f : X ⟶ Y)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) :
    (Stacks.Cohomology.AbelianColimit.H'spacePullback f V U h n).app G =
      (extMapComp (Stacks.Cohomology.AbelianColimit.sheafPullback f)
        (Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap f V U h) n).app G :=
  rfl

end Bridge

/-! ### The corepresentation of sections, read on the pullback map of corepresenting objects -/

section Representation

universe u

open Stacks.Cohomology.AbelianColimit

attribute [local instance] additive_abSections

/-- **The corepresentation of sections over an open, read on a morphism.**  The inverse of
`ModuleSheafCohomology.evaluationRepresentation` carries a map out of `freeOfOpen U` to the
section it corresponds to under the sheafification adjunction and
`ModuleSheafCohomology.freeEvaluationHomAddEquiv`. -/
theorem evaluationRepresentation_inv_app_apply {Z : Type u} [TopologicalSpace Z]
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}] (U : Opens Z)
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (v : freeOfOpen U ⟶ G) :
    (evaluationRepresentation (Opens.grothendieckTopology Z) U).inv.app G v =
      freeEvaluationHomAddEquiv U G.obj
        ((sheafificationAdjunction (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).homEquiv
          (yoneda.obj U ⋙ AddCommGrpCat.free) G v) :=
  rfl

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens ↥Y) (U : Opens ↥X)
  (h : U ≤ (Opens.map f).obj V)

/-- The corepresentation of sections over `V` by `freeOfOpen V`. -/
abbrev repV : abSections V ≅ preadditiveCoyoneda.obj (op (freeOfOpen V)) :=
  evaluationRepresentation (Opens.grothendieckTopology ↥Y) V

/-- The corepresentation of sections over `U` by `freeOfOpen U`. -/
abbrev repU : abSections U ≅ preadditiveCoyoneda.obj (op (freeOfOpen U)) :=
  evaluationRepresentation (Opens.grothendieckTopology ↥X) U

/-- The unit of the inverse-image/direct-image adjunction at `freeOfOpen V`, with its target
written as the direct image of the inverse image rather than as the composite functor. -/
abbrev pullbackUnit : freeOfOpen V ⟶
    (Spaces.sheafPushforward f).obj ((sheafPullback f).obj (freeOfOpen V)) :=
  (Spaces.sheafAdjunction f).unit.app (freeOfOpen V)

/-- **The defining property of
`Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap`, read on sections.**  The section of
`f⁻¹ (freeOfOpen V)` over `U` that the pullback map of corepresenting objects corresponds to is
the tautological section carried across the adjunction unit and restricted to `U`. -/
theorem repU_inv_freeOfOpenPullbackMap :
    (repU U).inv.app ((sheafPullback f).obj (freeOfOpen V)) (freeOfOpenPullbackMap f V U h) =
      ((sheafPullback f).obj (freeOfOpen V)).obj.map (homOfLE h).op
        ((repV V).inv.app
          ((Spaces.sheafPushforward f).obj ((sheafPullback f).obj (freeOfOpen V)))
          (pullbackUnit f V)) := by
  rw [evaluationRepresentation_inv_app_apply (Z := ↥X) U _ (freeOfOpenPullbackMap f V U h),
    evaluationRepresentation_inv_app_apply (Z := ↥Y) V _
      (pullbackUnit f V)]
  exact (congrArg
      (fun z => freeEvaluationHomAddEquiv U ((sheafPullback f).obj (freeOfOpen V)).obj z)
      (Equiv.apply_symm_apply _ _)).trans (AddEquiv.apply_symm_apply _ _)

/-- **The one computation that connects the two descriptions of the comparison arrows.**  The
pullback map of corepresenting objects, read on sections and followed by an `f`-map through the
adjunction, is the `f`-map on sections over `V` followed by restriction to `U`, i.e.
`Stacks.Cohomology.SpectralLimit.sectionsRestrictMap` precomposed with the corepresentation.

Both sides send a map `t : freeOfOpen V ⟶ G` -- equivalently a section of `G` over `V` -- to the
image of that section under the `f`-map, restricted to `U`.  The proof is the naturality of the
two corepresentations, the naturality of a sheaf map against restriction,
`repU_inv_freeOfOpenPullbackMap`, and two adjunction identities,
`CategoryTheory.Adjunction.homEquiv_naturality_left_symm` and
`CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem coyonedaMapComp_comp_eq_sectionsRestrictMap
    (G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u})
    (F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F) :
    (coyonedaMapComp (sheafPullback f) (freeOfOpen U) (freeOfOpen V)
          (freeOfOpenPullbackMap f V U h)).app G ≫
        (repU U).inv.app ((sheafPullback f).obj G) ≫
        (abSections U).map (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) =
      (repV V).inv.app G ≫
        Stacks.Cohomology.SpectralLimit.sectionsRestrictMap f φ V U h := by
  set adj := Spaces.sheafAdjunction f with hadj
  set ρ := freeOfOpenPullbackMap f V U h with hρ
  set σ' := (adj.homEquiv G F).symm φ with hσ'
  ext t
  set v := (adj.homEquiv (freeOfOpen V) F).symm (t ≫ φ) with hv
  set τ := (repV V).inv.app
    ((Spaces.sheafPushforward f).obj ((sheafPullback f).obj (freeOfOpen V)))
    (pullbackUnit f V) with hτ
  have e1 := NatTrans.naturality_apply (repU U).inv σ'
    ((coyonedaMapComp (sheafPullback f) (freeOfOpen U) (freeOfOpen V) ρ).app G t)
  have e2 : (ρ ≫ (sheafPullback f).map t) ≫ σ' = ρ ≫ v :=
    (Category.assoc ρ ((sheafPullback f).map t) σ').trans
      (congrArg (fun z => ρ ≫ z) (Adjunction.homEquiv_naturality_left_symm adj t φ).symm)
  have e2' : (repU U).inv.app F ((ρ ≫ (sheafPullback f).map t) ≫ σ') =
      (repU U).inv.app F (ρ ≫ v) :=
    congrArg (fun z : freeOfOpen U ⟶ F => (repU U).inv.app F z) e2
  have e3 := NatTrans.naturality_apply (repU U).inv v
    (ρ : freeOfOpen U ⟶ (sheafPullback f).obj (freeOfOpen V))
  have e4 : (abSections U).map v
        ((repU U).inv.app ((sheafPullback f).obj (freeOfOpen V)) ρ) =
      (abSections U).map v
        (((sheafPullback f).obj (freeOfOpen V)).obj.map (homOfLE h).op τ) :=
    congrArg
      (fun z : (abSections U).obj ((sheafPullback f).obj (freeOfOpen V)) =>
        (abSections U).map v z)
      (repU_inv_freeOfOpenPullbackMap f V U h)
  have e5 : (abSections U).map v
        (((sheafPullback f).obj (freeOfOpen V)).obj.map (homOfLE h).op τ) =
      F.obj.map (homOfLE h).op
        ((abSections V).map ((Spaces.sheafPushforward f).map v) τ) :=
    ConcreteCategory.congr_hom (v.hom.naturality (homOfLE h).op) τ
  have e7 := (NatTrans.naturality_apply (repV V).inv ((Spaces.sheafPushforward f).map v)
    (pullbackUnit f V)).symm
  have e8 : pullbackUnit f V ≫ (Spaces.sheafPushforward f).map v = t ≫ φ :=
    (Adjunction.homEquiv_unit adj _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have e8' := ConcreteCategory.congr_arg
    ((repV V).inv.app ((Spaces.sheafPushforward f).obj F)) e8
  have e9 := NatTrans.naturality_apply (repV V).inv φ t
  exact e1.symm.trans (e2'.trans (e3.trans (e4.trans (e5.trans
    (ConcreteCategory.congr_arg (F.obj.map (homOfLE h).op)
      (e7.trans (e8'.trans e9)))))))

/-- **The pullback map on sections, followed by an `f`-map, is the `f`-map on sections followed
by restriction.**  `coyonedaMapComp_comp_eq_sectionsRestrictMap` with the corepresentation of
sections over `V` cancelled, i.e. stated for `derivedSectionsMap`, the map of corepresented
functors.  This is the form the degree-zero identification consumes. -/
theorem derivedSectionsMap_comp_eq_sectionsRestrictMap
    (G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u})
    (F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u})
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F) :
    (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
          (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h)).app G ≫
        (abSections U).map (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) =
      Stacks.Cohomology.SpectralLimit.sectionsRestrictMap f φ V U h := by
  have hd : (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
        (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h)).app G =
      (repV V).hom.app G ≫
        (coyonedaMapComp (sheafPullback f) (freeOfOpen U) (freeOfOpen V)
          (freeOfOpenPullbackMap f V U h)).app G ≫
        (repU U).inv.app ((sheafPullback f).obj G) := rfl
  rw [hd, Category.assoc, Category.assoc,
    coyonedaMapComp_comp_eq_sectionsRestrictMap f V U h G F φ]
  exact (repV V).hom_inv_id_app_assoc G _

/-! ### The canonical identification of native cohomology with right-derived sections -/

/-- **The canonical identification of native cohomology over an open with the right-derived
functors of sections**, in every degree: `ModuleSheafCohomology.extFunctorObjIsoRightDerived` at
the corepresentation of sections by `freeOfOpen U`.  Nothing is chosen, and the identification
has a formula in every degree.

It is stated at the `extFunctorObj` spelling of native cohomology rather than at the `H'functor`
spelling, although the two are equal by
`Stacks.Cohomology.AbelianColimit.H'functor_eq_extFunctorObj`: the equality is one of *functors*,
and crossing it inside a composite costs the `whnf` budget at the `TopCat` spelling. -/
def H'isoRightDerivedSections {Z : Type u} [TopologicalSpace Z]
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}] (U : Opens Z) (p : ℕ) :
    extFunctorObj (freeOfOpen U) p ≅ (abSections U).rightDerived p :=
  extFunctorObjIsoRightDerived (abSections U) (freeOfOpen U)
    (evaluationRepresentation (Opens.grothendieckTopology Z) U) p

/-- `Stacks.Cohomology.AbelianColimit.rightDerivedSectionsDeltaFunctor` is the transport of
`Stacks.Cohomology.AbelianColimit.H'deltaFunctor` along `H'isoRightDerivedSections`. -/
theorem rightDerivedSectionsDeltaFunctor_eq_ofIso {Z : Type u} [TopologicalSpace Z]
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}] (U : Opens Z) :
    rightDerivedSectionsDeltaFunctor U =
      (H'deltaFunctor U).ofIso (fun n => (abSections U).rightDerived n)
        (fun n => H'isoRightDerivedSections U n) :=
  rfl

/-- **The canonical identification is an isomorphism of δ-functors.**  Unlike
`Stacks.Cohomology.AbelianColimit.H'isoRightDerivedDelta`, which is built by
`CategoryTheory.DeltaFunctor.IsUniversal.isoOfIso` out of a degree-zero isomorphism and has no
formula in positive degree, this one is the transporting isomorphism of the δ-functor
`rightDerivedSectionsDeltaFunctor` itself, so its degree-`n` component is
`H'isoRightDerivedSections U n` by construction.  In particular it commutes with the connecting
morphisms in every degree. -/
def H'isoRightDerivedSectionsDelta {Z : Type u} [TopologicalSpace Z]
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}] (U : Opens Z) :
    rightDerivedSectionsDeltaFunctor U ≅ H'deltaFunctor U :=
  CategoryTheory.DeltaFunctor.ofIsoIso (H'deltaFunctor U)
    (fun n => (abSections U).rightDerived n) (fun n => H'isoRightDerivedSections U n)

/-- The components of the δ-functor isomorphism are the canonical identifications. -/
theorem H'isoRightDerivedSectionsDelta_hom_app {Z : Type u} [TopologicalSpace Z]
    [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}] (U : Opens Z) (n : ℕ) :
    (H'isoRightDerivedSectionsDelta U).hom.app n = (H'isoRightDerivedSections U n).inv :=
  rfl

/-! ### The `Ext`-side comparison arrow of Tag 0A37, and its degree-zero identification -/

/-- **The `Ext`-side comparison arrow of Stacks 0A37** attached to an `f`-map `φ : G ⟶ f_* F` and
a compatible pair of opens: the pullback map on native cohomology along `f`, followed by the map
induced by the adjoint `f⁻¹ G ⟶ F` of `φ`.  This is the arrow that
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap` prescribes by a lift of injective resolutions,
and its first factor is a component of a morphism
of δ-functors (`Stacks.Cohomology.AbelianColimit.H'spacePullback_map_comp_H'δ`). -/
def extSpacePullbackMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) (p : ℕ) :
    (extFunctorObj (freeOfOpen V) p).obj G ⟶ (extFunctorObj (freeOfOpen U) p).obj F :=
  (extMapComp (sheafPullback f) (freeOfOpenPullbackMap f V U h) p).app G ≫
    (extFunctorObj (freeOfOpen U) p).map (((Spaces.sheafAdjunction f).homEquiv G F).symm φ)

/-- `extSpacePullbackMap` is `Stacks.Cohomology.AbelianColimit.H'spacePullback`
followed by the map induced by the adjoint of the `f`-map. -/
theorem extSpacePullbackMap_eq {X Y : TopCat.{u}} (f : X ⟶ Y)
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) (p : ℕ) :
    extSpacePullbackMap f φ V U h p =
      (H'spacePullback f V U h p).app G ≫
        (H'functor U p).map (((Spaces.sheafAdjunction f).homEquiv G F).symm φ) :=
  rfl

/-- **The degree-zero reading of the `Ext`-side pullback map at a sheaf.**  This is
`extMapComp_conj_zero` evaluated at `G` and read through the canonical identification
`H'isoRightDerivedSections`; it is stated at a sheaf because the corresponding equality of
natural transformations has an equality of *functors* in its type. -/
theorem extMapComp_conj_zero_app {X Y : TopCat.{u}} (f : X ⟶ Y)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V)
    (G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}) :
    (H'isoRightDerivedSections V 0).inv.app G ≫
        (extMapComp (sheafPullback f) (freeOfOpenPullbackMap f V U h) 0).app G ≫
        (H'isoRightDerivedSections U 0).hom.app ((sheafPullback f).obj G) =
      (abSections V).rightDerivedZeroIsoSelf.hom.app G ≫
        (derivedSectionsMap (sheafPullback f) (abSections U) (freeOfOpen U) (repU U)
          (abSections V) (freeOfOpen V) (repV V) (freeOfOpenPullbackMap f V U h)).app G ≫
        (abSections U).toRightDerivedZero.app ((sheafPullback f).obj G) := by
  have hA := NatTrans.congr_app (extMapComp_conj_zero (sheafPullback f) (abSections U)
    (freeOfOpen U) (repU U) (abSections V) (freeOfOpen V) (repV V)
    (freeOfOpenPullbackMap f V U h)) G
  exact hA

/-- **In degree zero the `Ext`-side comparison arrow is the arrow prescribed by Tag 0A37.**  Under
the canonical identifications of cohomology with right-derived sections it is the `f`-map on
sections over `V` followed by restriction to `U`, which by
`Stacks.Cohomology.SpectralLimit.IsCohomologyMap.eq_sectionsRestrictMap` is exactly the arrow
that predicate prescribes in degree zero.

The proof is `extMapComp_conj_zero_app`, the naturality of the canonical identification and of
`CategoryTheory.Functor.toRightDerivedZero` at the adjoint of `φ`, and
`derivedSectionsMap_comp_eq_sectionsRestrictMap`. -/
theorem extSpacePullbackMap_zero_eq {X Y : TopCat.{u}} (f : X ⟶ Y)
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) :
    extSpacePullbackMap f φ V U h 0 ≫ (H'isoRightDerivedSections U 0).hom.app F =
      (H'isoRightDerivedSections V 0).hom.app G ≫
        (abSections V).rightDerivedZeroIsoSelf.hom.app G ≫
        Stacks.Cohomology.SpectralLimit.sectionsRestrictMap f φ V U h ≫
        (abSections U).toRightDerivedZero.app F := by
  have hA := extMapComp_conj_zero_app f V U h G
  have hnat := (H'isoRightDerivedSections U 0).hom.naturality
    (((Spaces.sheafAdjunction f).homEquiv G F).symm φ)
  have hz := (abSections U).toRightDerivedZero.naturality
    (((Spaces.sheafAdjunction f).homEquiv G F).symm φ)
  have hkey := derivedSectionsMap_comp_eq_sectionsRestrictMap f V U h G F φ
  have main : (H'isoRightDerivedSections V 0).inv.app G ≫
      extSpacePullbackMap f φ V U h 0 ≫ (H'isoRightDerivedSections U 0).hom.app F =
      (abSections V).rightDerivedZeroIsoSelf.hom.app G ≫
        Stacks.Cohomology.SpectralLimit.sectionsRestrictMap f φ V U h ≫
        (abSections U).toRightDerivedZero.app F := by
    have hA3 := (assoc₃ _ _ _
      (((abSections U).rightDerived 0).map
        (((Spaces.sheafAdjunction f).homEquiv G F).symm φ))).symm.trans
      ((whiskerRightEq hA _).trans (assoc₃ _ _ _ _))
    have hkey2 := (assoc₂ _ _ ((abSections U).toRightDerivedZero.app F)).symm.trans
      (whiskerRightEq hkey _)
    rw [extSpacePullbackMap, Category.assoc, hnat, hA3, ← hz, hkey2]
    rfl
  rw [← main, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The degree-zero case of the identification Tag 0A37 asks for.**  The `Ext`-side comparison
arrow satisfies `Stacks.Cohomology.SpectralLimit.IsCohomologyMap` in degree zero, for the
canonical identifications of
cohomology with right-derived sections.

Together with `Stacks.Cohomology.AbelianColimit.H'spacePullback_map_comp_H'δ` this says: the
arrows that commute with the connecting morphism are, in degree zero, exactly the arrows
prescribed by a lift of injective resolutions.  Positive degree is not covered here; it is
`Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap_succ`, and the two are joined
into every degree by `Stacks.Cohomology.ExtComparison.isCohomologyMap_extSpacePullbackMap`. -/
theorem isCohomologyMap_extSpacePullbackMap_zero {X Y : TopCat.{u}} (f : X ⟶ Y)
    {G : Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}}
    (φ : G ⟶ (Spaces.sheafPushforward f).obj F)
    (V : Opens ↥Y) (U : Opens ↥X) (h : U ≤ (Opens.map f).obj V) :
    Stacks.Cohomology.SpectralLimit.IsCohomologyMap f φ V U h 0
      ((H'isoRightDerivedSections V 0).app G) ((H'isoRightDerivedSections U 0).app F)
      (extSpacePullbackMap f φ V U h 0) := by
  have h0 := Stacks.Cohomology.SpectralLimit.IsCohomologyMap.eq_sectionsRestrictMap f φ V U h
    ((H'isoRightDerivedSections V 0).app G) ((H'isoRightDerivedSections U 0).app F)
    (Stacks.Cohomology.SpectralLimit.isCohomologyMap_cohomologyMap f φ V U h 0
      ((H'isoRightDerivedSections V 0).app G) ((H'isoRightDerivedSections U 0).app F))
  have key := extSpacePullbackMap_zero_eq f φ V U h
  have hm : extSpacePullbackMap f φ V U h 0 =
      Stacks.Cohomology.SpectralLimit.cohomologyMap f φ V U h 0
        ((H'isoRightDerivedSections V 0).app G)
        ((H'isoRightDerivedSections U 0).app F) := by
    have k3 := (assoc₂ _ _ ((H'isoRightDerivedSections U 0).inv.app F)).symm.trans
      ((whiskerRightEq key _).trans (assoc₃ _ _ _ _))
    rw [Iso.hom_inv_id_app, Category.comp_id] at k3
    rw [h0]
    exact k3
  rw [hm]
  exact Stacks.Cohomology.SpectralLimit.isCohomologyMap_cohomologyMap f φ V U h 0 _ _

end Representation

end Stacks.Cohomology.ExtComparison

end
