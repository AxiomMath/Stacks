module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Comparison with Mathlib's Galois categories, and quotients by open subgroups

Two pieces of bookkeeping are needed throughout the study of functors between Galois categories
and the homomorphisms they induce. The first translates the Galois category axioms for a fixed
finite-set-valued fibre functor into Mathlib's `GaloisCategory` and `FiberFunctor` classes, which
unlocks Mathlib's equivalence with finite continuous actions. The second produces, from an open
subgroup of a compact topological group, the finite continuous action on the quotient, together
with the fact that the subgroup fixes its base point; this is the test object used to detect
non-surjectivity of an induced homomorphism.

## Main definitions

* `CategoryTheory.quotientContAction` is the quotient by an open subgroup as a finite continuous
  action.
* `CategoryTheory.quotientContActionSwitch` is the same action with values in finite sets of a
  prescribed universe.

## Main results

* `CategoryTheory.preGalois_of_isGaloisCategory` provides Mathlib's `PreGaloisCategory`; the
  companion bridges to `PreGaloisCategory.FiberFunctor` and to `GaloisCategory` are
  `CategoryTheory.IsGaloisCategory.fiberFunctor` and
  `CategoryTheory.IsGaloisCategory.toGaloisCategory`, which are declared with the axioms.
* `CategoryTheory.isConnected_of_fiber_pretransitive` recognises connected objects by
  transitivity on fibres, and `CategoryTheory.pretransitive_of_actionIso` and
  `CategoryTheory.pretransitive_uSwitch` transport transitivity.
* `CategoryTheory.fixed_quotient` and `CategoryTheory.fixed_quotientSwitch` say the subgroup
  fixes the base point of the quotient.

## Implementation notes

The quotient of a compact group by an open subgroup is finite and discrete, so the quotient
action is continuous; `quotientContActionSwitch` applies the universe-switching equivalence of
finite sets to place it in the universe where the fibre functor takes its values.

## References

* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' w
universe uG

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- A category with a finite-set-valued fibre functor satisfying the Galois category axioms has
quotients by finite groups, and every monomorphism into an object exhibits that object as a
coproduct; that is, it is a pre-Galois category in Mathlib's sense. -/
public theorem preGalois_of_isGaloisCategory
    (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)] :
    PreGaloisCategory C :=
  (IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)).toPreGaloisCategory

/-- An object whose fibre is nonempty and on which the automorphism group of the fibre functor
acts transitively is connected. -/
public theorem isConnected_of_fiber_pretransitive
    (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] :
    PreGaloisCategory.IsConnected X := by
  let G := setValuedFiberFunctor F
  have : F.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F FintypeCat.incl
  have hne (Y : C) : (IsInitial Y → False) ↔ Nonempty (F.obj Y) := by
    have h₁ : Nonempty (IsInitial Y) ↔ IsEmpty (G.obj Y) := by
      rw [(IsInitial.isInitialIffObj G Y).nonempty_congr]
      exact Types.initial_iff_empty _
    exact ⟨fun h => not_isEmpty_iff.mp fun he => h (h₁.mpr he).some,
      fun h hi => (h₁.mp ⟨hi⟩).false h.some⟩
  refine ⟨(hne X).mpr inferInstance, ?_⟩
  intro Y i _ hY
  have : Mono (G.map i) := Functor.map_mono G i
  have hinj : Function.Injective (F.map i).hom :=
    CategoryTheory.injective_of_mono (G.map i)
  have hsurj : Function.Surjective (F.map i).hom := by
    obtain ⟨y⟩ := (hne Y).mp hY
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) ((F.map i).hom y) x
    refine ⟨g • y, ?_⟩
    show (F.map i).hom ((g.hom.app Y).hom y) = x
    exact (PreGaloisCategory.mulAction_naturality F g i y).symm.trans hg
  have : IsIso (F.map i) :=
    (ConcreteCategory.isIso_iff_bijective (F.map i)).mpr ⟨hinj, hsurj⟩
  exact isIso_of_reflects_iso i F

/-- Transitivity of a group action on a finite set transports along an isomorphism of actions. -/
public theorem pretransitive_of_actionIso {G : Type*} [Group G]
    {A B : Action FintypeCat.{w} G} (e : A ≅ B)
    [MulAction.IsPretransitive G A.V] : MulAction.IsPretransitive G B.V := by
  refine ⟨fun x y => ?_⟩
  have h (z : B.V) : e.hom.hom (e.inv.hom z) = z := by
    simpa only [FintypeCat.comp_apply, FintypeCat.id_apply] using
      ConcreteCategory.congr_hom (Action.inv_hom_hom e) z
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.inv.hom x) (e.inv.hom y)
  refine ⟨g, ?_⟩
  have hm : e.hom.hom (g • e.inv.hom x) = g • e.hom.hom (e.inv.hom x) :=
    ConcreteCategory.congr_hom (e.hom.comm g) _
  rw [h] at hm
  rw [← hm, hg, h]

/-- Transitivity of a group action on a finite set is preserved by the universe-switching
equivalence of categories of finite sets. -/
public theorem pretransitive_uSwitch
    {G : Type uG} [Group G] {A : Action FintypeCat.{uG} G}
    [MulAction.IsPretransitive G A.V] :
    MulAction.IsPretransitive G ((FintypeCat.uSwitch.{uG,w}).mapAction G |>.obj A).V := by
  refine ⟨fun x y => ?_⟩
  let e := FintypeCat.uSwitchEquiv.{uG,w} A.V
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e x) (e y)
  refine ⟨g, ?_⟩
  show (FintypeCat.uSwitch.map (A.ρ g)) x = y
  exact e.injective ((FintypeCat.uSwitchEquiv_naturality (A.ρ g) x).symm.trans hg)

/-- The quotient of a compact topological group by an open subgroup, as a finite continuous action
of the group. -/
public noncomputable def quotientContAction
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : ContAction FintypeCat.{uG} G := by
  letI : Fintype (G ⧸ U.toSubgroup) := Fintype.ofFinite (G ⧸ U.toSubgroup)
  let Q : Action FintypeCat.{uG} G := G ⧸ₐ U.toSubgroup
  have hdisc : DiscreteTopology (G ⧸ U.toSubgroup) :=
    QuotientGroup.discreteTopology U.isOpen
  have htop : (inferInstance : TopologicalSpace (G ⧸ U.toSubgroup)) = ⊥ :=
    DiscreteTopology.eq_bot
  change QuotientGroup.instTopologicalSpace U.toSubgroup = ⊥ at htop
  have hcont := (inferInstance : ContinuousSMul G (G ⧸ U.toSubgroup)).1
  rw [htop] at hcont
  letI : TopologicalSpace (G ⧸ U.toSubgroup) := ⊥
  have hc : Action.IsContinuous Q := by
    rw [Action.isContinuous_def]
    change Continuous (fun p : G × (G ⧸ U.toSubgroup) => p.1 • p.2)
    exact hcont
  exact ⟨Q, hc⟩

/-- The quotient by an open subgroup, transported to a finite continuous action valued in finite
sets of a prescribed universe. -/
public noncomputable def quotientContActionSwitch
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : ContAction FintypeCat.{w} G :=
  ((FintypeCat.uSwitch.{uG,w}).mapContAction G
    (fun X => by
      rw [Action.isContinuous_def]
      change Continuous ((fun p => (FintypeCat.uSwitchEquiv X.obj.V).symm p) ∘
        (fun p : G × _ => (X.obj.ρ p.1).hom p.2) ∘
        (fun p : G × _ => (p.1, FintypeCat.uSwitchEquiv _ p.2)))
      exact Continuous.comp (by fun_prop) (Continuous.comp X.2.1 (by fun_prop)))).obj
    (quotientContAction U)

/-- An element of an open subgroup acts trivially on the base point of the quotient. -/
public theorem fixed_quotient
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G)
    (g : G) (hg : g ∈ U) :
    (⟦g⟧ : G ⧸ U.toSubgroup) = ⟦1⟧ := by
  apply QuotientGroup.eq.mpr
  simpa using U.inv_mem hg

/-- An element of an open subgroup fixes the base point of the universe-switched quotient
action. -/
public theorem fixed_quotientSwitch
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) (g : G) (hg : g ∈ U) :
    let Q0 := quotientContAction U
    let q : (quotientContActionSwitch U).obj.V :=
      (FintypeCat.uSwitchEquiv Q0.obj.V).symm (⟦1⟧ : G ⧸ U.toSubgroup)
    g • q = q := by
  intro Q0 q
  show (FintypeCat.uSwitch.map (Q0.obj.ρ g)) q = q
  apply (FintypeCat.uSwitchEquiv Q0.obj.V).injective
  rw [← FintypeCat.uSwitchEquiv_naturality]
  have hq : (FintypeCat.uSwitchEquiv Q0.obj.V) q =
      (⟦1⟧ : G ⧸ U.toSubgroup) := Equiv.apply_symm_apply _ _
  rw [hq]
  let : MulAction G (G ⧸ U.toSubgroup) := MulAction.quotient G U.toSubgroup
  show (g • (⟦1⟧ : G ⧸ U.toSubgroup) : G ⧸ U.toSubgroup) = ⟦1⟧
  rw [MulAction.Quotient.smul_mk]
  simpa using fixed_quotient U g hg

end CategoryTheory
