module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# The module associated to a torsor under the sheaf of units

A torsor `F` under the sheaf of units `O_X^*` of a ringed space is glued from copies of
`O_X` over a trivializing cover, the transition data being the units `s_j / s_i` on
overlaps.  This file carries out that gluing, shows the resulting sheaf of modules is
finite locally free of rank one, and shows that its own torsor of generators is
isomorphic to `F`.  This is the surjectivity half of Stacks Tag 09NU.

## Main definitions

* `TorsorCoverData` packages a cover of `X` together with a section of `F` over each
  member — the trivializing data a torsor provides.
* `torsorTransitionUnit` is the unit carrying one local section to another on an overlap,
  and `torsorTransitionUnit_cocycle` is its cocycle identity.
* `torsorAssociatedSheafOfModules` is the sheaf of modules glued along those units, and
  `torsorAssociatedChartIso` its trivialization on each member of the cover.
* `torsorAssociatedGeneratorTorsorHom` is the equivariant morphism from the generator
  torsor of that module back to `F`.

## Main results

* `torsorAssociatedSheafOfModules_isFiniteLocallyFreeOfRank`: the glued module is finite
  locally free of rank one.
* `torsorAssociatedGeneratorTorsorHom_isIso`: that morphism is an isomorphism, so every
  torsor under `O_X^*` arises as the generator torsor of a rank-one module.

## Implementation notes

The gluing uses `StacksDraft.Topology.Sheaves.Glueing`: the chart presheaves are copies
of the structure sheaf restricted to the members of the cover, and the glued sections are
the compatible families, cut out as `torsorAssociatedSectionsSubmodule`.  Coordinates in a
chart are read off by `torsorAssociatedChartLinearEquiv`, and the generating condition is
tested there (`torsorAssociatedChart_isUnit_of_generator`).

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

/-- An isomorphism of sheaves of modules is bijective on sections over every open. -/
public theorem moduleIso_app_bijective (X : RingedSpace.{u, u})
    {L N : SheafOfModules.{u} (structureSheaf X.sheaf)} (e : L ≅ N)
    (U : Opens X) : Function.Bijective (e.hom.val.app (op U)) := by
  let m := (SheafOfModules.evaluation (structureSheaf X.sheaf) (op U)).map e.hom
  have hm : Function.Bijective m := by
    let _ : IsIso m := Functor.map_isIso
      (SheafOfModules.evaluation (structureSheaf X.sheaf) (op U)) e.hom
    exact ConcreteCategory.bijective_of_isIso m
  exact hm

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
private theorem moduleHom_app_restrictₛₗ (X : RingedSpace.{u, u})
    {L N : SheafOfModules.{u} (structureSheaf X.sheaf)} (f : L ⟶ N) {U V : Opens X}
    (hVU : V ≤ U) (x : L.val.obj (op U)) :
    f.val.app (op V) (L.val.restrictₛₗ (homOfLE hVU).op x) =
      N.val.restrictₛₗ (homOfLE hVU).op (f.val.app (op U) x) := by
  have h := congrArg (fun m => m.hom x) (f.val.naturality ((homOfLE hVU).op))
  exact h

/-- Transporting along an isomorphism preserves the bijectivity of `r ↦ r • restrict x`. -/
private theorem bijective_smul_restrict_of_iso (X : RingedSpace.{u, u})
    {L N : SheafOfModules.{u} (structureSheaf X.sheaf)} (e : L ≅ N) {U V : Opens X}
    (hVU : V ≤ U) (x : L.val.obj (op U))
    (hx : Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • L.val.restrictₛₗ (homOfLE hVU).op x)) :
    Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • N.val.restrictₛₗ (homOfLE hVU).op (e.hom.val.app (op U) x)) := by
  have hfun : (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • N.val.restrictₛₗ (homOfLE hVU).op (e.hom.val.app (op U) x)) =
      fun r => e.hom.val.app (op V) (r • L.val.restrictₛₗ (homOfLE hVU).op x) := by
    funext r
    rw [(e.hom.val.app (op V)).hom.map_smul, moduleHom_app_restrictₛₗ]
  rw [hfun]
  exact (moduleIso_app_bijective X e V).comp hx

/-- An isomorphism of invertible modules induces an equivariant isomorphism of their
generator torsors. -/
public theorem generatorTorsor_iso_of_iso (X : RingedSpace.{u, u})
    {L N : SheafOfModules.{u} (structureSheaf X.sheaf)}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) N 1]
    (e : L ≅ N) :
    (generatorTorsor X L).toTorsor.action.Iso
      (generatorTorsor X N).toTorsor.action := by
  let gL := generatorTorsor X L
  let gN := generatorTorsor X N
  let app (U : Opens X) (s : gL.toTorsor.F.obj U) : gN.toTorsor.F.obj U :=
    (gN.sectionsEquiv U).symm ⟨e.hom.val.app (op U) (gL.sectionsEquiv U s).val, fun V hVU =>
      bijective_smul_restrict_of_iso X e hVU _ ((gL.sectionsEquiv U s).property V hVU)⟩
  refine ⟨{
    app := app
    naturality := by
      intro U V hVU s
      apply (gN.sectionsEquiv V).injective
      apply Subtype.ext
      exact moduleHom_app_restrictₛₗ X e.hom hVU _
    map_act := by
      intro U f s
      apply (gN.sectionsEquiv U).injective
      apply Subtype.ext
      let fu : ((structureSheaf X.sheaf).obj.obj (op U))ˣ :=
        Additive.toMul (Multiplicative.toAdd f)
      have hf : Multiplicative.ofAdd (Additive.ofMul fu) = f := rfl
      change e.hom.val.app (op U)
          ((gL.sectionsEquiv U (gL.action.act f s)).val) =
        (fu : (structureSheaf X.sheaf).obj.obj (op U)) •
          e.hom.val.app (op U) ((gL.sectionsEquiv U s).val)
      rw [← hf]
      exact (congrArg (e.hom.val.app (op U)) (gL.sectionsEquiv_smul U fu s)).trans
        ((e.hom.val.app (op U)).hom.map_smul _ _) }, ?_⟩
  intro U
  constructor
  · intro s t hst
    apply (gL.sectionsEquiv U).injective
    apply Subtype.ext
    apply (moduleIso_app_bijective X e U).1
    have h := congrArg (gN.sectionsEquiv U) hst
    simp only [app, Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  · intro t
    let ev := e.inv.val.app (op U)
    let t' := gN.sectionsEquiv U t
    let s' : GeneratorSections X L U := ⟨ev t'.val, fun V hVU =>
      bijective_smul_restrict_of_iso X e.symm hVU _ (t'.property V hVU)⟩
    refine ⟨(gL.sectionsEquiv U).symm s', ?_⟩
    apply (gN.sectionsEquiv U).injective
    apply Subtype.ext
    change e.hom.val.app (op U) (e.inv.val.app (op U) t'.val) = t'.val
    have hcomp : e.inv.val.app (op U) ≫ e.hom.val.app (op U) = 𝟙 _ :=
      congrArg (fun f => f.val.app (op U)) e.inv_hom_id
    have hcomp' := congrArg (fun f => f t'.val)
      (congrArg ModuleCat.Hom.hom hcomp)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.id_apply] using hcomp'

/-- A torsor section on a neighbourhood of a point. -/
structure TorsorLocalSection (X : RingedSpace.{u, u})
    (F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)) (x : X) where
  U : Opens X
  point_mem : x ∈ U
  localSection : F.F.obj U

attribute [-simp] TorsorLocalSection.mk.injEq TorsorLocalSection.mk.sizeOf_spec

/-- A torsor has a section on a neighbourhood of every point. -/
noncomputable def torsorLocalSection
    (X : RingedSpace.{u, u}) (F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)) (x : X) :
    TorsorLocalSection X F x := Classical.choice (by
  obtain ⟨U, hxU, ⟨s⟩⟩ := F.isTorsor.2 x
  exact ⟨⟨U, hxU, s⟩⟩)

/-- Choices of local sections of a torsor, indexed by the points they cover. -/
structure TorsorCoverData (X : RingedSpace.{u, u})
    (F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)) where
  U : X → Opens X
  point_mem : ∀ x, x ∈ U x
  localSection : ∀ x, F.F.obj (U x)
  covers : (⊤ : Opens X) = ⨆ x, U x

attribute [-simp] TorsorCoverData.mk.injEq TorsorCoverData.mk.sizeOf_spec

/-- The local sections of a torsor give a cover of the ringed space. -/
noncomputable def torsorCoverData (X : RingedSpace.{u, u})
    (F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)) : TorsorCoverData X F := by
  classical
  let U (x : X) := (torsorLocalSection X F x).U
  refine ⟨U, fun x => (torsorLocalSection X F x).point_mem,
    fun x => (torsorLocalSection X F x).localSection, ?_⟩
  exact le_antisymm (fun x _ => Opens.mem_iSup.mpr ⟨x, (torsorLocalSection X F x).point_mem⟩)
    le_top

/-- The transition unit carrying the chosen section on `U i` to the one on `U j`. -/
noncomputable def torsorTransitionElement {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V :=
  Classical.choose ((F.isTorsor.1 V
    ⟨F.F.res hi (D.localSection i)⟩).2
      (F.F.res hi (D.localSection i)) (F.F.res hj (D.localSection j)))

/-- The chosen transition element acts by carrying one local torsor section to the next. -/
theorem torsorTransitionElement_spec {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    F.action.act (torsorTransitionElement D i j hi hj)
      (F.F.res hi (D.localSection i)) = F.F.res hj (D.localSection j) :=
  (Classical.choose_spec ((F.isTorsor.1 V
    ⟨F.F.res hi (D.localSection i)⟩).2
      (F.F.res hi (D.localSection i)) (F.F.res hj (D.localSection j)))).1

/-- The transition element is uniquely determined by the torsor action. -/
theorem torsorTransitionElement_unique {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j)
    (g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V)
    (hg : F.action.act g (F.F.res hi (D.localSection i)) =
      F.F.res hj (D.localSection j)) :
    g = torsorTransitionElement D i j hi hj :=
  (Classical.choose_spec ((F.isTorsor.1 V
    ⟨F.F.res hi (D.localSection i)⟩).2
      (F.F.res hi (D.localSection i)) (F.F.res hj (D.localSection j)))).2 g hg

/-- Transition elements commute with restriction to smaller opens. -/
theorem torsorTransitionElement_restrict {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V W : Opens X} (hWV : W ≤ V)
    (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hWV
        (torsorTransitionElement D i j hi hj) =
      torsorTransitionElement D i j (hWV.trans hi) (hWV.trans hj) := by
  apply torsorTransitionElement_unique D i j (hWV.trans hi) (hWV.trans hj)
  calc
    F.action.act
        ((Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hWV
          (torsorTransitionElement D i j hi hj))
        (F.F.res (hWV.trans hi) (D.localSection i)) =
      F.F.res hWV (F.action.act (torsorTransitionElement D i j hi hj)
        (F.F.res hi (D.localSection i))) := by
          rw [← F.F.res_comp hWV hi]
          exact (F.action.res_act hWV _ _).symm
    _ = F.F.res hWV (F.F.res hj (D.localSection j)) := by
      rw [torsorTransitionElement_spec]
    _ = F.F.res (hWV.trans hj) (D.localSection j) := F.F.res_comp hWV hj _

/-- The transition elements satisfy the cocycle law on triple overlaps. -/
theorem torsorTransitionElement_cocycle {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j k : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) (hk : V ≤ D.U k) :
    torsorTransitionElement D i j hi hj * torsorTransitionElement D j k hj hk =
      torsorTransitionElement D i k hi hk := by
  let _ : CommGroup
      ((Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V) := by
    change CommGroup (Multiplicative ((unitsSheaf X).presheaf.obj (op V)))
    infer_instance
  have hact : F.action.act
      (torsorTransitionElement D j k hj hk * torsorTransitionElement D i j hi hj)
      (F.F.res hi (D.localSection i)) = F.F.res hk (D.localSection k) := by
    rw [F.action.mul_act, torsorTransitionElement_spec, torsorTransitionElement_spec]
  exact (mul_comm (torsorTransitionElement D i j hi hj) _).trans
    (torsorTransitionElement_unique D i k hi hk _ hact)

/-- The underlying element of `O_X(V)ˣ` represented by the transition group section. -/
noncomputable def torsorTransitionUnit {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    ((structureSheaf X.sheaf).obj.obj (op V))ˣ :=
  Additive.toMul (Multiplicative.toAdd (torsorTransitionElement D i j hi hj))

/-- A section of the presheaf of groups underlying `O_X^*`, read as a unit of `O_X(V)`; as a
monoid homomorphism. -/
def transitionUnitsHom {X : RingedSpace.{u, u}}
    (V : Opens X) :
    (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V →* 
      ((structureSheaf X.sheaf).obj.obj (op V))ˣ where
  toFun g := Additive.toMul (Multiplicative.toAdd g)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `transitionUnitsHom` commutes with restriction to a smaller open. -/
theorem transitionUnitsHom_res {X : RingedSpace.{u, u}}
    (V W : Opens X) (hWV : W ≤ V)
    (g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V) :
    transitionUnitsHom (X := X) W
        ((Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hWV g) =
      Units.map ((structureSheaf X.sheaf).obj.map (homOfLE hWV).op).hom.toMonoidHom
        (transitionUnitsHom (X := X) V g) :=
  Units.ext rfl

/-- Transition units commute with restriction to a smaller overlap. -/
theorem torsorTransitionUnit_restrict {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V W : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) (hWV : W ≤ V) :
  Units.map ((structureSheaf X.sheaf).obj.map (homOfLE hWV).op).hom.toMonoidHom
        (torsorTransitionUnit D i j hi hj) =
      torsorTransitionUnit D i j (hWV.trans hi) (hWV.trans hj) := by
  change Units.map ((structureSheaf X.sheaf).obj.map (homOfLE hWV).op).hom.toMonoidHom
      (transitionUnitsHom (X := X) V (torsorTransitionElement D i j hi hj)) = _
  rw [← transitionUnitsHom_res (X := X) V W hWV]
  exact congrArg (transitionUnitsHom (X := X) W)
    (torsorTransitionElement_restrict D i j hWV hi hj)

/-- Transition units satisfy the usual multiplicative cocycle identity. -/
theorem torsorTransitionUnit_cocycle {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j k : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) (hk : V ≤ D.U k) :
    torsorTransitionUnit D i j hi hj * torsorTransitionUnit D j k hj hk =
      torsorTransitionUnit D i k hi hk := by
  change transitionUnitsHom (X := X) V (torsorTransitionElement D i j hi hj) *
      transitionUnitsHom (X := X) V (torsorTransitionElement D j k hj hk) =
    transitionUnitsHom (X := X) V (torsorTransitionElement D i k hi hk)
  rw [← (transitionUnitsHom (X := X) V).map_mul]
  exact congrArg (transitionUnitsHom (X := X) V)
    (torsorTransitionElement_cocycle D i j k hi hj hk)

/-- A transition unit from a chosen local section to itself is the identity. -/
theorem torsorTransitionUnit_self {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i : X) {V : Opens X} (hi : V ≤ D.U i) :
    torsorTransitionUnit D i i hi hi = 1 := by
  have h := torsorTransitionElement_unique D i i hi hi 1
    (F.action.one_act (F.F.res hi (D.localSection i)))
  rw [torsorTransitionUnit, ← h]
  rfl

/-- Reversing the two local sections inverts the transition unit. -/
theorem torsorTransitionUnit_symm {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (i j : X) {V : Opens X} (hi : V ≤ D.U i) (hj : V ≤ D.U j) :
    torsorTransitionUnit D j i hj hi = (torsorTransitionUnit D i j hi hj)⁻¹ := by
  have h := torsorTransitionUnit_cocycle D i j i hi hj hi
  rwa [torsorTransitionUnit_self D i hi, mul_eq_one_iff_eq_inv'] at h

/-- The structure sheaf viewed as a sheaf of sets. -/
abbrev structureSheafType (X : RingedSpace.{u, u}) :
    TopCat.Sheaf (Type u) X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget RingCat)).obj X.sheaf

/-- The sections of `structureSheafType X` over `V` form a commutative ring. -/
local instance structureSheafType_commRing (X : RingedSpace.{u, u}) (V : Opens X) :
    CommRing ((structureSheafType X).presheaf.obj (op V)) := by
  change CommRing (X.presheaf.obj (op V))
  infer_instance

/-- The structure sheaf on an open, retaining the ring-section types. -/
abbrev structureSheafLocalPresheaf (X : RingedSpace.{u, u}) (U : Opens X) :
    TopCat.Sheaf.LocalPresheaf X U where
  obj V _ := (structureSheaf X.sheaf).obj.obj (op V)
  map hWV s := (structureSheaf X.sheaf).obj.map (homOfLE hWV).op s
  map_id := by
    intro V hV s
    rw [show (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) from Subsingleton.elim _ _]
    simp
  map_map := by
    intro V W Z hV hWV hZW s
    rw [← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp]
    congr 1

/-- The torsor's transition units glue copies of the structure sheaf as sets. -/
noncomputable def torsorAssociatedGlueData {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    TopCat.Sheaf.GlueData X D.U := by
  classical
  refine {
    sheaf := fun i => structureSheafLocalPresheaf X (D.U i)
    isSheaf := fun i => TopCat.Presheaf.isSheaf_toLocalPresheaf
      (structureSheafType X).property (D.U i)
    trans := fun i j V hi hj => ?_
    trans_map := ?_
    trans_trans := ?_ }
  · let t := torsorTransitionUnit D i j hi hj
    letI : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op V)))
    refine {
      toFun := fun x => (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * x
      invFun := fun x => (↑t : (structureSheaf X.sheaf).obj.obj (op V)) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  · intro i j V W hi hj hWV s
    let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op V)))
    let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op W)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op W)))
    let t := torsorTransitionUnit D i j hi hj
    have ht := torsorTransitionUnit_restrict D i j hi hj hWV
    dsimp [structureSheafLocalPresheaf]
    rw [map_mul]
    congr 1
    · have hti : Units.map ((structureSheaf X.sheaf).obj.map (homOfLE hWV).op).hom.toMonoidHom
          (t⁻¹) = (torsorTransitionUnit D i j (hWV.trans hi) (hWV.trans hj))⁻¹ := by
        rw [map_inv, ht]
      exact congrArg (fun f : _ˣ => (f : (structureSheaf X.sheaf).obj.obj (op W))) hti.symm
  · intro i j k V hi hj hk s
    let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op V)))
    let tij := torsorTransitionUnit D i j hi hj
    let tjk := torsorTransitionUnit D j k hj hk
    let tik := torsorTransitionUnit D i k hi hk
    have h := torsorTransitionUnit_cocycle D i j k hi hj hk
    have hinv : tjk⁻¹ * tij⁻¹ = tik⁻¹ := by rw [← mul_inv_rev, h]
    have hinv_val : (↑(tjk⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
        (↑(tij⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) =
      (↑(tik⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) := by
        simpa using congrArg (fun f : _ˣ => (f : (structureSheaf X.sheaf).obj.obj (op V))) hinv
    calc
      (↑(tjk⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
          ((↑(tij⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * s) =
        ((↑(tjk⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
          (↑(tij⁻¹) : (structureSheaf X.sheaf).obj.obj (op V))) * s := by rw [mul_assoc]
      _ = (↑(tik⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * s := by rw [hinv_val]

/-- The ring of sections on `W` acts on the `i`th coordinate by restriction. -/
local instance torsorAssociatedCoordinateModule (X : RingedSpace.{u, u})
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (i : X) :
    Module ((structureSheaf X.sheaf).obj.obj (op W))
      ((structureSheaf X.sheaf).obj.obj (op (W ⊓ D.U i))) := by
  let f : ((structureSheaf X.sheaf).obj.obj (op W)) →+*
      ((structureSheaf X.sheaf).obj.obj (op (W ⊓ D.U i))) :=
    ((structureSheaf X.sheaf).obj.map (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom
  exact Module.compHom _ f

/-- A compatible family of local coordinates, viewed as a submodule of the product of
the structure-sheaf sections on the members of a torsor cover. -/
noncomputable def torsorAssociatedSectionsSubmodule {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) :
    Submodule ((structureSheaf X.sheaf).obj.obj (op W))
      (∀ i : X, (structureSheaf X.sheaf).obj.obj (op (W ⊓ D.U i))) := by
  classical
  refine {
    carrier := {s | ∀ i j : X,
      (torsorAssociatedGlueData D).trans i j
        (V := W ⊓ D.U i ⊓ (W ⊓ D.U j))
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_left : W ⊓ D.U i ⊓ (W ⊓ D.U j) ≤ W ⊓ D.U i)).op) (s i)) =
      ((structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_right : W ⊓ D.U i ⊓ (W ⊓ D.U j) ≤ W ⊓ D.U j)).op) (s j)}
    zero_mem' := by
      intro i j
      let V := W ⊓ D.U i ⊓ (W ⊓ D.U j)
      let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
        inferInstanceAs (CommRing (X.presheaf.obj (op V)))
      let fi := (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_left : V ≤ W ⊓ D.U i)).op
      let t := torsorTransitionUnit D i j (V := V)
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      change (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi 0 = _
      simp
    add_mem' := by
      intro s q hs hq i j
      let V := W ⊓ D.U i ⊓ (W ⊓ D.U j)
      let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
        inferInstanceAs (CommRing (X.presheaf.obj (op V)))
      let fi := (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_left : V ≤ W ⊓ D.U i)).op
      let fj := (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_right : V ≤ W ⊓ D.U j)).op
      let u := torsorTransitionUnit D i j (V := V)
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      have hsi := hs i j
      have hqi := hq i j
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi (s i) = fj (s j) at hsi
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi (q i) = fj (q j) at hqi
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi (s i + q i) = fj (s j + q j)
      rw [map_add, map_add, mul_add, hsi, hqi]
    smul_mem' := by
      intro r s hs i j
      let V := W ⊓ D.U i ⊓ (W ⊓ D.U j)
      let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
        inferInstanceAs (CommRing (X.presheaf.obj (op V)))
      let fi := (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_left : V ≤ W ⊓ D.U i)).op
      let fj := (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_right : V ≤ W ⊓ D.U j)).op
      have hVW : V ≤ W := (inf_le_left : V ≤ W ⊓ D.U i).trans inf_le_left
      let u := torsorTransitionUnit D i j (V := V)
        (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      have hsi := hs i j
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi (s i) = fj (s j) at hsi
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * fi (r • s i) = fj (r • s j)
      change (↑(u⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
          fi (((((structureSheaf X.sheaf).obj.map
            (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom) r) * s i) =
        fj (((((structureSheaf X.sheaf).obj.map
            (homOfLE (inf_le_left : W ⊓ D.U j ≤ W)).op).hom) r) * s j)
      rw [map_mul, map_mul]
      have hri : fi (((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom r) =
        (structureSheaf X.sheaf).obj.map (homOfLE hVW).op r := by
        dsimp [fi, V]
        rw [← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp]
        congr 1
      have hrj : fj (((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_left : W ⊓ D.U j ≤ W)).op).hom r) =
        (structureSheaf X.sheaf).obj.map (homOfLE hVW).op r := by
        dsimp [fj, V]
        rw [← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp]
        congr 1
      rw [hri, hrj, mul_left_comm, hsi]
  }

/-- The compatible-coordinate modules with their restriction maps form a presheaf of modules. -/
noncomputable def torsorAssociatedModulePresheaf {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    PresheafOfModules (structureSheaf X.sheaf).obj := by
  classical
  refine {
    obj := fun U => ModuleCat.of ((structureSheaf X.sheaf).obj.obj U)
      (torsorAssociatedSectionsSubmodule D U.unop)
    map := fun {U V} f => ?_
    map_id := ?_
    map_comp := ?_ }
  · let h := f.unop.le
    letI : Module ((structureSheaf X.sheaf).obj.obj U)
        (torsorAssociatedSectionsSubmodule D V.unop) :=
      Module.compHom _ ((structureSheaf X.sheaf).obj.map f).hom
    refine ModuleCat.ofHom {
      toFun := fun s => (torsorAssociatedGlueData D).sectionsMap h s
      map_add' := by
        intro s t
        apply Subtype.ext
        funext i
        change ((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_inf_right (D.U i) h)).op).hom (s.1 i + t.1 i) =
          ((structureSheaf X.sheaf).obj.map
            (homOfLE (inf_le_inf_right (D.U i) h)).op).hom (s.1 i) +
          ((structureSheaf X.sheaf).obj.map
            (homOfLE (inf_le_inf_right (D.U i) h)).op).hom (t.1 i)
        exact map_add _ _ _
      map_smul' := by
        intro r s
        let W := U.unop
        let W' := V.unop
        apply Subtype.ext
        funext i
        let g := ((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom
        let g' := ((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_left : W' ⊓ D.U i ≤ W')).op).hom
        let p := ((structureSheaf X.sheaf).obj.map
          (homOfLE (inf_le_inf_right (D.U i) h)).op).hom
        have hr : p (g r) = g' (((structureSheaf X.sheaf).obj.map f).hom r) := by
          dsimp [p, g, g']
          have hf : f = (homOfLE h).op := Subsingleton.elim _ _
          rw [hf]
          let f₁ := (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op
          let f₂ := (homOfLE (inf_le_inf_right (D.U i) h)).op
          let f₃ := (homOfLE (inf_le_left : W' ⊓ D.U i ≤ W')).op
          have hpaths : f₁ ≫ f₂ = (homOfLE h).op ≫ f₃ := Subsingleton.elim _ _
          rw [← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp,
            ← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp, hpaths]
        change p (g r * s.1 i) = g' (((structureSheaf X.sheaf).obj.map f).hom r) * p (s.1 i)
        rw [map_mul, hr]
  }
  · intro U
    let e := (ModuleCat.restrictScalarsId'
      (RingCat.Hom.hom ((structureSheaf X.sheaf).obj.map (𝟙 U)))
      (congrArg RingCat.Hom.hom ((structureSheaf X.sheaf).obj.map_id U))).app
      (ModuleCat.of _ (torsorAssociatedSectionsSubmodule D U.unop))
    apply (cancel_mono e.hom).mp
    simp only [op_unop, Functor.id_obj, ModuleCat.restrictScalarsId'_inv_app]
    apply ConcreteCategory.hom_ext
    intro s
    simp only [ConcreteCategory.comp_apply]
    change (torsorAssociatedGlueData D).gluedPresheaf.map (𝟙 U) s = s
    exact congrArg (fun f => f s) ((torsorAssociatedGlueData D).gluedPresheaf.map_id U)
  · intro U V W f g
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun s => ?_))
    simp only [ModuleCat.restrictScalarsComp', NatIso.ofComponents_inv_app]
    apply Subtype.ext
    funext i
    exact ((structureSheafLocalPresheaf X (D.U i)).map_map _ _ _).symm

/-- On a member of the chosen cover, a compatible family is determined linearly by its
coordinate on that member. -/
noncomputable def torsorAssociatedChartLinearEquiv {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (i : X) (h : W ≤ D.U i) :
    letI : CommRing ((structureSheaf X.sheaf).obj.obj (op W)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op W)))
    torsorAssociatedSectionsSubmodule D W ≃ₗ[(structureSheaf X.sheaf).obj.obj (op W)]
      (structureSheaf X.sheaf).obj.obj (op W) := by
  letI : CommRing ((structureSheaf X.sheaf).obj.obj (op W)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op W)))
  let e := (torsorAssociatedGlueData D).sectionsEquiv i h
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    change (structureSheafLocalPresheaf X (D.U i)).map
        (hV := inf_le_right) (le_inf le_rfl h) (s.1 i + t.1 i) = _
    exact map_add _ _ _
  · intro r s
    let p : (structureSheaf X.sheaf).obj.obj (op W) →+*
        (structureSheaf X.sheaf).obj.obj (op (W ⊓ D.U i)) :=
      ((structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom
    let q : (structureSheaf X.sheaf).obj.obj (op (W ⊓ D.U i)) →+*
        (structureSheaf X.sheaf).obj.obj (op W) :=
      ((structureSheaf X.sheaf).obj.map (homOfLE (le_inf le_rfl h)).op).hom
    change q (p r * s.1 i) = r * q (s.1 i)
    rw [map_mul]
    have hr : q (p r) = r := by
      dsimp [q, p]
      rw [← ConcreteCategory.comp_apply, ← (structureSheaf X.sheaf).obj.map_comp]
      have hp : (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op ≫
          (homOfLE (le_inf le_rfl h)).op = 𝟙 (op W) := Subsingleton.elim _ _
      rw [hp]
      simp
    rw [hr]

/-- The chart coordinate is the restriction of the matching component of the compatible family. -/
theorem torsorAssociatedChartLinearEquiv_apply {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (i : X) (h : W ≤ D.U i)
    (s : torsorAssociatedSectionsSubmodule D W) :
    torsorAssociatedChartLinearEquiv D W i h s =
      (structureSheafLocalPresheaf X (D.U i)).map (hV := inf_le_right)
        (le_inf le_rfl h) (s.1 i) := rfl

/-- The local linear charts commute with restriction inside the cover member. -/
theorem torsorAssociatedChartLinearEquiv_restrict {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    {W W' : Opens X} (i : X) (h : W ≤ D.U i) (h' : W' ≤ W)
    (s : torsorAssociatedSectionsSubmodule D W) :
    torsorAssociatedChartLinearEquiv D W' i (h'.trans h)
        ((torsorAssociatedGlueData D).sectionsMap h' s) =
      (structureSheaf X.sheaf).obj.map (homOfLE h').op
        (torsorAssociatedChartLinearEquiv D W i h s) :=
  (torsorAssociatedGlueData D).sectionsEquiv_map i h h' s

/-- The chart over `W ⊓ U i` reads off the `i`th compatible coordinate. -/
theorem torsorAssociatedChartLinearEquiv_coordinate {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (s : torsorAssociatedSectionsSubmodule D W) (i : X) :
    torsorAssociatedChartLinearEquiv D (W ⊓ D.U i) i inf_le_right
      ((torsorAssociatedModulePresheaf D).map
        (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op s) = s.1 i := by
  let V := W ⊓ D.U i
  let hA : V ⊓ D.U i ≤ W ⊓ D.U i :=
    inf_le_inf_right (D.U i) (inf_le_left : V ≤ W)
  let hB : V ≤ V ⊓ D.U i := le_inf le_rfl inf_le_right
  change torsorAssociatedChartLinearEquiv D (W ⊓ D.U i) i inf_le_right
    ((torsorAssociatedGlueData D).sectionsMap
      (inf_le_left : W ⊓ D.U i ≤ W) s) = s.1 i
  change (torsorAssociatedGlueData D).sectionsEquiv i inf_le_right
      ((torsorAssociatedGlueData D).sectionsMap
        (inf_le_left : V ≤ W) s) = s.1 i
  rw [TopCat.Sheaf.GlueData.sectionsEquiv_apply]
  change (structureSheafLocalPresheaf X (D.U i)).map hB
      (((torsorAssociatedGlueData D).sectionsMap
        (inf_le_left : V ≤ W) s).1 i) = s.1 i
  rw [(torsorAssociatedGlueData D).sectionsMap_val
    (inf_le_left : V ≤ W) s i]
  change (structureSheafLocalPresheaf X (D.U i)).map hB
      ((structureSheafLocalPresheaf X (D.U i)).map hA (s.1 i)) = s.1 i
  rw [(structureSheafLocalPresheaf X (D.U i)).map_map hA hB]
  have hBA : hB.trans hA = le_rfl := Subsingleton.elim _ _
  rw [hBA, (structureSheafLocalPresheaf X (D.U i)).map_id]

/-- The sheaf condition for the compatible-coordinate modules is inherited from the set-valued
glueing construction. -/
theorem torsorAssociatedModulePresheaf_isSheaf {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (torsorAssociatedModulePresheaf D).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget AddCommGrpCat) (torsorAssociatedModulePresheaf D).presheaf).2
  change Presheaf.IsSheaf (Opens.grothendieckTopology X)
    ((torsorAssociatedModulePresheaf D).presheaf ⋙ forget AddCommGrpCat)
  have h : (torsorAssociatedModulePresheaf D).presheaf ⋙ forget AddCommGrpCat =
      (torsorAssociatedGlueData D).gluedPresheaf :=
    CategoryTheory.Functor.ext (fun U => rfl) (fun U V f => rfl)
  rw [h]
  exact (torsorAssociatedGlueData D).gluedPresheaf_isSheaf

/-- The associated sheaf of modules of a torsor, constructed from its transition units. -/
noncomputable def torsorAssociatedSheafOfModules {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    SheafOfModules (structureSheaf X.sheaf) where
  val := torsorAssociatedModulePresheaf D
  isSheaf := torsorAssociatedModulePresheaf_isSheaf D

/-- The local linear charts assemble into an isomorphism of sheaves of modules on each
cover member. -/
noncomputable def torsorAssociatedChartIso {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) (i : X) :
    (torsorAssociatedSheafOfModules D).over (D.U i) ≅
      SheafOfModules.unit ((structureSheaf X.sheaf).over (D.U i)) := by
  let M := torsorAssociatedSheafOfModules D
  let U := D.U i
  let E : (M.over U).val ≅
      (SheafOfModules.unit ((structureSheaf X.sheaf).over U)).val :=
    PresheafOfModules.isoMk (fun V => by
      let W := V.unop.left
      let hW : W ≤ U := V.unop.hom.le
      exact (torsorAssociatedChartLinearEquiv D W i hW).toModuleIso) (by
        intro V V' f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        let W := V.unop.left
        let W' := V'.unop.left
        let hW : W ≤ U := V.unop.hom.le
        let hW' : W' ≤ U := V'.unop.hom.le
        let h' : W' ≤ W := f.unop.left.down.down
        change torsorAssociatedChartLinearEquiv D W' i hW'
            ((torsorAssociatedGlueData D).sectionsMap h' s) =
          (structureSheaf X.sheaf).obj.map (homOfLE h').op
            (torsorAssociatedChartLinearEquiv D W i hW s)
        have hp : h'.trans hW = hW' := Subsingleton.elim _ _
        rw [← hp]
        exact torsorAssociatedChartLinearEquiv_restrict D i hW h' s)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso E

/-- The module associated to a torsor is finite locally free of rank one. -/
instance torsorAssociatedSheafOfModules_isFiniteLocallyFreeOfRank
    {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) (torsorAssociatedSheafOfModules D) 1 := by
  let M := torsorAssociatedSheafOfModules D
  let q : SheafOfModules.LocalGeneratorsData.{u} M := {
    I := X
    X := D.U
    coversTop := (Opens.coversTop_iff X D.U).mpr
      (TopologicalSpace.IsOpenCover.mk D.covers.symm)
    generators := fun i => {
      I := PUnit
      s := ((M.over (D.U i)).freeHomEquiv
        ((freeUniqueIsoUnit (R := (structureSheaf X.sheaf).over (D.U i))
          (I := PUnit)).hom ≫ (torsorAssociatedChartIso D i).inv))
      epi := by
        change Epi ((M.over (D.U i)).freeHomEquiv.symm
          ((M.over (D.U i)).freeHomEquiv _))
        rw [Equiv.symm_apply_apply]
        infer_instance }
  }
  have hq : q.IsLocallyFreeData := by
    constructor
    intro i
    change IsIso ((M.over (D.U i)).freeHomEquiv.symm
      ((M.over (D.U i)).freeHomEquiv
        ((freeUniqueIsoUnit (R := (structureSheaf X.sheaf).over (D.U i))
          (I := PUnit)).hom ≫ (torsorAssociatedChartIso D i).inv)))
    rw [Equiv.symm_apply_apply]
    infer_instance
  have hRank : ∀ i, Nonempty ((q.generators i).I ≃ Fin 1) := by
    intro i
    change Nonempty (PUnit ≃ Fin 1)
    exact ⟨Equiv.ofUnique PUnit (Fin 1)⟩
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q, hq, hRank⟩ }

/-- A generating section of the associated module has unit coordinates in every local chart. -/
theorem torsorAssociatedChart_isUnit_of_generator {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W)
    (i : X) :
    IsUnit (torsorAssociatedChartLinearEquiv D (W ⊓ D.U i) i inf_le_right
      ((torsorAssociatedSheafOfModules D).val.restrictₛₗ
        (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op s.val)) := by
  let V := W ⊓ D.U i
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op V)))
  let M := torsorAssociatedSheafOfModules D
  let e := torsorAssociatedChartLinearEquiv D V i inf_le_right
  let sV : M.val.obj (op V) := M.val.restrictₛₗ
    (homOfLE (inf_le_left : V ≤ W)).op s.val
  let x := e sV
  have hgen := s.property V inf_le_left
  have hchart (r : (structureSheaf X.sheaf).obj.obj (op V)) : e (r • sV) = r * x :=
    e.map_smul r sV
  have hbij : Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) => r * x) := by
    constructor
    · intro r t hrt
      exact hgen.1 (e.injective ((hchart r).trans (hrt.trans (hchart t).symm)))
    · intro y
      obtain ⟨m, hm⟩ := hgen.2 (e.symm y)
      exact ⟨m, (hchart m).symm.trans ((congrArg e hm).trans (e.apply_symm_apply y))⟩
  obtain ⟨a, ha⟩ := hbij.2 1
  exact ⟨⟨x, a, (mul_comm x a).trans ha, ha⟩, rfl⟩

/-- On each chosen chart, a generator of the associated module determines a section of the
original torsor by its unit coordinate. -/
noncomputable def torsorAssociatedLocalGeneratorImage {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W)
    (i : X) : F.F.obj (W ⊓ D.U i) := by
  let V := W ⊓ D.U i
  let M := torsorAssociatedSheafOfModules D
  let e := torsorAssociatedChartLinearEquiv D V i inf_le_right
  let sV : M.val.obj (op V) := M.val.restrictₛₗ
    (homOfLE (inf_le_left : V ≤ W)).op s.val
  let x := e sV
  let hx : IsUnit x := torsorAssociatedChart_isUnit_of_generator D W s i
  exact F.action.act (Multiplicative.ofAdd (Additive.ofMul hx.unit))
    (F.F.res inf_le_right (D.localSection i))

/-- The unit coordinate on a cover member is a generator of the associated module. -/
noncomputable def torsorAssociatedChartGenerator {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) (i : X) :
    GeneratorSections X (torsorAssociatedSheafOfModules D) (D.U i) := by
  let M := torsorAssociatedSheafOfModules D
  letI : CommRing ((structureSheaf X.sheaf).obj.obj (op (D.U i))) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op (D.U i))))
  let e := torsorAssociatedChartLinearEquiv D (D.U i) i le_rfl
  let s : torsorAssociatedSectionsSubmodule D (D.U i) := e.symm 1
  refine ⟨s, ?_⟩
  intro V hV
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op V)))
  let eV := torsorAssociatedChartLinearEquiv D V i hV
  let sV := M.val.restrictₛₗ (homOfLE hV).op s
  have hsV : eV sV = 1 := by
    have hr := torsorAssociatedChartLinearEquiv_restrict D i le_rfl hV s
    change eV sV = (structureSheaf X.sheaf).obj.map (homOfLE hV).op (e s) at hr
    rw [hr]
    change (structureSheaf X.sheaf).obj.map (homOfLE hV).op (e (e.symm 1)) = 1
    rw [e.apply_symm_apply]
    simp
  have hchart (r : (structureSheaf X.sheaf).obj.obj (op V)) : eV (r • sV) = r :=
    (eV.map_smul r sV).trans (by rw [hsV]; simp)
  constructor
  · intro r t hrt
    exact (hchart r).symm.trans ((congrArg eV hrt).trans (hchart t))
  · intro y
    refine ⟨eV y, ?_⟩
    apply eV.injective
    exact hchart (eV y)

/-- The sections of the original torsor obtained from a generator of the
associated module agree on overlaps of the chosen trivializing cover. -/
theorem torsorAssociatedLocalGeneratorImage_compatible
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) (W : Opens X)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) (i j : X) :
    F.F.res (inf_le_left :
        (W ⊓ D.U i) ⊓ (W ⊓ D.U j) ≤ W ⊓ D.U i)
        (torsorAssociatedLocalGeneratorImage D W s i) =
      F.F.res (inf_le_right :
        (W ⊓ D.U i) ⊓ (W ⊓ D.U j) ≤ W ⊓ D.U j)
        (torsorAssociatedLocalGeneratorImage D W s j) := by
  classical
  let M := torsorAssociatedSheafOfModules D
  let Wi := W ⊓ D.U i
  let Wj := W ⊓ D.U j
  let V := Wi ⊓ Wj
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op Wi)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op Wi)))
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op Wj)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op Wj)))
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op V)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op V)))
  let hVi : V ≤ Wi := inf_le_left
  let hVj : V ≤ Wj := inf_le_right
  let hVW : V ≤ W := hVi.trans inf_le_left
  let hVUi : V ≤ D.U i := hVi.trans inf_le_right
  let hVUj : V ≤ D.U j := hVj.trans inf_le_right
  let ei := torsorAssociatedChartLinearEquiv D Wi i inf_le_right
  let ej := torsorAssociatedChartLinearEquiv D Wj j inf_le_right
  let si : M.val.obj (op Wi) := M.val.restrictₛₗ (homOfLE inf_le_left).op s.val
  let sj : M.val.obj (op Wj) := M.val.restrictₛₗ (homOfLE inf_le_left).op s.val
  let xi := ei si
  let xj := ej sj
  let t := torsorTransitionUnit D i j (V := V) hVUi hVUj
  have hxi : IsUnit xi := torsorAssociatedChart_isUnit_of_generator D W s i
  have hxj : IsUnit xj := torsorAssociatedChart_isUnit_of_generator D W s j
  have hcoord : (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
      (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi =
      (structureSheaf X.sheaf).obj.map (homOfLE hVj).op xj := by
    have hcompat := s.val.property i j
    change (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
        (structureSheaf X.sheaf).obj.map (homOfLE hVi).op (s.val.1 i) =
      (structureSheaf X.sheaf).obj.map (homOfLE hVj).op (s.val.1 j) at hcompat
    have hxi' : xi = s.val.1 i := by
      dsimp [xi, ei, si]
      exact torsorAssociatedChartLinearEquiv_coordinate D W s.val i
    have hxj' : xj = s.val.1 j := by
      dsimp [xj, ej, sj]
      exact torsorAssociatedChartLinearEquiv_coordinate D W s.val j
    rw [hxi', hxj']
    exact hcompat
  let ui := hxi.unit
  let uj := hxj.unit
  let gi : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj Wi :=
    Multiplicative.ofAdd (Additive.ofMul ui)
  let gj : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj Wj :=
    Multiplicative.ofAdd (Additive.ofMul uj)
  let gt : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj V :=
    Multiplicative.ofAdd (Additive.ofMul t)
  have hui : (ui : (structureSheaf X.sheaf).obj.obj (op Wi)) = xi := hxi.unit_spec
  have huJ : (uj : (structureSheaf X.sheaf).obj.obj (op Wj)) = xj := hxj.unit_spec
  let giV := (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hVi gi
  let gjV := (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hVj gj
  have hgroup : giV = gjV * gt := by
    apply Multiplicative.ext
    apply Additive.ext
    apply Units.ext
    change (structureSheaf X.sheaf).obj.map (homOfLE hVi).op ui =
      (structureSheaf X.sheaf).obj.map (homOfLE hVj).op uj * t
    rw [hui, huJ]
    have hmul :
        (structureSheaf X.sheaf).obj.map (homOfLE hVj).op xj * ↑t =
          (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi := by
      calc
        (structureSheaf X.sheaf).obj.map (homOfLE hVj).op xj * ↑t =
            (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) *
              (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi * ↑t :=
          congrArg (fun a => a * ↑t) hcoord.symm
        _ = (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi := by
          calc
            _ = (↑(t⁻¹) : (structureSheaf X.sheaf).obj.obj (op V)) * ↑t *
                (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi := by ac_rfl
            _ = (structureSheaf X.sheaf).obj.map (homOfLE hVi).op xi := by simp
    exact hmul.symm
  have htransition : F.action.act gt (F.F.res hVUi (D.localSection i)) =
      F.F.res hVUj (D.localSection j) := torsorTransitionElement_spec D i j hVUi hVUj
  change F.F.res hVi
      (F.action.act gi (F.F.res inf_le_right (D.localSection i))) =
    F.F.res hVj
      (F.action.act gj (F.F.res inf_le_right (D.localSection j)))
  rw [F.action.res_act hVi, F.action.res_act hVj]
  have hbase_i : F.F.res hVi (F.F.res inf_le_right (D.localSection i)) =
      F.F.res hVUi (D.localSection i) := by
    rw [F.F.res_comp]
  have hbase_j : F.F.res hVj (F.F.res inf_le_right (D.localSection j)) =
      F.F.res hVUj (D.localSection j) := by
    rw [F.F.res_comp]
  rw [hbase_i, hbase_j, ← htransition]
  change F.action.act giV (F.F.res hVUi (D.localSection i)) =
    F.action.act gjV
      (F.action.act gt (F.F.res hVUi (D.localSection i)))
  rw [← F.action.mul_act gjV gt, ← hgroup]

/-- Restricting a torsor cover to an open gives a cover of that open. -/
theorem torsorCoverData_restrict_covers {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F)
    (W : Opens X) : W = ⨆ i : X, W ⊓ D.U i := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ⨆ i : X, D.U i := by
      rw [← D.covers]
      trivial
    rcases Opens.mem_iSup.mp hx' with ⟨i, hi⟩
    exact Opens.mem_iSup.mpr ⟨i, ⟨hx, hi⟩⟩
  · exact iSup_le fun i => inf_le_left

/-- A generator of the associated module recovers compatible local sections of the
original torsor. -/
noncomputable def torsorAssociatedLocalGeneratorSection
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) (W : Opens X)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) : F.F.obj W := by
  classical
  let P := F.F.toPresheafOfSets
  let V (i : X) := W ⊓ D.U i
  have hP := F.F.isSheaf W X V (fun _ => inf_le_left)
    (torsorCoverData_restrict_covers D W)
  let q : P.CompatibleFamily V := ⟨
    fun i => torsorAssociatedLocalGeneratorImage D W s i,
    fun i j Y hYi hYj => by
      have hY : Y ≤ V i ⊓ V j := le_inf hYi hYj
      exact (P.res_comp hY inf_le_left _).symm.trans
        ((congrArg (P.res hY) (torsorAssociatedLocalGeneratorImage_compatible D W s i j)).trans
          (P.res_comp hY inf_le_right _))⟩
  exact Classical.choose (hP.2 q)

/-- The glued torsor section restricts to the chartwise section used to define it. -/
theorem torsorAssociatedLocalGeneratorSection_spec
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) (W : Opens X)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) (i : X) :
    F.F.res (inf_le_left : W ⊓ D.U i ≤ W)
        (torsorAssociatedLocalGeneratorSection D W s) =
      torsorAssociatedLocalGeneratorImage D W s i := by
  classical
  let P := F.F.toPresheafOfSets
  let V (k : X) := W ⊓ D.U k
  have hP := F.F.isSheaf W X V (fun _ => inf_le_left)
    (torsorCoverData_restrict_covers D W)
  let q : P.CompatibleFamily V := ⟨
    fun k => torsorAssociatedLocalGeneratorImage D W s k,
    fun k l Y hYk hYl => by
      have hY : Y ≤ V k ⊓ V l := le_inf hYk hYl
      exact (P.res_comp hY inf_le_left _).symm.trans
        ((congrArg (P.res hY) (torsorAssociatedLocalGeneratorImage_compatible D W s k l)).trans
          (P.res_comp hY inf_le_right _))⟩
  have hspec : P.toCompatibleFamily V (fun _ => inf_le_left)
      (torsorAssociatedLocalGeneratorSection D W s) = q :=
    Classical.choose_spec (hP.2 q)
  exact congrArg (fun c => c.1 i) hspec

/-- The chartwise torsor sections used in the gluing construction commute with
restriction to smaller opens. -/
theorem torsorAssociatedLocalGeneratorImage_restrict
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) {W W' : Opens X} (h : W' ≤ W)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) (i : X) :
    F.F.res (inf_le_inf_right (D.U i) h)
        (torsorAssociatedLocalGeneratorImage D W s i) =
      torsorAssociatedLocalGeneratorImage D W'
        (generatorSectionsRestrict X (torsorAssociatedSheafOfModules D) h s) i := by
  classical
  let M := torsorAssociatedSheafOfModules D
  let Wi := W ⊓ D.U i
  let Wi' := W' ⊓ D.U i
  let hWi : Wi' ≤ Wi := inf_le_inf_right (D.U i) h
  let e := torsorAssociatedChartLinearEquiv D Wi i inf_le_right
  let e' := torsorAssociatedChartLinearEquiv D Wi' i inf_le_right
  let si : M.val.obj (op Wi) := M.val.restrictₛₗ (homOfLE inf_le_left).op s.val
  let si' : M.val.obj (op Wi') := M.val.restrictₛₗ (homOfLE inf_le_left).op
    (generatorSectionsRestrict X M h s).val
  let xi := e si
  let xi' := e' si'
  have hsi : si' = M.val.restrictₛₗ (homOfLE hWi).op si := by
    change M.val.map (homOfLE inf_le_left).op
        (M.val.map (homOfLE h).op s.val) =
      M.val.map (homOfLE hWi).op
        (M.val.map (homOfLE inf_le_left).op s.val)
    rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
    congr 1
  have hcoord : xi' = (structureSheaf X.sheaf).obj.map (homOfLE hWi).op xi := by
    dsimp [xi', e']
    rw [hsi]
    exact torsorAssociatedChartLinearEquiv_restrict D i inf_le_right hWi si
  let hx := torsorAssociatedChart_isUnit_of_generator D W s i
  let hx' := torsorAssociatedChart_isUnit_of_generator D W'
    (generatorSectionsRestrict X M h s) i
  have hunit : Units.map
      ((structureSheaf X.sheaf).obj.map (homOfLE hWi).op).hom.toMonoidHom hx.unit =
      hx'.unit := by
    apply Units.ext
    change (structureSheaf X.sheaf).obj.map (homOfLE hWi).op
        (hx.unit : (structureSheaf X.sheaf).obj.obj (op Wi)) =
      (hx'.unit : (structureSheaf X.sheaf).obj.obj (op Wi'))
    exact (congrArg ((structureSheaf X.sheaf).obj.map (homOfLE hWi).op) hx.unit_spec).trans
      (hcoord.symm.trans hx'.unit_spec.symm)
  let g := Multiplicative.ofAdd (Additive.ofMul hx.unit)
  let g' := Multiplicative.ofAdd (Additive.ofMul hx'.unit)
  have hgroup :
      (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res hWi g =
        g' := by
    apply Multiplicative.ext
    apply Additive.ext
    exact hunit
  have hbase : F.F.res hWi (F.F.res inf_le_right (D.localSection i)) =
      F.F.res (inf_le_right : Wi' ≤ D.U i) (D.localSection i) := by
    rw [F.F.res_comp]
  change F.F.res hWi
      (F.action.act g (F.F.res inf_le_right (D.localSection i))) =
    F.action.act g'
      (F.F.res (inf_le_right : Wi' ≤ D.U i) (D.localSection i))
  rw [F.action.res_act hWi g, hgroup, hbase]

/-- The global section recovered from a generator commutes with restriction. -/
theorem torsorAssociatedLocalGeneratorSection_restrict
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) {W W' : Opens X} (h : W' ≤ W)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) :
    F.F.res h (torsorAssociatedLocalGeneratorSection D W s) =
      torsorAssociatedLocalGeneratorSection D W'
        (generatorSectionsRestrict X (torsorAssociatedSheafOfModules D) h s) := by
  classical
  let P := F.F.toPresheafOfSets
  let V (i : X) := W' ⊓ D.U i
  have hP := F.F.isSheaf W' X V (fun _ => inf_le_left)
    (torsorCoverData_restrict_covers D W')
  apply hP.1
  apply Subtype.ext
  funext i
  let hVi : V i ≤ W ⊓ D.U i := inf_le_inf_right (D.U i) h
  calc
    P.res (inf_le_left : V i ≤ W')
        (P.res h (torsorAssociatedLocalGeneratorSection D W s)) =
      P.res (inf_le_left.trans h) (torsorAssociatedLocalGeneratorSection D W s) :=
        P.res_comp (inf_le_left : V i ≤ W') h _
    _ = P.res (hVi.trans inf_le_left)
        (torsorAssociatedLocalGeneratorSection D W s) := by
          congr 1
    _ = P.res hVi
        (P.res inf_le_left (torsorAssociatedLocalGeneratorSection D W s)) :=
          (P.res_comp hVi inf_le_left _).symm
    _ = P.res hVi (torsorAssociatedLocalGeneratorImage D W s i) := by
          rw [torsorAssociatedLocalGeneratorSection_spec]
    _ = torsorAssociatedLocalGeneratorImage D W'
        (generatorSectionsRestrict X (torsorAssociatedSheafOfModules D) h s) i :=
          torsorAssociatedLocalGeneratorImage_restrict D h s i
    _ = P.res (inf_le_left : V i ≤ W')
        (torsorAssociatedLocalGeneratorSection D W'
          (generatorSectionsRestrict X (torsorAssociatedSheafOfModules D) h s)) := by
          rw [torsorAssociatedLocalGeneratorSection_spec]

/-- Multiplying an associated-module generator by a unit multiplies its recovered
torsor section by the same unit. -/
theorem torsorAssociatedLocalGeneratorImage_smul
    {X : RingedSpace.{u, u}} {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)}
    (D : TorsorCoverData X F) (W : Opens X)
    (f : ((structureSheaf X.sheaf).obj.obj (op W))ˣ)
    (s : GeneratorSections X (torsorAssociatedSheafOfModules D) W) (i : X) :
    torsorAssociatedLocalGeneratorImage D W
        (generatorSectionsSmul X (torsorAssociatedSheafOfModules D) W f s) i =
      F.action.act
        (Multiplicative.ofAdd (Additive.ofMul
          (Units.map ((structureSheaf X.sheaf).obj.map
            (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom.toMonoidHom f)))
        (torsorAssociatedLocalGeneratorImage D W s i) := by
  classical
  let M := torsorAssociatedSheafOfModules D
  let Wi := W ⊓ D.U i
  let fWi : ((structureSheaf X.sheaf).obj.obj (op Wi))ˣ :=
    Units.map ((structureSheaf X.sheaf).obj.map
      (homOfLE (inf_le_left : Wi ≤ W)).op).hom.toMonoidHom f
  let e := torsorAssociatedChartLinearEquiv D Wi i inf_le_right
  let si : M.val.obj (op Wi) := M.val.restrictₛₗ (homOfLE inf_le_left).op s.val
  let s' := generatorSectionsSmul X M W f s
  let si' : M.val.obj (op Wi) := M.val.restrictₛₗ (homOfLE inf_le_left).op s'.val
  let xi := e si
  let xi' := e si'
  have hsi : si' = (fWi : (structureSheaf X.sheaf).obj.obj (op Wi)) • si := by
    change M.val.restrictₛₗ (homOfLE inf_le_left).op
        ((f : (structureSheaf X.sheaf).obj.obj (op W)) • s.val) = _
    rw [PresheafOfModules.restrictₛₗ_apply, map_smul]
    simp [fWi, si]
  have hcoord : xi' = (fWi : (structureSheaf X.sheaf).obj.obj (op Wi)) * xi := by
    dsimp [xi', xi]
    rw [hsi]
    exact e.map_smul _ _
  let hx := torsorAssociatedChart_isUnit_of_generator D W s i
  let hx' := torsorAssociatedChart_isUnit_of_generator D W s' i
  have hunit : fWi * hx.unit = hx'.unit := by
    apply Units.ext
    change (fWi : (structureSheaf X.sheaf).obj.obj (op Wi)) *
        (hx.unit : (structureSheaf X.sheaf).obj.obj (op Wi)) =
      (hx'.unit : (structureSheaf X.sheaf).obj.obj (op Wi))
    exact (congrArg (fun a => (fWi : (structureSheaf X.sheaf).obj.obj (op Wi)) * a)
      hx.unit_spec).trans (hcoord.symm.trans hx'.unit_spec.symm)
  let g := Multiplicative.ofAdd (Additive.ofMul hx.unit)
  let g' := Multiplicative.ofAdd (Additive.ofMul hx'.unit)
  let gf := Multiplicative.ofAdd (Additive.ofMul fWi)
  have hgroup : g' = gf * g := by
    apply Multiplicative.ext
    apply Additive.ext
    change hx'.unit = fWi * hx.unit
    exact hunit.symm
  change F.action.act g' (F.F.res inf_le_right (D.localSection i)) =
    F.action.act gf (F.action.act g (F.F.res inf_le_right (D.localSection i)))
  exact (congrArg (fun z => F.action.act z
    (F.F.res inf_le_right (D.localSection i))) hgroup).trans
      (F.action.mul_act gf g (F.F.res inf_le_right (D.localSection i)))

/-- The chartwise recovery maps glue to a natural equivariant morphism from the
generator torsor of the associated module to the original torsor. -/
noncomputable def torsorAssociatedGeneratorTorsorHom
    {X : RingedSpace.{u, u}} [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    Stacks.SpaceTorsor.TorsorHom
      (generatorTorsor X (torsorAssociatedSheafOfModules D)).action F.action := by
  classical
  let G := generatorTorsor X (torsorAssociatedSheafOfModules D)
  refine {
    app := fun W s =>
      torsorAssociatedLocalGeneratorSection D W (G.sectionsEquiv W s)
    naturality := ?_
    map_act := ?_ }
  · intro W W' h s
    have hsections : G.sectionsEquiv W' (G.F.res h s) =
        generatorSectionsRestrict X (torsorAssociatedSheafOfModules D) h
          (G.sectionsEquiv W s) :=
      Subtype.ext (G.sectionsEquiv_restrict h s)
    change torsorAssociatedLocalGeneratorSection D W'
        (G.sectionsEquiv W' (G.F.res h s)) =
      F.F.res h (torsorAssociatedLocalGeneratorSection D W (G.sectionsEquiv W s))
    rw [hsections]
    exact (torsorAssociatedLocalGeneratorSection_restrict D h
      (G.sectionsEquiv W s)).symm
  · intro W g s
    let P := F.F.toPresheafOfSets
    let V (i : X) := W ⊓ D.U i
    have hP := F.F.isSheaf W X V (fun _ => inf_le_left)
      (torsorCoverData_restrict_covers D W)
    apply hP.1
    apply Subtype.ext
    funext i
    have hspec₁ := torsorAssociatedLocalGeneratorSection_spec D W
      (G.sectionsEquiv W (G.action.act g s)) i
    have hspec₂ := torsorAssociatedLocalGeneratorSection_spec D W
      (G.sectionsEquiv W s) i
    change F.F.res (inf_le_left : V i ≤ W)
        (torsorAssociatedLocalGeneratorSection D W
          (G.sectionsEquiv W (G.action.act g s))) =
      F.F.res (inf_le_left : V i ≤ W)
        (F.action.act g
          (torsorAssociatedLocalGeneratorSection D W (G.sectionsEquiv W s)))
    rw [hspec₁, F.action.res_act, hspec₂]
    let f := Additive.toMul (Multiplicative.toAdd g)
    have hg : g = Multiplicative.ofAdd (Additive.ofMul f) := rfl
    have hs : G.sectionsEquiv W (G.action.act g s) =
        generatorSectionsSmul X (torsorAssociatedSheafOfModules D) W f
          (G.sectionsEquiv W s) := by
      rw [hg]
      apply Subtype.ext
      exact G.sectionsEquiv_smul W f s
    rw [hs]
    have hres :
        (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).res
            (inf_le_left : W ⊓ D.U i ≤ W) g =
          Multiplicative.ofAdd (Additive.ofMul
            (Units.map ((structureSheaf X.sheaf).obj.map
              (homOfLE (inf_le_left : W ⊓ D.U i ≤ W)).op).hom.toMonoidHom f)) := rfl
    rw [hres]
    exact torsorAssociatedLocalGeneratorImage_smul D W f
      (G.sectionsEquiv W s) i

/-- An equivariant map of pseudo-torsor actions is injective on sections wherever the
source has a section. -/
public theorem torsorHom_injective_of_nonempty {X : Type u} [TopologicalSpace X]
    {G : Stacks.SpaceTorsor.PresheafOfGroups.{u, u} X}
    {F F' : Stacks.SpaceTorsor.PresheafOfSets.{u, u} X}
    {a : Stacks.SpaceTorsor.Action G F} {a' : Stacks.SpaceTorsor.Action G F'}
    (ha : a.IsPseudoTorsor) (ha' : a'.IsPseudoTorsor)
    (φ : Stacks.SpaceTorsor.TorsorHom a a') (U : Opens X)
    (hF : Nonempty (F.obj U)) : Function.Injective (φ.app U) := by
  classical
  obtain ⟨s⟩ := hF
  intro x y hxy
  obtain ⟨g, hg, hgu⟩ := (ha U ⟨s⟩).2 s x
  obtain ⟨h, hh, hhu⟩ := (ha U ⟨s⟩).2 s y
  have hgh : g = h := by
    have hgs : a'.act g (φ.app U s) = φ.app U x := by
      rw [← φ.map_act]
      exact congrArg (φ.app U) hg
    have hhs : a'.act h (φ.app U s) = φ.app U y := by
      rw [← φ.map_act]
      exact congrArg (φ.app U) hh
    exact ((ha' U ⟨φ.app U s⟩).2 (φ.app U s) (φ.app U x)).unique hgs (hhs.trans hxy.symm)
  rw [← hg, ← hh, hgh]

/-- The generator torsor of the module glued from a torsor `F` under the sheaf of units is
isomorphic to `F` itself. -/
public theorem torsorAssociatedGeneratorTorsorHom_isIso
    {X : RingedSpace.{u, u}} [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    (torsorAssociatedGeneratorTorsorHom D).IsIso := by
  classical
  let M := torsorAssociatedSheafOfModules D
  let G := generatorTorsor X M
  let φ := torsorAssociatedGeneratorTorsorHom D
  intro W
  let V (i : X) := W ⊓ D.U i
  have hV : ∀ i, V i ≤ W := fun _ => inf_le_left
  have hcover : W = ⨆ i, V i := torsorCoverData_restrict_covers D W
  let cU (i : X) : G.F.obj (D.U i) :=
    (G.sectionsEquiv (D.U i)).symm (torsorAssociatedChartGenerator D i)
  let c (i : X) : G.F.obj (V i) := G.F.res inf_le_right (cU i)
  have hcF (i : X) : Nonempty (F.F.obj (V i)) := ⟨F.F.res inf_le_right (D.localSection i)⟩
  have hcG (i : X) : Nonempty (G.F.obj (V i)) := ⟨c i⟩
  have hlocal_inj (i : X) : Function.Injective (φ.app (V i)) :=
    torsorHom_injective_of_nonempty G.isTorsor.1 F.isTorsor.1 φ (V i) (hcG i)
  have hinj : Function.Injective (φ.app W) := by
    intro s t hst
    have hcompat := G.F.isSheaf W X V hV hcover
    apply hcompat.1
    apply Subtype.ext
    funext i
    have hi : φ.app (V i) (G.F.res (hV i) s) =
        φ.app (V i) (G.F.res (hV i) t) := by
      rw [φ.naturality (hV i) s, φ.naturality (hV i) t]
      exact congrArg (F.F.res (hV i)) hst
    exact hlocal_inj i hi
  apply And.intro hinj
  intro t
  let b (i : X) : G.F.obj (V i) := by
    let ti := F.F.res (hV i) t
    let ci := c i
    let htrans := (F.isTorsor.1 (V i) (hcF i)).2 (φ.app (V i) ci) ti
    exact G.action.act (Classical.choose htrans) ci
  have hbmap (i : X) : φ.app (V i) (b i) = F.F.res (hV i) t := by
    dsimp [b]
    let ti := F.F.res (hV i) t
    let ci := c i
    let htrans := (F.isTorsor.1 (V i) (hcF i)).2 (φ.app (V i) ci) ti
    exact (φ.map_act (Classical.choose htrans) ci).trans (Classical.choose_spec htrans).1
  have hbc (i j : X) (Z : Opens X) (hZi : Z ≤ V i) (hZj : Z ≤ V j) :
      G.F.res hZi (b i) = G.F.res hZj (b j) := by
    apply torsorHom_injective_of_nonempty G.isTorsor.1 F.isTorsor.1 φ Z
      ⟨G.F.res hZi (c i)⟩
    have hi : φ.app Z (G.F.res hZi (b i)) = F.F.res hZi (F.F.res (hV i) t) :=
      (φ.naturality hZi (b i)).trans (congrArg (F.F.res hZi) (hbmap i))
    have hj : φ.app Z (G.F.res hZj (b j)) = F.F.res hZj (F.F.res (hV j) t) :=
      (φ.naturality hZj (b j)).trans (congrArg (F.F.res hZj) (hbmap j))
    rw [hi, hj, F.F.res_comp, F.F.res_comp]
  let bf : G.F.toPresheafOfSets.CompatibleFamily V := ⟨b, hbc⟩
  obtain ⟨s, hs⟩ := (G.F.isSheaf W X V hV hcover).2 bf
  refine ⟨s, ?_⟩
  apply (F.F.isSheaf W X V hV hcover).1
  apply Subtype.ext
  funext i
  have hres : G.F.res (hV i) s = b i :=
    congrArg (fun q : G.F.toPresheafOfSets.CompatibleFamily V => q.val i) hs
  exact (φ.naturality (hV i) s).symm.trans ((congrArg _ hres).trans (hbmap i))

end Stacks.Cohomology.Generators

end
