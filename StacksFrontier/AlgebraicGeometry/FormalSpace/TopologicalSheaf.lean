module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Limits.Defs

/-!
# Sheaves of topological spaces on a site

Sheaves valued in topological spaces are the coefficient category for formal algebraic spaces
in the sense of EGA.  This file records the content of Stacks 0AI4 for presheaves of
topological spaces on a site `C`:

* `Sh(C, Top)` has limits, computed sectionwise, and the inclusion into presheaves creates them
  (`CategoryTheory.Sheaf.hasLimitsOfSize`, `CategoryTheory.Sheaf.createsLimits`);
* every map from a fixed presheaf to a sheaf factors through a subsheaf of bounded size
  (`exists_bounded_subsheaf_factorization`, with the size `sheafSize`);
* sheafification exists, as the left adjoint given by the adjoint functor theorem
  (`hasWeakSheafify_topCat`);
* for a point `p` of the site given by `u : C ⥤ Sets` (Stacks 00Y5), the presheaf
  `U ↦ Map(u(U), M)` with the product topology is a sheaf (`isSheaf_mappingPresheaf`) and
  `F_p = (F^#)_p` (`isIso_elementColimit_map_toSheafify_topCat`), both in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.TopologicalSheafPoint`. These two are stated
  directly for a functor `u` satisfying conditions (1) and (2) of Stacks 00Y5, not for Mathlib's
  `GrothendieckTopology.Point`, which additionally assumes the category of neighbourhoods
  cofiltered.

## Implementation notes

Stacks remarks that the same arguments work for presheaves of topological abelian groups,
topological rings and topological modules. Those variants (limits, the size bound, existence of
sheafification, the sheaf `U ↦ Map(u(U), M)` and `F_p = (F^#)_p`) are proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.TopologicalAlgebraicSheaf`, for Mathlib's
`TopModuleCat R` and `TopCommRingCat` and for `TopAddCommGrpCat` (topological `ℤ`-modules), by
the general argument of `StacksFrontier.CategoryTheory.Sites.SheafificationOfClosedSubobjects`.

## References

* [Stacks Project, Tag 0AI4](https://stacks.math.columbia.edu/tag/0AI4)
-/

@[expose] public section

namespace CategoryTheory.TopologicalSheaf

section

open CategoryTheory Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The size of a sheaf of topological spaces is the supremum of the cardinalities of its
values on objects of the site. -/
@[stacks 0AI4 "size"]
public noncomputable abbrev sheafSize (H : Sheaf J TopCat.{w}) : Cardinal.{max u w} :=
  ⨆ U : C, Cardinal.lift.{u} (Cardinal.mk (H.obj.obj (op U)))

end

section

add_to_stacks 0AI4 "limits" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_sga "3 IV 4.4.1" "(i)" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_sga "4 I 8.12.9" "partial" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_sga "4 II 4.1" "more general" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_sga "4 II 4.8" "more general" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_ega "0 3.2.6" "partial" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_stacks 0AI4 "limits" CategoryTheory.Sheaf.createsLimits
add_to_sga "3 IV 4.4.1" "more general" CategoryTheory.Sheaf.createsLimits
add_to_sga "4 II 4.1" "more general" CategoryTheory.Sheaf.createsLimits
add_to_ega "0 3.2.6" "more general" CategoryTheory.Sheaf.createsLimits

end

section

open CategoryTheory Opposite

universe w w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private inductive BoundedWitness (K : Precoverage C) (ι : C → Type w) :
    C → Type max (max u w) v where
  | base (X : C) : ι X → BoundedWitness K ι X
  | restrict {X Y : C} (f : X ⟶ Y) : BoundedWitness K ι Y → BoundedWitness K ι X
  | amalgamate {X : C} {R : Presieve X} (hR : R ∈ K X)
      (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → BoundedWitness K ι Y) :
      BoundedWitness K ι X

private noncomputable def BoundedWitness.eval {K : Precoverage C} {ι : C → Type w}
    {P : Cᵒᵖ ⥤ Type w'}
    (hP : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R)
    (g : ∀ X, ι X → P.obj (op X)) : {X : C} → BoundedWitness K ι X →
      Option (P.obj (op X))
  | _, .base X i => some (g X i)
  | _, .restrict f i => (eval hP g i).map (P.map f.op)
  | _, .amalgamate (R := R) hR h => by
    let vals := fun Y (f : Y ⟶ _) (hf : R f) => eval hP g (h f hf)
    classical
    exact if hall : ∀ (Y : C) (f : Y ⟶ _) (hf : R f), (vals Y f hf).isSome then
      let y : R.FamilyOfElements P := fun Y f hf => (vals Y f hf).get (hall Y f hf)
      if hy : y.Compatible then some (hP _ hR y hy).choose else none
    else none

private theorem exists_boundedWitness_eval {K : Precoverage C} {ι : C → Type w}
    {P : Cᵒᵖ ⥤ Type w'}
    (hP : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R)
    (g : ∀ X, ι X → P.obj (op X)) (X : C) {x : P.obj (op X)}
    (hx : K.SubsheafClosure (fun Y => Set.range (g Y)) X x) :
    ∃ z : BoundedWitness K ι X, BoundedWitness.eval hP g z = some x := by
  induction hx with
  | base hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨.base _ i, rfl⟩
  | restrict f hx ih =>
      obtain ⟨z, hz⟩ := ih
      exact ⟨.restrict f z, by simp [BoundedWitness.eval, hz]⟩
  | @amalgamate Z R hR fam hcompat hmem t ht ih =>
      choose z hz using ih
      refine ⟨.amalgamate hR z, ?_⟩
      classical
      have hall : ∀ (Y : C) (f : Y ⟶ Z), (hf : R f) →
          (BoundedWitness.eval hP g (z f hf)).isSome :=
        fun Y f hf => by simp [hz]
      let y : R.FamilyOfElements P := fun Y f hf =>
        ((BoundedWitness.eval hP g (z f hf)).get (hall Y f hf))
      have hyeq : y = fam := by
        ext Y f hf
        simp [y, hz]
      have hy' : y.Compatible := hyeq ▸ hcompat
      simp only [BoundedWitness.eval, dite_eq_left hall]
      change (if hy : y.Compatible then some (hP _ hR y hy).choose else none) = some t
      rw [dite_eq_left hy']
      exact congrArg some ((hP _ hR y hy').choose_spec.2 t (hyeq ▸ ht)).symm

private noncomputable def generatedSubfunctor
    (F : Cᵒᵖ ⥤ TopCat.{w}) (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj) :
  Subfunctor (G.obj ⋙ CategoryTheory.forget TopCat) :=
  J.toPrecoverage.subsheafify (fun X =>
    Set.range fun x : F.obj (op X) => (f.app (op X)).hom x)

private noncomputable def topologicalSubfunctorObj
    (P : Cᵒᵖ ⥤ TopCat.{w}) (H : Subfunctor (P ⋙ CategoryTheory.forget TopCat))
    (U : Cᵒᵖ) : TopCat.{w} where
  carrier := {x : (P.obj U : Type w) // x ∈ H.obj U}
  str := TopologicalSpace.induced Subtype.val (P.obj U).str

private noncomputable def topologicalSubfunctor
    (P : Cᵒᵖ ⥤ TopCat.{w}) (H : Subfunctor (P ⋙ CategoryTheory.forget TopCat)) :
  Cᵒᵖ ⥤ TopCat.{w} where
  obj U := topologicalSubfunctorObj P H U
  map {U V} f := TopCat.ofHom ⟨fun x => ⟨(P.map f).hom x.1, H.map f x.2⟩,
    Continuous.subtype_mk ((P.map f).hom.continuous.comp continuous_subtype_val) _⟩
  map_id U := by
    ext x
    change (P.map (𝟙 U)).hom x.1 = x.1
    simp
  map_comp f g := by
    ext x
    change (P.map (f ≫ g)).hom x.1 = (P.map g).hom ((P.map f).hom x.1)
    simp

private noncomputable def topologicalSubfunctorInclusion
    (P : Cᵒᵖ ⥤ TopCat.{w}) (H : Subfunctor (P ⋙ CategoryTheory.forget TopCat)) :
    topologicalSubfunctor P H ⟶ P where
  app U := TopCat.ofHom ⟨fun x : (topologicalSubfunctorObj P H U : Type w) => x.1,
    (continuous_subtype_val : Continuous
      (fun x : (topologicalSubfunctorObj P H U : Type w) => x.1))⟩
  naturality {_ _} _ := rfl

private theorem mono_topologicalSubfunctorInclusion_app
    (P : Cᵒᵖ ⥤ TopCat.{w}) (H : Subfunctor (P ⋙ CategoryTheory.forget TopCat)) (U : Cᵒᵖ) :
    Mono ((topologicalSubfunctorInclusion P H).app U) :=
  (TopCat.mono_iff_injective _).2 fun _ _ h => Subtype.ext h

private theorem subsheafClosure_of_isAmalgamation
    (F : Cᵒᵖ ⥤ TopCat.{w}) (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj) {E : TopCat.{w}} {X : C}
    {S : Sieve X} (hS : S ∈ J X)
    {x : S.arrows.FamilyOfElements
      (topologicalSubfunctor G.obj (generatedSubfunctor F G f) ⋙ coyoneda.obj (op E))}
    (hx : x.Compatible) {t : E ⟶ G.obj.obj (op X)}
    (ht : (x.map (Functor.whiskerRight (topologicalSubfunctorInclusion G.obj
      (generatedSubfunctor F G f)) (coyoneda.obj (op E)))).IsAmalgamation t) (a : E) :
    J.toPrecoverage.SubsheafClosure (F := G.obj ⋙ CategoryTheory.forget TopCat)
      (fun X => Set.range fun b : F.obj (op X) => (f.app (op X)).hom b) X (t.hom a) := by
  let z : S.arrows.FamilyOfElements (G.obj ⋙ CategoryTheory.forget TopCat) :=
    fun Y r hr => ((x r hr).hom a).val
  have hz : z.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ hcomm =>
    congrArg Subtype.val (congrArg (fun k => k.hom a) (hx g₁ g₂ h₁ h₂ hcomm))
  have hzt : z.IsAmalgamation (t.hom a) := fun _ r hr => congrArg (fun k => k.hom a) (ht r hr)
  exact .amalgamate
    (by simpa using (GrothendieckTopology.arrows_mem_toPrecoverage_iff J S).2 hS)
    hz (fun {Y} r hr => (x r hr).hom a |>.property) hzt

private theorem generatedSubfunctor_isSheafTopological
    (F : Cᵒᵖ ⥤ TopCat.{w}) (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj) :
    Presheaf.IsSheaf J
      (topologicalSubfunctor G.obj (generatedSubfunctor F G f)) := by
  let H := generatedSubfunctor F G f
  let Q := topologicalSubfunctor G.obj H
  let ι := topologicalSubfunctorInclusion G.obj H
  change Presheaf.IsSheaf J Q
  intro E X S hS x hx
  let α : Q ⋙ coyoneda.obj (op E) ⟶ G.obj ⋙ coyoneda.obj (op E) :=
    Functor.whiskerRight ι (coyoneda.obj (op E))
  let y : S.arrows.FamilyOfElements (G.obj ⋙ coyoneda.obj (op E)) := x.map α
  obtain ⟨t, ht, hu⟩ := G.property E S hS y (hx.map α)
  have hmem := subsheafClosure_of_isAmalgamation F G f hS hx ht
  let t' : E ⟶ Q.obj (op X) := TopCat.ofHom ⟨
    fun a => ⟨t.hom a, hmem a⟩,
    Continuous.subtype_mk t.hom.continuous hmem⟩
  have hti : t' ≫ ι.app (op X) = t := by
    ext a
    rfl
  have hmono (U : Cᵒᵖ) : Mono (ι.app U) := mono_topologicalSubfunctorInclusion_app G.obj H U
  have hamalg (s : E ⟶ Q.obj (op X)) :
      x.IsAmalgamation s ↔ y.IsAmalgamation (s ≫ ι.app (op X)) := by
    refine forall₃_congr fun Y r hr => ?_
    change s ≫ Q.map r.op = x r hr ↔ (s ≫ ι.app (op X)) ≫ G.obj.map r.op = x r hr ≫ ι.app (op Y)
    rw [Category.assoc, ← ι.naturality, ← Category.assoc, cancel_mono]
  refine ⟨t', (hamalg t').2 (hti ▸ ht), fun s₁ hs₁ => ?_⟩
  rw [← cancel_mono (ι.app (op X)), hti]
  exact (hu _ ((hamalg s₁).1 hs₁)).trans (hu t ht).symm

private theorem generatedSection_card_le_witness
    (F : Cᵒᵖ ⥤ TopCat.{w}) (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj)
    (X : C)
    (hP : ∀ ⦃Y : C⦄ (R : Presieve Y), R ∈ J.toPrecoverage Y →
      Presieve.IsSheafFor (G.obj ⋙ CategoryTheory.forget TopCat) R) :
    Cardinal.lift.{max u v, w}
        (Cardinal.mk ((generatedSubfunctor F G f).obj (op X))) ≤
      Cardinal.mk (BoundedWitness J.toPrecoverage (fun Y => F.obj (op Y)) X) := by
  classical
  let P := G.obj ⋙ CategoryTheory.forget TopCat
  let g : ∀ Y, F.obj (op Y) → P.obj (op Y) := fun Y a => (f.app (op Y)).hom a
  choose witness hwitness using fun s : (generatedSubfunctor F G f).obj (op X) =>
    exists_boundedWitness_eval hP g X s.2
  have hinj : Function.Injective witness := fun s t hst =>
    Subtype.ext (by simpa [hwitness] using congrArg (BoundedWitness.eval hP g) hst)
  have hinj' : Function.Injective
      (fun s : ULift.{max u v, w} ((generatedSubfunctor F G f).obj (op X)) =>
        witness s.down) := hinj.comp ULift.down_injective
  simpa only [Cardinal.mk_uLift] using Cardinal.mk_le_of_injective hinj'

private theorem lift_sheafSize_generatedSubfunctor_le
    (F : Cᵒᵖ ⥤ TopCat.{w}) (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj)
    (hP : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ J.toPrecoverage X →
      Presieve.IsSheafFor (G.obj ⋙ CategoryTheory.forget TopCat) R) :
    Cardinal.lift.{v} (sheafSize (⟨topologicalSubfunctor G.obj (generatedSubfunctor F G f),
        generatedSubfunctor_isSheafTopological F G f⟩ : Sheaf J TopCat.{w})) ≤
      ⨆ X : C, Cardinal.mk (BoundedWitness J.toPrecoverage (fun Y => F.obj (op Y)) X) := by
  have hbdd : BddAbove (Set.range fun X : C => Cardinal.lift.{u}
      (Cardinal.mk ((topologicalSubfunctor G.obj (generatedSubfunctor F G f)).obj (op X)))) :=
    Cardinal.bddAbove_of_small
  rw [sheafSize, Cardinal.lift_iSup hbdd]
  refine ciSup_le' fun X => ?_
  rw [Cardinal.lift_lift]
  change Cardinal.lift.{max u v, w}
    (Cardinal.mk ((generatedSubfunctor F G f).obj (op X))) ≤ _
  exact (generatedSection_card_le_witness F G f X hP).trans
    (le_ciSup Cardinal.bddAbove_of_small X)

/-- Any map from a fixed presheaf of topological spaces to a sheaf factors through a
subsheaf of uniformly bounded size. -/
@[stacks 0AI4 "bounded_subsheaf"]
public theorem exists_bounded_subsheaf_factorization (F : Cᵒᵖ ⥤ TopCat.{w}) :
    ∃ κ : Cardinal.{max u v w}, ∀ (G : Sheaf J TopCat.{w}) (f : F ⟶ G.obj),
      ∃ (G' : Sheaf J TopCat.{w}) (i : G' ⟶ G),
        Mono i ∧ Cardinal.lift.{v} (sheafSize G') ≤ κ ∧
          ∃ f' : F ⟶ G'.obj, f' ≫ i.hom = f := by
  let K := J.toPrecoverage
  let κ : Cardinal.{max (max u w) v} :=
    ⨆ X : C, Cardinal.mk (BoundedWitness K (fun Y => F.obj (op Y)) X)
  refine ⟨κ, fun G f => ?_⟩
  let P := G.obj ⋙ CategoryTheory.forget TopCat
  have hP : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor P R := fun X R hR =>
    ((isSheaf_iff_isSheaf_of_type J P).1 (Presheaf.isSheaf_comp_of_isSheaf J G.obj
      (CategoryTheory.forget TopCat) G.property)).isSheafFor R
      ((GrothendieckTopology.mem_toPrecoverage_iff J R).1 hR)
  let H := generatedSubfunctor F G f
  let Q := topologicalSubfunctor G.obj H
  let i₀ : Q ⟶ G.obj := topologicalSubfunctorInclusion G.obj H
  let G' : Sheaf J TopCat.{w} := ⟨Q, generatedSubfunctor_isSheafTopological F G f⟩
  let i : G' ⟶ G := ObjectProperty.homMk i₀
  have hi : Mono i := by
    have := mono_topologicalSubfunctorInclusion_app G.obj H
    exact (sheafToPresheaf J TopCat).mono_of_mono_map (NatTrans.mono_of_mono_app i₀)
  have hbase (U : Cᵒᵖ) (a : F.obj U) : (f.app U).hom a ∈ H.obj U := by
    change K.SubsheafClosure (F := G.obj ⋙ CategoryTheory.forget TopCat)
      (fun X => Set.range fun b : F.obj (op X) => (f.app (op X)).hom b)
      U.unop ((f.app U).hom a)
    exact .base ⟨a, rfl⟩
  let f' : F ⟶ Q := {
    app U := TopCat.ofHom ⟨fun a => ⟨(f.app U).hom a, hbase U a⟩,
      Continuous.subtype_mk (f.app U).hom.continuous (hbase U)⟩
    naturality U V g := by
      ext a
      exact Subtype.ext <| congrArg (fun q => q.hom a) (f.naturality g)
  }
  exact ⟨G', i, hi, lift_sheafSize_generatedSubfunctor_le F G f hP, ⟨f', by ext; rfl⟩⟩

end

section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe w v u z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private structure SmallTopSpace (κ : Cardinal.{z}) where
  carrier : Set (κ.ord.ToType)
  topology : TopologicalSpace carrier

private def SmallTopSpace.toTopCat {κ : Cardinal.{z}} (X : SmallTopSpace κ) :
    TopCat.{z} :=
  @TopCat.of X.carrier X.topology

private structure SmallPresheafCode {C : Type u} [Category.{v} C] (κ : Cardinal.{z}) where
  obj : Cᵒᵖ → SmallTopSpace κ
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : (obj X).toTopCat ⟶ (obj Y).toTopCat
  map_id' (X : Cᵒᵖ) : map (𝟙 X) = 𝟙 ((obj X).toTopCat)
  map_comp' {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g

private def SmallPresheafCode.toPresheaf {κ : Cardinal.{z}}
    (S : SmallPresheafCode (C := C) κ) : Cᵒᵖ ⥤ TopCat.{z} where
  obj X := (S.obj X).toTopCat
  map := S.map
  map_id := S.map_id'
  map_comp := S.map_comp'

@[instance_reducible]
private noncomputable def imageTopology {X : Type z} [TopologicalSpace X] {α : Type z} (j : X ↪ α) :
    TopologicalSpace (Set.range j) :=
  TopologicalSpace.induced (Equiv.ofInjective j j.injective).symm inferInstance

private noncomputable def boundedCarrierEmbedding (κ : Cardinal.{z}) (X : Type z)
    (hX : Cardinal.mk X ≤ κ) : X ↪ κ.ord.ToType :=
  Classical.choice (Cardinal.lift_mk_le'.1 (by simpa using hX))

private noncomputable def imageSmallTopSpace (κ : Cardinal.{z}) {X : Type z}
    [TopologicalSpace X] (j : X ↪ κ.ord.ToType) : SmallTopSpace κ :=
  ⟨Set.range j, imageTopology j⟩

private noncomputable def imageHomeomorphHom (κ : Cardinal.{z}) {X : TopCat.{z}}
    (j : X ↪ κ.ord.ToType) : X ⟶ (imageSmallTopSpace κ j).toTopCat := by
  let S := imageSmallTopSpace κ j
  let : TopologicalSpace S.carrier := S.topology
  let e : X ≃ Set.range j := Equiv.ofInjective j j.injective
  exact TopCat.ofHom ⟨e, by
    apply continuous_induced_rng.2
    change Continuous (e.symm ∘ e)
    rw [e.symm_comp_self]
    exact continuous_id⟩

private noncomputable def imageHomeomorphInv (κ : Cardinal.{z}) {X : TopCat.{z}}
    (j : X ↪ κ.ord.ToType) : (imageSmallTopSpace κ j).toTopCat ⟶ X := by
  let S := imageSmallTopSpace κ j
  let : TopologicalSpace S.carrier := S.topology
  let e : X ≃ Set.range j := Equiv.ofInjective j j.injective
  exact TopCat.ofHom ⟨e.symm, continuous_induced_dom⟩

@[simp] private theorem imageHomeomorphInv_comp_Hom (κ : Cardinal.{z})
    {X : TopCat.{z}} (j : X ↪ κ.ord.ToType) :
    imageHomeomorphInv κ j ≫ imageHomeomorphHom κ j = 𝟙 ((imageSmallTopSpace κ j).toTopCat) := by
  ext x
  exact (Equiv.ofInjective j j.injective).apply_symm_apply x

@[simp] private theorem imageHomeomorphHom_comp_Inv (κ : Cardinal.{z})
    {X : TopCat.{z}} (j : X ↪ κ.ord.ToType) :
    imageHomeomorphHom κ j ≫ imageHomeomorphInv κ j = 𝟙 X := by
  ext x
  exact (Equiv.ofInjective j j.injective).symm_apply_apply x

private noncomputable def SmallPresheafCode.ofBoundedWithEmbedding {κ : Cardinal.{z}}
    (P : Cᵒᵖ ⥤ TopCat.{z}) (j : ∀ X, P.obj X ↪ κ.ord.ToType) :
    SmallPresheafCode (C := C) κ where
  obj X := imageSmallTopSpace κ (j X)
  map {X Y} f := imageHomeomorphInv κ (j X) ≫ P.map f ≫ imageHomeomorphHom κ (j Y)
  map_id' X := by
    ext x
    simp
  map_comp' f g := by simp [reassoc_of% imageHomeomorphHom_comp_Inv]

private noncomputable def SmallPresheafCode.isoOfBoundedWithEmbedding {κ : Cardinal.{z}}
    {P : Cᵒᵖ ⥤ TopCat.{z}} (j : ∀ X, P.obj X ↪ κ.ord.ToType) :
    (SmallPresheafCode.ofBoundedWithEmbedding P j).toPresheaf ≅ P :=
  NatIso.ofComponents
    (fun X => ⟨imageHomeomorphInv κ (j X), imageHomeomorphHom κ (j X),
      imageHomeomorphInv_comp_Hom κ (j X), imageHomeomorphHom_comp_Inv κ (j X)⟩)
    (fun {X Y} f => by
      change (imageHomeomorphInv κ (j X) ≫ P.map f ≫ imageHomeomorphHom κ (j Y)) ≫
          imageHomeomorphInv κ (j Y) = imageHomeomorphInv κ (j X) ≫ P.map f
      simp only [Category.assoc, imageHomeomorphHom_comp_Inv, Category.comp_id])

/-- The inclusion of topological-space-valued sheaves into presheaves has a left adjoint. -/
@[stacks 0AI4 "sheafification"]
public noncomputable instance hasWeakSheafify_topCat :
    HasWeakSheafify J TopCat.{max u v w} := by
  let G := sheafToPresheaf J TopCat.{max u v w}
  have hG : SolutionSetCondition.{max u v w} G := by
    intro F
    obtain ⟨κ, hκ⟩ := exists_bounded_subsheaf_factorization (J := J) F
    let ι : Type (max u v w) := Σ S : SmallPresheafCode (C := C) κ,
      {f : F ⟶ S.toPresheaf // Presheaf.IsSheaf J S.toPresheaf}
    let B : ι → Sheaf J TopCat.{max u v w} := fun i => ⟨i.1.toPresheaf, i.2.2⟩
    let f₀ : ∀ i, F ⟶ G.obj (B i) := fun i => i.2.1
    refine ⟨ι, B, f₀, fun H f => ?_⟩
    obtain ⟨H', m, hm, hsize, f', hf'⟩ := hκ H f
    have hsections (U : C) : Cardinal.mk (H'.obj.obj (op U)) ≤ κ := by
      apply Cardinal.lift_le.mp
      calc
        Cardinal.lift.{max u v} (Cardinal.mk (H'.obj.obj (op U))) ≤
            Cardinal.lift.{v} (sheafSize H') := by
          simpa only [Cardinal.lift_lift] using
            (Cardinal.lift_le.mpr (show Cardinal.lift.{u}
              (Cardinal.mk (H'.obj.obj (op U))) ≤ sheafSize H' from
                le_ciSup Cardinal.bddAbove_of_small U))
        _ ≤ κ := hsize
        _ = Cardinal.lift.{max u v} κ := (Cardinal.lift_id'.{max u v, w} κ).symm
    let j : ∀ X : Cᵒᵖ, H'.obj.obj X ↪ κ.ord.ToType := fun X =>
      boundedCarrierEmbedding κ (H'.obj.obj X) (hsections X.unop)
    let S : SmallPresheafCode (C := C) κ :=
      SmallPresheafCode.ofBoundedWithEmbedding H'.obj j
    let e := SmallPresheafCode.isoOfBoundedWithEmbedding (P := H'.obj) j
    have hS : Presheaf.IsSheaf J S.toPresheaf :=
      (Presheaf.isSheaf_of_iso_iff e).2 H'.property
    refine ⟨⟨S, ⟨f' ≫ e.inv, hS⟩⟩,
      (⟨e.hom⟩ : (⟨S.toPresheaf, hS⟩ : Sheaf J TopCat.{max u v w}) ⟶ H') ≫ m, ?_⟩
    change (f' ≫ e.inv) ≫ (e.hom ≫ m.hom) = f
    simp [hf']
  exact isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

end

end CategoryTheory.TopologicalSheaf

end
