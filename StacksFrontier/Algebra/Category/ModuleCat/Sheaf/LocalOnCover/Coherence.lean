module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of a sheaf of modules is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the clause for coherence:
a sheaf of modules on a ringed site is coherent exactly when its restrictions to the members
of some covering family are coherent on the localized ringed sites.

Coherence is two conditions, and both have to travel.  Finite type of the underlying presheaf
of modules travels by restricting a finite generating family along an arrow of the slice, and
descends because a covering family of covering families covers; this is
`isFiniteType_over` and `isFiniteType_of_over` below.  The sheaf of relations among a
finite family of sections is a presheaf on an iterated slice site, and the whole difficulty is
that the same relations can be read on three sites — over the base object, over a member of
the covering family, and over the iterated slice — which are identified by
`Over.iteratedSliceEquiv`.  Since that identification is an equivalence of sites which is a
dense subsite in both directions, finite type of a presheaf of modules is carried across it by
`isFiniteType_pushforward_of_equiv`, and the three readings of the relations presheaf are
compared by the three objectwise-identity isomorphisms
`relationsIteratedSliceIso`, `relationsIteratedSliceSymmIso` and `relationsRestrictIso`.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_over`: coherence passes to the slice site over every
  object.  This is the site-level heredity of coherence, the analogue for
  `SheafOfModules.IsCoherentOnSite` of `Stacks.SheafOfModules.IsCoherentOn.mono`.
* `Stacks.SheafOfModules.isCoherentOnSite_of_coversTop`: coherence of the restrictions to the
  members of a family covering the final object implies coherence.
* `Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite`: coherence is
  equivalent to coherence of the restrictions to the members of some covering family of the
  final object.  This is Stacks 03DN for coherence.
* `Stacks.SheafOfModules.isFiniteType_of_presheafIso`: the sectionwise finite type condition on
  a presheaf of modules is invariant under isomorphism.
* `Stacks.SheafOfModules.isFiniteType_over` and
  `Stacks.SheafOfModules.isFiniteType_of_over`: the sectionwise finite type condition is local
  on the site, in the same two halves.  These are the finite-type half of the two coherence
  statements, stated separately because every other local condition of Stacks 03DL that implies
  finite type needs them on their own.
* `Stacks.SheafOfModules.relations_isFiniteType_of_coversTop`: the relations half descends along
  a covering family of the slice site over an object.  This is the step of
  `isCoherentOnSite_of_coversTop` that moves the relations condition from the members of a
  covering family to the object they cover, stated on its own because the relations condition
  also has to be descended when the covering family comes from somewhere else than Stacks 03DN.

## Implementation notes

Coherence is `SheafOfModules.IsCoherentOnSite`, which is Stacks 03DL(8), and the localized
ringed site is `AlgebraicGeometry.RingedSite.over`, which is Stacks 04IX; no notion is
introduced here.

The two halves of the locality statement, `isCoherentOnSite_over` and
`isCoherentOnSite_of_coversTop`, are proved for an arbitrary sheaf of rings on an arbitrary
site, since `SheafOfModules.IsCoherentOnSite` is; only the Stacks 03DN equivalence itself is
phrased with a bundled ringed site, which is the special case `R := X.ringSheaf`, the two
spellings of the localized structure sheaf being definitionally equal.

`PresheafOfModules.Generates` is the sectionwise form of generation by finitely many sections,
so moving generators between sites is a computation with restriction maps rather than with
free sheaves, and needs no sheafification hypotheses anywhere in this file.  That is why the
module universe `m` is free of the ring universe `w` throughout.

The three relations isomorphisms are `PresheafOfModules.isoMk` on identity components: the
sections of the relations presheaf at an object of any of the three sites are literally the
same kernel, because `Over.iteratedSliceEquiv` and `Over.forget` agree on underlying objects
of the base category.  `relationsRestrictIso` is the one exception: there the two families of
sections are restrictions of one another rather than equal, so its components are
`LinearEquiv.ofEq` on the two kernels, equal by `Over.w`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w m u₁ v₁ u₂ v₂

private noncomputable def overObjIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{m} R}
    (U : C) (V : Over U) :
    (M.over U).val.obj (op V) ≅ M.val.obj (op V.left) := by
  change (ModuleCat.restrictScalars (RingHom.id _)).obj _ ≅ _
  exact ModuleCat.restrictScalarsId'App (RingHom.id _) rfl _

private theorem generates_on_slice
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{m} R}
    {A U : C} {n : ℕ} (s : Fin n → M.val.obj (op A))
    (hs : PresheafOfModules.Generates J M.val s)
    (V : Over U) (g : V.left ⟶ A) :
    PresheafOfModules.Generates (J.over U) (M.over U).val
      (fun i =>
        ((M.val.map g.op (s i) : M.val.obj (op V.left)) :
          (M.over U).val.obj (op V))) := by
  intro W f t
  obtain ⟨S, hS, hSgen⟩ := hs W.left (f.left ≫ g)
    (t : M.val.obj (op W.left))
  refine ⟨(Sieve.overEquiv W).symm S, J.overEquiv_symm_mem_over W S hS, ?_⟩
  intro Z k hk
  have hk' : S k.left := by simpa using hk
  obtain ⟨a, ha⟩ := hSgen Z.left k.left hk'
  refine ⟨a, ?_⟩
  have hc (i : Fin n) :
      M.val.restrictₛₗ (k.left ≫ f.left).op (M.val.map g.op (s i)) =
        M.val.restrictₛₗ (k.left ≫ f.left ≫ g).op (s i) := by
    change M.val.map ((k.left ≫ f.left).op) (M.val.map g.op (s i)) =
      M.val.map (k.left ≫ f.left ≫ g).op (s i)
    have hcomp := M.val.map_comp_apply g.op (k.left ≫ f.left).op (s i)
    have he : g.op ≫ (k.left ≫ f.left).op = (k.left ≫ f.left ≫ g).op := by
      simp only [← op_comp]
      cat_disch
    exact hcomp.symm.trans (M.val.congr_map_apply he (s i))
  change (∑ i, a i • M.val.restrictₛₗ (k.left ≫ f.left).op
      (M.val.map g.op (s i))) = M.val.restrictₛₗ k.left.op t
  simpa only [hc] using ha

private noncomputable def relationsIteratedSliceIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{m} R}
    (U : C) (V : Over U) {n : ℕ}
    (s : Fin n → (M.over U).val.obj (op V)) :
    ((PresheafOfModules.pushforward₀ (F := (Over.iteratedSliceEquiv V).inverse)
      ((Over.forget V).op ⋙ (R.over U).obj)).obj
      (PresheafOfModules.relations (M.over U).val s)) ≅
      PresheafOfModules.relations M.val
        (fun i => (overObjIso (R := R) (M := M) U V).hom.hom (s i)) :=
  PresheafOfModules.isoMk (fun Z => Iso.refl _)
private noncomputable def relationsIteratedSliceSymmIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{m} R}
    (U : C) (V : Over U) {n : ℕ}
    (s : Fin n → M.val.obj (op V.left)) :
    ((PresheafOfModules.pushforward₀ (F := (Over.iteratedSliceEquiv V).functor)
      ((Over.forget V.left).op ⋙ R.obj)).obj
      (PresheafOfModules.relations M.val s)) ≅
      PresheafOfModules.relations (M.over U).val
        (fun i => (overObjIso U V).inv.hom (s i)) :=
  PresheafOfModules.isoMk (fun Z => Iso.refl _)

private noncomputable def relationsRestrictIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{m} R)
    {U : C} {n : ℕ} (s : Fin n → M.val.obj (op U)) (V : Over U) :
    ((PresheafOfModules.pushforward₀ (Over.forget V)
      ((Over.forget U).op ⋙ R.obj)).obj
      (PresheafOfModules.relations M.val s)) ≅
    PresheafOfModules.relations (M.over U).val
      (fun i => M.val.map V.hom.op (s i)) := by
  let e (W : (Over V)ᵒᵖ) :
      (((PresheafOfModules.pushforward₀ (Over.forget V)
        ((Over.forget U).op ⋙ R.obj)).obj
        (PresheafOfModules.relations M.val s)).obj W) ≅
      (PresheafOfModules.relations (M.over U).val
        (fun i => M.val.map V.hom.op (s i))).obj W := by
    refine LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ ?_)
    congr 1
    congr 1
    funext i
    change M.val.map W.unop.left.hom.op (s i) =
      M.val.map W.unop.hom.left.op (M.val.map V.hom.op (s i))
    rw [← M.val.map_comp_apply, ← op_comp, Over.w W.unop.hom]
  refine PresheafOfModules.isoMk e ?_
  intro W Z f
  ext a
  rfl

private theorem coversTop_map_of_denseEquiv
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
    (e : C ≌ D) [e.functor.IsDenseSubsite J K]
    {I : Type*} (Xc : I → C) (hX : J.CoversTop Xc) :
    K.CoversTop (fun i => e.functor.obj (Xc i)) := by
  intro Z
  let S := Sieve.ofObjects Xc (e.inverse.obj Z)
  have hS : S ∈ J (e.inverse.obj Z) := hX (e.inverse.obj Z)
  have hpush : S.functorPushforward e.functor ∈ K
      (e.functor.obj (e.inverse.obj Z)) :=
    (e.functor.functorPushforward_mem_iff J K).2 hS
  have hcover : Sieve.ofObjects (fun i => e.functor.obj (Xc i))
      (e.functor.obj (e.inverse.obj Z)) ∈ K (e.functor.obj (e.inverse.obj Z)) :=
    K.superset_covering (Sieve.functorPushforward_ofObjects_le _ _ _) hpush
  have hpull := K.pullback_stable (e.counitIso.inv.app Z) hcover
  refine K.superset_covering ?_ hpull
  intro T f hf
  rw [Sieve.pullback_apply] at hf
  change (∃ i, Nonempty (T ⟶ e.functor.obj (Xc i))) at hf ⊢
  exact hf

private theorem isFiniteType_pushforward_of_equiv
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
    (e : C ≌ D) [e.functor.IsDenseSubsite J K]
    {S : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{m} S}
    (hM : PresheafOfModules.IsFiniteType J M) :
    PresheafOfModules.IsFiniteType K
      ((PresheafOfModules.pushforward₀ (F := e.inverse) S).obj M) := by
  classical
  obtain ⟨I, A, hA, hgen⟩ := hM.exists_generators
  let B : I → D := fun i => e.functor.obj (A i)
  let T : Set D := Set.range B
  refine ⟨⟨T, fun t => t.1, ?_, ?_⟩⟩
  · intro Z
    apply K.superset_covering ?_ (coversTop_map_of_denseEquiv e A hA Z)
    intro Y f hf
    rw [Sieve.mem_ofObjects_iff] at hf ⊢
    obtain ⟨i, ⟨g⟩⟩ := hf
    exact ⟨⟨B i, ⟨i, rfl⟩⟩, ⟨g⟩⟩
  · intro t
    rcases t with ⟨d, ⟨i, hi⟩⟩
    subst d
    obtain ⟨n, s, hs⟩ := hgen i
    refine ⟨n, fun j => M.map (e.unitInv.app (A i)).op (s j), ?_⟩
    intro Z f t
    let Z' := e.inverse.obj Z
    let f' : Z' ⟶ A i := e.inverse.map f ≫ e.unitInv.app (A i)
    obtain ⟨T, hT, hTgen⟩ := hs Z' f' t
    let T' : Sieve Z := (T.functorPushforward e.functor).pullback (e.counitIso.inv.app Z)
    refine ⟨T', ?_, ?_⟩
    · exact K.pullback_stable (e.counitIso.inv.app Z)
        ((e.functor.functorPushforward_mem_iff J K).2 hT)
    · intro Y g hg
      rw [Sieve.pullback_apply] at hg
      rw [Sieve.mem_functorPushforward_functor] at hg
      have htri :
          (e.inverse.map (g ≫ e.counitIso.inv.app Z) ≫
              e.unitInv.app Z') = e.inverse.map g := by
        rw [Functor.map_comp, Category.assoc,
          Equivalence.inverse_counitInv_comp]
        simp
      have hg' : T (e.inverse.map g) := htri ▸ hg
      obtain ⟨a, ha⟩ := hTgen (e.inverse.obj Y) (e.inverse.map g) hg'
      refine ⟨a, ?_⟩
      have hArrow : e.inverse.map (g ≫ f) ≫ e.unitInv.app (A i) =
          e.inverse.map g ≫ f' := by
        dsimp [f']
        rw [Functor.map_comp]
        simp [Category.assoc]
      have hArrowOp : (e.unitInv.app (A i)).op ≫
          (e.inverse.map (g ≫ f)).op = (e.inverse.map g ≫ f').op := by
        simpa only [op_comp] using congrArg Quiver.Hom.op hArrow
      have hc (j : Fin n) :
          M.map (e.inverse.map (g ≫ f)).op
              (M.map (e.unitInv.app (A i)).op (s j)) =
            M.restrictₛₗ (e.inverse.map g ≫ f').op (s j) := by
        rw [← M.map_comp_apply]
        rw [hArrowOp]
        rfl
      change (∑ j, a j • M.map (e.inverse.map (g ≫ f)).op
        (M.map (e.unitInv.app (A i)).op (s j))) =
        M.map (e.inverse.map g).op t
      simp_rw [hc]
      convert ha using 1
      rfl

/-- Generating families of sections transport along an isomorphism of presheaves of modules:
the image of a generating family generates, because the isomorphism is linear and natural, so
it carries a local linear combination to a local linear combination. -/
theorem generates_of_presheafIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M N : PresheafOfModules.{m} R} (e : M ≅ N)
    {U : C} {n : ℕ} (s : Fin n → M.obj (op U))
    (hs : PresheafOfModules.Generates J M s) :
    PresheafOfModules.Generates J N
      (fun i => e.hom.app (op U) (s i)) := by
  intro V f t
  let t' := e.inv.app (op V) t
  obtain ⟨S, hS, hSgen⟩ := hs V f t'
  refine ⟨S, hS, ?_⟩
  intro W g hg
  obtain ⟨a, ha⟩ := hSgen W g hg
  refine ⟨a, ?_⟩
  have ha' := congrArg (fun x => e.hom.app (op W) x) ha
  simp only [map_sum, map_smul] at ha'
  have hL (i : Fin n) :
      e.hom.app (op W) (M.restrictₛₗ (g ≫ f).op (s i)) =
        N.restrictₛₗ (g ≫ f).op (e.hom.app (op U) (s i)) := by
    exact PresheafOfModules.naturality_apply e.hom (g ≫ f).op (s i)
  have hR : e.hom.app (op W) (M.restrictₛₗ g.op t') =
      N.restrictₛₗ g.op t := by
    have h := PresheafOfModules.naturality_apply e.hom g.op t'
    have ht : e.hom.app (op V) t' = t := by
      have hIso : e.inv.app (op V) ≫ e.hom.app (op V) = 𝟙 _ := by
        have h := congrArg (fun q => q.app (op V)) (Iso.inv_hom_id e)
        simpa only [PresheafOfModules.comp_app, PresheafOfModules.id_app] using h
      have hval := congrArg (fun q => q t) hIso
      simpa using hval
    rw [ht] at h
    exact h
  simp_rw [hL, hR] at ha'
  exact ha'

/-- Being of finite type is invariant under isomorphism of presheaves of modules. -/
theorem isFiniteType_of_presheafIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M N : PresheafOfModules.{m} R} (e : M ≅ N)
    (hM : PresheafOfModules.IsFiniteType J M) :
    PresheafOfModules.IsFiniteType J N := by
  obtain ⟨I, U, hU, hgen⟩ := hM.exists_generators
  refine ⟨I, U, hU, ?_⟩
  intro i
  obtain ⟨n, s, hs⟩ := hgen i
  exact ⟨n, fun j => e.hom.app (op (U i)) (s j), generates_of_presheafIso e s hs⟩
private theorem generates_of_pushforward_forget
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{m} R}
    {U : C} {V : Over U} {n : ℕ}
    (s : Fin n → M.obj (op V.left))
    (hs : PresheafOfModules.Generates (J.over U)
      ((PresheafOfModules.pushforward₀ (Over.forget U) R).obj M) s) :
    PresheafOfModules.Generates J M s := by
  intro W f t
  let Y : Over U := Over.mk (f ≫ V.hom)
  let q : Y ⟶ V := Over.homMk f
  obtain ⟨T, hT, hTgen⟩ := hs Y q t
  refine ⟨Sieve.overEquiv Y T, (J.mem_over_iff T).mp hT, ?_⟩
  intro Z k hk
  have hk' : T (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y) := by
    exact (Sieve.overEquiv_iff T k).mp hk
  let Z' : Over U := Over.mk (k ≫ Y.hom)
  let q' : Z' ⟶ Y := Over.homMk k
  obtain ⟨a, ha⟩ := hTgen Z' q' hk'
  refine ⟨a, ?_⟩
  change (∑ i, a i • M.restrictₛₗ (k ≫ f).op (s i)) = M.restrictₛₗ k.op t
  convert ha using 1 <;> rfl

private theorem generates_transport_obj
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{m} R}
    {A B : C} (h : A = B) {n : ℕ} (s : Fin n → M.obj (op A))
    (hs : PresheafOfModules.Generates J M s) :
    PresheafOfModules.Generates J M
      (fun i => h ▸ s i) := by
  cases h
  exact hs

private theorem isFiniteType_of_restrictions
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{m} R}
    {I : Type u₁} (U : I → C) (hU : J.CoversTop U)
    (hM : ∀ i, PresheafOfModules.IsFiniteType (J.over (U i))
      ((PresheafOfModules.pushforward₀ (Over.forget (U i)) R).obj M)) :
    PresheafOfModules.IsFiniteType J M := by
  classical
  choose Ii Vi hVi hgen using fun i => (hM i).exists_generators
  let A : (Σ i, Ii i) → C := fun j => (Vi j.1 j.2).left
  let T : Set C := Set.range A
  have hflat : J.CoversTop A := hU.over hVi
  refine ⟨⟨T, fun t => t.1, ?_, ?_⟩⟩
  · intro Z
    apply J.superset_covering ?_ (hflat Z)
    intro Y f hf
    rw [Sieve.mem_ofObjects_iff] at hf ⊢
    obtain ⟨j, ⟨g⟩⟩ := hf
    exact ⟨⟨A j, ⟨j, rfl⟩⟩, ⟨g⟩⟩
  · intro t
    change ∃ (n : ℕ) (s : Fin n → M.obj (op (t : C))),
      PresheafOfModules.Generates J M s
    obtain ⟨j, hj⟩ := t.2
    obtain ⟨n, s, hs⟩ := hgen j.1 j.2
    let s' : Fin n → M.obj (op (A j)) := fun i => s i
    have hs' : PresheafOfModules.Generates J M s' :=
      generates_of_pushforward_forget s hs
    exact ⟨n, fun i => hj ▸ s' i,
      generates_transport_obj (M := M) hj s' hs'⟩

private def inducedCoverInSlice {C : Type u} [Category.{v} C] {U : C}
    {I : Type w} (Xc : I → C) :
    (Σ i, Σ V : Over U, V.left ⟶ Xc i) → Over U := fun j => j.2.1

private theorem inducedCoverInSlice_coversTop
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {I : Type w} (Xc : I → C) (hX : J.CoversTop Xc) (U : C) :
    (J.over U).CoversTop (inducedCoverInSlice Xc) := by
  intro Z
  rw [J.mem_over_iff]
  apply J.superset_covering ?_ (hX Z.left)
  intro T f hf
  rw [Sieve.overEquiv_iff]
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff Xc f).mp hf
  refine ⟨⟨i, ⟨Over.mk (f ≫ Z.hom), g⟩⟩, ?_⟩
  exact ⟨𝟙 _⟩

/-- **Sectionwise finite type restricts to every slice.**  If the underlying presheaf of modules
of a sheaf of modules is of finite type, then so is the one of its restriction to the slice site
over any object: a finite generating family over an object `A` of a covering family restricts,
along any arrow of the slice landing in `A`, to a finite generating family there. -/
theorem isFiniteType_over
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R)
    (hM : PresheafOfModules.IsFiniteType J M.val) (U : C) :
    PresheafOfModules.IsFiniteType (J.over U) (M.over U).val := by
  classical
  obtain ⟨I, A, hA, hgen⟩ := hM.exists_generators
  refine ⟨⟨(Σ i, Σ V : Over U, V.left ⟶ A i), inducedCoverInSlice A,
    inducedCoverInSlice_coversTop J A hA U, ?_⟩⟩
  intro j
  obtain ⟨n, s, hs⟩ := hgen j.1
  exact ⟨n, fun i => M.val.map j.2.2.op (s i),
    generates_on_slice s hs (j.2.1) j.2.2⟩

/-- **Sectionwise finite type is local on a covering family.**  A sheaf of modules whose
restriction to each member of a family covering the final object has a presheaf of modules of
finite type has one itself: a covering family of covering families covers, and the generators
on the members of the inner families, read on the base, generate there.

The index type of the covering family is arbitrary; the covering family of the base produced by
the proof is indexed by a *set* of objects of the site, which is what
`PresheafOfModules.IsFiniteType` asks for. -/
theorem isFiniteType_of_over
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R)
    {I : Type u₁} (U : I → C) (hU : J.CoversTop U)
    (hM : ∀ i, PresheafOfModules.IsFiniteType
      (J.over (U i)) (M.over (U i)).val) :
    PresheafOfModules.IsFiniteType J M.val := by
  exact isFiniteType_of_restrictions U hU hM

/-- **The relations among a family of sections are of finite type as soon as they are so on a
covering family.**  Let `s` be a finite family of sections of a sheaf of modules over an object
`A`, and let `V` be a family of objects of the slice site over `A` covering its terminal object.
If, for each member, the relations among the family restricted to that member are of finite type
on the slice site over the member's underlying object, then the relations among `s` are of
finite type on the slice site over `A`.

The relations among `s`, read on the slice over a member `V i`, are the relations among the
restricted family read on the slice over `(V i).left`: the two sites are identified by
`Over.iteratedSliceEquiv`, which carries finite type by `isFiniteType_pushforward_of_equiv`, and
the two readings of the relations presheaf are compared by `relationsIteratedSliceSymmIso` and
`relationsRestrictIso`.  Finite type then descends along the covering family by
`isFiniteType_of_restrictions`. -/
theorem relations_isFiniteType_of_coversTop
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R) {A : C} {n : ℕ} (s : Fin n → M.val.obj (op A))
    {I : Type u₁} (V : I → Over A) (hV : (J.over A).CoversTop V)
    (hrel : ∀ i, PresheafOfModules.IsFiniteType (J.over (V i).left)
      (PresheafOfModules.relations M.val
        (fun j => M.val.restrictₛₗ (V i).hom.op (s j)))) :
    PresheafOfModules.IsFiniteType (J.over A) (PresheafOfModules.relations M.val s) := by
  apply isFiniteType_of_restrictions V hV
  intro i
  let : (V i).iteratedSliceEquiv.symm.functor.IsDenseSubsite
      (J.over (V i).left) ((J.over A).over (V i)) := by
    change (V i).iteratedSliceEquiv.inverse.IsDenseSubsite
      (J.over (V i).left) ((J.over A).over (V i))
    infer_instance
  have hiter := isFiniteType_of_presheafIso
    (relationsIteratedSliceSymmIso (R := R) (M := M) A (V i)
      (fun j => M.val.restrictₛₗ (V i).hom.op (s j)))
    (isFiniteType_pushforward_of_equiv (K := (J.over A).over (V i))
      (Over.iteratedSliceEquiv (V i)).symm (hrel i))
  exact isFiniteType_of_presheafIso (relationsRestrictIso M s (V i)).symm hiter

/-- **Coherence restricts to every slice.** If a sheaf of modules on a site is coherent, then
its restriction to the slice site over any object is coherent there.

This is the site-level analogue of `Stacks.SheafOfModules.IsCoherentOn.mono`, the heredity of
coherence on an open of a ringed space.  Where the ringed space predicate has to quantify over
the opens below a given one — because `Stacks.SheafOfModules.IsCoherent` is defined only over a
site of opens, so coherence of a restriction to a slice is not even statable —
`SheafOfModules.IsCoherentOnSite` is defined over an arbitrary site, so restriction to the slice
is itself the analogue of passing to a smaller open, and heredity is this theorem rather than a
definitional unfolding of a second predicate.

Finite type of the underlying presheaf restricts by `isFiniteType_over`.  For the relations
condition, a finite family of sections over an object `V` of the slice at `A` is a family of
sections over `V.left` on the base, whose relations presheaf lives on the slice at `V.left`;
`Over.iteratedSliceEquiv` identifies that site with the iterated slice, and the two readings of
the relations presheaf are compared by `relationsIteratedSliceSymmIso`. -/
theorem isCoherentOnSite_over
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R) (hM : SheafOfModules.IsCoherentOnSite M) (A : C) :
    SheafOfModules.IsCoherentOnSite (R := R.over A) (M.over A) := by
  refine ⟨isFiniteType_over M hM.isFiniteType A, ?_⟩
  intro V n s
  let s' : Fin n → M.val.obj (op V.left) := fun j =>
    (overObjIso (R := R) (M := M) A V).hom.hom (s j)
  have hbase := hM.kernel_isFiniteType V.left n s'
  let e := (Over.iteratedSliceEquiv V).symm
  let : e.functor.IsDenseSubsite (J.over V.left) ((J.over A).over V) := by
    dsimp [e]
    infer_instance
  have hpush := isFiniteType_pushforward_of_equiv
    (J := J.over V.left) (K := (J.over A).over V) e hbase
  exact isFiniteType_of_presheafIso
    (relationsIteratedSliceSymmIso (R := R) (M := M) A V s') hpush

/-- **Coherence glues.** A sheaf of modules whose restrictions to the members of a family
covering the final object are coherent on the corresponding slice sites is coherent.

This is the site-level analogue of `Stacks.SheafOfModules.isCoherent_of_coversTop`.  Together
with `isCoherentOnSite_over` it says that coherence is local on the site, with restriction to a
slice playing the role that restriction to a smaller open plays over a ringed space. -/
theorem isCoherentOnSite_of_coversTop
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    (M : SheafOfModules.{m} R) {I : Type (max u v)} (U : I → C) (hU : J.CoversTop U)
    (hM : ∀ i, SheafOfModules.IsCoherentOnSite (R := R.over (U i)) (M.over (U i))) :
    SheafOfModules.IsCoherentOnSite M := by
  refine ⟨isFiniteType_of_over M U hU (fun i => (hM i).isFiniteType), ?_⟩
  intro A n s
  refine relations_isFiniteType_of_coversTop M s (inducedCoverInSlice U)
    (inducedCoverInSlice_coversTop J U hU A) ?_
  rintro ⟨i, V, g⟩
  let W : Over (U i) := Over.mk g
  let t : Fin n → (M.over (U i)).val.obj (op W) :=
    fun j => M.val.map V.hom.op (s j)
  have hrel := (hM i).kernel_isFiniteType W n t
  let : W.iteratedSliceEquiv.functor.IsDenseSubsite
      ((J.over (U i)).over W) (J.over V.left) := by
    change W.iteratedSliceEquiv.functor.IsDenseSubsite
      ((J.over (U i)).over W) (J.over W.left)
    infer_instance
  exact isFiniteType_of_presheafIso
    (relationsIteratedSliceIso (M := M) (U i) W t)
    (isFiniteType_pushforward_of_equiv (K := J.over V.left)
      (Over.iteratedSliceEquiv W) hrel)

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (F : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Stacks 03DN, coherence.** A sheaf of modules on a ringed site is coherent if and only if
its restriction to each member of some covering family of the final object is coherent on the
corresponding localized ringed site. -/
@[stacks 03DN "coherent"]
theorem isCoherentOnSite_iff_exists_cover_isCoherentOnSite :
    SheafOfModules.IsCoherentOnSite F ↔
      ∃ (I : Type (max u v)) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (U i)).O)) (F.over (U i)) := by
  constructor
  · intro h
    obtain ⟨I, U, hU, -⟩ := h.isFiniteType.exists_generators
    let I' := ULift.{max u v} I
    have hU' : X.J.CoversTop (fun i : I' => U i.down) := by
      intro Z
      have hS : Sieve.ofObjects (fun i : I' => U i.down) Z =
          Sieve.ofObjects U Z := by
        ext Y f
        rw [Sieve.mem_ofObjects_iff, Sieve.mem_ofObjects_iff]
        constructor
        · rintro ⟨i, ⟨g⟩⟩
          exact ⟨i.down, ⟨g⟩⟩
        · rintro ⟨i, ⟨g⟩⟩
          exact ⟨ULift.up i, ⟨g⟩⟩
      simpa [hS] using hU Z
    refine ⟨I', fun i => U i.down, hU', ?_⟩
    intro i
    exact isCoherentOnSite_over F h (U i.down)
  · rintro ⟨I, U, hU, hlocal⟩
    exact isCoherentOnSite_of_coversTop F U hU hlocal

end Stacks.SheafOfModules

end
