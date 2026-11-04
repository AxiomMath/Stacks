module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationSections
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabited

/-!
# Finite freeness is section-level presentation data with no relations

Stacks 03DL states finite presentation of a sheaf of modules on a ringed site *on sections*: over
a suitable object `V` there are `n` sections `s` of `M` which generate locally and `m` tuples
`t j` of sections of the structure sheaf, each a relation among the `s`, such that every relation
among the `s` is locally a combination of the `t j`.  That predicate is
`Stacks.Sheaves.LocalGeneration.IsPresentationData`, and it is parameterized by the number `m` of
relations.

The case `m = 0` is **finite freeness**, Stacks 03DE(2), of the restriction `M.over V`.

## Main results

* `Stacks.Sheaves.LocalGeneration.exists_isPresentationData_of_isFiniteFree`: **the encoding.**
  A finite free `M.over V` yields presentation data for `M` over `V` with no relation tuples.
* `Stacks.Sheaves.LocalGeneration.isFiniteFree_of_isPresentationData_zero`: **the decoding.**
  Presentation data for `M` over `V` indexed by `Fin 0` relations makes `M.over V` finite free.
* `Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf_zero`: if `M` is finite
  locally free, Stacks 03DL(2), then the family `n ↦ presDataSheaf M n 0` — indexed by `ℕ`, not by
  `ℕ × ℕ` — is jointly locally inhabited.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open Stacks.SheafOfModules

universe v u u'

namespace Stacks.Sheaves.LocalGeneration

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-! ### Reindexed cofans and sections of the structure sheaf vanishing on a covering -/

/-- A colimiting cofan over a constant family stays one after reindexing the index type along an
equivalence. -/
def isColimitCofanReindex {D : Type*} [Category D] {β γ : Type*} {A P : D} (q : γ ≃ β)
    (inj : β → (A ⟶ P)) (h : IsColimit (Cofan.mk (f := fun _ : β => A) P inj)) :
    IsColimit (Cofan.mk (f := fun _ : γ => A) P fun i => inj (q i)) := by
  refine Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc h fun b => s.inj (q.symm b)) ?_ ?_
  · intro s i
    simpa only [cofan_mk_inj, Equiv.symm_apply_apply] using
      Cofan.IsColimit.fac h (fun b => s.inj (q.symm b)) (q i)
  · intro s n hn
    refine Cofan.IsColimit.hom_ext h _ _ fun b => ?_
    rw [Cofan.IsColimit.fac h (fun b => s.inj (q.symm b)) b]
    simpa only [cofan_mk_inj, Equiv.apply_symm_apply] using hn (q.symm b)

/-- A section of a sheaf of rings which restricts to zero along every member of a covering is
zero. -/
theorem ringSection_eq_zero_of_cover [J.HasSheafCompose (forget RingCat.{u})]
    (R : Sheaf J RingCat.{u}) {U : C} (S : Sieve U) (hS : S ∈ J U)
    {a : R.obj.obj (op U)}
    (h : ∀ (V : C) (f : V ⟶ U), S f → R.obj.map f.op a = 0) : a = 0 := by
  have hA := (isSheaf_iff_isSheaf_of_type J _).1 (Sheaf.ringSheaf R).property S hS
  refine hA.isSeparatedFor.ext fun V f hf => ?_
  show (R.obj.map f.op a : R.obj.obj (op V)) = R.obj.map f.op (0 : R.obj.obj (op U))
  rw [h V f hf, map_zero]

/-! ### Encoding: a finite free restriction gives presentation data with no relations -/

section Encode

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The coordinates of the zero section of a finite free sheaf of modules on a slice site vanish. -/
private theorem coordsOver_zero {U : C} {ι : Type u} [DecidableEq ι] (V : Over U) (i : ι) :
    coordsOver (R := R) (ι := ι) V 0 i = 0 :=
  map_zero ((freeProj (S := R.over U) i).val.app (op V)).hom

/-- **A finite free restriction `M.over V` is presentation data for `M` over `V` with no
relations.** -/
theorem exists_isPresentationData_of_isFiniteFree (M : SheafOfModules.{u} R) (V : C)
    (h : _root_.SheafOfModules.IsFiniteFree (R.over V) (M.over V)) :
    ∃ (n : ℕ) (s : Fin n → M.val.obj (op V))
      (t : Fin 0 → Fin n → R.obj.obj (op V)), IsPresentationData M s t := by
  classical
  obtain ⟨n, ι, ⟨hc⟩⟩ :=
    (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit (R.over V) (M.over V)).1 h
  have hc' : IsColimit (Cofan.mk
      (f := fun _ : ULift.{u} (Fin n) => _root_.SheafOfModules.unit (R.over V))
      (M.over V) fun i => ι (Equiv.ulift i)) :=
    isColimitCofanReindex Equiv.ulift ι hc
  let e : free (R := R.over V) (ULift.{u} (Fin n)) ≅ M.over V :=
    (isColimitFreeCofan (R := R.over V) (ULift.{u} (Fin n))).coconePointUniqueUpToIso hc'
  let gens : ULift.{u} (Fin n) → M.val.obj (op V) :=
    fun k => ((M.over V).freeHomEquiv e.hom k).eval (op (Over.mk (𝟙 V)))
  have hπ : e.hom = freeToOver M gens :=
    ((M.over V).freeHomEquiv.symm_apply_apply e.hom).symm.trans
      (freeHomEquiv_symm_eq_freeToOver M _)
  let σ : (M.over V).GeneratingSections :=
    { I := ULift.{u} (Fin n)
      s := (M.over V).freeHomEquiv e.hom
      epi := by
        rw [(M.over V).freeHomEquiv.symm_apply_apply e.hom]
        infer_instance }
  refine ⟨n, fun i => gens (Equiv.ulift.symm i), Fin.elim0, fun j => j.elim0,
    locallySpans_of_generatingSections_over M σ n Equiv.ulift, fun W f a ha => ?_⟩
  have hz : (∑ k : ULift.{u} (Fin n), a (Equiv.ulift k) • res M f (gens k)) = 0 :=
    (Fintype.sum_equiv Equiv.ulift _
      (fun i : Fin n => a i • restr M f.op (gens (Equiv.ulift.symm i))) fun _ => rfl).trans ha
  set x := ofCoordsOver (R := R) (ι := ULift.{u} (Fin n)) (Over.mk f)
    (fun k => a (Equiv.ulift k)) with hxdef
  have hco := coordsOver_ofCoordsOver (R := R) (ι := ULift.{u} (Fin n)) (Over.mk f)
    (fun k => a (Equiv.ulift k))
  have h0 : e.hom.val.app (op (Over.mk f)) x = 0 := by
    rw [hπ, app_freeToOver_eq_sum_smul_coordsOver]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hz
    exact congrArg (fun c => c • res M (Over.mk f).hom (gens k)) (congrFun hco k)
  have hback : e.inv.val.app (op (Over.mk f)) (e.hom.val.app (op (Over.mk f)) x) = x :=
    congrArg (fun φ : free (R := R.over V) (ULift.{u} (Fin n)) ⟶
      free (R := R.over V) (ULift.{u} (Fin n)) => φ.val.app (op (Over.mk f)) x) e.hom_inv_id
  have hx0 : x = 0 :=
    hback.symm.trans ((congrArg (fun y => e.inv.val.app (op (Over.mk f)) y) h0).trans
      (map_zero (e.inv.val.app (op (Over.mk f))).hom))
  have hazero : ∀ i, a i = 0 := by
    intro i
    refine (congrFun hco (Equiv.ulift.symm i)).symm.trans ?_
    rw [← hxdef, hx0]
    exact coordsOver_zero _ _
  refine J.superset_covering (fun Z g _ => ⟨Fin.elim0, fun i => ?_⟩) (J.top_mem W)
  rw [hazero i, Finset.univ_eq_empty, Finset.sum_empty]
  exact (map_zero (R.obj.map g.op).hom).symm

end Encode

/-! ### Decoding: presentation data with no relations gives a finite free restriction -/

section Decode

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget RingCat.{u})]

/-- **Presentation data with no relation tuples makes the restriction finite free.** This is
Stacks 03DE(2) for `M.over V` out of the section-level data of Stacks 03DL at `m = 0`. -/
theorem isFiniteFree_of_isPresentationData_zero (M : SheafOfModules.{u} R) {V : C} {n : ℕ}
    (s : Fin n → M.val.obj (op V)) (t : Fin 0 → Fin n → R.obj.obj (op V))
    (h : IsPresentationData M s t) :
    _root_.SheafOfModules.IsFiniteFree (R.over V) (M.over V) := by
  classical
  let _ : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hgen : GeneratesLocally J M.val (fun i : ULift.{u} (Fin n) => s i.down) :=
    generatesLocally_comp_equiv Equiv.ulift s (generatesLocally_of_locallySpans s h.2.1)
  have hepi : Epi (freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)) :=
    epi_freeHomEquiv_symm_mkOver _ hgen
  have hker : ∀ (X : (Over V)ᵒᵖ)
      (y : (free (R := R.over V) (ULift.{u} (Fin n))).val.obj X),
      (freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)).val.app X y = 0 → y = 0 := by
    intro X y hy
    have hy' : (∑ k : ULift.{u} (Fin n),
        coordsOver (R := R) X.unop y k • res M X.unop.hom (s k.down)) = 0 :=
      (app_freeToOver_eq_sum_smul_coordsOver M
        (fun i : ULift.{u} (Fin n) => s i.down) X.unop y).symm.trans hy
    have ha : combinationValue M (fun i : Fin n => coordsOver (R := R) X.unop y (ULift.up i))
        (fun i => restr M X.unop.hom.op (s i)) = 0 :=
      (Fintype.sum_equiv Equiv.ulift.symm _
        (fun k : ULift.{u} (Fin n) =>
          coordsOver (R := R) X.unop y k • res M X.unop.hom (s k.down)) fun _ => rfl).trans hy'
    have hcoord : ∀ k : ULift.{u} (Fin n), coordsOver (R := R) X.unop y k = 0 := by
      intro k
      refine ringSection_eq_zero_of_cover R _ (h.2.2 X.unop.left X.unop.hom _ ha)
        fun Z g hg => ?_
      obtain ⟨c, hc⟩ := hg
      refine (hc k.down).symm.trans ?_
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact (coordsOver_bijective (R := R) (ι := ULift.{u} (Fin n)) X.unop).injective
      (funext fun k => (hcoord k).trans (coordsOver_zero _ k).symm)
  have hmono : Mono (freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)) :=
    (_root_.SheafOfModules.forget (R.over V)).mono_of_mono_map
      (PresheafOfModules.mono_of_injective
        (f := (freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)).val)
        fun {X} y₁ y₂ hy => sub_eq_zero.1 (hker X (y₁ - y₂)
          ((map_sub ((freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)).val.app X).hom
            y₁ y₂).trans (sub_eq_zero.2 hy))))
  have hiso : IsIso (freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)) :=
    isIso_of_mono_of_epi _
  have hcofan : IsColimit (Cofan.mk
      (f := fun _ : ULift.{u} (Fin n) => _root_.SheafOfModules.unit (R.over V))
      (M.over V) fun k => ιFree (R := R.over V) k ≫
        freeToOver M (fun i : ULift.{u} (Fin n) => s i.down)) :=
    IsColimit.ofIsoColimit (isColimitFreeCofan (R := R.over V) (ULift.{u} (Fin n)))
      (Cocone.ext (@asIso _ _ _ _ _ hiso) (by rintro ⟨k⟩; rfl))
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit (R.over V) (M.over V)).2
    ⟨n, _, ⟨isColimitCofanReindex Equiv.ulift.symm _ hcofan⟩⟩

end Decode

/-! ### The family of data sheaves with no relations is jointly locally inhabited -/

section Joint

variable [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **If `M` is finite locally free then the family of data sheaves with no relations is jointly
locally inhabited**: every object of the site is covered by objects over which `M` has, for some
`n`, a presentation by `n` sections and no relation tuples. -/
theorem jointlyLocallyInhabited_presDataSheaf_zero (M : SheafOfModules.{u} R)
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    Stacks.Topos.JointlyLocallyInhabited J (fun n : ℕ => presDataSheaf M n 0) := by
  intro U
  obtain ⟨I, V, f, hcov, hfree⟩ := hM U
  refine J.superset_covering (fun Z g hg => ?_) hcov
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff V f g).1 hg
  obtain ⟨n, s, t, hd⟩ := exists_isPresentationData_of_isFiniteFree M (V i) (hfree i)
  exact ⟨n, ⟨(presDataSheaf M n 0).obj.map k.op (presDataMk M hd)⟩⟩

end Joint

end Stacks.Sheaves.LocalGeneration

end
