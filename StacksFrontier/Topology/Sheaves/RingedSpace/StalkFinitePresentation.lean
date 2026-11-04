module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a finitely presented sheaf of modules is a finitely presented module

Let `(Y, 𝒪_Y)` be a ringed space and let `F` be a sheaf of `𝒪_Y`-modules of finite presentation.
This file shows that for every point `x` the stalk `F_x` is a finitely presented
`𝒪_{Y,x}`-module.

## Main results

* `Stacks.SheafOfModules.finitePresentation_stalk`: the stalk of a finitely presented sheaf of
  modules is a finitely presented module over the local ring, together with the `instance`
  version `Stacks.SheafOfModules.instFinitePresentationStalk`.
* `Module.finitePresentation_of_gens_rel` is the underlying algebra: a module with finitely
  many generators and finitely many relations which generate all relations is finitely
  presented.

## References

* [Stacks Project, Tag 01BN](https://stacks.math.columbia.edu/tag/01BN)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

/-- A module with a finite generating family `g` and a finite family `r` of relations between
the `g` which generates all relations is finitely presented. -/
@[ega "0 1.0.5" "partial"]
theorem Module.finitePresentation_of_gens_rel {A : Type*} [Ring A] {M : Type*}
    [AddCommGroup M] [Module A M] {Gen Rel : Type*} [Fintype Gen] [Fintype Rel]
    (g : Gen → M) (r : Rel → Gen → A)
    (hr : ∀ l, ∑ k, r l k • g k = 0)
    (hgen : ∀ m : M, ∃ c : Gen → A, m = ∑ k, c k • g k)
    (hrel : ∀ z : Gen → A, ∑ k, z k • g k = 0 →
      ∃ b : Rel → A, ∀ k, z k = ∑ l, b l * r l k) :
    Module.FinitePresentation A M := by
  classical
  have happ : ∀ c : Gen → A, Fintype.linearCombination A g c = ∑ k, c k • g k :=
    fun c => Fintype.linearCombination_apply A g c
  have hsurj : Function.Surjective (Fintype.linearCombination A g) := by
    intro m
    obtain ⟨c, hc⟩ := hgen m
    exact ⟨c, by rw [happ, ← hc]⟩
  refine Module.finitePresentation_of_free_of_surjective _ hsurj ?_
  have hker : LinearMap.ker (Fintype.linearCombination A g) = Submodule.span A (Set.range r) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨b, hb⟩ := hrel z (by rw [← happ]; exact hz)
      have hz' : z = ∑ l, b l • r l := by
        funext k
        rw [hb k, Finset.sum_apply]
        exact Finset.sum_congr rfl fun l _ => rfl
      rw [hz']
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      simpa only [SetLike.mem_coe, LinearMap.mem_ker, happ] using hr l
  rw [hker]
  exact Submodule.fg_span (Set.finite_range r)

namespace Stacks.SheafOfModules

variable {Y : RingedSpace.{u, u}}

/-- The canonical module structure of the stalk of an `𝒪_Y`-module over the local ring of the
ringed space at the point. -/
@[instance_reducible]
noncomputable def stalkModule (F : _root_.SheafOfModules.{u} (structureSheafRing Y)) (x : Y) :
    Module (Y.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) F.val x

/-- The germ at `x` of a section of the structure sheaf, in the `CommRingCat`-valued stalk
`Y.presheaf.stalk x`. -/
noncomputable def ringGerm (x : Y) {U : Opens Y} (hx : x ∈ U)
    (a : ToType ((structureSheafRing Y).obj.obj (op U))) : ToType (Y.presheaf.stalk x) :=
  Y.presheaf.germ U x hx a

/-- Compatibility of `ringGerm` and `germ` with the scalar action. -/
lemma germ_commRingCat_smul (F : _root_.SheafOfModules.{u} (structureSheafRing Y)) (x : Y)
    {U : Opens Y} (hx : x ∈ U) (a : ToType ((structureSheafRing Y).obj.obj (op U)))
    (m : ToType (F.val.obj (op U))) :
    letI := stalkModule F x
    germ F x hx (a • m) = ringGerm x hx a • germ F x hx m :=
  PresheafOfModules.germ_smul (R := Y.presheaf) F.val x U hx a m

/-- The germ of the restriction of a section is the germ of the section. -/
lemma ringGerm_resR (x : Y) {U V : Opens Y} (h : V ⟶ U) (hx : x ∈ V)
    (a : ToType ((structureSheafRing Y).obj.obj (op U))) :
    ringGerm x hx (resR (structureSheafRing Y) h a) = ringGerm x (h.le hx) a :=
  TopCat.Presheaf.germ_res_apply Y.presheaf h x hx a

/-- `ringGerm` is multiplicative. -/
lemma ringGerm_mul (x : Y) {U : Opens Y} (hx : x ∈ U)
    (a b : ToType ((structureSheafRing Y).obj.obj (op U))) :
    ringGerm x hx (a * b) = ringGerm x hx a * ringGerm x hx b :=
  map_mul (Y.presheaf.germ U x hx).hom a b

/-- `ringGerm` commutes with finite sums. -/
lemma ringGerm_sum (x : Y) {U : Opens Y} (hx : x ∈ U) {ι : Type*} (t : Finset ι)
    (a : ι → ToType ((structureSheafRing Y).obj.obj (op U))) :
    ringGerm x hx (∑ i ∈ t, a i) = ∑ i ∈ t, ringGerm x hx (a i) :=
  map_sum (Y.presheaf.germ U x hx).hom a t

/-- Every element of the stalk of the structure sheaf is the germ of a section. -/
lemma exists_ringGerm_eq (x : Y) (b : ToType (Y.presheaf.stalk x)) :
    ∃ (U : Opens Y) (hx : x ∈ U) (a : ToType ((structureSheafRing Y).obj.obj (op U))),
      ringGerm x hx a = b :=
  TopCat.Presheaf.exists_germ_eq Y.presheaf b

/-- Every element of the stalk of a sheaf of modules is the germ of a section. -/
lemma exists_germ_eq (F : _root_.SheafOfModules.{u} (structureSheafRing Y)) (x : Y)
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)) :
    ∃ (U : Opens Y) (hx : x ∈ U) (t : ToType (F.val.obj (op U))), germ F x hx t = m :=
  TopCat.Presheaf.exists_germ_eq F.val.presheaf m

/-- A relation between the germs of the generators of a local presentation, with coefficients
written as germs of sections over a neighbourhood `V₀`, is a combination of the germs of the
given relations. -/
lemma exists_ringGerm_rel (F : _root_.SheafOfModules.{u} (structureSheafRing Y)) (x : Y)
    (LP : LocalPresentation F x) {V₀ : Opens Y} (hxV₀ : x ∈ V₀) (fnhd : V₀ ⟶ LP.nhd)
    (aV : LP.Gen → ToType ((structureSheafRing Y).obj.obj (op V₀))) :
    letI := stalkModule F x
    (∑ k, ringGerm x hxV₀ (aV k) • germ F x LP.mem_nhd (LP.gens k) = 0) →
      ∃ b : LP.Rel → ToType (Y.presheaf.stalk x), ∀ k,
        ringGerm x hxV₀ (aV k) = ∑ l, b l * ringGerm x LP.mem_nhd (LP.rel l k) := by
  let : Module (Y.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) := stalkModule F x
  intro hz
  have hs : germ F x hxV₀ (∑ k, aV k • res F fnhd (LP.gens k)) = 0 := by
    simpa only [germ_sum, germ_commRingCat_smul, germ_res] using hz
  obtain ⟨W, gw, hxW, hres⟩ := exists_res_eq x hxV₀ _ 0 (by rw [hs, germ_zero])
  rw [res_zero, res_sum] at hres
  have h0 : ∑ k, resR (structureSheafRing Y) gw (aV k) • res F (gw ≫ fnhd) (LP.gens k) = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hres
    rw [res_smul, res_res]
  obtain ⟨W', g', hxW', b, hb⟩ := LP.relations (gw ≫ fnhd) _ h0 x hxW
  refine ⟨fun l => ringGerm x hxW' (b l), fun k => ?_⟩
  have hk := congrArg (ringGerm x hxW') (hb k)
  rw [ringGerm_resR, ringGerm_resR, ringGerm_sum] at hk
  refine hk.trans (Finset.sum_congr rfl fun l _ => ?_)
  rw [ringGerm_mul, ringGerm_resR]

/-- The stalk of a sheaf of modules of finite presentation on a ringed space is a finitely
presented module over the local ring of the space at the point. -/
theorem finitePresentation_stalk (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    [F.IsFinitePresentation] (x : Y) :
    letI := stalkModule F x
    Module.FinitePresentation (Y.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) := by
  let : Module (Y.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) := stalkModule F x
  obtain ⟨LP⟩ := nonempty_localPresentation F x
  refine Module.finitePresentation_of_gens_rel (fun k => germ F x LP.mem_nhd (LP.gens k))
    (fun l k => ringGerm x LP.mem_nhd (LP.rel l k)) ?_ ?_ ?_
  · intro l
    have h0 : germ F x LP.mem_nhd (∑ k, LP.rel l k • LP.gens k) = 0 := by
      rw [LP.rel_apply l]; exact germ_zero x LP.mem_nhd
    simpa only [germ_sum, germ_commRingCat_smul] using h0
  · intro m
    obtain ⟨V, hxV, t, ht⟩ := exists_germ_eq F x m
    obtain ⟨W, gw, hxW, c, hc⟩ :=
      LP.generates (homOfLE (inf_le_right : V ⊓ LP.nhd ≤ LP.nhd))
        (res F (homOfLE (inf_le_left : V ⊓ LP.nhd ≤ V)) t) x ⟨hxV, LP.mem_nhd⟩
    refine ⟨fun k => ringGerm x hxW (c k), ?_⟩
    have hL := congrArg (germ F x hxW) hc
    simpa only [germ_res, germ_sum, germ_commRingCat_smul, ← ht] using hL
  · intro z hz
    choose V hxV a ha using fun k => exists_ringGerm_eq x (z k)
    obtain ⟨V₁, hxV₁, hle⟩ := exists_nbhd_le x V hxV
    have hxV₀ : x ∈ V₁ ⊓ LP.nhd := ⟨hxV₁, LP.mem_nhd⟩
    have haz : ∀ k, ringGerm x hxV₀
        (resR (structureSheafRing Y) (homOfLE (le_trans inf_le_left (hle k))) (a k)) = z k :=
      fun k => by rw [ringGerm_resR, ha k]
    obtain ⟨b, hb⟩ := exists_ringGerm_rel F x LP hxV₀ (homOfLE inf_le_right)
      (fun k => resR (structureSheafRing Y) (homOfLE (le_trans inf_le_left (hle k))) (a k))
      (by rw [← hz]; exact Finset.sum_congr rfl fun k _ => by rw [haz])
    exact ⟨b, fun k => by rw [← haz k]; exact hb k⟩

/-- The stalk of a sheaf of modules of finite presentation on a ringed space is a finitely
presented module over the local ring of the space at the point, with the module structure
`Stacks.SheafOfModules.stalkModule`. -/
instance instFinitePresentationStalk (F : _root_.SheafOfModules.{u} (structureSheafRing Y))
    [F.IsFinitePresentation] (x : Y) :
    letI := stalkModule F x
    Module.FinitePresentation (Y.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) :=
  finitePresentation_stalk F x

end Stacks.SheafOfModules
