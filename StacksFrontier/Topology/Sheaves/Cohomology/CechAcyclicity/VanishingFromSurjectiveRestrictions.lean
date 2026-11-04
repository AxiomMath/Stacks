module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing

/-!
# Vanishing of Čech cohomology from surjective restrictions

Let an open subset `U₀` of a topological space be covered by opens `U i`. If an abelian sheaf
restricts surjectively from `U₀` to every arbitrary union of nonempty finite intersections of
the `U i`, then its positive-degree Čech cohomology for this covering vanishes.

## Main definitions

* `interF U s`: the intersection of the members of `U` indexed by a finite subset `s` of the
  index type.
* `IsUnionInter U V`: the open `V` is a union of intersections `interF U s` over nonempty finite
  subsets `s`.

## Main results

* `isZero_cechCohomology_of_surjective_restrictions`: positive-degree Čech cohomology vanishes
  under the stated surjectivity hypothesis.

## References

* [Stacks Project, Tag 0A36](https://stacks.math.columbia.edu/tag/0A36)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.FlasqueCech
open Stacks.Cohomology.Basis (res res_res)

universe u v

namespace Stacks.Cohomology.RaviCech

noncomputable section

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)

/-! ### Unions of finite intersections -/

/-- The intersection of the members of the family `U` indexed by a finite subset of the index
type. -/
def interF (s : Finset ι) : Opens X := ⨅ i : (s : Finset ι), U i

/-- `interF U s` is the bounded infimum of `U i` over `i ∈ s`. -/
theorem interF_eq_biInf (s : Finset ι) : interF U s = ⨅ i ∈ s, U i := by
  rw [interF, iInf_subtype]

/-- The intersection indexed by `s ∪ t` is the meet of the intersections indexed by `s` and `t`. -/
theorem interF_union [DecidableEq ι] (s t : Finset ι) :
    interF U (s ∪ t) = interF U s ⊓ interF U t := by
  rw [interF_eq_biInf, interF_eq_biInf, interF_eq_biInf, Finset.iInf_union]

/-- The intersection indexed by a singleton `{a}` is `U a`. -/
theorem interF_singleton (a : ι) : interF U {a} = U a := by
  rw [interF_eq_biInf, Finset.iInf_singleton]

/-- The intersection indexed by a nonempty finite set is contained in the union of the family. -/
theorem interF_le_iSup {s : Finset ι} (hs : s.Nonempty) : interF U s ≤ ⨆ i, U i := by
  obtain ⟨i, hi⟩ := hs
  exact (interF_eq_biInf U s ▸ iInf₂_le i hi).trans (le_iSup U i)

/-- The intersection selected by a nonempty tuple is the intersection indexed by the finite set
of its entries. -/
theorem exists_interF_eq_inter {m : ℕ} (y : Fin (m + 1) → ι) :
    ∃ s : Finset ι, s.Nonempty ∧ interF U s = inter U y := by
  classical
  refine ⟨Finset.image y Finset.univ, ⟨y 0, Finset.mem_image.2 ⟨0, Finset.mem_univ 0, rfl⟩⟩, ?_⟩
  rw [interF, inter_eq_iInf]
  refine le_antisymm (le_iInf fun a => iInf_le
      (fun i : (Finset.image y Finset.univ : Finset ι) => U i)
      ⟨y a, Finset.mem_image.2 ⟨a, Finset.mem_univ a, rfl⟩⟩) (le_iInf fun i => ?_)
  obtain ⟨a, _, ha⟩ := Finset.mem_image.1 i.2
  exact ha ▸ iInf_le (fun a => U (y a)) a

/-- An open is a *union of finite intersections* for the family `U` if it is a union of
intersections of nonempty finite subfamilies of `U`. -/
def IsUnionInter (V : Opens X) : Prop :=
  ∃ S : Set (Finset ι), (∀ s ∈ S, s.Nonempty) ∧ V = ⨆ s ∈ S, interF U s

/-- A union of finite intersections for `U` is a union, indexed by a set of nonempty finite
subsets of the index type, of the intersections `⨅ i : s, U i`. -/
theorem isUnionInter_exists_subtype {V : Opens X} (h : IsUnionInter U V) :
    ∃ S : Set (Finset ι), (∀ s ∈ S, s.Nonempty) ∧
      V = ⨆ s : S, ⨅ i : (s : Finset ι), U i := by
  obtain ⟨S, hS, hV⟩ := h
  refine ⟨S, hS, ?_⟩
  rw [hV, iSup_subtype]
  rfl

/-- A union of finite intersections for `U` is contained in the union of the family. -/
theorem isUnionInter_le_iSup {V : Opens X} (h : IsUnionInter U V) : V ≤ ⨆ i, U i := by
  obtain ⟨S, hS, rfl⟩ := h
  exact iSup₂_le fun s hs => interF_le_iSup U (hS s hs)

/-- The intersection indexed by a nonempty finite set is a union of finite intersections. -/
theorem isUnionInter_interF {s : Finset ι} (hs : s.Nonempty) : IsUnionInter U (interF U s) :=
  ⟨{s}, fun _t ht => ht ▸ hs,
    le_antisymm (le_iSup₂_of_le s rfl le_rfl) (iSup₂_le fun _t ht => ht ▸ le_rfl)⟩

/-- The intersection selected by a nonempty tuple is a union of finite intersections. -/
theorem isUnionInter_inter {m : ℕ} (y : Fin (m + 1) → ι) : IsUnionInter U (inter U y) := by
  obtain ⟨s, hs, hse⟩ := exists_interF_eq_inter U y
  exact hse ▸ isUnionInter_interF U hs

/-- Each member `U a` of the family is a union of finite intersections. -/
theorem isUnionInter_single (a : ι) : IsUnionInter U (U a) :=
  interF_singleton U a ▸ isUnionInter_interF U ⟨a, Finset.mem_singleton_self a⟩

/-- The union of the members indexed by `A` is a union of finite intersections. -/
private theorem isUnionInter_biSup (A : Set ι) : IsUnionInter U (⨆ i ∈ A, U i) := by
  refine ⟨{s : Finset ι | ∃ i ∈ A, s = {i}}, ?_, le_antisymm (iSup₂_le fun i hi => ?_)
    (iSup₂_le fun s hs => ?_)⟩
  · rintro s ⟨i, -, rfl⟩
    exact ⟨i, Finset.mem_singleton_self i⟩
  · exact le_iSup₂_of_le ({i} : Finset ι) ⟨i, hi, rfl⟩ (le_of_eq (interF_singleton U i).symm)
  · obtain ⟨i, hi, rfl⟩ := hs
    exact (interF_singleton U i).le.trans (le_part U hi)

/-- The union of the whole family is a union of finite intersections. -/
theorem isUnionInter_iSup : IsUnionInter U (⨆ i, U i) := by
  simpa using isUnionInter_biSup U Set.univ

/-- The union `part U A` of the members indexed by `A` is a union of finite intersections. -/
theorem isUnionInter_part (A : Set ι) : IsUnionInter U (part U A) :=
  isUnionInter_biSup U A

/-- The meet of two unions of finite intersections is a union of finite intersections. -/
theorem isUnionInter_inf {V W : Opens X} (hV : IsUnionInter U V) (hW : IsUnionInter U W) :
    IsUnionInter U (V ⊓ W) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hV
  obtain ⟨T, hT, rfl⟩ := hW
  refine ⟨{r : Finset ι | ∃ s ∈ S, ∃ t ∈ T, r = s ∪ t}, ?_,
    le_antisymm ?_ (iSup₂_le fun r hr => ?_)⟩
  · rintro r ⟨s, hs, t, -, rfl⟩
    obtain ⟨i, hi⟩ := hS s hs
    exact ⟨i, Finset.mem_union_left _ hi⟩
  · rw [iSup_subtype' (p := fun s => s ∈ S) (f := fun s _ => interF U s),
      iSup_subtype' (p := fun t => t ∈ T) (f := fun t _ => interF U t), iSup_inf_iSup]
    refine iSup_le fun p => le_iSup₂_of_le ((p.1 : Finset ι) ∪ (p.2 : Finset ι))
      ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩ ?_
    rw [interF_union]
  · obtain ⟨s, hs, t, ht, rfl⟩ := hr
    rw [interF_union]
    exact inf_le_inf (le_iSup₂_of_le s hs le_rfl) (le_iSup₂_of_le t ht le_rfl)

/-- If `Z ⊓ ⨆ i, U i` and `V` are unions of finite intersections for `U`, then so is
`Z ⊓ V ⊓ ⨆ i, U i`. -/
theorem isUnionInter_inf_right {Z : Opens X} (hZ : IsUnionInter U (Z ⊓ ⨆ i, U i)) {V : Opens X}
    (hV : IsUnionInter U V) : IsUnionInter U (Z ⊓ V ⊓ ⨆ i, U i) := by
  rw [inf_right_comm]
  exact isUnionInter_inf U hZ hV

/-! ### Intersections with the union of the family -/

/-- An intersection selected by a nonempty tuple absorbs the union of the family. -/
theorem inter_inf_inf_iSup {m : ℕ} (y : Fin (m + 1) → ι) (Z : Opens X) :
    inter U y ⊓ (Z ⊓ ⨆ i, U i) = inter U y ⊓ Z :=
  le_antisymm (inf_le_inf_left _ inf_le_left)
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (inter_le_iSup U y))))

/-- The union of the one-element intersections met with `Z` is the union of the family met with
`Z`. -/
theorem iSup_inter_single_inf (Z : Opens X) :
    (⨆ i, inter U (single i) ⊓ Z) = (⨆ i, U i) ⊓ Z := by
  rw [iSup_inf_eq]
  exact iSup_congr fun i => by rw [inter_eq_single, single_apply]

end

/-! ### Vanishing of Čech cohomology -/

section

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)
  (F : TopCat.Sheaf AddCommGrpCat.{v} X)

/-- If the restriction maps of `F` from `⨆ i, U i` onto the unions of finite intersections are
surjective, then every section over a union of finite intersections `W'` extends to any larger
open `W` contained in `⨆ i, U i`. -/
theorem exists_res_eq_of_surjective
    (hres : ∀ (V : Opens X) (hVU : V ≤ ⨆ i, U i),
      (∃ S : Set (Finset ι), (∀ s ∈ S, s.Nonempty) ∧
        V = ⨆ s : S, ⨅ i : (s : Finset ι), U i) →
      Function.Surjective (F.obj.map (homOfLE hVU).op))
    {W W' : Opens X} (hW : W ≤ ⨆ i, U i) (h : W' ≤ W) (hW' : IsUnionInter U W')
    (s : ToType (F.obj.obj (op W'))) :
    ∃ t : ToType (F.obj.obj (op W)), res F.obj h t = s := by
  obtain ⟨u, hu⟩ := hres W' (h.trans hW) (isUnionInter_exists_subtype U hW') s
  exact ⟨res F.obj hW u, (res_res F.obj h hW u).trans hu⟩

/-- If restriction from the covered open to every union of nonempty finite intersections of
members of the cover is surjective, then the positive-degree Čech cohomology of the cover
vanishes. -/
@[stacks 0A36]
lemma isZero_cechCohomology_of_surjective_restrictions
    (U₀ : Opens X) (hcover : U₀ = ⨆ i, U i)
    (hres : ∀ (V : Opens X) (hVU : V ≤ U₀),
      (∃ S : Set (Finset ι), (∀ s ∈ S, s.Nonempty) ∧
        V = ⨆ s : S, ⨅ i : (s : Finset ι), U i) →
      Function.Surjective (F.obj.map (homOfLE hVU).op))
    (p : ℕ) (hp : 0 < p) :
    IsZero
      (((CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U).obj F.obj).homology p) := by
  subst hcover
  have hinf : ∀ {Z : Opens X}, IsUnionInter U (Z ⊓ ⨆ i, U i) → ∀ α : ι,
      IsUnionInter U (Z ⊓ U α ⊓ ⨆ i, U i) :=
    fun hZ α => isUnionInter_inf_right U hZ (isUnionInter_single U α)
  have hpart : ∀ {Z : Opens X}, IsUnionInter U (Z ⊓ ⨆ i, U i) → ∀ A : Set ι,
      IsUnionInter U (Z ⊓ part U A ⊓ ⨆ i, U i) :=
    fun hZ A => isUnionInter_inf_right U hZ (isUnionInter_part U A)
  have hE : Extends U F (fun Z => IsUnionInter U (Z ⊓ ⨆ i, U i)) :=
    ⟨fun _ Z' _ hZ' {_} y h s => exists_res_eq_of_surjective U F hres
        (inf_le_left.trans (inter_le_iSup U y)) h
        (inter_inf_inf_iSup U y Z' ▸ isUnionInter_inf U (isUnionInter_inter U y) hZ') s,
      fun _ Z' _ hZ' h s => exists_res_eq_of_surjective U F hres inf_le_left h
        (by rwa [iSup_inter_single_inf, inf_comm]) s⟩
  have hcls : IsUnionInter U ((⊤ : Opens X) ⊓ ⨆ i, U i) :=
    (top_inf_eq (⨆ i, U i)).symm ▸ isUnionInter_iSup U
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have key : IsZero ((relComplex U F.obj ⊤).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro s hs
    obtain ⟨b, hb⟩ := FlasqueCech.vanishing U F
      (Cls := fun Z => IsUnionInter U (Z ⊓ ⨆ i, U i)) hinf hpart hE n ⊤ hcls s hs
    exact ⟨b, hb⟩
  exact key.of_iso <| (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ)
    (n + 1)).mapIso ((cechComplexFunctor U).mapIso (shrinkTopIso (P := F.obj)).symm)

end

end Stacks.Cohomology.RaviCech

end
