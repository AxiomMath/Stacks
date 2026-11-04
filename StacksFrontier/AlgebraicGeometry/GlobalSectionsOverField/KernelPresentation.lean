module

public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Opens

/-!
# Global sections as the kernel of the overlap difference of a covering

Let `X` be a scheme over a field `k`, let `F` be a module on `X` and let `W i` be an open
covering of `X`. The sheaf axiom says that the sequence

`Γ(X, F) ⟶ ∏ᵢ Γ(F, W i) ⟶ ∏_{i, i'} Γ(F, W i ⊓ W i')`

is exact at the left two terms: a global section is determined by its restrictions, and a family
of local sections agreeing pairwise comes from one. This file packages both halves as a single
`k`-linear statement: the restriction map, corestricted to the kernel of the difference of the two
restrictions, is **bijective**.

That is the shape in which the sheaf axiom can be tensored. Over a field every module is flat, so
`Module.Flat.rTensor_exact` carries the exactness through `⊗_k B` — which is what turns a family
of local box sections into a global one.

## Main definitions

* `AlgebraicGeometry.sectionsRestrictPi`: the family of restrictions to the members of the
  covering, as a `k`-linear map into the product.
* `AlgebraicGeometry.sectionsOverlapDiff`: the difference of the two restrictions to an overlap.
* `AlgebraicGeometry.sectionsRestrictKer`: the first map, corestricted to the kernel of the
  second, with `AlgebraicGeometry.sectionsKerEquiv` the resulting `k`-linear equivalence.

## Main results

* `AlgebraicGeometry.exists_section_of_isCompatible`: **sections of a sheaf of modules glue along
  an open covering.**
* `AlgebraicGeometry.bijective_sectionsRestrictKer`: **the global sections are the kernel of the
  overlap difference.**
* `AlgebraicGeometry.sectionsKerEquiv_symm_apply_coe`: reading the inverse of that equivalence
  back on a member of the covering gives the component one started with.

## Implementation notes

The index of the overlap product is the full square `ι × ι` rather than a set of unordered pairs:
that way the difference map is a plain `AlgebraicGeometry.sectionsOverFieldRestrict` composed with
two `LinearMap.proj`s, with no case distinction, and the diagonal entries are zero rather than
absent.

Gluing is `TopCat.Sheaf.existsUnique_gluing'` for the sheaf of abelian groups underlying `F`; its
compatibility hypothesis `TopCat.Presheaf.IsCompatible` is stated with
`TopologicalSpace.Opens.infLELeft`, which is `homOfLE inf_le_left`, so the two spellings are
interchangeable and no transport is needed.

## References

* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

/-- **Sections of a sheaf of modules glue along an open covering.** -/
theorem exists_section_of_isCompatible {X : Scheme.{u}} (F : X.Modules) {ι : Type*}
    {W : ι → X.Opens} (hW : ⨆ i, W i = ⊤) (x : ∀ i, Γ(F, W i))
    (hx : ∀ i j, F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (x i)
      = F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (x j)) :
    ∃ s : Γ(F, ⊤), ∀ i, F.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op s = x i := by
  let S : TopCat.Sheaf AddCommGrpCat X := ⟨F.presheaf, F.isSheaf⟩
  exact (S.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) (by rw [hW]) x hx).exists

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)
  {ι : Type*} (W : ι → X.Opens)

/-- The family of restrictions of a global section to the members of a covering. -/
def sectionsRestrictPi :
    ↑(sectionsOverField k f F ⊤) →ₗ[k] (∀ i, ↑(sectionsOverField k f F (W i))) :=
  LinearMap.pi fun i => sectionsOverFieldRestrict k f F (le_top (a := W i))

/-- The `i`-th component of `AlgebraicGeometry.sectionsRestrictPi` is the restriction of a global
section to `W i`. -/
@[simp] theorem sectionsRestrictPi_apply (s : ↑(sectionsOverField k f F ⊤)) (i : ι) :
    sectionsRestrictPi k f F W s i
      = sectionsOverFieldRestrict k f F (le_top (a := W i)) s := rfl

/-- The difference of the two restrictions of a family of local sections to an overlap. -/
def sectionsOverlapDiff :
    (∀ i, ↑(sectionsOverField k f F (W i))) →ₗ[k]
      (∀ p : ι × ι, ↑(sectionsOverField k f F (W p.1 ⊓ W p.2))) :=
  LinearMap.pi fun p =>
    (sectionsOverFieldRestrict k f F (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1)).comp
        (LinearMap.proj p.1) -
      (sectionsOverFieldRestrict k f F (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2)).comp
        (LinearMap.proj p.2)

/-- The `(i, i')`-th component of `AlgebraicGeometry.sectionsOverlapDiff` is the difference of the
restrictions of the `i`-th and `i'`-th local sections to `W i ⊓ W i'`. -/
@[simp] theorem sectionsOverlapDiff_apply (x : ∀ i, ↑(sectionsOverField k f F (W i)))
    (p : ι × ι) :
    sectionsOverlapDiff k f F W x p
      = sectionsOverFieldRestrict k f F (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1) (x p.1) -
        sectionsOverFieldRestrict k f F (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2) (x p.2) := rfl

/-- The restrictions of a global section agree on the overlaps. -/
theorem sectionsOverlapDiff_sectionsRestrictPi (s : ↑(sectionsOverField k f F ⊤)) :
    sectionsOverlapDiff k f F W (sectionsRestrictPi k f F W s) = 0 := by
  funext p
  refine sub_eq_zero.mpr ?_
  have key : ∀ {U V : X.Opens} (h : V ≤ U),
      sectionsOverFieldRestrict k f F h (sectionsOverFieldRestrict k f F (le_top (a := U)) s)
        = sectionsOverFieldRestrict k f F (le_top (a := V)) s := fun h =>
    presheaf_map_map F (homOfLE le_top) (homOfLE h) (homOfLE le_top) s
  exact (key _).trans (key _).symm

/-- The family of restrictions of a global section, as a map into the kernel of the overlap
difference. -/
def sectionsRestrictKer : ↑(sectionsOverField k f F ⊤) →ₗ[k]
    LinearMap.ker (sectionsOverlapDiff k f F W) :=
  LinearMap.codRestrict _ (sectionsRestrictPi k f F W)
    (sectionsOverlapDiff_sectionsRestrictPi k f F W)

/-- The family of local sections underlying `AlgebraicGeometry.sectionsRestrictKer` is
`AlgebraicGeometry.sectionsRestrictPi`. -/
@[simp] theorem sectionsRestrictKer_coe (s : ↑(sectionsOverField k f F ⊤)) :
    ((sectionsRestrictKer k f F W s : ∀ i, ↑(sectionsOverField k f F (W i))))
      = sectionsRestrictPi k f F W s := rfl

/-- **The global sections are the kernel of the overlap difference of a covering.** -/
theorem bijective_sectionsRestrictKer (hW : ⨆ i, W i = ⊤) :
    Function.Bijective (sectionsRestrictKer k f F W) := by
  refine ⟨fun s s' hss => ?_, fun v => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_sectionsOverFieldRestrict_eq_zero k f F hW (s - s') fun i => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun (congrArg Subtype.val hss) i
  · obtain ⟨s, hs⟩ := exists_section_of_isCompatible F hW (fun i => v.1 i) fun i j =>
      sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp v.2) (i, j))
    exact ⟨s, Subtype.ext (funext fun i => hs i)⟩

/-- **The global sections, as a `k`-linear equivalence onto the kernel of the overlap
difference.** -/
def sectionsKerEquiv (hW : ⨆ i, W i = ⊤) :
    ↑(sectionsOverField k f F ⊤) ≃ₗ[k] LinearMap.ker (sectionsOverlapDiff k f F W) :=
  LinearEquiv.ofBijective _ (bijective_sectionsRestrictKer k f F W hW)

/-- Reading the inverse of `AlgebraicGeometry.sectionsKerEquiv` back on a member of the covering
gives the component one started with. -/
theorem sectionsKerEquiv_symm_apply_coe (hW : ⨆ i, W i = ⊤)
    (v : LinearMap.ker (sectionsOverlapDiff k f F W)) (i : ι) :
    sectionsOverFieldRestrict k f F (le_top (a := W i))
        ((sectionsKerEquiv k f F W hW).symm v) = v.1 i :=
  congrFun (congrArg Subtype.val ((sectionsKerEquiv k f F W hW).apply_symm_apply v)) i

end AlgebraicGeometry

end
