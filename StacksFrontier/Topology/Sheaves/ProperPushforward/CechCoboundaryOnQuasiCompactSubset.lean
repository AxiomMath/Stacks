module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAbelian
public import StacksFrontier.Topology.Sheaves.ProperPushforward.FlasqueCochainsOnQuasiCompactSubset

/-!
# A Čech cochain that is a cocycle only along a quasi-compact subset is a coboundary

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points of
which are separated by disjoint opens *of `X`*, and let `F` be a **flasque** sheaf of abelian
groups on `X`.  Let `U : ι → Opens X` be an open cover of `Z` and let `s` be a family of sections
of `F`, one over each `⨅ k, U (τ k)` for `τ` a `(q+2)`-tuple of indices — that is, a Čech
`(q+1)`-cochain of `F` for the cover `U` of the open neighbourhood `⨆ i, U i` of `Z`.

This file proves that if the Čech differential of `s` has vanishing germ at every point of `Z`,
then the cover can be **shrunk** to an open cover `V : ι → Opens X` of `Z` with `V i ≤ U i` over
which `s` becomes an honest Čech coboundary.

This is the last paragraph of the proof of [Stacks, Tag 09V3] in positive degrees, where it is
applied to the cochain obtained from a Čech cocycle of `I|_Z` by
`Stacks.Topology.SectionsOnQuasiCompactSubset.exists_refinement_sections_of_isFlasque`: the
differential of that cochain restricts to zero on `Z` because the original family was a cocycle
there, which is exactly the hypothesis below.  Two inputs combine:

* the shrinking step of the same tag,
  `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_refinement_eq_of_germ_eq`, which turns the
  germwise vanishing of the differential into vanishing on a shrunken cover (this is where
  [Stacks, Tag 0CY5] enters), and
* [Stacks, Tag 01EP] in positive degrees for abelian sheaves, in the element form
  `Stacks.Cohomology.CechSheaf.exists_sum_res_eq`, which is available for every *flasque* sheaf of
  abelian groups by [Stacks, Tag 09SZ]; an injective abelian sheaf is flasque by
  [Stacks, Tag 09SX].

## Main definitions

* `Stacks.Topology.SectionsOnQuasiCompactSubset.cechDiff`: the Čech differential of a family of
  sections indexed by the tuples of an open cover, as the alternating sum of the restrictions
  along the face maps.

## Main results

* `Stacks.Topology.SectionsOnQuasiCompactSubset.iInf_le_comp`: reindexing a tuple enlarges the
  infimum of the opens it selects.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.cechDiff_res`: restricting a Čech differential is
  the Čech differential of the restrictions.
* `Stacks.Topology.SectionsOnQuasiCompactSubset.exists_shrink_cechDiff_eq_of_germ_eq_zero`: the
  statement above ([Stacks, Tag 09V3], positive degrees).

## Implementation notes

The families are indexed by the *infimum* `⨅ k, U (τ k)` of the selected opens, which is the
spelling of the two refinement steps of [Stacks, Tag 09V3] and of [Stacks, Tag 0CY5], and
not by `Stacks.CategoryTheory.CechComplex.inter`, which is the spelling of
`Stacks.Cohomology.CechSheaf.exists_sum_res_eq`.  The two opens are *equal*, by
`Stacks.CategoryTheory.CechComplex.inter_eq_iInf`, so crossing between them needs no `eqToHom`:
every restriction map here is `Stacks.Cohomology.Basis.res`, which takes an inclusion of opens as
a *proof*, and `Stacks.Cohomology.Basis.res_res` composes two of them away.

The conclusion quantifies over the proof `hle` of the inclusion of the shrunken intersection in
the original one, rather than fixing one, exactly as
`Stacks.Topology.SectionsOnQuasiCompactSubset.exists_refinement_eq_of_germ_eq` does: `Opens X` is
a partial order, so all such proofs are equal and the choice is immaterial.

The germwise hypothesis is phrased with `GermPullback.germAddHom`, the germ map of the underlying
presheaf of types of a presheaf of abelian groups read as a morphism of abelian groups: the
shrinking step is a statement about sheaves of *sets* and speaks of germs in the stalks of the
underlying presheaf of types, whereas the hypothesis one wants to supply is that an element of an
abelian group of sections has zero germ.  `GermPullback.germAddHom` is precisely the bridge, and
`GermPullback.germ_zero` identifies the germ of the zero section with zero.

The index type is taken in the universe of the space.  This is no restriction: an open cover of a
subset of `X` indexed by an arbitrary type may be reindexed by its image in `Opens X`, which lives
in that universe, and `Stacks.Cohomology.CechSheaf.exists_sum_res_eq` ties the index type to the
universe of the coefficients.

## References

* [Stacks, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks, Tag 09SX](https://stacks.math.columbia.edu/tag/09SX)
* [Stacks, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks, Tag 0CY5](https://stacks.math.columbia.edu/tag/0CY5)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sum res_zsmul)
open Stacks.Cohomology.CechSheaf (exists_sum_res_eq inter_le_reindex)
open Stacks.CategoryTheory.CechComplex (inter inter_eq_iInf)

universe u

noncomputable section

namespace Stacks.Topology.SectionsOnQuasiCompactSubset

variable {X : TopCat.{u}}

/-! ### The Čech differential of a family of sections -/

/-- **Reindexing a tuple enlarges the infimum of the opens it selects.**  This is the inclusion
along which the face maps of the Čech differential restrict (Stacks 09V3). -/
theorem iInf_le_comp {ι : Type*} {m m' : ℕ} (U : ι → Opens X) (τ : Fin m → ι)
    (h : Fin m' → Fin m) : (⨅ k, U (τ k)) ≤ ⨅ k, U ((τ ∘ h) k) :=
  le_iInf fun k ↦ iInf_le _ (h k)

/-- **Shrinking each member of a family of opens shrinks the infimum selected by a tuple**
(Stacks 09V3). -/
theorem iInf_le_iInf_of_le {ι : Type*} {m : ℕ} {U V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)
    (τ : Fin m → ι) : (⨅ k, V (τ k)) ≤ ⨅ k, U (τ k) :=
  le_iInf fun k ↦ (iInf_le _ k).trans (hVU (τ k))

/-- A section of a sheaf of abelian groups whose germ at a point vanishes has, at that point, the
same germ as the zero section in the underlying presheaf of types.  This is the bridge between
the abelian hypothesis one wants to supply and the germ equality that the shrinking step of
Stacks 09V3, a statement about sheaves of sets, asks for. -/
theorem typePresheaf_germ_eq_germ_zero (F : X.Sheaf AddCommGrpCat.{u}) {W : Opens X} {x : ↥X}
    (hx : x ∈ W) (t : ToType (F.presheaf.obj (op W)))
    (ht : GermPullback.germAddHom F.presheaf W hx t = 0) :
    (GermPullback.typePresheaf F.presheaf).germOfSize W x hx t =
      (GermPullback.typePresheaf F.presheaf).germOfSize W x hx
        (0 : ToType (F.presheaf.obj (op W))) := by
  rw [GermPullback.germ_zero F.presheaf W hx,
    ← GermPullback.germAddHom_apply F.presheaf W hx]
  exact ht

/-- **The Čech differential of a family of sections**, indexed by the tuples of a family of
opens: the alternating sum of the restrictions of the components along the face maps of the
tuple.  This is the differential of the Čech complex read on components, in the indexing by
infima of opens that the refinement steps of Stacks 09V3 use. -/
def cechDiff {ι : Type*} (P : (Opens ↥X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {p : ℕ} (U : ι → Opens X)
    (s : ∀ τ : Fin (p + 1) → ι, ToType (P.obj (op (⨅ k, U (τ k)))))
    (τ : Fin (p + 2) → ι) : ToType (P.obj (op (⨅ k, U (τ k)))) :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
    res P (iInf_le_comp U τ a.succAbove) (s (τ ∘ a.succAbove))

/-- Restricting an alternating sum of restrictions restricts each of its terms. -/
private theorem res_alt_sum_res {A B : Opens X} {n : ℕ} {C : Fin n → Opens X}
    (P : (Opens ↥X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (h : A ≤ B) (g : ∀ a, B ≤ C a)
    (t : ∀ a, ToType (P.obj (op (C a)))) :
    res P h (∑ a : Fin n, (-1 : ℤ) ^ (a : ℕ) • res P (g a) (t a)) =
      ∑ a : Fin n, (-1 : ℤ) ^ (a : ℕ) • res P (h.trans (g a)) (t a) := by
  rw [res_sum P h]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [res_zsmul P h, res_res]

/-- **Restricting a Čech differential is the Čech differential of the restrictions.**  Both sides
are the alternating sum of the components of the family restricted to the smaller intersection
(Stacks 09V3). -/
theorem cechDiff_res {ι : Type*} (P : (Opens ↥X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {p : ℕ}
    (U V : ι → Opens X) (hVU : ∀ i, V i ≤ U i)
    (s : ∀ τ : Fin (p + 1) → ι, ToType (P.obj (op (⨅ k, U (τ k)))))
    (τ : Fin (p + 2) → ι)
    (hle : (⨅ k, V (τ k)) ≤ ⨅ k, U (τ k)) :
    cechDiff P V (fun σ ↦ res P (iInf_le_iInf_of_le hVU σ) (s σ)) τ =
      res P hle (cechDiff P U s τ) := by
  rw [cechDiff, cechDiff, res_alt_sum_res P hle]
  simp only [res_res]

/-! ### Shrinking a cover so that a cochain becomes a coboundary -/

/-- **Stacks 09V3, positive degrees: a cochain that is a cocycle only along `Z` is a coboundary
on a shrunken cover.**  Let `F` be a flasque sheaf of abelian groups on `X`, let `Z` be a
quasi-compact subset of `X` whose distinct points are separated by disjoint opens of `X`, and let
`U : ι → Opens X` be an open cover of `Z`.  Let `s` be a family of sections of `F`, one over each
`⨅ k, U (τ k)` for `τ` a `(q+2)`-tuple of indices, whose Čech differential has vanishing germ at
every point of `Z`.  Then there is an open cover `V : ι → Opens X` of `Z` with `V i ≤ U i` and a
family `h` indexed by the `(q+1)`-tuples whose Čech differential is the restriction of `s`.

In the source this is the final step: the cochain `s` of the injective sheaf `I` produced from a
Čech cocycle of `I|_Z` has a differential vanishing along `Z`, so by Stacks 0CY5 it becomes a
genuine Čech cocycle after shrinking the cover, and then it is a coboundary because the higher
Čech cohomology of `I` vanishes (Stacks 01EP), which holds for any flasque sheaf of abelian
groups by Stacks 09SZ. -/
theorem exists_shrink_cechDiff_eq_of_germ_eq_zero (F : X.Sheaf AddCommGrpCat.{u})
    [F.IsFlasque] {Z : Set ↥X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set ↥X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    {ι : Type u} (q : ℕ) (U : ι → Opens X) (hcov : Z ⊆ ⋃ i, ((U i : Opens X) : Set ↥X))
    (s : ∀ τ : Fin (q + 2) → ι, ToType (F.presheaf.obj (op (⨅ k, U (τ k)))))
    (hs : ∀ (τ : Fin (q + 3) → ι) (x : ↥X), x ∈ Z → ∀ hx : x ∈ ⨅ k, U (τ k),
      GermPullback.germAddHom F.presheaf (⨅ k, U (τ k)) hx (cechDiff F.presheaf U s τ) = 0) :
    ∃ V : ι → Opens X, (∀ i, V i ≤ U i) ∧ Z ⊆ ⋃ i, ((V i : Opens X) : Set ↥X) ∧
      ∃ h : ∀ σ : Fin (q + 1) → ι, ToType (F.presheaf.obj (op (⨅ k, V (σ k)))),
        ∀ (τ : Fin (q + 2) → ι) (hle : (⨅ k, V (τ k)) ≤ ⨅ k, U (τ k)),
          cechDiff F.presheaf V h τ = res F.presheaf hle (s τ) := by
  classical
  -- Step 1: shrink the cover so that the differential of `s` vanishes on the nose.
  obtain ⟨V, hVU, hVcov, hVzero⟩ :=
    exists_refinement_eq_of_germ_eq (GermPullback.typeSheaf F) hZ hSep (q + 2) U hcov
      (fun τ ↦ cechDiff F.presheaf U s τ)
      (fun τ ↦ (0 : ToType (F.presheaf.obj (op (⨅ k, U (τ k))))))
      (fun τ x hxZ hx ↦ typePresheaf_germ_eq_germ_zero F hx _ (hs τ x hxZ hx))
  have hVzero' : ∀ (τ : Fin (q + 3) → ι) (hle : (⨅ k, V (τ k)) ≤ ⨅ k, U (τ k)),
      res F.presheaf hle (cechDiff F.presheaf U s τ) = 0 := fun τ hle ↦
    (hVzero τ hle).trans (res_zero F.presheaf hle)
  -- Step 2: the restricted family is an honest Čech cocycle.
  have hcocycle : ∀ τ : Fin (q + 3) → ι, cechDiff F.presheaf V
      (fun σ ↦ res F.presheaf (iInf_le_iInf_of_le hVU σ) (s σ)) τ = 0 := fun τ ↦ by
    rw [cechDiff_res F.presheaf U V hVU s τ (iInf_le_iInf_of_le hVU τ),
      hVzero' τ (iInf_le_iInf_of_le hVU τ)]
  -- Step 3: apply Stacks 01EP in positive degrees, in the `inter` spelling.
  obtain ⟨h', hh'⟩ := exists_sum_res_eq (T := X) V F q
    (fun y ↦ res F.presheaf (inter_eq_iInf V y).le
      (res F.presheaf (iInf_le_iInf_of_le hVU y) (s y)))
    (fun x ↦ by
      have hx := congrArg (res F.presheaf (inter_eq_iInf V x).le) (hcocycle x)
      rw [cechDiff, res_alt_sum_res, res_zero] at hx
      simpa only [res_res] using hx)
  -- Step 4: transport the primitive back to the `⨅` spelling.
  refine ⟨V, hVU, hVcov, fun σ ↦ res F.presheaf (inter_eq_iInf V σ).ge (h' σ),
    fun τ hle ↦ ?_⟩
  have key := congrArg (res F.presheaf (inter_eq_iInf V τ).ge) (hh' τ)
  rw [res_alt_sum_res] at key
  simpa only [cechDiff, res_res] using key

end Stacks.Topology.SectionsOnQuasiCompactSubset

end
