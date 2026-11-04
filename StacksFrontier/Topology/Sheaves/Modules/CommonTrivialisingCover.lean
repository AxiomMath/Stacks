module

public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# A single open cover trivialising two finite locally free modules at once

Finite local freeness of a sheaf of modules is witnessed by a cover of the space together with a
finite basis over each member, and the cover depends on the module. A local argument about a
*pair* of modules — the Hom-sets of two finite locally free modules, say — needs one cover over
each member of which *both* are free. This file produces it, from the two individual covers and
the fact that freeness over an open persists over any smaller object of the site.

## Main definitions

* `CategoryTheory.SheafOfModules.overFreeOfHom`: **a module free over one object of the site is
  free over any object mapping to it**, in the slice spelling `M.over x`. Site-general and at an
  arbitrary sheaf of rings.

## Main results

* `Stacks.SheafOfModules.exists_common_cover_free`: **two finite locally free sheaves of modules
  on a topological space are both free over every member of a single open cover.**
* `Stacks.SheafOfModules.isBasis_commonFree`: **the members of a basis over which two finite
  locally free sheaves of modules are both free again form a basis.** This is the form in which a
  local argument can be run over a cover drawn from a *prescribed* basis — the basic opens of an
  affine scheme, say — rather than over the cover that finite local freeness happens to supply.

## Implementation notes

The restriction of freeness is Mathlib's `CategoryTheory.SheafOfModules.overFunctorMap`, which
identifies restricting to a smaller slice with restricting once, together with
`CategoryTheory.SheafOfModules.overMapFreeIso`, which says extension between slices carries free
sheaves of modules to free ones. Neither needs the sheaf of rings to be a structure sheaf, which
is why the statement is available here at an arbitrary `R` — the scheme-level analogue
`AlgebraicGeometry.Scheme.Modules.restrictFreeOfLE` is stated for `X.Modules` and in the
`restrict`-along-an-open-immersion spelling, which a statement about `colim_F 𝒪_X` cannot use.

The common cover is the family of pairwise intersections of the two covers, indexed by the
product of the two index sets; that it still covers is `iSup_inf_iSup`, the frame distributivity
of the lattice of opens. The index types of the bases are unchanged by the refinement, so
finiteness of the ranks is inherited with no further argument.

Passing from that cover to a basis costs nothing beyond the same persistence of freeness: a
basis neighbourhood of a point inside the intersection of a given open with a member of the
common cover is a basis element over which both modules are free, which is exactly the
neighbourhood criterion `TopologicalSpace.Opens.isBasis_iff_nbhd`. The resulting family is
closed downwards among the members of the basis, which is what makes it usable for a gluing
argument whose compatibility condition has to be checked on overlaps.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasPullbacks C] [∀ Y, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A module which is free over one object of the site is free over every object mapping to
it.**

The restriction along `f : x ⟶ y` of the slice restriction to `y` is the slice restriction to `x`
by Mathlib's `CategoryTheory.SheafOfModules.overFunctorMap`, and extension between slices carries
free sheaves of modules to free ones by
`CategoryTheory.SheafOfModules.overMapFreeIso`; the index type is unchanged.

This is the slice-spelling, arbitrary-sheaf-of-rings form of
`AlgebraicGeometry.Scheme.Modules.restrictFreeOfLE`. -/
noncomputable def overFreeOfHom (M : SheafOfModules.{u} R) {x y : C} (f : x ⟶ y) (I : Type u)
    (e : M.over y ≅ free I) :
    M.over x ≅ free (R := R.over x) I :=
  ((overFunctorMap R f).app M).symm ≪≫ (overMap R f).mapIso e ≪≫
    (overMapFreeIso R f I).symm

end SheafOfModules

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u})

/-- Freeness of `M.over y` passes to `M.over x` for opens `x ≤ y`. -/
private theorem nonempty_over_free_of_le (M : _root_.SheafOfModules.{u} R)
    {x y : Opens (X : TopCat)} (h : x ≤ y) {I : Type u}
    (e : Nonempty (M.over y ≅ _root_.SheafOfModules.free I)) :
    Nonempty (M.over x ≅ _root_.SheafOfModules.free I) :=
  ⟨_root_.SheafOfModules.overFreeOfHom R M (homOfLE h) I e.some⟩

/-- **Two finite locally free sheaves of modules are both free over every member of a single open
cover.**

Each is free over the members of its own cover; the pairwise intersections of the two covers still
cover the space, by the frame distributivity of the lattice of opens, and freeness persists on
passing to a smaller open by `CategoryTheory.SheafOfModules.overFreeOfHom`. The index types of the
two bases are the ones of the original covers, so their finiteness is inherited.

This is what a local argument about the Hom-set of a pair of finite locally free modules needs:
over each member of one cover, both modules are free, so a statement proved for free modules
applies there to both at once. -/
theorem exists_common_cover_free (M N : _root_.SheafOfModules.{u} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ (ι : Type u) (V : ι → Opens (X : TopCat)) (K L : ι → Type u), (⨆ i, V i = ⊤) ∧
      (∀ i, Finite (K i)) ∧ (∀ i, Finite (L i)) ∧
      (∀ i, Nonempty (M.over (V i) ≅ _root_.SheafOfModules.free (K i))) ∧
      (∀ i, Nonempty (N.over (V i) ≅ _root_.SheafOfModules.free (L i))) := by
  obtain ⟨q, hq, hqf⟩ := hM.exists_isFiniteLocallyFreeData
  obtain ⟨r, hr, hrf⟩ := hN.exists_isFiniteLocallyFreeData
  refine ⟨q.I × r.I, fun ij => q.X ij.1 ⊓ r.X ij.2,
    fun ij => (q.generators ij.1).I, fun ij => (r.generators ij.2).I, ?_,
    fun ij => (hqf.isFiniteType ij.1).finite, fun ij => (hrf.isFiniteType ij.2).finite,
    fun ij => ?_, fun ij => ?_⟩
  · rw [← iSup_inf_iSup, (Opens.coversTop_iff _ q.X).mp q.coversTop,
      (Opens.coversTop_iff _ r.X).mp r.coversTop, top_inf_eq]
  · have : IsIso (q.generators ij.1).π := hq.isIso ij.1
    exact nonempty_over_free_of_le R M inf_le_left ⟨(asIso (q.generators ij.1).π).symm⟩
  · have : IsIso (r.generators ij.2).π := hr.isIso ij.2
    exact nonempty_over_free_of_le R N inf_le_right ⟨(asIso (r.generators ij.2).π).symm⟩

/-- **The members of a basis over which two finite locally free sheaves of modules are both free
again form a basis.**

Given a prescribed basis `B` of the topology — the basic opens of an affine scheme, say — the
elements of `B` over which both `M` and `N` are free still form a basis: a point of an open `U`
lies in some member `V i` of the common trivialising cover
`Stacks.SheafOfModules.exists_common_cover_free`, a basis neighbourhood of it inside `U ⊓ V i`
lies below `V i`, and freeness persists downwards by
`CategoryTheory.SheafOfModules.overFreeOfHom`.

This is what a Zariski-local argument needs when the local statement is only available over the
members of a *particular* basis, so that the trivialising cover cannot simply be used as it
comes. -/
theorem isBasis_commonFree (M N : _root_.SheafOfModules.{u} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    (B : Set (Opens (X : TopCat))) (hB : Opens.IsBasis B) :
    Opens.IsBasis {V ∈ B |
      (∃ K : Type u, Finite K ∧ Nonempty (M.over V ≅ _root_.SheafOfModules.free K)) ∧
      (∃ L : Type u, Finite L ∧ Nonempty (N.over V ≅ _root_.SheafOfModules.free L))} := by
  obtain ⟨ι, V, K, L, hcov, hKfin, hLfin, hMfree, hNfree⟩ := exists_common_cover_free R M N hM hN
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov ▸ Opens.mem_top x : x ∈ ⨆ i, V i)
  obtain ⟨W, hWB, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp hB (show x ∈ U ⊓ V i from ⟨hx, hi⟩)
  have hWV := hWle.trans inf_le_right
  exact ⟨W, ⟨hWB, ⟨K i, hKfin i, nonempty_over_free_of_le R M hWV (hMfree i)⟩,
    ⟨L i, hLfin i, nonempty_over_free_of_le R N hWV (hNfree i)⟩⟩, hxW, hWle.trans inf_le_left⟩

/-- **Two finite locally free sheaves of modules are both free over every member of a cover drawn
from any prescribed basis of the topology.**

This is `Stacks.SheafOfModules.isBasis_commonFree` turned into a covering: the members of the
basis `β` over which both modules are free form a basis by that lemma, and a basis covers the
whole space, which is `TopologicalSpace.Opens.IsBasis.exists_iSup_eq` at `⊤`. The index of the
resulting cover is a family of indices *of the given basis*, so a statement available only over
the members of that basis — the basic opens of an affine scheme, say — applies over every member
of the cover.

The refinement does not shrink the ranks: the index types of the two bases are the ones of the
cover that finite local freeness supplies, so their finiteness is inherited. -/
theorem exists_cover_commonFree_of_isBasis (M N : _root_.SheafOfModules.{u} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N)
    {κ : Type*} (β : κ → Opens (X : TopCat)) (hβ : Opens.IsBasis (Set.range β)) :
    ∃ (σ : Type u) (a : σ → κ) (K L : σ → Type u), (⨆ s, β (a s)) = ⊤ ∧
      (∀ s, Finite (K s)) ∧ (∀ s, Finite (L s)) ∧
      (∀ s, Nonempty (M.over (β (a s)) ≅ _root_.SheafOfModules.free (K s))) ∧
      (∀ s, Nonempty (N.over (β (a s)) ≅ _root_.SheafOfModules.free (L s))) := by
  have hbas := isBasis_commonFree R M N hM hN _ hβ
  have hrange : {V ∈ Set.range β |
      (∃ K : Type u, Finite K ∧ Nonempty (M.over V ≅ _root_.SheafOfModules.free K)) ∧
      (∃ L : Type u, Finite L ∧ Nonempty (N.over V ≅ _root_.SheafOfModules.free L))} =
        Set.range fun k : {k : κ //
            (∃ K : Type u, Finite K ∧ Nonempty
              (M.over (β k) ≅ _root_.SheafOfModules.free K)) ∧
            (∃ L : Type u, Finite L ∧ Nonempty
              (N.over (β k) ≅ _root_.SheafOfModules.free L))} => β k.1 := by
    ext V
    constructor
    · rintro ⟨⟨k, rfl⟩, hP⟩
      exact ⟨⟨k, hP⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, rfl⟩, hk⟩
  rw [hrange] at hbas
  obtain ⟨σ, a, heq⟩ := hbas.exists_iSup_eq ⊤
  choose K hKfin hMfree using fun s : σ => (a s).2.1
  choose L hLfin hNfree using fun s : σ => (a s).2.2
  exact ⟨σ, fun s => (a s).1, K, L, heq.symm, hKfin, hLfin, hMfree, hNfree⟩

end Stacks.SheafOfModules

end
