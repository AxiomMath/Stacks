module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ConstructingInvariantOpens
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteSetInBasicOpen

/-!
# Invariant affine opens of a finite flat groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme whose source and target maps are finite locally free,
and let `u` be a point of `U` whose equivalence class `t(s⁻¹({u}))` lies in an affine open of
`U`. Then `u` has an `R`-invariant affine open neighbourhood.

This is the construction that makes a finite flat groupoid locally affine in the invariant
topology, and hence the entry point of the affine quotient theory of Tag 03BH.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem` is the statement
  above.
* `AlgebraicGeometry.GroupoidScheme.exists_isAffineOpen_source_preimage_eq_target_preimage_mem`
  restates it with invariance written as the equality `s⁻¹(V) = t⁻¹(V)` of the source's
  definition of an invariant open, rather than as `Stacks.Groupoids.IsInvariantOpen`.

## Implementation notes

The invariant open produced is the nonvanishing locus of a *norm*. Writing `W` for the given
affine open containing the class of `u`, the proof is the source's:

* the saturation `t(s⁻¹(Wᶜ))` of the complement of `W` is closed, because `t` is finite and
  hence a closed map, and it is invariant, so its complement `W'` is an invariant open; `W'` is
  contained in `W` and still contains the class of `u`;
* a section `f` over `W` with `t(s⁻¹({u})) ⊆ D(f) ⊆ W'` exists by the relative prime avoidance
  `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_subset_of_finite`, the class of `u` being
  finite because the fibres of a finite morphism are;
* `D(f)` is affine and `s⁻¹(D(f))` is affine because `s` is an affine morphism, so
  `Γ(R, s⁻¹D(f))` is a finite projective `Γ(U, D(f))`-module by
  `AlgebraicGeometry.finite_projective_app_of_isFiniteLocallyFree`, and the norm of the pullback
  `t♯f` along `s` is a section `g` over `D(f)`;
* `AlgebraicGeometry.mem_basicOpen_projectiveNorm_iff` identifies `D(g)` with the set of points
  `w` at which `f` is nonvanishing at *every* point of `R` with source `w`. That description is
  invariant, because the set of targets of the arrows with a given source depends only on the
  equivalence class of that source, and it contains `u`, because `f` is nonvanishing on the whole
  class of `u`. Finally `D(g)` is affine, being a basic open of the affine `D(f)`.

Only `t` being finite is used, not its local freeness; the hypothesis is kept as the source
states it.

Invariance of an open is `Stacks.Groupoids.IsInvariantOpen`, the repository's form of Tag 03BC
part (2): every arrow starting in the open ends in it. For a groupoid this single implication is
equivalent to the equality `s⁻¹(V) = t⁻¹(V)` of the source's definition, which
`AlgebraicGeometry.GroupoidScheme.source_preimage_eq_target_preimage` supplies and which the
second result above records explicitly.

The hypothesis of the source — "`t(s⁻¹({u}))` is contained in an affine open of `U`" — is taken
in its existential form, so the statement is the source's without a chosen witness.

## References

* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-! ### The saturation of a subset, read through the equivalence relation -/

/-- A point lies in the saturation `t(s⁻¹(A))` of a subset `A` exactly when it is related to a
point of `A` by the equivalence relation that `s` and `t` induce. -/
private theorem mem_target_image_source_preimage_iff (A : Set G.objects.left)
    (x : G.objects.left) :
    x ∈ G.target.left.base '' (G.source.left.base ⁻¹' A) ↔
      ∃ y ∈ A, Function.SourceTargetRel G.source.left.base G.target.left.base x y := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨G.source.left.base r, hr, r, rfl, rfl⟩
  · rintro ⟨y, hy, r, hrt, hrs⟩
    exact ⟨r, by rw [Set.mem_preimage, hrs]; exact hy, hrt⟩

/-- If the whole equivalence class of `u` lies in `W`, then no point of that class is related to
a point outside `W`: that is, the class avoids the saturation of the complement of `W`. -/
private theorem notMem_saturation_compl_of_subset {W : Set G.objects.left}
    (u : G.objects.left)
    (hTW : G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ W)
    {x : G.objects.left}
    (hx : x ∈ G.target.left.base '' (G.source.left.base ⁻¹' {u})) :
    x ∉ G.target.left.base '' (G.source.left.base ⁻¹' Wᶜ) := by
  rw [mem_target_image_source_preimage_iff] at hx
  obtain ⟨y, hy, hrel⟩ := hx
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [mem_target_image_source_preimage_iff]
  rintro ⟨z, hz, hrel2⟩
  refine hz (hTW ?_)
  rw [mem_target_image_source_preimage_iff]
  exact ⟨y, rfl, (equivalence_sourceTargetRel G).symm
    ((equivalence_sourceTargetRel G).trans ((equivalence_sourceTargetRel G).symm hrel) hrel2)⟩

/-- An arrow whose source avoids the saturation of the complement of `W` has its target in `W`:
otherwise the inverse arrow would put the source into that saturation. -/
private theorem target_mem_of_source_notMem_saturation_compl {W : Set G.objects.left}
    {r : G.arrows.left}
    (hr : G.source.left.base r ∉ G.target.left.base '' (G.source.left.base ⁻¹' Wᶜ)) :
    G.target.left.base r ∈ W := by
  by_contra hc
  refine hr ?_
  have h2 : r ∈ G.source.left.base ⁻¹'
      (G.target.left.base '' (G.source.left.base ⁻¹' Wᶜ)) := by
    rw [source_preimage_eq_target_preimage G
      (isInvariantSet_target_image_source_preimage G Wᶜ)]
    exact subset_target_image_source_preimage G Wᶜ hc
  exact h2

/-- A subset cut out by a condition on the targets of all the arrows with a given source is
invariant: the arrows with source `t(r)` have the same targets as the arrows with source `s(r)`,
because `s(r)` and `t(r)` are equivalent. -/
private theorem isInvariantSet_of_forall_target_mem {B E : Set G.objects.left}
    (hE : ∀ w, w ∈ E ↔ ∀ r, G.source.left.base r = w → G.target.left.base r ∈ B) :
    IsInvariantSet G E := by
  intro r hr
  rw [hE] at hr ⊢
  intro r' hr'
  obtain ⟨r'', hr''t, hr''s⟩ :=
    (equivalence_sourceTargetRel G).trans
      (show Function.SourceTargetRel G.source.left.base G.target.left.base
          (G.target.left.base r') (G.target.left.base r) from ⟨r', rfl, hr'⟩)
      (sourceTargetRel_target_source G r)
  rw [← hr''t]
  exact hr _ hr''s

/-! ### The invariant affine open -/

/-- **Stacks Project, Tag 03JE.** Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t`
finite locally free, and let `u` be a point of `U` whose equivalence class `t(s⁻¹({u}))` is
contained in an affine open of `U`. Then `u` has an `R`-invariant affine open neighbourhood in
`U`.

The neighbourhood is the nonvanishing locus of the norm along `s` of the pullback along `t` of a
function cutting the class of `u` out of an invariant open inside the given affine open; see the
implementation notes. -/
@[stacks 03JE, sga "1 V 1.8" "orbit⊂affine⇒inv affine"]
theorem exists_isInvariantOpen_isAffineOpen_mem
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (u : G.objects.left)
    (hu : ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
      G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    ∃ V : G.objects.left.Opens, IsInvariantOpen G V ∧ IsAffineOpen V ∧ u ∈ V := by
  obtain ⟨W, hWaff, hTW⟩ := hu
  have hs : IsFinite G.source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp inferInstance).1
  have ht : IsFinite G.target.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp inferInstance).1
  have hTfin : (G.target.left.base '' (G.source.left.base ⁻¹' {u})).Finite :=
    (G.source.left.finite_preimage_singleton u).image _
  have hsatClosed : IsClosed (G.target.left.base ''
      (G.source.left.base ⁻¹' (W : Set G.objects.left)ᶜ)) :=
    G.target.left.isClosedMap _ (W.2.isClosed_compl.preimage G.source.left.continuous)
  have hTW' : G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆
      (G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left)ᶜ))ᶜ :=
    fun x hx => notMem_saturation_compl_of_subset G u hTW hx
  obtain ⟨f, hfT, hfW'⟩ := hWaff.exists_basicOpen_subset_of_finite hTfin
    (fun x hx => hTW hx) ⟨_, hsatClosed.isOpen_compl⟩ hTW'
  have hPaff : IsAffineOpen (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    IsAffineHom.isAffine_preimage _ (hWaff.basicOpen f)
  have hle : G.source.left ⁻¹ᵁ G.objects.left.basicOpen f ≤ G.target.left ⁻¹ᵁ W := by
    intro r hr
    exact target_mem_of_source_notMem_saturation_compl G (hfW' hr)
  obtain ⟨hfin, hproj⟩ :=
    finite_projective_app_of_isFiniteLocallyFree G.source.left (hWaff.basicOpen f)
  let a : Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    G.target.left.appLE W (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) hle f
  have hbo : G.arrows.left.basicOpen a =
      (G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) ⊓
        G.target.left ⁻¹ᵁ G.objects.left.basicOpen f :=
    Scheme.basicOpen_appLE _ _ _ hle f
  let : Algebra Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) :=
    (G.source.left.app (G.objects.left.basicOpen f)).hom.toAlgebra
  let : Module.Finite Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) := hfin
  let : Module.Projective Γ(G.objects.left, G.objects.left.basicOpen f)
      Γ(G.arrows.left, G.source.left ⁻¹ᵁ G.objects.left.basicOpen f) := hproj
  have hiff : ∀ v : G.objects.left, v ∈ G.objects.left.basicOpen f →
      (v ∈ G.objects.left.basicOpen
          (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a) ↔
        ∀ p : G.arrows.left, G.source.left.base p = v → p ∈ G.arrows.left.basicOpen a) :=
    fun v hv => mem_basicOpen_projectiveNorm_iff G.source.left (hWaff.basicOpen f) hPaff
      hfin hproj a hv
  have hkey : ∀ w : G.objects.left,
      w ∈ G.objects.left.basicOpen
          (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a) ↔
        ∀ r : G.arrows.left, G.source.left.base r = w →
          G.target.left.base r ∈ G.objects.left.basicOpen f := by
    intro w
    constructor
    · intro hw r hr
      have hwf : w ∈ G.objects.left.basicOpen f := G.objects.left.basicOpen_le _ hw
      have hmem := (hiff w hwf).mp hw r hr
      rw [hbo] at hmem
      exact hmem.2
    · intro hall
      obtain ⟨r₀, hr₀s, hr₀t⟩ := subset_target_image_source_preimage G {w} rfl
      have hwf : w ∈ G.objects.left.basicOpen f := hr₀t ▸ hall r₀ hr₀s
      refine (hiff w hwf).mpr fun p hp => ?_
      rw [hbo]
      exact ⟨show G.source.left.base p ∈ G.objects.left.basicOpen f from hp ▸ hwf, hall p hp⟩
  refine ⟨G.objects.left.basicOpen
      (Algebra.projectiveNorm Γ(G.objects.left, G.objects.left.basicOpen f) a),
    isInvariantSet_of_forall_target_mem G hkey, (hWaff.basicOpen f).basicOpen _, ?_⟩
  exact (hkey u).mpr fun r hr => hfT ⟨r, hr, rfl⟩

/-- Tag 03JE with invariance written as the source writes it: the invariant affine open
neighbourhood `V` of `u` satisfies `s⁻¹(V) = t⁻¹(V)`. -/
theorem exists_isAffineOpen_source_preimage_eq_target_preimage_mem
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (u : G.objects.left)
    (hu : ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
      G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    ∃ V : G.objects.left.Opens,
      G.source.left.base ⁻¹' (V : Set G.objects.left) =
        G.target.left.base ⁻¹' (V : Set G.objects.left) ∧
      IsAffineOpen V ∧ u ∈ V := by
  obtain ⟨V, hVinv, hVaff, hVu⟩ := exists_isInvariantOpen_isAffineOpen_mem G u hu
  exact ⟨V, source_preimage_eq_target_preimage G hVinv, hVaff, hVu⟩

end AlgebraicGeometry.GroupoidScheme

end
