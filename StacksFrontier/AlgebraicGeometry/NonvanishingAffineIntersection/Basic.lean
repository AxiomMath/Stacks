module

public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# An affine open meets a nonvanishing locus in an affine open

Let `X` be a scheme, `M` an invertible `𝒪_X`-module and `s ∈ Γ(X, M)` a global section. For every
affine open `U ⊆ X` the intersection `U ∩ X_s` is affine, where `X_s` is the nonvanishing locus
of `s`.

## Main definitions

* `Stacks.NonvanishingAffineIntersection.cutters`: the sections `g` over `U` such that
  `X.basicOpen g ∩ X_s` is affine.

## Main results

* `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`: for an affine open
  `U`, the intersection `U ∩ X_s` is affine.
* `Stacks.NonvanishingAffineIntersection.isAffineOpen_basicOpen_inf`: on an open trivializing
  `M`, `X_s` meets a basic open of an affine open in an affine open.
* `Stacks.NonvanishingAffineIntersection.span_cutters_eq_top`: the cutters of an affine open `U`
  span the unit ideal of `Γ(X, U)`.
* `Stacks.NonvanishingAffineIntersection.isCompact_nonvanishingLocus`: on a quasi-compact scheme,
  `X_s` is quasi-compact.

## Implementation notes

The source's proof is algebraic: for a ring `R`, an invertible module `N` and `s ∈ N`, it forms
the symmetric algebra `A = ⨁_{n ≥ 0} Sym^n_R(N)` and identifies `Spec(A/(s - 1)A)` with
`{𝔭 ∣ s ∉ 𝔭N}`. Here instead affineness is checked locally on `U ∩ X_s` by
`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`. On an open `V` carrying a
trivialization of `M`, the locus `X_s` is the basic open of the trivializing function of `s`, so
`X.basicOpen g ∩ X_s` is affine whenever `X.basicOpen g ≤ V`. Such `g` cover `U`, hence span the
unit ideal of `Γ(X, U)`, and their restrictions to `U ∩ X_s` have affine basic opens spanning the
unit ideal of `Γ(X, U ∩ X_s)`.

The statement is for an arbitrary invertible `M`, so it applies to every tensor power of a line
bundle.

## References

* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.NonvanishingAffineIntersection

variable {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤))

/-! ### The local step -/

/-- **On a trivializing open, `X_s` cuts an affine open out of a basic open of an affine open.**
If `g` is a section of the structure sheaf over an affine open `U` whose basic open lies inside an
open `V` carrying a sectionwise trivialization of `M`, then `X.basicOpen g ∩ X_s` is affine: it is
the basic open, inside the affine open `X.basicOpen g`, of the trivializing function of `s`. -/
theorem isAffineOpen_basicOpen_inf {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U))
    {V : X.Opens} (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V)
    (hgV : X.basicOpen g ≤ V) :
    IsAffineOpen (X.basicOpen g ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s) := by
  have key : X.basicOpen g ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s =
      X.basicOpen (Stacks.NonvanishingOpen.trivTop (t.comp (homOfLE hgV)) s) := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      Set.inter_comm]
    exact Stacks.NonvanishingOpen.nonvanishingLocus_inter (t.comp (homOfLE hgV)) s
  rw [key]
  exact (hU.basicOpen g).basicOpen _

/-! ### The covering step -/

/-- **The cutters of an affine open**: the sections `g` of the structure sheaf over `U` whose basic
open meets the nonvanishing locus of `s` in an affine open. -/
def cutters (U : X.Opens) : Set Γ(X, U) :=
  {g | IsAffineOpen (X.basicOpen g ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s)}

/-- A section `g` over `U` is a cutter if and only if `X.basicOpen g ∩ X_s` is affine. -/
theorem mem_cutters_iff {U : X.Opens} {g : Γ(X, U)} :
    g ∈ cutters M s U ↔
      IsAffineOpen (X.basicOpen g ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s) :=
  Iff.rfl

/-- **The basic opens of the cutters cover the affine open.** Every point of `U` has a
trivializing neighbourhood, and the basic opens of `U` are a basis of `U`, so some basic open of
`U` containing the point lies inside a trivializing open and is therefore a cutter. -/
theorem self_le_iSup_basicOpen_cutters {U : X.Opens} (hU : IsAffineOpen U) :
    U ≤ ⨆ g : cutters M s U, X.basicOpen g.1 := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  intro x hx
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨t⟩ := htriv z
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V z) ⟨x, hz⟩ hx
  exact Opens.mem_iSup.mpr ⟨⟨g, isAffineOpen_basicOpen_inf M s hU g t hgV⟩, hxg⟩

/-- **The cutters span the unit ideal of `Γ(X, U)`.** This is the covering statement of
`self_le_iSup_basicOpen_cutters` read through
`AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`, and it is the only place affineness
of `U` is used for anything other than affineness of its basic opens. -/
theorem span_cutters_eq_top {U : X.Opens} (hU : IsAffineOpen U) :
    Ideal.span (cutters M s U) = ⊤ :=
  hU.self_le_iSup_basicOpen_iff.mp (self_le_iSup_basicOpen_cutters M s hU)

/-! ### Stacks Tag 01PV -/

/-- Let `X` be a scheme, `M` an invertible `𝒪_X`-module and `s` a global section of `M`. For every
affine open `U` of `X`, the intersection `U ∩ X_s` of `U` with the nonvanishing locus of `s` is
affine. -/
@[stacks 01PV,
  stacks 01SF "affineness of the inclusion j : X_s -> X, i.e. preimages of affine opens under j",
  ega "II 5.5.8", sga "6 II 2.2.3.1"]
theorem isAffineOpen_inf_nonvanishingOpen {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (U ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s) := by
  set W : X.Opens := U ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s with hW
  have hWU : W ≤ U := hW ▸ inf_le_left
  set ρ : Γ(X, U) →+* Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom with hρ
  refine AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen W (ρ '' cutters M s U) ?_ ?_
  · rw [← Ideal.map_span, span_cutters_eq_top M s hU, Ideal.map_top]
  · rintro _ ⟨g, hg, rfl⟩
    have hres : X.basicOpen (ρ g) = W ⊓ X.basicOpen g :=
      X.basicOpen_res (f := g) (homOfLE hWU).op
    have hBU : X.basicOpen g ≤ U := X.basicOpen_le g
    have hinf : W ⊓ X.basicOpen g =
        X.basicOpen g ⊓ Stacks.NonvanishingOpen.nonvanishingOpen X M s := by
      rw [hW]
      exact le_antisymm (le_inf inf_le_right (inf_le_left.trans inf_le_right))
        (le_inf (le_inf (inf_le_left.trans hBU) inf_le_right) inf_le_left)
    rw [hres, hinf]
    exact hg

/-! ### Quasi-compactness of the nonvanishing locus -/

/-- **On a quasi-compact scheme the nonvanishing locus of a global section of an invertible module
is quasi-compact.** -/
theorem isCompact_nonvanishingLocus [CompactSpace X] :
    IsCompact (Stacks.Ample.nonvanishingLocus M s) := by
  have hsub : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => (V.1 : Set X)) (fun V => V.1.2) hsub
  have hEq : Stacks.Ample.nonvanishingLocus M s =
      ⋃ V ∈ F, ((V.1 : Set X) ∩ Stacks.Ample.nonvanishingLocus M s) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun V _ => ?_)
    · obtain ⟨V, hVF, hxV⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
      exact Set.mem_biUnion hVF ⟨hxV, hx⟩
    · exact Set.inter_subset_right
  rw [hEq]
  refine F.finite_toSet.isCompact_biUnion fun V _ => ?_
  have h := (isAffineOpen_inf_nonvanishingOpen M s V.2).isCompact
  rwa [TopologicalSpace.Opens.coe_inf, Stacks.NonvanishingOpen.coe_nonvanishingOpen] at h

/-- `isCompact_nonvanishingLocus` for the bundled open set. -/
theorem isCompact_nonvanishingOpen [CompactSpace X] :
    IsCompact ((Stacks.NonvanishingOpen.nonvanishingOpen X M s : X.Opens) : Set X) :=
  isCompact_nonvanishingLocus M s

end Stacks.NonvanishingAffineIntersection

end
