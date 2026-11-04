module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSeparation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Making the generic-fibre rank constant by an admissible blowup

Let `g : X ⟶ S` be flat, of finite presentation, with geometrically integral fibres, let `F` be a
finitely presented `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open over which `F` is flat
at the generic point of every fibre. Then

* `U` is the disjoint union of finitely many quasi-compact opens `U_0, …, U_c` on each of which
  the generic-fibre rank `r(t) = dim_{κ(ξ_t)}(ℱ_{ξ_t} ⊗ κ(ξ_t))` is constant, and
* there is a `U`-admissible blowup of `S` whose source is the disjoint union of opens
  `S_0, …, S_c` with the inverse image of `U_i` inside `S_i`.

This is the first reduction in the proof of [Stacks, Tag 0811]: "thus we may assume `r` is
constant". It is the composite of the local constancy of `r`
(`AlgebraicGeometry.exists_opens_forall_fiberRank_eq_of_isFlatOverAt_fibre_dense`) with
quasi-compactness of `U` and with [Stacks, Tag 080P] for a finite family
(`Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover`).

## Main results

* `AlgebraicGeometry.exists_finite_opens_constant_fiberRank`: the decomposition
  `U = U_0 ⊔ … ⊔ U_c` by the value of `r`.
* `AlgebraicGeometry.exists_admissibleBlowup_constant_fiberRank`: that decomposition separated by
  a single `U`-admissible blowup.

## Implementation notes

The decomposition is indexed by the set of values `r` takes on the chosen finite cover rather
than by `Fin (c + 1)`; the two differ only by a reindexing, and the value is carried as the
function `n` of the statement, so each piece *names* the rank on it.

`r` itself is not introduced as a function `S → ℕ`: a generic point of a fibre is not canonical,
and the statement is instead that every point of `X` lying over `U_i` which is a generic point of
its fibre — in the topological form `g⁻¹(g b) ⊆ closure {b}` used throughout — has
`AlgebraicGeometry.Scheme.Modules.fiberRank` equal to `n i`. Since every fibre of `g` does have
such a point (`AlgebraicGeometry.exists_fibre_dense_preimage`, from geometric integrality), this
pins the value down and is what makes the pieces pairwise disjoint.

Each piece has to be quasi-compact for [Stacks, Tag 080P] to apply, so the neighbourhood on which
`r` is constant is shrunk to an affine open before being intersected with `U`: an affine open and
a quasi-compact open of a quasi-separated space meet in a quasi-compact open
(`IsCompact.inter_of_isOpen`), and a finite union of quasi-compact opens is quasi-compact.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The decomposition of the base by the generic-fibre rank.** Let `g : X ⟶ S` be flat, of
finite presentation, with geometrically integral fibres, let `F` be a finitely presented
`𝒪_X`-module and let `U ⊆ S` be a quasi-compact open over which `F` is flat over `S` at the
generic point of every fibre. Then `U` is the supremum of a finite family of pairwise disjoint
quasi-compact opens `V i`, each carrying a rank `n i` such that every generic point of a fibre
over `V i` has fibre rank `n i`.

This is the sentence "we see that `r` is locally constant, i.e. we obtain a decomposition
`U = U_0 ⨿ … ⨿ U_c`" of the proof of [Stacks, Tag 0811]. Local constancy is
`AlgebraicGeometry.exists_opens_forall_fiberRank_eq_of_isFlatOverAt_fibre_dense`; the finiteness
is quasi-compactness of `U`, and the pieces are the unions of the members of a finite subcover
on which the rank takes a given value. -/
@[ega "III 7.3.4" "special case"]
theorem exists_finite_opens_constant_fiberRank {X S : Scheme.{u}} [QuasiSeparatedSpace S]
    (g : X ⟶ S) (hg : AlgebraicGeometry.FinitePresentation g) [Flat g]
    [GeometricallyIntegral g] (F : X.Modules) [F.IsFinitePresentation] (U : S.Opens)
    (hU : IsCompact (U : Set S))
    (hflat : ∀ b : X, g.base b ∈ U → g.base ⁻¹' {g.base b} ⊆ closure {b} →
      IsFlatOverAt g.toLRSHom.toShHom F b) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → S.Opens) (n : ι → ℕ),
      (Pairwise fun i j => Disjoint (V i) (V j)) ∧ (⨆ i, V i) = U ∧
        (∀ i, IsCompact (V i : Set S)) ∧
          ∀ i, ∀ b : X, g.base b ∈ V i → g.base ⁻¹' {g.base b} ⊆ closure {b} →
            F.fiberRank b = n i := by
  classical
  -- A generic point of the fibre over every point of `S`.
  choose ξ hξ hξcl using fun t : S => exists_fibre_dense_preimage g t
  have hξcl' : ∀ t : S, g.base ⁻¹' {g.base (ξ t)} ⊆ closure {ξ t} := fun t => by
    rw [hξ t]; exact hξcl t
  -- An affine open on which the generic-fibre rank is the one at `ξ t`, for `t ∈ U`.
  have hstep : ∀ t : (U : Set S), ∃ A : S.Opens, IsAffineOpen A ∧ (t : S) ∈ A ∧
      ∀ b : X, g.base b ∈ A → g.base ⁻¹' {g.base b} ⊆ closure {b} →
        F.fiberRank b = F.fiberRank (ξ t) := by
    intro t
    have hcl := hξcl' (t : S)
    have hmemU : g.base (ξ (t : S)) ∈ U := by rw [hξ (t : S)]; exact t.2
    obtain ⟨W, hWmem, hWprop⟩ :=
      exists_opens_forall_fiberRank_eq_of_isFlatOverAt_fibre_dense g hg F (ξ (t : S)) hcl
        (hflat (ξ (t : S)) hmemU hcl)
    obtain ⟨A, hAaff, hAmem, hAW⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (t : S)) (U := W) (by rw [← hξ (t : S)]; exact hWmem)
    exact ⟨A, hAaff, hAmem, fun b hb hbcl => hWprop b hbcl (hAW hb)⟩
  choose A hAaff hAmem hAprop using hstep
  -- A finite subcover of `U`.
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun t : (U : Set S) => (A t : Set S))
    (fun t => (A t).2) fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hAmem ⟨t, ht⟩⟩
  -- The pieces, indexed by the values the rank takes on that subcover.
  set m : ↥(U : Set S) → ℕ := fun t => F.fiberRank (ξ (t : S))
  set N : Finset ℕ := s.image m
  -- The rank on a piece is the value indexing it.
  have hrank : ∀ (v : ℕ) (b : X),
      g.base b ∈ (⨆ t ∈ s.filter fun t => m t = v, U ⊓ A t : S.Opens) →
        g.base ⁻¹' {g.base b} ⊆ closure {b} → F.fiberRank b = v := by
    intro v b hb hbcl
    obtain ⟨t', ht'⟩ := Opens.mem_iSup.mp hb
    obtain ⟨ht'mem, ht'⟩ := Opens.mem_iSup.mp ht'
    exact (hAprop t' b ht'.2 hbcl).trans (Finset.mem_filter.mp ht'mem).2
  refine ⟨{v : ℕ // v ∈ N}, inferInstance,
    fun v => ⨆ t ∈ s.filter fun t => m t = (v : ℕ), U ⊓ A t, fun v => (v : ℕ), ?_, ?_, ?_, ?_⟩
  · -- Two pieces with different ranks are disjoint: a common point has a generic point above it.
    intro v w hvw
    refine Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun t htv htw => ?_)
    exact hvw (Subtype.ext <|
      (hrank _ (ξ t) (by rw [hξ t]; exact htv) (hξcl' t)).symm.trans
        (hrank _ (ξ t) (by rw [hξ t]; exact htw) (hξcl' t)))
  · -- The pieces cover `U`, and each is inside `U`.
    refine le_antisymm (iSup_le fun v => iSup_le fun t => iSup_le fun _ => inf_le_left)
      fun t ht => ?_
    obtain ⟨t', ht'mem, ht'⟩ := Set.mem_iUnion₂.mp (hs ht)
    refine Opens.mem_iSup.mpr ⟨⟨m t', Finset.mem_image.mpr ⟨t', ht'mem, rfl⟩⟩, ?_⟩
    exact Opens.mem_iSup.mpr ⟨t', Opens.mem_iSup.mpr ⟨Finset.mem_filter.mpr ⟨ht'mem, rfl⟩,
      ⟨ht, ht'⟩⟩⟩
  · -- Each piece is a finite union of quasi-compact opens.
    intro v
    rw [show ((⨆ t ∈ s.filter fun t => m t = (v : ℕ), U ⊓ A t : S.Opens) : Set S) =
        ⋃ t ∈ (s.filter fun t => m t = (v : ℕ) : Finset (U : Set S)), ((U ⊓ A t : S.Opens) : Set S)
      from by simp]
    refine (Finset.finite_toSet _).isCompact_biUnion fun t _ => ?_
    rw [Opens.coe_inf]
    exact hU.inter_of_isOpen (hAaff t).isCompact U.2 (A t).2
  · exact fun v b hb hbcl => hrank v b hb hbcl

/-- **The generic-fibre rank may be assumed constant after a `U`-admissible blowup.** In the
situation of `AlgebraicGeometry.exists_finite_opens_constant_fiberRank` there is a
`U`-admissible blowup `b : S' ⟶ S` whose source is the disjoint union of opens `W i` with the
inverse image of the `i`-th piece `V i` of `U` contained in `W i`, so that on each `W i` the
generic-fibre rank of the family restricted over it is the single value `n i`.

This is the step "using Divisors, Lemma 31.35.5 repeatedly we may assume `r` is constant" of the
proof of [Stacks, Tag 0811]: the decomposition of `U` by the value of `r` is separated by one
blowup through `Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover`, the finite
family form of [Stacks, Tag 080P]. -/
theorem exists_admissibleBlowup_constant_fiberRank {X S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (g : X ⟶ S) (hg : AlgebraicGeometry.FinitePresentation g) [Flat g]
    [GeometricallyIntegral g] (F : X.Modules) [F.IsFinitePresentation] (U : S.Opens)
    (hU : IsCompact (U : Set S))
    (hflat : ∀ b : X, g.base b ∈ U → g.base ⁻¹' {g.base b} ⊆ closure {b} →
      IsFlatOverAt g.toLRSHom.toShHom F b) :
    ∃ (ι : Type) (_ : Finite ι) (V : ι → S.Opens) (n : ι → ℕ),
      (⨆ i, V i) = U ∧
        (∀ i, ∀ b : X, g.base b ∈ V i → g.base ⁻¹' {g.base b} ⊆ closure {b} →
          F.fiberRank b = n i) ∧
          ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (W : ι → S'.Opens),
            Stacks.Blowup.IsAdmissibleBlowup U p ∧
              (Pairwise fun i j => Disjoint (W i) (W j)) ∧ (⨆ i, W i) = ⊤ ∧
                ∀ i, p ⁻¹ᵁ V i ≤ W i := by
  obtain ⟨ι, hιfin, V, n, hdisj, hsup, hcomp, hrank⟩ :=
    exists_finite_opens_constant_fiberRank g hg F U hU hflat
  obtain ⟨S', p, W, hadm, hWdisj, hWsup, hWle⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover S V hcomp hdisj
  exact ⟨ι, hιfin, V, n, hsup, hrank, S', p, W, hsup ▸ hadm, hWdisj, hWsup, hWle⟩

end AlgebraicGeometry

end
