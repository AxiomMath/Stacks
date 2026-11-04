module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FiniteLocallyFreeNeighbourhoods
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local constancy of the generic-fibre rank

Let `g : X ⟶ S` be flat, of finite presentation, with geometrically integral fibres, and let `F`
be a finitely presented `𝒪_X`-module which is flat over `S` at the generic point `ξ_t` of the
fibre over every `t` in some open of `S`. Then the function

`t ↦ dim_{κ(ξ_t)} (ℱ_{ξ_t} ⊗ κ(ξ_t))`

is locally constant on that open.

This is the step of [Stacks, Tag 0811] which produces the decomposition `U = U_0 ⊔ … ⊔ U_c` of
the distinguished open into the finitely many loci of a fixed generic-fibre rank, separated by a
single blowup through
`Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover`. The source obtains it from
More on Morphisms, Lemma 37.16.7 ([Stacks, Tag 080Q]) together with openness of the image.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_iso_free_over`: on an open over which a
  module is free of rank `n`, its fibre rank is `n` at every point.
* `AlgebraicGeometry.exists_opens_forall_fiberRank_eq_of_isFlatOverAt_fibre_dense`: the local
  constancy above, in the pointwise form "there is an open `V ∋ g(b)` of `S` such that every
  point which is a generic point of its fibre and lies over `V` has the same fibre rank as `b`".

## Implementation notes

"Generic point of the fibre" is written, as in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/BlowupIntegralFibresFlattening.lean`, in the
purely topological form `g⁻¹(g b) ⊆ closure {b}`. That form is what makes the proof short: the
open `V` is the image of the free neighbourhood `W` of `b` given by [Stacks, Tag 080Q], and a
generic point `b'` of a fibre meeting `W` *lies in* `W`, because some `w ∈ W` has
`g(w) = g(b')`, hence `w ∈ closure {b'}`, and an open set containing a point of `closure {b'}`
contains `b'`. No irreducibility of the fibre is needed for that step, only the hypothesis on
`b'`.

The rank function is `AlgebraicGeometry.Scheme.Modules.fiberRank`, which is by definition
`Module.finrank κ(x) (κ(x) ⊗_{𝒪_x} ℱ_x)` — the source's `r`. Reading it off a free
restriction goes through `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of the
restriction to the slice site, which
`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank_over` consumes: a
single free restriction is the local generators data of the one-member cover of the open by
itself, presented as `AlgebraicGeometry.SheafOfModules.iSupGenerators` over a one-point index
type.

Openness of the image is `AlgebraicGeometry.isOpenMap_of_generalizingMap` ([Stacks, Tag 01U1])
applied to `AlgebraicGeometry.Flat.generalizingMap`; that is Stacks tag 01UA, which is the
"openness of the image" the source's proof cites.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A module free of finite rank on an open has that rank as its fibre rank there.** The single
free restriction is local generators data for the one-member cover of the open by itself, so the
module is finite locally free of rank `n` on the slice site over the open, and
`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank_over` evaluates the
fibre rank. -/
theorem fiberRank_eq_of_iso_free_over {X : Scheme.{u}} (F : X.Modules) (W : X.Opens) (n : ℕ)
    (e : F.over W ≅ SheafOfModules.free (ULift.{u} (Fin n))) {x : X} (hx : x ∈ W) :
    F.fiberRank x = n := by
  have hconst : (⨆ _ : PUnit.{u + 1}, W) = W := iSup_const
  have hinst : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (F.over (⨆ _ : PUnit.{u + 1}, W)) n := by
    refine ⟨AlgebraicGeometry.SheafOfModules.iSupGenerators F (fun _ => W) (fun _ => n)
      (fun _ => e), ⟨fun _ => ?_⟩, fun _ => ⟨Equiv.ulift⟩⟩
    exact AlgebraicGeometry.SheafOfModules.isIso_ofEpi_free_generatingSections_π _ _
  rw [hconst] at hinst
  exact fiberRank_eq_of_isFiniteLocallyFreeOfRank_over F W n hx

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **Local constancy of the generic-fibre rank.** Let `g : X ⟶ S` be flat, of finite
presentation, with geometrically integral fibres, let `F` be a finitely presented
`𝒪_X`-module, and let `b` be a point whose closure contains its whole fibre — the generic point
of that fibre — at which `F` is flat over `S`. Then there is an open `V ⊆ S` containing `g(b)`
such that every point `b'` whose closure contains its whole fibre and which lies over `V` has
the same fibre rank as `b`.

Since `dim_{κ(ξ_t)}(ℱ_{ξ_t} ⊗ κ(ξ_t))` is `AlgebraicGeometry.Scheme.Modules.fiberRank` at the
generic point `ξ_t` of the fibre over `t`, this says exactly that the source's function `r` is
locally constant wherever its hypotheses hold. It is what gives [Stacks, Tag 0811] the finite
decomposition `U = U_0 ⊔ … ⊔ U_c` of the distinguished open by the value of `r`.

[Stacks, Tag 080Q] produces an open `W ∋ b` on which `F` is free of some finite rank `n`, using
that the local ring of the fibre at its generic point is a field. Its image `V = g(W)` is open
because `g` is flat and locally of finite presentation. If `b'` is a generic point of its fibre
and `g(b') ∈ V`, say `g(w) = g(b')` with `w ∈ W`, then `w ∈ closure {b'}`, so the open set `W`
meets `{b'}`, that is `b' ∈ W`; hence the fibre rank at `b'` is `n`, as it is at `b`. -/
@[ega "III 7.3.4" "special case"]
theorem exists_opens_forall_fiberRank_eq_of_isFlatOverAt_fibre_dense {X S : Scheme.{u}}
    (g : X ⟶ S) (hg : AlgebraicGeometry.FinitePresentation g) [Flat g]
    [GeometricallyIntegral g] (F : X.Modules) [F.IsFinitePresentation] (b : X)
    (hb : g.base ⁻¹' {g.base b} ⊆ closure {b})
    (hflat : IsFlatOverAt g.toLRSHom.toShHom F b) :
    ∃ V : S.Opens, g.base b ∈ V ∧
      ∀ b' : X, g.base ⁻¹' {g.base b'} ⊆ closure {b'} → g.base b' ∈ V →
        F.fiberRank b' = F.fiberRank b := by
  obtain ⟨W, hbW, n, ⟨e⟩⟩ :=
    Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk g hg F b hflat
      (flat_fibre_stalk_of_fibre_subset_closure g F b hb)
  have _ : LocallyOfFinitePresentation g := hg.locallyOfFinitePresentation
  have hgopen : IsOpenMap g.base :=
    isOpenMap_of_generalizingMap g (Flat.generalizingMap g)
  refine ⟨⟨g.base '' (W : Set X), hgopen _ W.2⟩, ⟨b, hbW, rfl⟩, fun b' hb' hmem => ?_⟩
  obtain ⟨w, hwW, hwb'⟩ := hmem
  have hwcl : w ∈ closure ({b'} : Set X) := hb' hwb'
  obtain ⟨y, hyW, hy⟩ := mem_closure_iff.mp hwcl (W : Set X) W.2 hwW
  rw [Set.mem_singleton_iff] at hy
  rw [Scheme.Modules.fiberRank_eq_of_iso_free_over F W n e (hy ▸ hyW),
    Scheme.Modules.fiberRank_eq_of_iso_free_over F W n e hbW]

end AlgebraicGeometry

end
