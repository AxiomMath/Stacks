module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtDimensionShift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal

/-!
# Dimension shifting for `Ext`-classes on an open subscheme

Let `X` be a Noetherian scheme, `U ⊆ X` an open subscheme and `𝓕`, `𝓖` coherent `𝒪_X`-modules.
Every class in `Ext^{i + 1}_U(𝓕|_U, 𝓖|_U)` is the boundary class of a short exact sequence

`0 ⟶ ker φ ⟶ 𝓗 ⟶ 𝓕|_U ⟶ 0`

of coherent `𝒪_U`-modules, applied to a class in `Ext^i_U(ker φ, 𝓖|_U)` one degree lower.

This is the **coherent effacement run on `U`** together with the **boundary map** — the first and
third of the four inputs of the surjectivity half of the induction on `i` in the core case of
[Stacks, Tag 0G2H]. The surjectivity chase starts from a class on `U` and must efface it there,
exactly as the injectivity chase effaces a class on `X`; the source's argument then extends the
effacing epimorphism `𝓗 ↠ 𝓕|_U` across the open immersion by [Stacks, Tag 01PI] and compares the
resulting sequence on `X` with the one produced here.

## What has to be supplied

Nothing of the mathematics: `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos` is
stated for an arbitrary Noetherian scheme, and `U` is one
(`AlgebraicGeometry.Scheme.Opens.isNoetherian`). What the statement below adds is that its two
coherence hypotheses hold for the restrictions, by
`AlgebraicGeometry.Modules.isCoherent_restrict`, and that is not found by instance search: the
restriction of a coherent module is coherent by a theorem, not an instance, and
`AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own `Category` instance.

The `CategoryTheory.HasExt` universe is the one of `U.toScheme.Modules`, as in
`Stacks.AlgebraicGeometry.IdealPowerColimit.extRestrict`: the classes being effaced here live in
the `Ext`-groups of `U`, and nothing relates them to the `Ext`-groups of `X` until the extension
across `j` is made.

## Main results

* `Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_restrict_of_pos`: **a positive-degree
  `Ext`-class between the restrictions of coherent modules to an open subscheme is a boundary
  class applied to a class one degree lower**, for a short exact sequence of coherent modules on
  that open subscheme.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe w u

namespace Stacks.ExtEffacement

variable {X : Scheme.{u}}

/-- **A positive-degree `Ext`-class on an open subscheme between the restrictions of coherent
modules is a boundary class applied to a class one degree lower.** For
`η ∈ Ext^{i + 1}_U(𝓕|_U, 𝓖|_U)` with `𝓕`, `𝓖` coherent on a Noetherian scheme `X` and `U ⊆ X`
open there are a coherent `𝒪_U`-module `𝓗`, an epimorphism `φ : 𝓗 ⟶ 𝓕|_U`, and a class
`η' ∈ Ext^i_U(ker φ, 𝓖|_U)` with `η = hS.extClass ∘ η'`, where `S` is the short exact sequence
`0 ⟶ ker φ ⟶ 𝓗 ⟶ 𝓕|_U ⟶ 0` and `ker φ` is coherent as well.

This is the coherent effacement and the boundary map of the **surjectivity** half of the
induction on `i` in the proof of the core case of [Stacks, Tag 0G2H], where the class to be
effaced is given on `U` and not on `X`. It is
`Stacks.ExtEffacement.exists_shortExact_extClass_comp_eq_of_pos` for the Noetherian scheme `U`,
whose two coherence hypotheses are the coherence of the restrictions. -/
public theorem exists_shortExact_extClass_comp_eq_restrict_of_pos [IsNoetherian X]
    (U : X.Opens) [HasExt.{w} U.toScheme.Modules] {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    {i : ℕ}
    (η : Ext.{w} ((Scheme.Modules.restrictFunctor U.ι).obj F)
      ((Scheme.Modules.restrictFunctor U.ι).obj G) (i + 1)) :
    ∃ (H : U.toScheme.Modules) (φ : H ⟶ (Scheme.Modules.restrictFunctor U.ι).obj F)
      (_ : H.IsCoherent) (_ : Epi φ) (_ : (kerMod φ).IsCoherent)
      (hS : (ShortComplex.mk (kerInclusion φ) φ (kerInclusion_comp φ)).ShortExact)
      (η' : Ext.{w} (kerMod φ) ((Scheme.Modules.restrictFunctor U.ι).obj G) i),
      hS.extClass.comp η' (Nat.add_comm 1 i) = η := by
  have : ((Scheme.Modules.restrictFunctor U.ι).obj F).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict F U
  have : ((Scheme.Modules.restrictFunctor U.ι).obj G).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict G U
  exact exists_shortExact_extClass_comp_eq_of_pos.{w} η

end Stacks.ExtEffacement

end
