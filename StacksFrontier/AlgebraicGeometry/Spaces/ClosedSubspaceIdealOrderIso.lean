module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Stacks 03MB as an order isomorphism, and the two inputs it still lacks

Stacks 03MB asserts that `Z ↦ 𝓘_Z` is an inclusion-reversing *bijection* between the closed
subspaces of an algebraic space `X` and the **quasi-coherent** sheaves of ideals
`𝓘 ⊆ 𝒪_X` on the small étale site of `X`.  The injective, inclusion-reversing half of that
correspondence is `AlgebraicGeometry.Space.definingIdealOrderEmbedding` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealBijection.lean`.

**This file does not prove Stacks 03MB, and carries no `@[stacks]` attribute.**  What it does is
assemble the proved half into the shape the tag asks for — an
`AlgebraicGeometry.Space.QuasicoherentIdeals`-valued `OrderIso`, pinned down by the kernel
formula — *from two explicit hypotheses*, and those two hypotheses are exactly the whole of the
mathematics that is still missing:

* `hq`, that the defining ideal sheaf of a closed subspace is quasi-coherent on the site, which
  is what makes the forward map land in the quasi-coherent ideals at all;
* `hr`, that every quasi-coherent sheaf of ideals is the defining ideal sheaf of some closed
  subspace, which is the surjectivity half.

Nothing else is needed: injectivity and both directions of monotonicity come from
`AlgebraicGeometry.Space.definingIdealSheaf_injective`,
`AlgebraicGeometry.Space.definingIdealSheaf_antitone` and
`AlgebraicGeometry.Space.le_of_definingIdealSheaf_le`.  So this file is a *reduction*: it is
machine-checked that `hq` and `hr` suffice, and that there is no third gap.

Both `hq` and `hr` are out of reach of the present library, and for the same reason.  Each of
them needs quasi-coherence on the small étale site to be compared with quasi-coherence on an
étale scheme chart: `𝓘_Z` is a kernel, and quasi-coherence of a kernel of quasi-coherent
modules is Stacks 03M1, whose proof passes through the identification of quasi-coherent modules
on the small étale site of a scheme with quasi-coherent modules on that scheme, Stacks 03DX(2)
and 03LX.  That identification is absent from this library: it is carried as the hypothesis
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean`.  Going the other way, `hr` has to cut
out a closed subscheme inside each étale scheme chart from the chart sections of `𝓘`, which
needs the same comparison to know that those sections base-change along étale restriction.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentIdeals` is the ordered type of quasi-coherent sheaves of
  ideals of `𝒪_X` on the small étale site of an algebraic space `X`: the sheaf submodules of
  `𝒪_X` whose associated module is quasi-coherent in the sense of Stacks 03DL(6).
* `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` is the order isomorphism of Stacks 03MB,
  **conditional on the two hypotheses above**, together with the kernel formula that pins it
  down to the canonical rule.

## Main results

* `AlgebraicGeometry.Space.ker_fSharp_app` and
  `AlgebraicGeometry.Space.definingIdealAt_eq_ker_fSharp`: the defining ideal of a closed
  subspace on an étale chart is the kernel of the structure map of the morphism of ringed topoi
  of Stacks 03G8, read on sections, and not merely of its underlying map of sheaves of rings.
* `AlgebraicGeometry.Space.toDual_definingIdealSheaf_bijective` and
  `AlgebraicGeometry.Space.toDual_definingIdealSheaf_le_toDual_iff`: the two halves of the
  order isomorphism, the first conditional on the hypotheses above and the second
  unconditional.

## Implementation notes

The statement of `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` writes the subspace
`⟨Z.1.toFunctor, Z.2.1⟩` and its inclusion `ObjectProperty.homMk Z.1.ι` out where they are used
instead of binding them with `let`; the two readings are the same up to zeta reduction.

The kernel in that statement is taken of the structure map of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, a homomorphism of sheaves of *commutative*
rings, whereas `AlgebraicGeometry.Space.definingIdealAt` is defined from
`AlgebraicGeometry.Space.structureSharp`, the same map read in sheaves of rings.  The two have
the same kernel because `AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp` identifies the
maps, and forgetting commutativity changes neither the sections nor the ring homomorphism
between them; `AlgebraicGeometry.Space.ker_fSharp_app` records this.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure map of the ringed topos has the same kernel on sections -/

/-- The structure map of the morphism of small étale ringed topoi of Stacks 03G8 has, on
sections over an étale chart, the same kernel as the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of
sheaves of rings: the first is the second with its commutativity remembered. -/
theorem ker_fSharp_app {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    RingHom.ker (((smallEtaleRingedToposHom B S hS f).fSharp.hom.app U).hom) =
      RingHom.ker ((structureSharp B S hS f).hom.app U).hom :=
  congrArg (fun φ : structureRingSheaf B S hS Y ⟶ structureRingSheafDirectImage B S hS f =>
    RingHom.ker (φ.hom.app U).hom) (forgetCommRingSheaf_map_fSharp B S hS f)

/-- **The defining ideal of a closed subspace is the kernel of the Stacks 03G8 structure map of
its inclusion**, read on sections over an étale chart.  This is the formula that fixes the
correspondence of Stacks 03MB to be the canonical rule rather than an unspecified order
isomorphism. -/
theorem definingIdealAt_eq_ker_fSharp (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    definingIdealAt B S hS X Z U =
      RingHom.ker (((smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk Z.1.ι :
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).fSharp.hom.app U).hom) :=
  (ker_fSharp_app B S hS _ U).symm

/-! ### Quasi-coherent sheaves of ideals -/

/-- **The quasi-coherent sheaves of ideals of `𝒪_X`**, ordered by inclusion: the sheaf
submodules of the structure sheaf of an algebraic space on its small étale site whose
associated sheaf of modules is quasi-coherent in the sense of Stacks 03DL(6).  This is the
right-hand side of the correspondence of Stacks 03MB. -/
abbrev QuasicoherentIdeals (X : AlgebraicSpaces B S hS) :=
  {I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule //
    I.toSheafOfModules.IsQuasicoherentOnSite}

variable (X : AlgebraicSpaces B S hS)

/-- **Stacks 03MB, the bijectivity, granted its two missing inputs.** If every closed subspace
of `X` has a quasi-coherent defining ideal sheaf and every quasi-coherent sheaf of ideals of
`𝒪_X` is such a defining ideal sheaf, then `Z ↦ 𝓘_Z` is a bijection from the closed subspaces
of `X` onto the quasi-coherent sheaves of ideals.

Injectivity is not a hypothesis: it is
`AlgebraicGeometry.Space.definingIdealSheaf_injective`. -/
theorem toDual_definingIdealSheaf_bijective
    (hq : ∀ Z : ClosedSubspaces B S hS X.1,
      (definingIdealSheaf B S hS X Z).toSheafOfModules.IsQuasicoherentOnSite)
    (hr : ∀ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite →
        ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I) :
    Function.Bijective (fun Z : ClosedSubspaces B S hS X.1 =>
      OrderDual.toDual (α := QuasicoherentIdeals B S hS X)
        ⟨definingIdealSheaf B S hS X Z, hq Z⟩) := by
  refine ⟨fun Z W h => ?_, fun I => ?_⟩
  · exact definingIdealSheaf_injective B S hS X (congrArg (fun t => (OrderDual.ofDual t).1) h)
  · obtain ⟨Z, hZ⟩ := hr (OrderDual.ofDual I).1 (OrderDual.ofDual I).2
    exact ⟨Z, Subtype.ext hZ⟩

/-- **Stacks 03MB, the inclusion-reversal, as an equivalence.** A closed subspace of `X` is
contained in another exactly when its defining ideal sheaf contains the other's.  This is
unconditional: the forward implication is
`AlgebraicGeometry.Space.definingIdealSheaf_antitone` and the backward one
`AlgebraicGeometry.Space.le_of_definingIdealSheaf_le`. -/
theorem toDual_definingIdealSheaf_le_toDual_iff
    (hq : ∀ Z : ClosedSubspaces B S hS X.1,
      (definingIdealSheaf B S hS X Z).toSheafOfModules.IsQuasicoherentOnSite)
    (Z W : ClosedSubspaces B S hS X.1) :
    (OrderDual.toDual (α := QuasicoherentIdeals B S hS X)
        ⟨definingIdealSheaf B S hS X Z, hq Z⟩) ≤
      (OrderDual.toDual (α := QuasicoherentIdeals B S hS X)
        ⟨definingIdealSheaf B S hS X W, hq W⟩) ↔ Z ≤ W := by
  rw [OrderDual.toDual_le_toDual, Subtype.mk_le_mk]
  exact ⟨fun h => Subtype.coe_le_coe.1 (le_of_definingIdealSheaf_le B S hS X Z W h),
    fun h => definingIdealSheaf_antitone B S hS X Z W (Subtype.coe_le_coe.2 h)⟩

/-- **Stacks 03MB, conditionally on its two missing inputs.** Granted that the defining ideal
sheaf of every closed subspace of `X` is quasi-coherent (`hq`) and that every quasi-coherent
sheaf of ideals of `𝒪_X` is a defining ideal sheaf (`hr`), the closed subspaces of `X` are
order-isomorphic to the order dual of the quasi-coherent sheaves of ideals of `𝒪_X`, by an
isomorphism sending a closed subspace to the kernel of the structure map of its inclusion on
every étale chart.

This is *not* a proof of Stacks 03MB; `hq` and `hr` are the whole of what Stacks 03MB asserts
beyond `AlgebraicGeometry.Space.definingIdealOrderEmbedding`, and neither is
available.  See the module documentation. -/
noncomputable def closedSubspaceIdealOrderIso
    (hq : ∀ Z : ClosedSubspaces B S hS X.1,
      (definingIdealSheaf B S hS X Z).toSheafOfModules.IsQuasicoherentOnSite)
    (hr : ∀ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite →
        ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I) :
    {e : ClosedSubspaces B S hS X.1 ≃o (QuasicoherentIdeals B S hS X)ᵒᵈ //
      ∀ (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ),
        (OrderDual.ofDual (e Z)).1.obj U =
          RingHom.ker (((smallEtaleRingedToposHom B S hS
            (ObjectProperty.homMk Z.1.ι :
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).fSharp.hom.app U).hom)} :=
  ⟨{ toEquiv := Equiv.ofBijective _ (toDual_definingIdealSheaf_bijective B S hS X hq hr)
     map_rel_iff' := toDual_definingIdealSheaf_le_toDual_iff B S hS X hq _ _ },
    fun Z U => definingIdealAt_eq_ker_fSharp B S hS X Z U⟩

end AlgebraicGeometry.Space

end
