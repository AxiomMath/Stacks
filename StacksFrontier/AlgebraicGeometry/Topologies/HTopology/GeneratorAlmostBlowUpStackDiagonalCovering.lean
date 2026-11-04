module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackMorSheaf

/-!
# The second h covering attached to an almost blowup square, in the site

The centre and the modification of an almost blowup square form an h covering of its base,
`AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_mem_topology`.  Gluing an *object* of a fibre along
that two-element covering, rather than an equation between morphisms, needs a second covering: the
two restrictions of the datum over the modification along the two projections of `X' ×_X X'` have
to be identified, and `X' ×_X X'` is itself covered by the base change of the centre and by the
diagonal of the modification.

This file records that second covering in the site, together with the fact that the centre is a
monomorphism.  Those are exactly the two facts that make the four pairs of members of the covering
`{Z, X'}` behave: the pair `(Z, Z)` because the centre is a monomorphism, the two mixed pairs
because the exceptional corner is the fibre product, and the pair `(X', X')` by this covering.

Both are transported from the geometry of schemes:
`AlgebraicGeometry.isProper_finitePresentation_range_union_exceptional_diagonal` and
`AlgebraicGeometry.isClosedImmersion_center_of_almostBlowUpSquare`, together with
`AlgebraicGeometry.isHCovering_bool_of_isProper_of_range_union` and
`AlgebraicGeometry.BigHOver.sieve₀_mem_topology_of_isHCovering`, exactly as
`AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_mem_topology` transports the first covering.

## Main results

* `AlgebraicGeometry.BigHOver.mono_center_of_almostBlowUpSquare`: the centre of an almost blowup
  square is a monomorphism of the site.
* `AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_diagonal_mem_topology`: the base change of the
  centre along the fibre square of the modification, together with the diagonal of the
  modification, generate a covering sieve of the h topology on that fibre square.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EVD](https://stacks.math.columbia.edu/tag/0EVD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The centre of an almost blowup square is a monomorphism of the site.**  Its underlying
morphism of schemes is a closed immersion by
`AlgebraicGeometry.isClosedImmersion_center_of_almostBlowUpSquare`, hence a monomorphism, and the
underlying-scheme functor is faithful. -/
public theorem mono_center_of_almostBlowUpSquare {X Z : BigHOver B S hS} (z : Z ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι)) :
    Mono z := by
  refine (BigHOver.toScheme B S hS).mono_of_mono_map (f := z) ?_
  have : IsClosedImmersion ((BigHOver.toScheme B S hS).map z) :=
    isClosedImmersion_center_of_almostBlowUpSquare I _ hZ
  infer_instance

/-- **The base change of the centre of an almost blowup square along the fibre square of the
modification, together with the diagonal of the modification, generate a covering sieve of the h
topology on that fibre square.**

Both morphisms are proper and of finite presentation and their images cover, by
`AlgebraicGeometry.isProper_finitePresentation_range_union_exceptional_diagonal`; so the
two-element family of their underlying morphisms of schemes is an h covering by
`AlgebraicGeometry.isHCovering_bool_of_isProper_of_range_union`, and
`AlgebraicGeometry.BigHOver.sieve₀_mem_topology_of_isHCovering` turns that into membership of the
h topology.  The family is reindexed along `Equiv.ulift` because a covering family of the site is
indexed by a type in `Type (u + 1)`.

The fibre square and the base change of the centre are quantified over rather than constructed, as
in `AlgebraicGeometry.isPullback_of_almostBlowUpSquare_bigH`, and the diagonal is presented by its
two factorizations. -/
public theorem sieve_ofArrows_pair_diagonal_mem_topology
    {X X' Z P T : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (f₁ f₂ : P ⟶ X') (hP : IsPullback f₁ f₂ b b) (m : P ⟶ X) (hm : f₁ ≫ b = m)
    (a : T ⟶ Z) (r : T ⟶ P) (hT : IsPullback a r z m)
    (d : X' ⟶ P) (hd₁ : d ≫ f₁ = 𝟙 X') (hd₂ : d ≫ f₂ = 𝟙 X')
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι)) :
    Sieve.ofArrows (fun j : ULift.{u + 1} Bool ↦ pairObj T X' j.down)
      (fun j ↦ pairHom r d j.down) ∈ BigHOver.topology B S hS P := by
  have hP' : IsPullback ((BigHOver.toScheme B S hS).map f₁) ((BigHOver.toScheme B S hS).map f₂)
      ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map b) :=
    hP.map (BigHOver.toScheme B S hS)
  have hT' : IsPullback ((BigHOver.toScheme B S hS).map a) ((BigHOver.toScheme B S hS).map r)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map m) :=
    hT.map (BigHOver.toScheme B S hS)
  have hm' : (BigHOver.toScheme B S hS).map m =
      (BigHOver.toScheme B S hS).map f₁ ≫ (BigHOver.toScheme B S hS).map b := by
    rw [← hm, Functor.map_comp]
  have hd' : ∀ g : P ⟶ X', d ≫ g = 𝟙 X' →
      (BigHOver.toScheme B S hS).map d ≫ (BigHOver.toScheme B S hS).map g =
        𝟙 ((BigHOver.toScheme B S hS).obj X') := fun g h ↦ by
    rw [← Functor.map_comp, h]
    exact (BigHOver.toScheme B S hS).map_id X'
  obtain ⟨hfpr, hfpd, hproperr, hproperd, hrange⟩ :=
    isProper_finitePresentation_range_union_exceptional_diagonal I
      ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map f₁) ((BigHOver.toScheme B S hS).map f₂) hP'
      ((BigHOver.toScheme B S hS).map m) hm' ((BigHOver.toScheme B S hS).map a)
      ((BigHOver.toScheme B S hS).map r) hT' ((BigHOver.toScheme B S hS).map d)
      (hd' _ hd₁) (hd' _ hd₂) hb hZ
  have hbool : IsHCovering (fun i : Bool ↦ (BigHOver.toScheme B S hS).obj (pairObj T X' i))
      (fun i : Bool ↦ (BigHOver.toScheme B S hS).map (pairHom r d i)) := by
    refine isHCovering_bool_of_isProper_of_range_union _ _ (fun i ↦ ?_) (fun i ↦ ?_) hrange
    · cases i
      · exact hfpr.1
      · exact hfpd.1
    · cases i
      · exact hproperr
      · exact hproperd
  exact sieve₀_mem_topology_of_isHCovering B S hS
    { I₀ := ULift.{u + 1} Bool
      X := fun j ↦ pairObj T X' j.down
      f := fun j ↦ pairHom r d j.down } (hbool.reindex Equiv.ulift)

end BigHOver

end AlgebraicGeometry

end
