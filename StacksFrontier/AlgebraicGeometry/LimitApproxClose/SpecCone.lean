module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.CompatibleFamily
public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.StageLimits

/-!
# The spectrum of the ring being added is the inverse limit of the spectra of the subalgebras

The affine open being added in the one-affine-open step of Tag 07RN is `Spec B`, and the system
of models of it is the diagram of spectra of the distinguished subalgebras,
`Stacks.StageSubalgebra.specDiagram`.  This file produces the cone from `Spec B` over that
diagram and shows it limiting, from the colimit of `Stacks.StageSubalgebra.ringCocone`.

This is the hypothesis `hY` of `AlgebraicGeometry.isLimitGluePairFunctorCone`.

## Main definitions

* `Stacks.StageSubalgebra.specDiagramCone` is the cone, its legs being the spectra of the legs of
  `Stacks.StageSubalgebra.ringCocone`.  Naturality is the naturality of that cocone, read
  backwards through `AlgebraicGeometry.Spec.map_comp`.

## Main results

* `Stacks.StageSubalgebra.isLimitSpecDiagramCone` is the limiting property:
  `AlgebraicGeometry.isLimitSpecMapCone` applied to the colimit, whiskered along the equivalence
  `CategoryTheory.orderDualEquivalence`, and compared with the cone above by
  `CategoryTheory.Limits.Cone.ext` at the identity.

## Implementation notes

`AlgebraicGeometry.isLimitSpecMapCone` produces a cone indexed by the **opposite** of the index
of pairs, while the structure recording the conclusion of Tag 07RN wants the **order dual**.
Mathlib's `CategoryTheory.orderDualEquivalence` identifies the order dual of a preorder with its
opposite, and `CategoryTheory.Limits.IsLimit.whiskerEquivalence` transports a limit along an
equivalence with **no finality or initiality hypothesis**.  The diagram obtained by whiskering is
the diagram of spectra on the nose: both send a pair to the spectrum of its subalgebra and a
morphism to the spectrum of the inclusion, the two inclusions differing only in which proof of
the same inequality they name.

The stages, the rings and the index of pairs share the universe `u`, which is what
`AlgebraicGeometry.isLimitSpecMapCone` requires of the index of the colimit it consumes — the
spectrum functor preserves limits of shape `K` with `K` and its homs in the universe of the
schemes.

* The whiskered diagram and `Stacks.StageSubalgebra.specDiagram` agree definitionally, the
  transition morphisms differing only by which proof of the stage inequality is named, which is
  proof-irrelevant.  The comparison is therefore `CategoryTheory.Limits.Cone.ext` at
  `CategoryTheory.Iso.refl` and the leg condition is closed without rewriting.

* The naturality of the cocone is taken from `CategoryTheory.Limits.Cocone.w` and **not** from
  `CategoryTheory.NatTrans.naturality`: the latter carries a trailing identity whose object is
  the cocone's own vertex, written through a `def`, and `Category.comp_id` then fails to match it
  at the transparency `rw` uses.  `Cocone.w` states the same thing already trimmed.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.StageSubalgebra

variable {K : Type u} [Preorder K] {F : K ⥤ CommRingCat.{u}} {B : CommRingCat.{u}}
  (τ : F ⟶ (Functor.const K).obj B) (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop)

/-- **The cone from the spectrum of the ring being added over the spectra of the distinguished
subalgebras.**  Its legs are the spectra of the legs of
`Stacks.StageSubalgebra.ringCocone`. -/
noncomputable def specDiagramCone :
    (Functor.const (StageSubalgebra F P)ᵒᵈ).obj (Spec B) ⟶ specDiagram F P where
  app j := Spec.map ((ringCocone (P := P) τ).ι.app (OrderDual.ofDual j))
  naturality {j k} u := by
    refine (Category.id_comp _).trans ?_
    exact (congrArg Spec.map
      ((ringCocone (P := P) τ).w (homOfLE (leOfHom u)))).symm.trans
      (Spec.map_comp _ _)

/-- The leg of the cone at a distinguished subalgebra is the spectrum of the corresponding leg
of `Stacks.StageSubalgebra.ringCocone`. -/
@[simp]
lemma specDiagramCone_app (j : (StageSubalgebra F P)ᵒᵈ) :
    (specDiagramCone τ P).app j =
      Spec.map ((ringCocone (P := P) τ).ι.app (OrderDual.ofDual j)) := rfl

/-- **The spectrum of the ring being added is the inverse limit of the spectra of the
distinguished subalgebras.**  This is the hypothesis `hY` of step (iii).

`AlgebraicGeometry.isLimitSpecMapCone` gives the limit over the *opposite* of the
index of pairs; `CategoryTheory.orderDualEquivalence` and
`CategoryTheory.Limits.IsLimit.whiskerEquivalence` carry it to the order dual with no finality
hypothesis, the reindexing being an equivalence. -/
noncomputable def isLimitSpecDiagramCone (hc : IsColimit (ringCocone (P := P) τ)) :
    IsLimit (Cone.mk (Spec B) (specDiagramCone τ P)) :=
  IsLimit.ofIsoLimit
    ((isLimitSpecMapCone hc).whiskerEquivalence (orderDualEquivalence (StageSubalgebra F P)))
    (Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm)

end Stacks.StageSubalgebra
