module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# The homology comparison of a left exact functor is Mathlib's `mapHomologyIso`

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison` is the map
`H^q(F K) ⟶ F(H^q K)` that a left exact additive functor supplies with no further hypothesis; it
is the complex-level ingredient of the edge morphism of a right derived functor.  Where `F`
*preserves* the left homology of the degree-`q` short complex of `K`, Mathlib's
`CategoryTheory.ShortComplex.mapHomologyIso` supplies an **isomorphism** in the opposite
direction's inverse spelling, `(S.map F).homology ≅ F.obj S.homology`, and it is that
isomorphism — not `homologyComparison` — which the degreewise comparisons of a composite of
derived functors are built from, among them
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`, the collapse behind [Stacks, Tag 01XK].

This file proves the two are the same map.  So a statement about one is a statement about the
other, and the degreewise collapse of [Stacks, Tag 01XK] may be read as the edge morphism whose
splitting `Stacks.EdgeCompat.derivedHomologyComparison_comp` describes.

## Main results

* `homologyπ_comp_mapHomologyIso_hom`: the factorisation of
  `CategoryTheory.ShortComplex.mapHomologyIso` through the projection from cycles, for an
  arbitrary short complex and an arbitrary functor preserving its left homology.  This is the
  defining property of `homologyComparison`, and Mathlib does not record it.
* `cyclesComparison_eq_mapCyclesIso_hom`: the comparison on cycles is
  `CategoryTheory.ShortComplex.mapCyclesIso`.
* `homologyComparison_eq_mapHomologyIso_hom`: **the comparison on homology is
  `CategoryTheory.ShortComplex.mapHomologyIso`.**  In particular it is an isomorphism exactly
  where `F` preserves the left homology that occurs.

## Implementation notes

The two comparisons are each characterised by one factorisation — on cycles through the
inclusion `iCycles`, which is a monomorphism after a left exact `F`, and on homology through the
projection `homologyπ`, which is an epimorphism — so each identification is one cancellation
once the matching factorisation is available for Mathlib's isomorphism.  On cycles Mathlib
records it, as `CategoryTheory.ShortComplex.mapCyclesIso_hom_iCycles`; on homology it does not,
which is what `homologyπ_comp_mapHomologyIso_hom` supplies.

That proof is written in term mode through `sandwich`, at variables of an abstract category.
`CategoryTheory.ShortComplex.LeftHomologyData.mapHomologyIso_eq` presents the isomorphism as a
`CategoryTheory.Iso.trans` whose two halves are joined by the definitional equality
`(h.map F).H = F.obj h.H`, which `CategoryTheory.ShortComplex.LeftHomologyData.map` establishes
but does not expose: the resulting goal is not type-correct at the `implicit` transparency level
at which a rewrite builds its motive, and `dsimp only [Iso.trans_hom]` reports *made no
progress*.  Supplying the two factorisations to an abstract lemma in argument position puts the
check at default transparency, where the equality is seen.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

/-- A functor applied to one factorisation, pasted onto another, at variables of an abstract
category: the shape in which `homologyπ_comp_mapHomologyIso_hom` meets its two inputs. -/
private theorem sandwich {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P Q : D} {k h c d : C}
    (π : P ⟶ Q) (α : Q ⟶ F.obj h) (κ : P ⟶ F.obj k)
    (p : k ⟶ h) (hi : h ⟶ d) (ci : k ⟶ c) (pr : c ⟶ d)
    (hA : π ≫ α = κ ≫ F.map p) (hB : p ≫ hi = ci ≫ pr) :
    π ≫ α ≫ F.map hi = (κ ≫ F.map ci) ≫ F.map pr := by
  rw [← Category.assoc, hA, Category.assoc, ← F.map_comp, hB, F.map_comp, Category.assoc]

/-- **`CategoryTheory.ShortComplex.mapHomologyIso` factors through the projection from cycles**,
by `CategoryTheory.ShortComplex.mapCyclesIso` and `F` of that projection. This is the property
that characterises `homologyComparison`, `homologyπ` being an epimorphism. -/
public theorem homologyπ_comp_mapHomologyIso_hom {C D : Type*} [Category* C] [Category* D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  have e1 := congrArg Iso.hom
    (ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.homologyData.left) F)
  have e2 := congrArg Iso.hom
    (ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.homologyData.left) F)
  have hA : (S.map F).homologyπ ≫ ((S.homologyData.left).map F).homologyIso.hom =
      ((S.homologyData.left).map F).cyclesIso.hom ≫ F.map (S.homologyData.left).π :=
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
        ((S.homologyData.left).map F)).trans
      (congrArg (fun z => ((S.homologyData.left).map F).cyclesIso.hom ≫ z)
        (ShortComplex.LeftHomologyData.map_π (S.homologyData.left) F))
  refine Eq.trans (congrArg (fun z => (S.map F).homologyπ ≫ z) e1)
    (Eq.trans ?_ (congrArg (fun z => z ≫ F.map S.homologyπ) e2.symm))
  exact sandwich F _ _ _ _ _ _ _ hA
    (ShortComplex.LeftHomologyData.π_comp_homologyIso_inv S (S.homologyData.left))

section Bridge

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- **The comparison on cycles is `CategoryTheory.ShortComplex.mapCyclesIso`.** Both satisfy the
same factorisation through the inclusion of cycles, and `F` applied to that inclusion is a
monomorphism. -/
public theorem cyclesComparison_eq_mapCyclesIso_hom (K : CochainComplex A ℤ) (q : ℤ)
    [F.PreservesLeftHomologyOf (K.sc q)] :
    cyclesComparison F K q = ((K.sc q).mapCyclesIso F).hom := by
  have hmono := mono_map_iCycles F K q
  apply (cancel_mono (F.map (K.iCycles q))).1
  rw [cyclesComparison_comp_map_iCycles]
  exact ((K.sc q).mapCyclesIso_hom_iCycles F).symm

/-- **The comparison on homology is `CategoryTheory.ShortComplex.mapHomologyIso`.** Both satisfy
the same factorisation through the projection from cycles — for `homologyComparison` that is
`homologyπ_comp_homologyComparison`, by which it is defined, and for Mathlib's isomorphism it is
`homologyπ_comp_mapHomologyIso_hom` — and the projection is an epimorphism.

So the degreewise comparison `H^q(F K) ⟶ F(H^q K)` that the edge morphism of a right derived
functor is built from, and the isomorphism that the degreewise collapse of
[Stacks, Tag 01XK] is built from, are the same map. -/
public theorem homologyComparison_eq_mapHomologyIso_hom (K : CochainComplex A ℤ) (q : ℤ)
    [F.PreservesLeftHomologyOf (K.sc q)] :
    homologyComparison F K q = ((K.sc q).mapHomologyIso F).hom := by
  apply (cancel_epi (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q)).1
  rw [homologyπ_comp_homologyComparison, cyclesComparison_eq_mapCyclesIso_hom]
  exact (homologyπ_comp_mapHomologyIso_hom (K.sc q) F).symm

end Bridge

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
