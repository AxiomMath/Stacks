module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisting sheaf on `Proj 𝒜` is invertible on the nose, and the twist is exact

This file proves that the twisting sheaf `𝒪(dn)` on `Proj 𝒜` is invertible when the open `W_d`
of Tag 01MU is all of `Proj 𝒜`, i.e. when `Proj 𝒜` is covered by the standard opens `D₊(fg)`
with `deg f = deg g + d`. That holds for every `d` as soon as `𝒜` is generated in degree one over
`𝒜 0`, and it holds for `d` the common degree of any standard-open cover. The twist functor is
then an equivalence, so it carries short exact sequences of `𝒪_{Proj 𝒜}`-modules to short exact
sequences.

## Main results

* `Stacks.AlgebraicGeometry.TwistFlatness.iSup_ratioOpen`: the standard opens indexed by
  `Stacks.AlgebraicGeometry.GoodOpenClose.RatioIndex 𝒜 d` have union `W_d`.
* `Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_ratioLocus_eq_top`:
  `𝒪(dn)` is invertible on all of `Proj 𝒜` when `W_d = Proj 𝒜`.
* `Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_commonDegreeCover`: the
  same from an `AlgebraicGeometry.Proj.CommonDegreeCover 𝒜 ⊤`.
* `Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one`:
  **every** `𝒪(n)` is invertible when `𝒜` is generated in degree one.
* `Stacks.AlgebraicGeometry.TwistFlatness.isEquivalence_twistFunctor_of_ratioLocus_eq_top` and
  `Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_twistFunctor_of_ratioLocus_eq_top`: the
  twist by `𝒪(dn)` is an equivalence and carries short exact sequences to short exact sequences
  when `W_d = Proj 𝒜`.
* `Stacks.AlgebraicGeometry.TwistFlatness.isEquivalence_twistFunctor_of_adjoin_degree_one`,
  `Stacks.AlgebraicGeometry.TwistFlatness.preservesMonomorphisms_twistFunctor_of_adjoin_degree_one`
  and `Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_twistFunctor_of_adjoin_degree_one`:
  when `𝒜` is generated in degree one, every twist functor is an equivalence, preserves
  monomorphisms, and carries short exact sequences to short exact sequences.

## Implementation notes

The statements are in the `Stacks.SheafOfModules.IsInvertible` spelling that
`Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor` consumes. No tag attribute is attached.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MW](https://stacks.math.columbia.edu/tag/01MW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.TwistFlatness

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Invertibility of the twisting sheaf on the whole of `Proj 𝒜` -/

/-- The standard opens indexed by `Stacks.AlgebraicGeometry.GoodOpenClose.RatioIndex 𝒜 d` have
the open `W_d` of Tag 01MU for their union. -/
theorem iSup_ratioOpen (d : ℕ) :
    (⨆ i, GoodOpenClose.ratioOpen 𝒜 d i) = ProjShared.ratioLocus 𝒜 d := by
  simp only [GoodOpenClose.ratioOpen, ProjShared.ratioLocus, iSup_sigma, iSup_prod]

/-- **The twisting sheaf `𝒪(dn)` is invertible on all of `Proj 𝒜`** as soon as the open `W_d`
of Tag 01MU is everything, i.e. as soon as `Proj 𝒜` is covered by the standard opens `D₊(fg)`
with `deg f = deg g + d`. -/
@[ega "II 3.2.5" "Second assertion"]
theorem isInvertible_twistingSheaf_of_ratioLocus_eq_top (d : ℕ)
    (h : ProjShared.ratioLocus 𝒜 d = ⊤) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2 (twistingSheaf 𝒜 ((d : ℤ) * n)) := by
  have hY : (⨆ i, GoodOpenClose.ratioOpen 𝒜 d i) = ⊤ := (iSup_ratioOpen 𝒜 d).trans h
  refine (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    (AlgebraicGeometry.Proj 𝒜).presheaf (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2
    (twistingSheaf 𝒜 ((d : ℤ) * n))).mpr ?_
  exact Stacks.SheafDescent.isInvertible_of_trivialization
    (AlgebraicGeometry.Proj 𝒜).presheaf (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2
    (twistingSheaf 𝒜 ((d : ℤ) * n))
    ((Opens.coversTop_iff _ (GoodOpenClose.ratioOpen 𝒜 d)).mpr
      (TopologicalSpace.IsOpenCover.mk hY))
    fun i => GoodOpenClose.ratioTriv 𝒜 i.2.1.2 i.2.2.2 (mul_comm (n : ℤ) (d : ℤ))

/-- **The twisting sheaf `𝒪(dn)` is invertible on all of `Proj 𝒜`** when `Proj 𝒜` itself carries
a finite cover by standard opens of one common degree `d`. -/
theorem isInvertible_twistingSheaf_of_commonDegreeCover
    (C : AlgebraicGeometry.Proj.CommonDegreeCover 𝒜 ⊤) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2
      (twistingSheaf 𝒜 ((C.degree : ℤ) * n)) :=
  isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒜 C.degree
    (top_le_iff.mp (((GoodOpenClose.whereInvertible_eq_ratioLocus 𝒜 C.degree) ▸
      CommonDegreeTwist.le_whereInvertible 𝒜 ⊤ C : (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens) ≤
        ProjShared.ratioLocus 𝒜 C.degree))) n

/-- **Every twisting sheaf on `Proj 𝒜` is invertible when `𝒜` is generated in degree one** over
its degree-zero part. -/
theorem isInvertible_twistingSheaf_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2 (twistingSheaf 𝒜 n) := by
  simpa using isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒜 1
    (ProjShared.ratioLocus_eq_top_of_adjoin_degree_one 𝒜 hgen 1) n

/-! ### Exactness of the twist functor -/

open Stacks.AlgebraicGeometry.ProjTwistFunctor

/-- **The twist by `𝒪(dn)` is an equivalence** when `W_d = Proj 𝒜`. -/
theorem isEquivalence_twistFunctor_of_ratioLocus_eq_top (d : ℕ)
    (h : ProjShared.ratioLocus 𝒜 d = ⊤) (n : ℤ) :
    (twistFunctor 𝒜 ((d : ℤ) * n)).IsEquivalence :=
  @isEquivalence_twistFunctor _ _ _ _ _ 𝒜 _ ((d : ℤ) * n)
    (isInvertible_twistingSheaf_of_ratioLocus_eq_top 𝒜 d h n)

/-- **The twist by `𝒪(n)` is an equivalence** for every `n`, when `𝒜` is generated in degree
one. -/
theorem isEquivalence_twistFunctor_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤) (n : ℤ) :
    (twistFunctor 𝒜 n).IsEquivalence :=
  @isEquivalence_twistFunctor _ _ _ _ _ 𝒜 _ n
    (isInvertible_twistingSheaf_of_adjoin_degree_one 𝒜 hgen n)

/-- **The twist by `𝒪(n)` preserves monomorphisms** for every `n`, when `𝒜` is generated in
degree one. -/
theorem preservesMonomorphisms_twistFunctor_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤) (n : ℤ) :
    (twistFunctor 𝒜 n).PreservesMonomorphisms :=
  let : (twistFunctor 𝒜 n).IsEquivalence :=
    isEquivalence_twistFunctor_of_adjoin_degree_one 𝒜 hgen n
  inferInstance

/-- **The twist of a short exact sequence by `𝒪(dn)` is short exact** when `W_d = Proj 𝒜`,
with no hypothesis on the sequence beyond short exactness. -/
theorem shortExact_map_twistFunctor_of_ratioLocus_eq_top (d : ℕ)
    (h : ProjShared.ratioLocus 𝒜 d = ⊤) (n : ℤ)
    {T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))} (hT : T.ShortExact) :
    (T.map (twistFunctor 𝒜 ((d : ℤ) * n))).ShortExact :=
  let : (twistFunctor 𝒜 ((d : ℤ) * n)).IsEquivalence :=
    isEquivalence_twistFunctor_of_ratioLocus_eq_top 𝒜 d h n
  hT.map_of_exact _

/-- **The twist of a short exact sequence is short exact, for every twist**, when `𝒜` is
generated in degree one. -/
theorem shortExact_map_twistFunctor_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤) (n : ℤ)
    {T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜))} (hT : T.ShortExact) :
    (T.map (twistFunctor 𝒜 n)).ShortExact :=
  let : (twistFunctor 𝒜 n).IsEquivalence :=
    isEquivalence_twistFunctor_of_adjoin_degree_one 𝒜 hgen n
  hT.map_of_exact _

end Stacks.AlgebraicGeometry.TwistFlatness

end
