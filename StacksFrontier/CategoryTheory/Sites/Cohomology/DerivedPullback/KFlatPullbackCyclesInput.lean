module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.CyclesOfAnAcyclicKFlatComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackAlongRingedTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# The cycles input of Tag 0G7E is inhabited

`Stacks.Sheaves.DerivedPullback.KFlatPullback.CyclesIsFlat` is the predicate, on a ringed topos,
  that the cycles of an
acyclic K-flat complex of modules with flat terms are flat.  It is taken as a hypothesis by
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex`.  This file proves it,
  unconditionally, for every ringed
topos, so that the hypothesis is no longer a weakening of the statement.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`: `CyclesIsFlat O` holds for every `O
  : RingedTopos.{v₁, u₁, w₁}`, the three universes independent.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_pullbackPreserves`: Tag
  0G7E with the cycles input
  discharged, so on two hypotheses rather than three.
* `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_acyclic`: the **acyclic**
  case of Tag 0G7E on
  `PullbackPreservesIsFlat` (Stacks 05VD) alone — `PullbackPreservesShortExact` (Stacks 0G6R)
  is not needed there either, since the resolution's kernel sequence never enters.

## Implementation notes

There is no mathematics here beyond Tag 0G7C.
`Stacks.SheafOfModules.KFlatCycles.isFlat_kernel_d_of_kFlat_of_acyclic` concludes flatness of
`kernel (K.d n (n + 1))`, whereas `CyclesIsFlat` asks for flatness of `K.cycles n`.  Those two
objects are both limits of `parallelPair (K.d n (n + 1)) 0` — `kernelIsKernel` and
`HomologicalComplex.cyclesIsKernel`, the latter at the index equality
`(ComplexShape.up ℤ).next n = n + 1` — so `IsLimit.conePointUniqueUpToIso` identifies them and
`AlgebraicGeometry.SheafOfModules.IsFlat.of_iso` transports flatness across.  No new
comparison morphism is built.

The K-flatness hypotheses of the two sides already agree: `CyclesIsFlat` is written with
`Stacks.SheafOfModules.KFlat.KFlat O.O`, Tag 0G7C with
`CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor O.O)`, and
`Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor` is `Iff.rfl`, so the hypothesis is passed
  through
unchanged.

**Universes.**  The ringed topos is taken at `RingedTopos.{v₁, u₁, w₁}` with the three
universes independent, inherited from
`Stacks.Sheaves.DerivedPullback.KFlatPullback.CyclesIsFlat` and not chosen here; Tag 0G7C is
stated at the same generality, so no narrowing happens in this file and the cycles input is
available at an `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — the shape of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`.  `HasSheafify` is the hypothesis
`CyclesIsFlat` carries and `HasWeakSheafify` is what Tag 0G7C asks for; the former implies the
latter.

The transport across the two limit cones is
`Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize` rather than
`AlgebraicGeometry.SheafOfModules.IsFlat.of_iso`: the latter reads flatness off the monoidal
closed structure of `Mod(𝒪)` and so pins the module universe to the site, while the former
reads it off Stacks 05NB and leaves the three universes free.  The two are the same statement
where both apply.

The rest of the file is still written over a `RingedTopos.{u, u, u}`, because
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` and the morphism
`AlgebraicGeometry.RingedToposSiteHom` it takes are, and those narrowings are not this file's
to remove.  What `cyclesIsFlat` no longer does is *add* one.

## References

* [The Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v₁ u₁ w₁ u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullback

/-- **The cycles input of Tag 0G7E holds for every ringed topos.**  This is Tag 0G7C
(`Stacks.SheafOfModules.KFlatCycles.isFlat_kernel_d_of_kFlat_of_acyclic`) transported from
`kernel (M.d n (n + 1))` to `M.cycles n` along the comparison of the two limit cones of
`parallelPair (M.d n (n + 1)) 0`. -/
theorem cyclesIsFlat (O : AlgebraicGeometry.RingedTopos.{v₁, u₁, w₁})
    [O.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
    [HasSheafify O.J AddCommGrpCat.{w₁}]
    [O.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor O.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor O.O).obj M).Additive]
    [∀ (K₁ K₂ :
        CochainComplex (SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf O.O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O.O)
        (ComplexShape.up ℤ)] :
    CyclesIsFlat O := by
  intro M hacyclic hK hflat n
  have hker : AlgebraicGeometry.SheafOfModules.IsFlat.{v₁, u₁, w₁, w₁} (O := O.O)
      (kernel (M.d n (n + 1))) :=
    Stacks.SheafOfModules.KFlatCycles.isFlat_kernel_d_of_kFlat_of_acyclic O.O M hK hacyclic hflat n
  exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize O.O
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (M.d n (n + 1)))
      (M.cyclesIsKernel n (n + 1) (by simp))) hker

section Main

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` with its cycles hypothesis
  discharged by
`cyclesIsFlat`.  Two hypotheses remain, `PullbackPreservesIsFlat` (Stacks 05VD) and
`PullbackPreservesShortExact` (Stacks 0G6R); this declaration records that the third one is
gone, and that it really does unify with the binder at its use site. -/
theorem kFlat_pullbackComplex_of_pullbackPreserves
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (hex : PullbackPreservesShortExact f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj K) :=
  kFlat_pullbackComplex f hmos hpf hex (cyclesIsFlat Y) K hK hflatK

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tag 0G7E for an acyclic complex, on Stacks 05VD alone.**  The pullback of an acyclic
K-flat complex with flat terms is K-flat, assuming only `PullbackPreservesIsFlat`.

Both of the other two inputs of `kFlat_pullbackComplex` are gone here, for different reasons:
`CyclesIsFlat` (Stacks 0G7C) by `cyclesIsFlat`, and `PullbackPreservesShortExact`
(Stacks 0G6R) because the acyclic case does not go through the resolution's kernel sequence at
all — an acyclic complex with flat terms has flat cycles, so it is already in the shape
`kFlat_pullbackComplex_of_isFlat_cycles` consumes, and the short exact sequence whose pullback
needs 0G6R never arises.  So the acyclic case of the statement, like the bounded above case
(`kFlat_pullbackComplex_of_isStrictlyLE`) and the colimit case
(`kFlat_pullbackComplex_of_isColimit`), is one input short of unconditional, and that one input
is Stacks 05VD. -/
theorem kFlat_pullbackComplex_of_acyclic
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlat f)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hMacyc : M.Acyclic)
    (hMk : Stacks.SheafOfModules.KFlat.KFlat Y.O M)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (M.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O ((pullbackComplex f).obj M) :=
  kFlat_pullbackComplex_of_isFlat_cycles f hmos hpf M hflat
    (cyclesIsFlat Y M hMacyc hMk hflat)

end Main

end Stacks.Sheaves.DerivedPullback.KFlatPullback

end

end

