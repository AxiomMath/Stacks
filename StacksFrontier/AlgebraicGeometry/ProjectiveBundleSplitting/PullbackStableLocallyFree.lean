module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StalkSplittingLocallyFree
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelHyperplaneRestriction

/-!
# Pullback keeps a short exact sequence with locally free quotient short exact

Let `0 ⟶ ℱ ⟶ 𝒢 ⟶ ℋ ⟶ 0` be a short exact sequence of modules on a scheme with `ℋ` locally
free. Then it stays short exact after pullback along **any** morphism of schemes, with no
flatness hypothesis on the morphism.

This generalizes `Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_kernelSequence` from
an invertible quotient to a locally free one of any rank — in particular to a finite locally free
quotient, since `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` yields
`SheafOfModules.IsLocallyFree` by instance search. Only the source of the projectivity of the
stalk changes; the rank of the free module plays no part in the lifting argument.

## Main results

* `Stacks.SheafOfModules.isSplitEpi_stalkFunctor_map_of_isLocallyFree`: a short exact sequence of
  sheaves of modules with locally free third term splits at every stalk, read as the second arrow
  being a split epimorphism there.
* `AlgebraicGeometry.mono_pullback_map_kernel_ι_of_isLocallyFree`: pullback keeps the kernel
  inclusion of such a sequence a monomorphism.
* `AlgebraicGeometry.shortExact_map_pullback_of_isLocallyFree`: **the pullback of a short exact
  sequence with locally free third term is short exact.**
* `AlgebraicGeometry.shortExact_map_pullback_kernelSequence_of_isLocallyFree`: the same read off
  an epimorphism onto a locally free module, the shape the invertible version is stated in.

## Implementation notes

**Why the quotient, and not the sub, carries the hypothesis.** Pullback of sheaves of modules is
a left adjoint, so it preserves the cokernel half for free; the content is that it keeps the
kernel inclusion monic. That is read at the stalks, where the surjection onto a locally free —
hence stalkwise free, hence projective — module splits, and an additive functor preserves the
kernel of a split epimorphism. Nothing is asked of the sub.

**The two stalk-module conventions.** The splitting is taken from
`Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactLocallyFree` rather than by
re-running the projective lifting here. Running it again does not work: the lifting lives over
the `CommRingCat`-valued stalk of the structure sheaf with
`LocallyFreeRank.instModuleStalkF`, while `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`
is linear over the `RingCat`-valued one with
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`. The two module structures are
definitionally but not reducibly equal, so `LinearMap.id` cannot even be formed between them, and
the section has to be carried across by
`Stacks.AlgebraicGeometry.ProjEulerSequence.stalkRingLinearOfCommLinear` — which is exactly what
`stalkSplittingOfShortExactLocallyFree` already does. Its `IsLocallyFree` argument is passed
positionally, because the instance is keyed on the sheaf-of-rings spelling: `structureSheafRing X`
and `Stacks.AlgebraicGeometry.ProjEulerSequence.ringSheafOfComm X.sheaf` are equal by `rfl`, but
instance search does not see through that and fails on the second spelling.

**Reducing a general sequence to the kernel sequence.** `S.f` is a kernel of `S.g`, so
`kernel.lift S.g S.f S.zero` is an isomorphism, and `S.f` factors through `kernel.ι S.g` by it.
The lift is written out rather than bound by `have`, which would forget its definition and leave
the comparison with `IsLimit.fac` unprovable.

**A note for whoever next works on the Stacks 02UJ towers.** The tower that Stacks 02UJ consumes
(`Stacks.Chow.chernClassCapExt_eq_esymRec`) is a chain of *quotients* `Q (j+1) ⟶ Q j` with the
invertible piece as the *kernel* at each step, whereas
`Stacks.AlgebraicGeometry.DevissageBounded.HasDevissageWith` is an increasing chain of *subobjects*
with the quotients as *cokernels*. They are opposite presentations of a filtration, so
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_trans'` does not state 02UJ's
splice and no amount of index or `eqToIso` transport makes it do so. What *is* 02UJ's step shape,
on the nose, is `CategoryTheory.FilteredObject.quotStepShortComplex_shortExact`: for a decreasing
filtration the sequence `0 ⟶ gr ⟶ X/F^{i+1} ⟶ X/F^i ⟶ 0` is short exact in any abelian category.
A splice for 02UJ should be built on that, not ported from the dévissage calculus.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

/-- **A short exact sequence of sheaves of modules with locally free third term splits at every
stalk.** The stalk of `G` is free on the index set of a trivialization near the point, hence
projective, so the stalk of `g` admits a section. This is
`Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactLocallyFree` read as a split
epimorphism; see the implementation notes for why the splitting is taken from there rather than
produced again here. -/
theorem isSplitEpi_stalkFunctor_map_of_isLocallyFree
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    {E F G : SheafOfModules.{u} (structureSheafRing X)} {f : E ⟶ F} {g : F ⟶ G}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact)
    (hG : SheafOfModules.IsLocallyFree G) (x : X.carrier) :
    IsSplitEpi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X) x).map g) :=
  let S := @Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactLocallyFree
    _ X.sheaf E F G hG f g hfg hSE x
  IsSplitEpi.mk' ⟨S.s, S.s_g⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-- **Pullback keeps the kernel inclusion of a surjection onto a locally free module a
monomorphism.** At every stalk the surjection splits, because the stalk of a locally free module
is projective, and a module pullback keeps the kernel inclusion of a stalkwise-split surjection
injective. -/
theorem mono_pullback_map_kernel_ι_of_isLocallyFree {X X' : Scheme.{u}} (g : X' ⟶ X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₃ : SheafOfModules.IsLocallyFree S.X₃) :
    Mono ((Scheme.Modules.pullback g).map (kernel.ι S.g)) :=
  Stacks.RingedSpace.mono_modulePullback_map_kernel_ι_of_isSplitEpi_stalk
    g.toLRSHom.toShHom S.g
    fun _ => Stacks.SheafOfModules.isSplitEpi_stalkFunctor_map_of_isLocallyFree
      X.toRingedSpace S.zero hS h₃ _

/-- **The pullback of a short exact sequence of modules with locally free third term is short
exact**, along an arbitrary morphism of schemes and with no flatness hypothesis on it. The
cokernel half is free, pullback being a left adjoint; monicity on the left comes from the
splitting of the sequence at every stalk. -/
theorem shortExact_map_pullback_of_isLocallyFree {X X' : Scheme.{u}} (g : X' ⟶ X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₃ : SheafOfModules.IsLocallyFree S.X₃) :
    (S.map (Scheme.Modules.pullback g)).ShortExact := by
  have hmk := hS.mono_f
  refine AlgebraicGeometry.shortExact_map_pullback_of_mono g hS ?_
  have hk : Mono ((Scheme.Modules.pullback g).map (kernel.ι S.g)) :=
    mono_pullback_map_kernel_ι_of_isLocallyFree g hS h₃
  have hfac : S.f = kernel.lift S.g S.f S.zero ≫ kernel.ι S.g := (kernel.lift_ι _ _ _).symm
  have ha : hS.fIsKernel.lift (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)) ≫ S.f
      = kernel.ι S.g := by
    simpa using hS.fIsKernel.fac (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g))
      WalkingParallelPair.zero
  have : IsIso (kernel.lift S.g S.f S.zero) := by
    refine ⟨hS.fIsKernel.lift (KernelFork.ofι (kernel.ι S.g) (kernel.condition S.g)), ?_, ?_⟩
    · refine (cancel_mono S.f).1 ?_
      rw [Category.assoc, ha, kernel.lift_ι, Category.id_comp]
    · refine (cancel_mono (kernel.ι S.g)).1 ?_
      rw [Category.assoc, kernel.lift_ι, ha, Category.id_comp]
  rw [hfac, Functor.map_comp]
  exact mono_comp _ _

/-- **The same read off an epimorphism onto a locally free module.** This is the shape
`Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_kernelSequence` is stated in, with the
invertibility of the quotient weakened to local freeness. -/
theorem shortExact_map_pullback_kernelSequence_of_isLocallyFree {X X' : Scheme.{u}} (g : X' ⟶ X)
    {E L : X.Modules} (q : E ⟶ L) (hq : Epi q) (hL : SheafOfModules.IsLocallyFree L) :
    ((ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
      (Scheme.Modules.pullback g)).ShortExact :=
  have := hq
  shortExact_map_pullback_of_isLocallyFree g { exact := ShortComplex.exact_kernel q } hL

end AlgebraicGeometry

end
