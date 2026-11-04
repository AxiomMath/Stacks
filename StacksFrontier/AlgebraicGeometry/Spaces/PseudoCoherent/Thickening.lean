module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Thickening
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedQuasicoherentFiniteOrder

/-!
# Stacks 0DL3: pseudo-coherence descends along a finite-order thickening of algebraic spaces

Let `S` be a scheme, let `i : Z ⟶ X'` be a finite-order thickening of algebraic spaces over `S`,
and let `K'` be an object of `D(𝒪_{X'})` such that `K = Li^*K'` is pseudo-coherent. Then `K'` is
pseudo-coherent.

Here `D(𝒪_{X'})` is the derived category of `𝒪_{X'}`-modules on the small étale site of `X'`,
pseudo-coherence is Stacks 08FT on that ringed site, `Li^*` is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` (Stacks 06YY for the morphism of small
étale ringed topoi of Stacks 03G8), and the thickening is a closed subspace `Z` of `X'` satisfying
`AlgebraicGeometry.Space.IsFiniteOrderThickening` (Stacks 05ZK), with `i` its inclusion.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isPseudoCoherentFrom_of_derivedPullback_representedSpaceMap_of_isFiniteOrderThickening`:
  the case of schemes, on represented algebraic spaces.
* `isPseudoCoherent_of_derivedPullback_of_isFiniteOrderThickening`:
  **Stacks 0DL3**.

## The argument

It is the source's.

1. *Quasi-coherence.* `K = Li^*K'` is pseudo-coherent, hence lies in `D_QCoh(𝒪_Z)` (Stacks
   08JL), hence `K'` lies in `D_QCoh(𝒪_{X'})` by
   `qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFiniteOrderThickening`,
   the dévissage of the first paragraph of the source's proof.
2. *Étale locality.* Pseudo-coherence may be checked after derived pullback to the algebraic
   spaces `h_V` represented by the étale charts `V` of `X'`
   (`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_charts`). Over such a chart the thickening
   pulls back to a finite-order thickening of schemes `j : V₀ ⟶ V`
   (`AlgebraicGeometry.Space.exists_finiteOrderThickening_chart_pullback`), and the derived
   pullback of `K'|_V` along `j` is the derived pullback of `K` to `V₀`, which is pseudo-coherent
   because derived pullback preserves pseudo-coherence of objects of `D_QCoh` (Stacks 08H4).
3. *The case of schemes.* On `h_V` the object `K'|_V` of `D_QCoh` is `ε^*` of a K-flat complex
   `E` on `V` (Stacks 071Q); derived pullback along `h_j` commutes with `ε^*` on `E` (Remark
   08GH, in the form `nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso`),
   pseudo-coherence crosses `ε^*` in both directions (Stacks 08HE), and on the scheme `V` the
   statement is Stacks 0DJX, `Stacks.Thickenings.isPseudoCoherent_of_derivedPullback`.

## References

* [Stacks Project, Tag 0DL3](https://stacks.math.columbia.edu/tag/0DL3)
* [Stacks Project, Tag 0DJX](https://stacks.math.columbia.edu/tag/0DJX)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Pseudo-coherence descends along a finite-order thickening of schemes, read on represented
algebraic spaces.** Let `q : T' ⟶ T` be a morphism of the big fppf site whose underlying morphism
of schemes is a finite-order thickening, and let `G` be an object of `D_QCoh` of `h_T`. If every
`Lh_q^*G` is `m`-pseudo-coherent, so is `G`.

`G` is `ε^*` of a K-flat complex `E` on `T` (Stacks 071Q), `Lh_q^*G` is `ε^*` of the pullback of
`E` (Remark 08GH), pseudo-coherence crosses `ε^*` (Stacks 08HE), and on `T` this is Stacks 0DJX. -/
theorem isPseudoCoherentFrom_of_derivedPullback_representedSpaceMap_of_isFiniteOrderThickening
    {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hq : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map q))
    (G : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hG : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) G)
    (h :
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (representedSpaceMap B S hS q)
      ∀ m : ℤ, (smallEtaleRingedSite B S hS (yoneda.obj T')
        (isAlgebraicSpace_yoneda B S hS T')).IsPseudoCoherentFrom
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q)).obj G) m)
    (m : ℤ) :
    (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom G m := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS q)
  obtain ⟨K, hK, hKf, -, ⟨eG⟩⟩ := exists_kFlatComplex_representedAssociatedModule_iso B S hS T G hG
  let r := ((BigFppfOver.toScheme B S hS).map q).toLRSHom.toShHom
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso B S hS q
    K hK hKf
  have h₁ : ∀ k : ℤ, RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
      (X := ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace)
      (((RingedSpaceModuleAdjunction.modulePullback r).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) k := fun k =>
    (isPseudoCoherentFrom_representedAssociatedModule_iff B S hS T' _ k).1
      (RingedSite.isPseudoCoherentFrom_of_iso _ k (h k)
        (e.symm ≪≫
          (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q)).mapIso eG))
  have h₂ : RingedSpace.IsPseudoCoherent
      (X := ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback r).obj
        (DerivedCategory.Q.obj K)) :=
    (RingedSpace.isPseudoCoherent_iff_forall.{u, u + 1} _).2 fun k =>
      ⟨_, h₁ k, ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat r K hK).symm⟩⟩
  have h₃ := Stacks.Thickenings.isPseudoCoherent_of_derivedPullback
    ((BigFppfOver.toScheme B S hS).map q) hq _ h₂
  have h₄ := RingedSpace.isPseudoCoherentComplexFrom_of_iso.{u, u + 1} _ m
    ((RingedSpace.isPseudoCoherent_iff_forall.{u, u + 1} _).1 h₃ m) K (Iso.refl _)
  exact RingedSite.isPseudoCoherentFrom_of_iso _ m
    ((isPseudoCoherentFrom_representedAssociatedModule_iff B S hS T K m).2 h₄) eG.symm

/-- **Stacks 0DL3.** Let `S` be a scheme and let `i : Z ⟶ X'` be a finite-order thickening of
algebraic spaces over `S`. Let `K'` be an object of `D(𝒪_{X'})` such that `K = Li^*K'` is
pseudo-coherent. Then `K'` is pseudo-coherent.

The thickening is the inclusion `AlgebraicGeometry.Space.subspaceInclusion` of a closed subspace
`Z` of `X'` which is a finite-order thickening (Stacks 05ZK), `Li^*` is the derived pullback of
Stacks 06YY along it, and pseudo-coherence is Stacks 08FT on the small étale ringed sites. -/
@[stacks 0DL3]
theorem isPseudoCoherent_of_derivedPullback_of_isFiniteOrderThickening
    {X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
    (hZ : IsFiniteOrderThickening B S hS X' Z.1)
    (K' : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2))
    (hK :
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (subspaceInclusion B S hS X' Z)
      (smallEtaleRingedSite B S hS Z.1.toFunctor Z.2.1).IsPseudoCoherent
        ((smallEtaleDerivedModulePullback B S hS (subspaceInclusion B S hS X' Z)).obj K')) :
    (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K' := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (subspaceInclusion B S hS X' Z)
  have hq := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ _ hK
  have hQ := qcohDerived_of_qcohDerived_smallEtaleDerivedModulePullback_of_isFiniteOrderThickening
    B S hS Z hZ K' hq
  have hK' := (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hK
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ K').2 fun m => ?_
  refine isPseudoCoherentFrom_of_charts B S hS K' m fun U => ⟨⊤, ?_, fun V _ _ => ?_⟩
  · rw [Sieve.generate_top]
    exact GrothendieckTopology.top_mem _ U
  obtain ⟨U₀, j, p, hpb, hthick⟩ :=
    exists_finiteOrderThickening_chart_pullback B S hS hZ V.1.left V.1.hom V.property
  have hG := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS
    (chartToSpace B S hS X' V) K' hQ
  refine isPseudoCoherentFrom_of_derivedPullback_representedSpaceMap_of_isFiniteOrderThickening
    B S hS j hthick _ hG (fun k => ?_) m
  let pSp : (⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨Z.1.toFunctor, Z.2.1⟩ := ObjectProperty.homMk p
  have hsq : pSp ≫ subspaceInclusion B S hS X' Z =
      representedSpaceMap B S hS j ≫ chartToSpace B S hS X' V :=
    ObjectProperty.hom_ext _ hpb.w
  exact RingedSite.isPseudoCoherentFrom_of_iso _ k
    (isPseudoCoherentFrom_smallEtaleDerivedModulePullback B S hS pSp _ hq k (hK' k))
    ((((smallEtaleDerivedPullbackData B S hS).compIso (representedSpaceMap B S hS j)
        (chartToSpace B S hS X' V)).app K').symm ≪≫
      ((smallEtaleDerivedPullbackData B S hS).triangle hsq).app K')

end AlgebraicGeometry.Space
