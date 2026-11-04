module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Tor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZero
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# The top cohomology of the derived tensor product of two modules

Let `(C, O)` be a ringed site and let `F` and `G` be sheaves of `O`-modules. Placing both in
degree zero of `D(Mod(O))`, the derived tensor product `F[0] ⊗^L_O G[0]` lies in `D^{≤ 0}` and
its cohomology in the top degree is the ordinary tensor product:

`H⁰(F[0] ⊗^L_O G[0]) ≅ F ⊗_O G`,

with **no flatness hypothesis on either factor**. Shifting the second factor into degree one,
`H¹(F[0] ⊗^L_O G[1]) ≅ F ⊗_O G`.

`Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingleIso` already computes this `H⁰`
when the left factor placed in degree zero is K-flat. What is added here is the general case:
the ordinary tensor product is the *top* cohomology of the derived one, which is the right
exactness of `· ⊗_O G` rather than its exactness.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.exists_flat_resolution`: a module placed in
  degree zero is quasi-isomorphic to a complex of flat modules vanishing in positive degrees.
* `Stacks.SheafOfModules.DerivedTensorProduct.nonempty_homologyZeroTensorIso`: the isomorphism
  `H⁰(F[0] ⊗^L_O G[0]) ≅ F ⊗_O G`.
* `Stacks.SheafOfModules.DerivedTensorProduct.nonempty_homologyOneTensorSingleOneIso`: the same
  isomorphism with the second factor in degree one, `H¹(F[0] ⊗^L_O G[1]) ≅ F ⊗_O G`.

## Implementation notes

The proof is the computation of `Stacks.DerivedTensor.RingedSite.torOneIso` run in degree zero
instead of degree `-1`, followed by the one extra step that degree zero needs. Resolve `F[0]`
by a complex `P` of flat modules vanishing in positive degrees (Tag 05T7, with the flat cover
of `Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat`); such a complex is K-flat
by Tag 06YQ, so the left K-flat comparison of the derived tensor product computes
`F[0] ⊗^L_O G[0]` as the total tensor complex, which for a second factor concentrated in degree
zero is the termwise complex `p ↦ P^p ⊗_O G`
(`CochainComplex.KFlatBifunctor.totalSingleIso`). The extra step is
`Stacks.DerivedTensor.RingedSite.isIso_homologyMap_mapHomologicalComplex` at the right exact
functor `· ⊗_O G`: a functor preserving finite colimits carries a quasi-isomorphism between
complexes vanishing in positive degrees to an isomorphism on degree-zero cohomology, so the
degree-zero cohomology of `p ↦ P^p ⊗_O G` is that of `p ↦ (F[0])^p ⊗_O G`, which is `F ⊗_O G`.

The degree-one statement is bookkeeping: `G[1]` is `G[0]` shifted by `-1`, the derived tensor
product commutes with that shift in its second variable
(`Stacks.SheafOfModules.DerivedTensorProduct.commShift_right`), and `H¹` of a `(-1)`-shift is
`H⁰`, the homology functors of the derived category forming a shift sequence.

The statements are `Nonempty` of an isomorphism rather than a construction because the
resolution is only known to exist; nothing below depends on a choice of it. All the site's
universes are equal, which is where flat resolutions are available.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

variable {Y : RingedSite.{u, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **A flat resolution of a module placed in degree zero.** Every sheaf of `O`-modules `F`
admits a quasi-isomorphism `P ⟶ F[0]` from a cochain complex `P` of *flat* `O`-modules which
vanishes in positive degrees. This is [Stacks, Tag 05T7] applied to the class of flat modules,
whose covering property is
`Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat`. -/
theorem exists_flat_resolution (F : RingedSite.Modules.{u, u, u} Y) :
    ∃ (P : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ)
      (p : P ⟶ (HomologicalComplex.single (RingedSite.Modules.{u, u, u} Y)
        (ComplexShape.up ℤ) 0).obj F),
      QuasiIso p ∧ P.IsStrictlyLE 0 ∧
        ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i) := by
  have hF := (inferInstance : CochainComplex.IsStrictlyLE
    ((HomologicalComplex.single (RingedSite.Modules.{u, u, u} Y) (ComplexShape.up ℤ) 0).obj F) 0)
  obtain ⟨P, p, -, hp, hflat, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop
      (Stacks.DerivedTensor.RingedSite.flatModules Y.O)
      (fun M => by
        obtain ⟨N, π, hN, hπ⟩ :=
          Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat Y.O M
        exact ⟨N, hN, π, hπ⟩) 0).1
      ((HomologicalComplex.single (RingedSite.Modules.{u, u, u} Y)
        (ComplexShape.up ℤ) 0).obj F)
  exact ⟨P, p, hp, hLE, hflat⟩

/-- **The degree-zero cohomology of the derived tensor product of two modules is their ordinary
tensor product**, `H⁰(F[0] ⊗^L_O G[0]) ≅ F ⊗_O G`, with no flatness hypothesis on either
factor. See the module documentation for the proof. -/
theorem nonempty_homologyZeroTensorIso (T : DerivedTensorProduct.{u, u, u, d} Y)
    (F G : RingedSite.Modules.{u, u, u} Y) :
    Nonempty ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj
        ((T.tensor.obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj F)).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G) := by
  obtain ⟨P, p, hp, hLE, hflat⟩ := exists_flat_resolution (Y := Y) F
  have := hp
  have := hLE
  have hPk : IsKFlat Y.O P :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O P ⟨0, hLE⟩ hflat
  have hcol := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj Y.O G
  have hiso : IsIso (HomologicalComplex.homologyMap
      ((((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G).mapHomologicalComplex
        (ComplexShape.up ℤ)).map p) 0) :=
    have : IsIso (HomologicalComplex.homologyMap p 0) :=
      (quasiIsoAt_iff_isIso_homologyMap p 0).mp inferInstance
    HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero _ p
  refine ⟨(DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 0).mapIso
      ((T.tensor.mapIso (asIso (DerivedCategory.Q.map p))).app
        (DerivedCategory.Q.obj ((HomologicalComplex.single (RingedSite.Modules.{u, u, u} Y)
          (ComplexShape.up ℤ) 0).obj G))).symm ≪≫
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 0).mapIso
      (T.comparisonLeft P _ hPk) ≪≫
    (DerivedCategory.homologyFunctorFactors (RingedSite.Modules.{u, u, u} Y) 0).app _ ≪≫
    (HomologicalComplex.homologyFunctor (RingedSite.Modules.{u, u, u} Y)
      (ComplexShape.up ℤ) 0).mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P G) ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    HomologicalComplex.homologyMapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G)
        (ComplexShape.up ℤ) 0).app F) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G).obj F)⟩

/-- **The derived tensor product of a module in degree zero with a module in degree one has
first cohomology the ordinary tensor product**, `H¹(F[0] ⊗^L_O G[1]) ≅ F ⊗_O G`.

`G[1]` is `G[0]` shifted by `-1`, the derived tensor product commutes with that shift in its
second variable, and `H¹` of a `(-1)`-shift is `H⁰`; so this is
`Stacks.SheafOfModules.DerivedTensorProduct.nonempty_homologyZeroTensorIso`. -/
theorem nonempty_homologyOneTensorSingleOneIso (T : DerivedTensorProduct.{u, u, u, d} Y)
    (F G : RingedSite.Modules.{u, u, u} Y) :
    Nonempty ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 1).obj
        ((T.tensor.obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj F)).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 1).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj F).obj G) := by
  obtain ⟨e⟩ := nonempty_homologyZeroTensorIso T F G
  refine ⟨(DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 1).mapIso
      ((T.tensor.obj ((DerivedCategory.singleFunctor
          (RingedSite.Modules.{u, u, u} Y) 0).obj F)).mapIso
        (((DerivedCategory.singleFunctors (RingedSite.Modules.{u, u, u} Y)).shiftIso
          (-1) 1 0 (by ring)).app G).symm) ≪≫
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 1).mapIso
      (((T.tensor.obj ((DerivedCategory.singleFunctor
          (RingedSite.Modules.{u, u, u} Y) 0).obj F)).commShiftIso (-1 : ℤ)).app
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G)) ≪≫
    ?_ ≪≫ e⟩
  exact (Functor.shiftIso (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 0)
    (-1) 1 0 (by ring)).app _

end Stacks.SheafOfModules.DerivedTensorProduct

end
