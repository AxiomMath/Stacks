module

public import StacksFrontier.AlgebraicGeometry.LocalIso.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkRingComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPseudoCoherent
public import StacksFrontier.Homology.Perfect.DerivedTensorFibre
public import StacksFrontier.Homology.Perfect.LocalRingFibreVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.Topology.Sheaves.Modules.Skyscraper
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a perfect complex near a point from its derived tensor product with a skyscraper

Let `X` be a Noetherian scheme, `x` a point of `X`, `𝒪_x` the skyscraper sheaf at `x` with value
the residue field `κ(x)` of the local ring `𝒪_{X,x}`, and `K` a perfect object of `D(𝒪_X)`. If
the derived tensor product `K ⊗^𝐋_{𝒪_X} 𝒪_x` has no cohomology at `x` in degree `i`, then the
degree-`i` cohomology of `K` vanishes on an open neighbourhood of `x`; if it has no cohomology at
`x` at all, then `K` vanishes on an open neighbourhood of `x`.

## Main definitions

* `AlgebraicGeometry.residueFieldStalkModule`: the residue field at `x` as a module over the
  stalk of the sheaf of rings at `x`.

## Main results

* `AlgebraicGeometry.exists_mem_isZero_stalkHomology_of_derivedTensor_residueField`:
  the derived-stalk form of [Stacks, Tag 0G03] part (5), one degree at a time.
* `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField`:
  the derived-stalk form of part (6), all degrees at once.

The forms with `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x)` in place of the derived stalk are in
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.DeducingFullyFaithfulness.LocalVanishingCriteria`.

## Implementation notes

The hypothesis is read on the derived stalk at `x`: the derived tensor product with a skyscraper at
`x` has its cohomology concentrated at `x`, and there global cohomology is the stalk.

Taking the derived stalk at `x` turns `⊗^𝐋_{𝒪_X}` into `⊗^𝐋_{𝒪_{X,x}}`, by the derived form of
[Stacks, Tag 01CB], and turns the skyscraper at `x` into its value, so the hypothesis becomes the
vanishing of `H^i(K_x ⊗^𝐋_{𝒪_{X,x}} κ(x))`. The derived stalk `K_x` is pseudo-coherent because `K`
is perfect, hence bounded with coherent cohomology by [Stacks, Tag 0FXU], and over a Noetherian
ring that is pseudo-coherence by [Stacks, Tag 066E]. So [Stacks, Tag 068U] applies at the maximal
ideal of `𝒪_{X,x}`: the element it produces outside the maximal ideal is a unit, and `H^i(K_x)`
vanishes. Finally the degree-`i` cohomology sheaf of `K` is coherent, so a vanishing stalk at `x`
forces vanishing stalks on a neighbourhood of `x`, by [Stacks, Tag 01Y3]; for part (6) just the
finitely many degrees inside the cohomological bounds of `K` need a neighbourhood, and their
intersection is still open.

The stalk of the sheaf of rings is taken in `RingCat`, which is where the derived tensor product of
sheaves of modules puts the scalars of a stalk. Its commutativity, locality and Noetherianness come
from `StacksDraft.StalkRingComparison`. The residue field is written as `κ(𝔪)` for the maximal
ideal of that ring, built through `AlgebraicGeometry.residueFieldModuleCat` because instance
synthesis cannot assemble the module structure at the stalk ring in place.

## References

* [Stacks Project, Tag 0G03](https://stacks.math.columbia.edu/tag/0G03)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StacksDraft.Perfect

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace AlgebraicGeometry

/-- The residue field `κ(p)` of a prime ideal, as a module over the ring. -/
public def residueFieldModuleCat {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ModuleCat.{u} R :=
  ModuleCat.of R p.ResidueField

/-- The residue field `κ(x) = 𝒪_{X,x}/𝔪_x` at a point of a scheme, as a module over the stalk at
`x` of the sheaf of rings, which is the ring over which the derived stalk of a sheaf of modules is
a module. -/
public def residueFieldStalkModule (X : Scheme.{u}) (x : X) :
    ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x)) :=
  residueFieldModuleCat
    (IsLocalRing.maximalIdeal (ToType (StacksDraft.StalkRingComparison.stalkRing X x)))

/-- The skyscraper sheaf `𝒪_x` of `𝒪_X`-modules at `x` with value the residue field `κ(x)`. -/
public def residueFieldSkyscraperSheaf (X : Scheme.{u}) (x : X) :
    SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.skyscraperObj X.ringCatSheaf x (residueFieldStalkModule X x)

/-- The derived tensor product `K ⊗^𝐋_{𝒪_X} 𝒪_x` of `K` with the residue-field skyscraper at
`x`, formed with the derived tensor product of [Stacks, Tag 06YU]. -/
public def derivedTensorResidueFieldSkyscraper (X : Scheme.{u}) (x : X)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).obj
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj
      (residueFieldSkyscraperSheaf X x))

/-- Taking the derived stalk at `x` identifies the cohomology of `K ⊗^𝐋_{𝒪_X} 𝒪_x` with the
cohomology of `K_x ⊗^𝐋_{𝒪_{X,x}} κ(x)`: the derived form of [Stacks, Tag 01CB] turns the sheaf
tensor product into the tensor product over the stalk ring, and the skyscraper at `x` into its
value. -/
private theorem isZero_homology_derivedTensor_residueField_of_derivedStalk
    (X : Scheme.{u}) (x : X) (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) i).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
          (derivedTensorResidueFieldSkyscraper X x K)))) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            (ToType (StacksDraft.StalkRingComparison.stalkRing X x))).tensor.obj
          ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K)).obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) 0).obj
            (residueFieldStalkModule X x)))) := by
  have e : (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (residueFieldSkyscraperSheaf X x) ≅ residueFieldStalkModule X x :=
    SheafOfModules.skyscraperStalkIsoObj X.ringCatSheaf x (residueFieldStalkModule X x)
  refine IsZero.of_iso h ((DerivedCategory.homologyFunctor _ i).mapIso ?_)
  exact (((Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor X.sheaf x).obj
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
        Stacks.SheafOfModules.DerivedTensorStalk.derivedStalkSingleIso X.sheaf x
          (residueFieldSkyscraperSheaf X x))) ≪≫
    Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoGeneral X.sheaf x K
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} X.ringCatSheaf) 0).obj
        (residueFieldSkyscraperSheaf X x))

/-- A coherent cohomology sheaf of `K` with vanishing stalk at `x` has vanishing stalks on a whole
neighbourhood of `x`, by [Stacks, Tag 01Y3]. -/
private theorem exists_mem_forall_isZero_stalkObj
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (i : ℤ)
    (hx : IsZero (SheafOfModules.stalkObj X.ringCatSheaf x
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) := by
  have hcoh : ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      K).IsCoherent :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK).2 i
  have hft : ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj
      K).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨U, hxU, hU⟩ :=
    Stacks.AlgebraicGeometry.Tag01Y3LocalIso.exists_forall_stalk_isZero_of_stalk_isZero
      (R := X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K) x
      ((SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf x _).1 hx)
  exact ⟨U, hxU, fun y hy =>
    (SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf y _).2 (hU y hy)⟩

/-- **The derived-stalk form of [Stacks, Tag 0G03] part (5).** Let `X` be a Noetherian scheme,
`x` a point of `X`, `𝒪_x` the skyscraper at `x` with value the residue field `κ(x)`, and `K` a
perfect object of `D(𝒪_X)`. If the degree-`i` cohomology of the derived stalk at `x` of
`K ⊗^𝐋_{𝒪_X} 𝒪_x` vanishes, then the degree-`i` cohomology sheaf of `K` has vanishing stalk at
every point of an open neighbourhood of `x`. The form with `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x)`, for `x`
closed, is
`exists_mem_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor`,
which reduces to this one. -/
public theorem exists_mem_isZero_stalkHomology_of_derivedTensor_residueField
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) i).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
          (derivedTensorResidueFieldSkyscraper X x K)))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) := by
  have hpc := @Stacks.AlgebraicGeometry.DerivedStalk.isPseudoCoherent_derivedStalk_of_isPerfect
    X inferInstance x (StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing X x) K hK
  have hfib := fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField
    (IsLocalRing.maximalIdeal (ToType (StacksDraft.StalkRingComparison.stalkRing X x)))
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K) hpc i
    (isZero_homology_derivedTensor_residueField_of_derivedStalk X x K i h)
  -- The base ring is named, not left to unification: the stalk ring is the ring of
  -- `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, which is the spelling the local-ring and
  -- commutative-ring instances are keyed on, and the one `hfib` carries.
  have hzero := isZero_homology_of_fibreCohomologyVanishes_maximalIdeal.{u, u}
    (R := ToType (StacksDraft.StalkRingComparison.stalkRing X x))
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj K) hpc i hfib
  refine exists_mem_forall_isZero_stalkObj X x K hK i (IsZero.of_iso hzero ?_)
  exact (((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategoryHomologyIso i).app
    K).symm

/-- **The derived-stalk form of [Stacks, Tag 0G03] part (6).** In the situation of
`exists_mem_isZero_stalkHomology_of_derivedTensor_residueField`, if the derived stalk at `x` of
`K ⊗^𝐋_{𝒪_X} 𝒪_x` has no cohomology in any degree, then `K` is zero on an open neighbourhood of
`x`: every cohomology sheaf of `K` has vanishing stalk at every point of that neighbourhood. The
form with `H^i(X, K ⊗^𝐋_{𝒪_X} 𝒪_x)`, for `x` closed, is
`exists_mem_forall_isZero_stalkHomology_of_isZero_homology_globalSections_derivedTensor`.
-/
public theorem exists_mem_forall_isZero_stalkHomology_of_derivedTensor_residueField
    (X : Scheme.{u}) [IsNoetherian X] (x : X)
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K)
    (h : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) i).obj
        ((SheafOfModules.stalkFunctor X.ringCatSheaf x).mapDerivedCategory.obj
          (derivedTensorResidueFieldSkyscraper X x K)))) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∀ y : X, y ∈ U → ∀ i : ℤ,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) := by
  classical
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK).1
  -- Outside the cohomological bounds of `K` the cohomology sheaf itself vanishes.
  have hout : ∀ i : ℤ, (i < a ∨ b < i) → ∀ y : X,
      IsZero (SheafOfModules.stalkObj X.ringCatSheaf y
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) := by
    intro i hi y
    exact Functor.map_isZero (SheafOfModules.stalkFunctor X.ringCatSheaf y) (hi.elim (ha i) (hb i))
  choose V hxV hV using fun i : ℤ =>
    exists_mem_isZero_stalkHomology_of_derivedTensor_residueField X x K hK i (h i)
  refine ⟨⟨⋂ i ∈ (Finset.Icc a b : Finset ℤ), (V i : Set X.carrier),
    isOpen_biInter_finset fun i _ => (V i).isOpen⟩, Set.mem_biInter fun i _ => hxV i, ?_⟩
  intro y hy i
  by_cases hi : a ≤ i ∧ i ≤ b
  · exact hV i y (Set.mem_iInter₂.1 hy i (Finset.mem_Icc.2 hi))
  · exact hout i (by omega) y

end AlgebraicGeometry

end
