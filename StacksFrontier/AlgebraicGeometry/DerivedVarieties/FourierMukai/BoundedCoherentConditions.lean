module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkDerivedTensorTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectBoundedCoherentTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionFlatOver
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.StacksAttribute

/-!
# The four conditions under which a Fourier-Mukai functor preserves `D^b_Coh`

Let `S` be a Noetherian scheme, let `X` and `Y` be of finite type over `S` and let
`K ∈ D^b_Coh(𝒪_{X ×_S Y})`. [Stacks, Tag 0FYU] asserts that the Fourier-Mukai functor
`Φ_K(M) = R pr_{2,*}(L pr_1^* M ⊗^𝐋 K)` carries `D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_Y)` as soon as
one of the following holds:

1. the support of every `H^i(K)` is proper over `Y`, and `K` has finite Tor dimension as an
   object of `D(pr_1^{-1}𝒪_X)`;
2. `K` is represented by a bounded complex of coherent modules, flat over `X`, with support
   proper over `Y`;
3. the support of every `H^i(K)` is proper over `Y`, and `X` is regular;
4. `K` is perfect, the support of every `H^i(K)` is proper over `Y`, and `Y ⟶ S` is flat;

and that in each case the support requirement is automatic when `X ⟶ S` is proper. This file
proves the whole statement.

## Main results

* `AlgebraicGeometry.fourierMukai_derivedCategoryBBounded`: **[Stacks, Tag 0FYU].**
* `AlgebraicGeometry.isGE_fourierMukaiTensor_of_hasTorAmplitude`: Tor amplitude of `K` over
  `pr_1^{-1}𝒪_X` in `[a, b]` bounds `L pr_1^* M ⊗^𝐋 K` below by `a + n` when `M` is in
  `D^{≥ n}`. This is case (1) of the source's proof.
* `AlgebraicGeometry.hasFiniteTorDimension_of_flatOver_representative`: a bounded complex of
  modules flat over `X` has finite Tor dimension over `pr_1^{-1}𝒪_X`, which is how the source
  reduces case (2) to case (1).
* `AlgebraicGeometry.isBoundedBelow_fourierMukaiTensor_of_isRegular` and
  `AlgebraicGeometry.isBoundedBelow_fourierMukaiTensor_of_isPerfect_of_flat`: the bound below in
  cases (3) and (4).
* `AlgebraicGeometry.isProperOver_supp_homology_fourierMukaiTensor`: the supports of the
  cohomology sheaves of `L pr_1^* M ⊗^𝐋 K` are proper over `Y` when those of `K` are.
* `AlgebraicGeometry.derivedCategoryBBounded_fourierMukai_of_isGE`: the part of the proof common
  to the four cases, with [Stacks, Tag 02O5] discharged.

## Implementation notes

*The common part.* The source shows in all four cases that `T = L pr_1^* M ⊗^𝐋 K` has coherent
cohomology sheaves, is bounded above, has cohomology supported in a closed subset proper over
`Y`, and is bounded below, and then applies [Stacks, Tag 08E2] to `pr₂`. Coherence and the bound
above are `AlgebraicGeometry.derivedCategoryBBounded_fourierMukai_of_isProperOver_supp`, which
asks for the remaining two facts and for [Stacks, Tag 02O5] in the affine-base form; the latter
is the theorem
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`. The support
of `H^i(T)` is contained in the union of the supports of the finitely many nonzero `H^j(K)`,
because at a point outside that union the stalk of `K` vanishes in the derived category and the
derived tensor product commutes with stalks (`notMem_supp_homology_derivedTensor`); a finite
union of closed subsets proper over `Y` is proper over `Y` by [Stacks, Tag 0CYR].

*Case (1).* Finite Tor dimension over `pr_1^{-1}𝒪_X` is
`Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension` ([Stacks, Tag 08CG]) on the
inverse-image ringed space `(X ×_S Y, pr_1^{-1}𝒪_X)`, read at
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` — the same spelling as relative
perfectness, [Stacks, Tag 0DI0]. Following the source, the bound uses [Stacks, Tag 08DE]
(`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedMixedTensorIso`): after restriction
of scalars, `K ⊗^𝐋 L pr_1^* M ≅ K ⊗^𝐋_{pr_1^{-1}𝒪_X} pr_1^{-1} M`, and the inverse image
`pr_1^{-1}` is exact. The inverse-image ringed space and the restriction of scalars of
[Stacks, Tag 08DE] are those of [Stacks, Tag 0DI0] on the nose; restriction of scalars commutes
with cohomology and reflects zero objects, so the bound passes back.

*Case (2).* The terms of the complex, read over `pr_1^{-1}𝒪_X`, are flat sheaves of modules
(`AlgebraicGeometry.Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver`), so [Stacks, Tag 08CI]
gives Tor amplitude in the interval where the complex lives; the cohomology sheaves of `K` are
subquotients of the terms, so their supports are proper over `Y`.

*Cases (3) and (4).* Here the bound below is reached without passing through `pr_1^{-1}𝒪_X`,
as the conclusion only needs `T` bounded below. In case (3) every object of `D^b_Coh(𝒪_X)` is
perfect ([Stacks, Tag 0FDC]), hence so is its derived pullback
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`), which has
finite Tor dimension on the quasi-compact scheme `X ×_S Y`; in case (4) `K` itself is perfect,
and `pr₁` is flat as a base change of `Y ⟶ S`, so `L pr_1^*` is exact and preserves the bound
below of `M`. In both a factor of finite Tor dimension tensored with a bounded-below object is
bounded below. This avoids the source's appeal in case (3) to the finiteness of the Krull
dimension of the rings `A`, which a regular Noetherian ring need not have.

*The final assertion.* When `X ⟶ S` is proper so is `pr₂`, and every closed subset of
`X ×_S Y` is then proper over `Y`; this covers the support requirement in each of the four
forms at once.

## References

* [Stacks Project, Tag 0FYU](https://stacks.math.columbia.edu/tag/0FYU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace StacksPullbackFactorization

universe u

-- Sheafification on the opens of a space is the instance of the small site here; the instance for
-- enlarged coefficients would make the abelian structures built from it differ by unfolding.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance] Stacks.SheafOfModules.KFlatStalkCriterion.monoidalStalkModuleCat
  Stacks.SheafOfModules.KFlatStalkCriterion.monoidalPreadditiveStalkModuleCat
  Stacks.SheafOfModules.DerivedTensorStalk.stalkKFlatQ_isLocalization
  Stacks.SheafOfModules.DerivedTensorStalk.stalkKFlatQLeft_isLocalization
  SheafOfModules.monoidalCategorySheafTensor

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The first projection `pr₁ : X ×_S Y ⟶ X` as a morphism of ringed spaces, the form in which
[Stacks, Tag 08DE] and the derived pullback of [Stacks, Tag 06YJ] take it. -/
abbrev fourierMukaiFst : (Limits.pullback f g).toRingedSpace ⟶ X.toRingedSpace :=
  (Limits.pullback.fst f g).toLRSHom.toShHom

/-! ### Restriction of scalars to `pr_1^{-1}𝒪_X` and the inverse image `pr_1^{-1}` -/

/-- **Restriction of scalars along `pr_1^{-1}𝒪_X ⟶ 𝒪_{X ×_S Y}` reflects a bound below.** It
is exact, so it commutes with the cohomology functors, and it is faithful, so it reflects zero
objects. -/
theorem isGE_of_isGE_derivedRestrictTensor (E : DerivedCategory (Limits.pullback f g).Modules)
    (n : ℤ) (h : ((Stacks.Cohomology.MixedDerivedTensor.derivedRestrictTensor
        (ringedToposSiteHom (fourierMukaiFst f g))).obj E).IsGE n) : E.IsGE n := by
  let F := Stacks.Cohomology.MixedDerivedTensor.restrictToInvRing
    (ringedToposSiteHom (fourierMukaiFst f g))
  obtain ⟨_, _⟩ : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    (exactFunctor_iff _).1 (Stacks.Cohomology.MixedDerivedTensor.exactFunctor_restrictToInvRing
      (ringedToposSiteHom (fourierMukaiFst f g)))
  have key : ∀ A : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.ToposBridge.ringedTopos (Limits.pullback f g).toRingedSpace).O),
      IsZero (F.obj A) → IsZero A := fun A hA => by
    rw [IsZero.iff_id_eq_zero] at hA ⊢
    exact Functor.zero_of_map_zero F (𝟙 A) (by rwa [F.map_id])
  exact (DerivedCategory.isGE_iff _ n).2 fun i hi =>
    key _ (((DerivedCategory.isGE_iff _ n).1 h i hi).of_iso
      ((F.mapDerivedCategoryHomologyIso i).app E).symm)

/-- **The inverse image `pr_1^{-1} : D(𝒪_X) ⥤ D(pr_1^{-1}𝒪_X)` preserves a bound below.** It is
the derived pullback along the geometric half of the factorization of `pr₁` through
`(X ×_S Y, pr_1^{-1}𝒪_X)`, whose degreewise pullback is the exact inverse image of sheaves of
modules. -/
theorem isGE_derivedPullback_auxHomG
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.ToposBridge.ringedTopos X.toRingedSpace).O)))
    (n : ℤ) (hM : M.IsGE n) :
    letI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      (auxHomG (ringedToposSiteHom (fourierMukaiFst f g))) (isMorphismOfSites (fourierMukaiFst f g))
    ((Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
      (X := auxTopos (ringedToposSiteHom (fourierMukaiFst f g)))
      (Y := Stacks.ToposBridge.ringedTopos X.toRingedSpace)
      (auxHomG (ringedToposSiteHom (fourierMukaiFst f g)))).obj M).IsGE n := by
  have := Stacks.Sheaves.InverseImageExactness.preservesFiniteLimits_pullbackTopos_auxHomG
    (ringedToposSiteHom (fourierMukaiFst f g)) (isMorphismOfSites (fourierMukaiFst f g))
  have := Stacks.Sheaves.InverseImageExactness.preservesFiniteColimits_pullbackTopos_auxHomG
    (ringedToposSiteHom (fourierMukaiFst f g))
  let := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      (auxHomG (ringedToposSiteHom (fourierMukaiFst f g))) (isMorphismOfSites (fourierMukaiFst f g))
  exact Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj
    (auxHomG (ringedToposSiteHom (fourierMukaiFst f g))) M n hM

/-! ### Supports of cohomology sheaves -/

/-- A point lies outside the support of a sheaf of modules exactly when the stalk there is a
zero module. -/
theorem notMem_supp_iff_isZero_stalkFunctor {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
    (E : SheafOfModules.{u} O) (x : T) :
    x ∉ SheafOfModules.supp E ↔
      IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj E) := by
  refine (not_congr (SheafOfModules.mem_supp_iff_nontrivial_stalk E x)).trans ?_
  refine not_nontrivial_iff_subsingleton.trans ?_
  refine AddCommGrpCat.isZero_iff_subsingleton.symm.trans ?_
  exact (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff O x E).symm

/-- **A point at which every cohomology sheaf of `K` vanishes lies outside the support of every
cohomology sheaf of `L ⊗^𝐋 K`.** The derived stalk of `K` at such a point has no cohomology, so
it is zero in `D(𝒪_z)`; the derived tensor product commutes with stalks
(`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkObjIso`), and tensoring with a zero
object gives a zero object. -/
theorem notMem_supp_homology_derivedTensor (Z : Scheme.{u}) (L K : DerivedCategory Z.Modules)
    (z : Z)
    (hz : ∀ j : ℤ, z ∉ SheafOfModules.supp ((DerivedCategory.homologyFunctor Z.Modules j).obj K))
    (i : ℤ) :
    z ∉ SheafOfModules.supp ((DerivedCategory.homologyFunctor Z.Modules i).obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        Z.toRingedSpace.sheaf).obj L).obj K)) := by
  let R : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u} := Z.toRingedSpace.sheaf
  let St := AlgebraicGeometry.SheafOfModules.stalkFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) z
  let := Stacks.SheafOfModules.DerivedTensorStalk.stalkFunctor_preservesFiniteColimits R z
  have hKz : IsZero (St.mapDerivedCategory.obj K) := by
    rw [DerivedCategory.isZero_iff_forall_isZero_homology]
    intro j
    exact ((notMem_supp_iff_isZero_stalkFunctor _ _ z).1 (hz j)).of_iso
      ((St.mapDerivedCategoryHomologyIso j).app K)
  have hRHS : IsZero (((CochainComplex.KFlatBifunctor.derivedBifunctor
      (MonoidalCategory.curriedTensor
        (ModuleCat.{u} (Stacks.SheafOfModules.DerivedTensorStalk.stalkRing R z)))).obj
        (St.mapDerivedCategory.obj L)).obj (St.mapDerivedCategory.obj K)) := by
    obtain ⟨s, hs⟩ := CochainComplex.KFlatBifunctor.derivedBifunctor_exact_right
      (MonoidalCategory.curriedTensor
        (ModuleCat.{u} (Stacks.SheafOfModules.DerivedTensorStalk.stalkRing R z)))
      (St.mapDerivedCategory.obj L)
    let := s
    exact Functor.map_isZero _ hKz
  have e2 : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj L).obj K) ≅
      ((CochainComplex.KFlatBifunctor.derivedBifunctor
        (Stacks.SheafOfModules.Tensor.sheafTensor R)).obj L).obj K :=
    (((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso R).app L).app K).symm
  have hT : IsZero (St.mapDerivedCategory.obj
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj L).obj K)) :=
    hRHS.of_iso (St.mapDerivedCategory.mapIso e2 ≪≫
      Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkObjIso R z L K)
  rw [DerivedCategory.isZero_iff_forall_isZero_homology] at hT
  exact (notMem_supp_iff_isZero_stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf R) _ z).2
    ((hT i).of_iso ((St.mapDerivedCategoryHomologyIso i).app _).symm)

/-- **The support of `H^i` of a complex is contained in the support of its term in degree `i`**,
`H^i` being a subquotient of that term and the stalk functor being exact. -/
theorem supp_homology_Q_obj_subset (Z : Scheme.{u}) (C : CochainComplex Z.Modules ℤ) (i : ℤ) :
    SheafOfModules.supp ((DerivedCategory.homologyFunctor Z.Modules i).obj
      (DerivedCategory.Q.obj C)) ⊆ SheafOfModules.supp (C.X i) := by
  intro z hz
  by_contra hzC
  let R : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u} := Z.toRingedSpace.sheaf
  let St := AlgebraicGeometry.SheafOfModules.stalkFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) z
  let := Stacks.SheafOfModules.DerivedTensorStalk.stalkFunctor_preservesFiniteColimits R z
  have hX : IsZero (((St.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X i) :=
    (notMem_supp_iff_isZero_stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf R) _ z).1 hzC
  have hH : IsZero (((St.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hX
  have hD : IsZero (St.obj ((DerivedCategory.homologyFunctor Z.Modules i).obj
      (DerivedCategory.Q.obj C))) :=
    hH.of_iso (((St.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (St.mapDerivedCategoryFactors.app C) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _)
  exact (notMem_supp_iff_isZero_stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf R) _ z).2
    hD hz

/-! ### The bound below in case (1) -/

/-- The bound below of a derived tensor product does not depend on the order of the factors, by
the symmetry of [Stacks, Tag 0FPB]. -/
theorem isGE_derivedTensor_swap (Z : RingedSpace.{u, u})
    (A B : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) (n : ℤ)
    (h : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj A).obj
      B).IsGE n) :
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj B).obj
      A).IsGE n := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.sheaf
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.sheaf
  exact DerivedCategory.TStructure.t.isGE_of_iso (β_ A B) n

/-- **Case (1) of [Stacks, Tag 0FYU]: the bound below.** If `K`, viewed in `D(pr_1^{-1}𝒪_X)`,
has Tor amplitude in `[a, b]` and `M ∈ D^{≥ n}(𝒪_X)`, then
`L pr_1^* M ⊗^𝐋 K ∈ D^{≥ a + n}(𝒪_{X ×_S Y})`.

After restriction of scalars to `pr_1^{-1}𝒪_X`, [Stacks, Tag 08DE] identifies
`K ⊗^𝐋 L pr_1^* M` with `K ⊗^𝐋_{pr_1^{-1}𝒪_X} pr_1^{-1}M`; the inverse image keeps `M` in
`D^{≥ n}`, and the Tor bound of `K` gives `D^{≥ a + n}` (`isGE_tensor_of_hasTorAmplitudeGE`). -/
theorem isGE_fourierMukaiTensor_of_hasTorAmplitude
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (a b : ℤ)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj K) a b)
    (M : DerivedCategory X.Modules) (n : ℤ) (hM : M.IsGE n) :
    ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)).IsGE (a + n) := by
  have hW := isGE_derivedPullback_auxHomG f g M n hM
  have hK' := Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_hasTorAmplitude _ _ a b hK
  rw [Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_eq_site] at hK'
  have hamp := Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE
    (Stacks.Cohomology.TorAmplitude.derTensorSite
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base))
    _ _ a n hK' hW
  have h1 : ((spaceDerivedTensorInverseImage (fourierMukaiFst f g)).obj (K, M)).IsGE (a + n) := hamp
  have h2 : ((spaceDerivedTensorPullback (fourierMukaiFst f g)).obj (K, M)).IsGE (a + n) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((derivedMixedTensorIso (fourierMukaiFst f g)).app (K, M)).symm (a + n)
  have h3 : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Limits.pullback f g).toRingedSpace.sheaf).obj K).obj
        ((fourierMukaiPullback f g).obj M)).IsGE (a + n) :=
    isGE_of_isGE_derivedRestrictTensor f g _ _ h2
  exact isGE_derivedTensor_swap (Limits.pullback f g).toRingedSpace _ _ _ h3

section FiniteType

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

omit [IsNoetherian S] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g] in
/-- **The supports of the cohomology sheaves of `L pr_1^* M ⊗^𝐋 K` are proper over `Y`** when
those of `K` are: they lie in the union of the supports of the finitely many nonzero `H^j(K)`,
which is proper over `Y` by [Stacks, Tag 0CYR], and a closed subset of a closed subset proper
over `Y` is proper over `Y` ([Stacks, Tag 0CYN]). -/
theorem isProperOver_supp_homology_fourierMukaiTensor
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (hsupp : ∀ (j : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K))),
      IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩)
    (M : DerivedCategory X.Modules) (i : ℤ)
    (hcl : IsClosed (SheafOfModules.supp ((DerivedCategory.homologyFunctor
      (Limits.pullback f g).Modules i).obj
        ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M))))) :
    IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩ := by
  obtain ⟨⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩, hc⟩ := hK
  have hclK : ∀ j : ℤ, IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K)) := fun j =>
    have := (hc j).isFiniteType
    SheafOfModules.isClosed_supp _
  let Zs : {j : ℤ // j ∈ Finset.Icc lo hi} → Closeds (Limits.pullback f g : Scheme.{u}) :=
    fun j => ⟨_, hclK j.1⟩
  have hZ : IsProperOver (Limits.pullback.snd f g) (iSup Zs) :=
    isProperOver_iSup _ Zs fun j => hsupp j.1 (hclK j.1)
  refine isProperOver_of_le _ ?_ hZ
  intro z hz
  by_contra hzZ
  refine notMem_supp_homology_derivedTensor (Limits.pullback f g)
    ((fourierMukaiPullback f g).obj M) K z (fun j hj => hzZ ?_) i hz
  by_cases hjr : j ∈ Finset.Icc lo hi
  · exact le_iSup Zs ⟨j, hjr⟩ hj
  · exfalso
    have hzero :
        IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K) := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hjr
      exact hjr.elim (hlo j) (hhi j)
    exact (notMem_supp_iff_isZero_stalkFunctor _ _ z).2
      (Functor.map_isZero _ hzero) hj

/-- **Case (3) of [Stacks, Tag 0FYU]: the bound below.** On a regular `X` every object of
`D^b_Coh(𝒪_X)` is perfect ([Stacks, Tag 0FDC]), its derived pullback along `pr₁` is perfect, and
a perfect object on the quasi-compact `X ×_S Y` has finite Tor dimension; tensoring it with the
bounded-below `K` gives a bounded-below object. -/
theorem isBoundedBelow_fourierMukaiTensor_of_isRegular (hX : IsRegular X)
    (K : DerivedCategory (Limits.pullback f g).Modules) (hK : DerivedCategoryB.IsBoundedBelow K)
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M) :
    DerivedCategoryB.IsBoundedBelow
      ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)) := by
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  have hPN : IsNoetherian (Limits.pullback f g) :=
    isNoetherian_of_locallyOfFiniteType (Limits.pullback.snd f g)
  have hMp : RingedSpace.IsPerfect (X := X.toRingedSpace) M :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular hX M hM
  have hLp := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (fourierMukaiFst f g) M hMp
  have hfin := Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_isPerfect
    (Limits.pullback f g).toRingedSpace _ hLp
  exact Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
    (Stacks.Cohomology.TorAmplitude.derTensorSite (Limits.pullback f g).toRingedSpace) _ K hfin hK

/-- **Case (4) of [Stacks, Tag 0FYU]: the bound below.** `pr₁` is flat as a base change of the
flat `Y ⟶ S`, so `L pr_1^*` is the exact degreewise pullback and keeps `M` bounded below; the
perfect `K` has finite Tor dimension on the quasi-compact `X ×_S Y`, and tensoring with it keeps
an object bounded below. -/
theorem isBoundedBelow_fourierMukaiTensor_of_isPerfect_of_flat [Flat g]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : DerivedCategoryB.IsBoundedBelow M) :
    DerivedCategoryB.IsBoundedBelow
      ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)) := by
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  have hPN : IsNoetherian (Limits.pullback f g) :=
    isNoetherian_of_locallyOfFiniteType (Limits.pullback.snd f g)
  have hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst f g) := fun x => Flat.stalkMap _ x
  have hfin := Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_of_isPerfect
    (Limits.pullback f g).toRingedSpace K hK
  obtain ⟨n, hMn⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE M).1 hM
  have hL : ((fourierMukaiPullback f g).obj M).IsGE n := by
    obtain ⟨C, hC, ⟨e⟩⟩ := M.exists_iso_Q_obj_of_isGE n
    have hstr : CochainComplex.IsStrictlyGE (((RingedSpaceModuleAdjunction.modulePullback
        (fourierMukaiFst f g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) n := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact Functor.map_isZero _ (C.isZero_of_isStrictlyGE n i hi)
    have hQ : (DerivedCategory.Q.obj (((RingedSpaceModuleAdjunction.modulePullback
        (fourierMukaiFst f g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).IsGE n :=
      (DerivedCategory.isGE_Q_obj_iff _ n).2 inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat
        (fourierMukaiFst f g) hflat C).symm
        ≪≫ (fourierMukaiPullback f g).mapIso e.symm) n
  obtain ⟨m, hm⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1
    (Stacks.SheafOfModules.DerivedTensorProduct.isBoundedBelow_tensor_of_hasFiniteTorDimension
      (Stacks.Cohomology.TorAmplitude.derTensorSite (Limits.pullback f g).toRingedSpace) K _ hfin
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨n, hL⟩))
  exact (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨m, isGE_derivedTensor_swap (Limits.pullback f g).toRingedSpace _ _ m hm⟩

/-! ### The four cases -/

/-- **The part of the proof of [Stacks, Tag 0FYU] common to its four cases.** If the supports of
the cohomology sheaves of `K` are proper over `Y` and `L pr_1^* M ⊗^𝐋 K` is bounded below, then
`Φ_K(M) ∈ D^b_Coh(𝒪_Y)`. [Stacks, Tag 02O5] is supplied by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`. -/
theorem derivedCategoryBBounded_fourierMukai_of_isGE
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (hsupp : ∀ (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))),
      IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩)
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M)
    (d : ℤ) (hGE : ((fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)).IsGE d) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
      ((fourierMukai f g K).obj M) :=
  derivedCategoryBBounded_fourierMukai_of_isProperOver_supp f g K hK M hM d hGE
    (isProperOver_supp_homology_fourierMukaiTensor f g K hK hsupp M)
    ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase

/-- **Case (1) of [Stacks, Tag 0FYU].** -/
theorem derivedCategoryBBounded_fourierMukai_of_hasFiniteTorDimension
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (hsupp : ∀ (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))),
      IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩)
    (htor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj K))
    (M : DerivedCategory X.Modules)
    (hM : DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
      ((fourierMukai f g K).obj M) := by
  obtain ⟨a, b, hab⟩ := htor
  obtain ⟨n, hn⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE M).1 hM.1.1
  exact derivedCategoryBBounded_fourierMukai_of_isGE f g K hK hsupp M hM (a + n)
    (isGE_fourierMukaiTensor_of_hasTorAmplitude f g K a b hab M n hn)

omit [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g]
  [QuasiCompact g] in
/-- **A bounded complex flat over `X` has Tor amplitude where it lives.** A complex of
`𝒪_{X ×_S Y}`-modules flat over `X`, living in `[a, b]`, has Tor amplitude in `[a, b]` over
`pr_1^{-1}𝒪_X`: its terms are flat over `pr_1^{-1}𝒪_X`, and [Stacks, Tag 08CI] applies. -/
theorem hasTorAmplitude_of_flatOver_representative
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (C : CochainComplex (Limits.pullback f g).Modules ℤ) (eC : DerivedCategory.Q.obj C ≅ K)
    (a b : ℤ) (hCa : C.IsStrictlyGE a) (hCb : C.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom (C.X i)) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj K) a b := by
  refine Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
    (X := RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base) _ a b
    (((Scheme.Hom.scalarRestriction (Limits.pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)
    (fun i => Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver _ _ (hflat i)) (fun i hi => ?_)
    (((Scheme.Hom.derivedScalarRestrictionFactors (Limits.pullback.fst f g)).app C).symm ≪≫
      (Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).mapIso eC)
  refine Functor.map_isZero (Scheme.Hom.scalarRestriction (Limits.pullback.fst f g)) ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  exact hi.elim (fun h => C.isZero_of_isStrictlyGE a i h) fun h => C.isZero_of_isStrictlyLE b i h

omit [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g]
  [QuasiCompact g] in
/-- **The reduction of case (2) to case (1).** A bounded complex of `𝒪_{X ×_S Y}`-modules flat
over `X`, living in `[a, b]`, has Tor amplitude in `[a, b]` over `pr_1^{-1}𝒪_X`, by
`hasTorAmplitude_of_flatOver_representative`. -/
theorem hasFiniteTorDimension_of_flatOver_representative
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (C : CochainComplex (Limits.pullback f g).Modules ℤ) (eC : DerivedCategory.Q.obj C ≅ K)
    (a b : ℤ) (hCa : C.IsStrictlyGE a) (hCb : C.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom (C.X i)) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj K) :=
  ⟨a, b, hasTorAmplitude_of_flatOver_representative f g K C eC a b hCa hCb hflat⟩

omit [IsNoetherian S] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g] in
/-- **The support requirement of case (2) gives the one of case (1).** If the terms of a complex
representing `K` are supported in a closed subset proper over `Y`, so are the cohomology sheaves
of `K`. -/
theorem isProperOver_supp_homology_of_representative
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (C : CochainComplex (Limits.pullback f g).Modules ℤ) (eC : DerivedCategory.Q.obj C ≅ K)
    (Zc : Closeds (Limits.pullback f g : Scheme.{u}))
    (hZ : IsProperOver (Limits.pullback.snd f g) Zc)
    (hCZ : ∀ i : ℤ, SheafOfModules.supp (C.X i) ⊆ (Zc : Set (Limits.pullback f g : Scheme.{u})))
    (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))) :
    IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩ := by
  refine isProperOver_of_le _ ?_ hZ
  intro z hz
  have hz' : z ∈ SheafOfModules.supp ((DerivedCategory.homologyFunctor
      (Limits.pullback f g).Modules i).obj (DerivedCategory.Q.obj C)) := by
    rwa [SheafOfModules.supp_eq_of_iso
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).mapIso eC)]
  exact hCZ i (supp_homology_Q_obj_subset (Limits.pullback f g) C i hz')

/-- **[Stacks, Tag 0FYU].** Let `S` be a Noetherian scheme, let `X` and `Y` be schemes of finite
type over `S` and let `K ∈ D^b_Coh(𝒪_{X ×_S Y})`. The Fourier-Mukai functor `Φ_K` sends
`D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_Y)` if at least one of the following holds:

1. the support of `H^i(K)` is proper over `Y` for all `i`, and `K` has finite Tor dimension as
   an object of `D(pr_1^{-1}𝒪_X)`;
2. `K` can be represented by a bounded complex `𝒦^•` of coherent `𝒪_{X ×_S Y}`-modules, flat
   over `X`, with support proper over `Y`;
3. the support of `H^i(K)` is proper over `Y` for all `i`, and `X` is a regular scheme;
4. `K` is perfect, the support of `H^i(K)` is proper over `Y` for all `i`, and `Y ⟶ S` is flat.

Furthermore, in each case the support condition is automatic if `X ⟶ S` is proper: then every
closed subset of `X ×_S Y` is proper over `Y`.

The support of a bounded complex of coherent modules is the union of the supports of its
finitely many nonzero terms; it is written as a closed subset proper over `Y` containing each of
them. Finite Tor dimension over `pr_1^{-1}𝒪_X` is [Stacks, Tag 08CG] on the inverse-image ringed
space `(X ×_S Y, pr_1^{-1}𝒪_X)`, after restriction of scalars along
`pr_1^{-1}𝒪_X ⟶ 𝒪_{X ×_S Y}`. -/
@[stacks 0FYU "Φ_K maps D^b_Coh(O_X) into D^b_Coh(O_Y) under each of (1)-(4); the support \
requirement is automatic when X → S is proper", sga "6 I 5.8.4" "5.8.4 b), special case"]
theorem fourierMukai_derivedCategoryBBounded
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K) :
    ((((∀ (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))),
          IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩) ∧
        Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
          (RingedSpace.inverseImage X.toRingedSpace (Limits.pullback.fst f g).base)
          ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.fst f g)).obj K)) ∨
      (∃ C : CochainComplex (Limits.pullback f g).Modules ℤ,
        (∃ a b : ℤ, C.IsStrictlyGE a ∧ C.IsStrictlyLE b) ∧
        (∀ i : ℤ, (C.X i).IsCoherent) ∧
        (∀ i : ℤ, IsFlatOver (Limits.pullback.fst f g).toLRSHom.toShHom (C.X i)) ∧
        (∃ Z : Closeds (Limits.pullback f g : Scheme.{u}),
          IsProperOver (Limits.pullback.snd f g) Z ∧
          ∀ i : ℤ, SheafOfModules.supp (C.X i) ⊆ (Z : Set (Limits.pullback f g : Scheme.{u}))) ∧
        Nonempty (DerivedCategory.Q.obj C ≅ K)) ∨
      ((∀ (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))),
          IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩) ∧ IsRegular X) ∨
      (RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K ∧
        (∀ (i : ℤ) (hcl : IsClosed (SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K))),
          IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩) ∧ Flat g)) →
      ∀ M : DerivedCategory X.Modules,
        DerivedCategoryB.derivedCategoryBBounded (fun F : X.Modules => F.IsCoherent) M →
        DerivedCategoryB.derivedCategoryBBounded (fun N : Y.Modules => N.IsCoherent)
          ((fourierMukai f g K).obj M)) ∧
    (IsProper f → ∀ T : Closeds (Limits.pullback f g : Scheme.{u}),
      IsProperOver (Limits.pullback.snd f g) T) := by
  refine ⟨fun hcond M hM => ?_, fun _ T => isProperOver_pullbackSnd_of_isProper f g T⟩
  rcases hcond with ⟨hsupp, htor⟩ | ⟨C, ⟨a, b, hCa, hCb⟩, -, hflat, ⟨Z, hZ, hCZ⟩, ⟨eC⟩⟩ |
      ⟨hsupp, hX⟩ | ⟨hperf, hsupp, hflat⟩
  · exact derivedCategoryBBounded_fourierMukai_of_hasFiniteTorDimension f g K hK hsupp htor M hM
  · exact derivedCategoryBBounded_fourierMukai_of_hasFiniteTorDimension f g K hK
      (isProperOver_supp_homology_of_representative f g K C eC Z hZ hCZ)
      (hasFiniteTorDimension_of_flatOver_representative f g K C eC a b hCa hCb hflat) M hM
  · obtain ⟨d, hd⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1
      (isBoundedBelow_fourierMukaiTensor_of_isRegular f g hX K hK.1.1 M hM)
    exact derivedCategoryBBounded_fourierMukai_of_isGE f g K hK hsupp M hM d hd
  · obtain ⟨d, hd⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1
      (isBoundedBelow_fourierMukaiTensor_of_isPerfect_of_flat f g K hperf M hM.1.1)
    exact derivedCategoryBBounded_fourierMukai_of_isGE f g K hK hsupp M hM d hd

end FiniteType

end AlgebraicGeometry

end
