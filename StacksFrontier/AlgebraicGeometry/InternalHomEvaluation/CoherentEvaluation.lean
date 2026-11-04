module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Evaluation of derived internal Homs on a Noetherian scheme

Let `X` be a Noetherian scheme and let `K`, `L`, `M` be objects of `D_QCoh(O_X)`. The evaluation
morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism in two cases: when `K ∈ D^-_Coh(O_X)`, `L ∈ D^+_Coh(O_X)` and `M` has finite
injective dimension affine locally; and when `K` and `L` are in `D_Coh(O_X)`, `RSheafHom(L, M)`
has finite tor dimension, and `L` and `M` have finite injective dimension affine locally.

## Main definitions

* `Stacks.SheafOfModules.HasCoherentCohomology`: all cohomology sheaves are coherent.
* `Stacks.SheafOfModules.HasFiniteInjectiveDimensionOverOpen`: the restriction of an object of
  `D(O_X)` to the slice site over an open has finite injective dimension.
* `Stacks.SheafOfModules.HasFiniteTorDimension`: tensoring with the object kills cohomology
  outside a fixed finite range, uniformly in the module tensored with.
* `Stacks.SheafOfModules.HoldsAffineLocally`: a property of opens holds on an affine open
  neighbourhood of every point.
* `Stacks.SheafOfModules.IsBoundedCoherentTriple` and
  `Stacks.SheafOfModules.IsCoherentFiniteTorTriple`: the hypotheses of the two cases, bundled.

## Main results

* `Stacks.SheafOfModules.exists_cover_of_holdsAffineLocally`: a property holding affine locally
  holds on a family of affine opens covering the scheme.
* `Stacks.SheafOfModules.derivedSheafHomEvaluation_isIso_of_boundedCoherent`: the evaluation
  morphism is an isomorphism in the first case.
* `Stacks.SheafOfModules.derivedSheafHomEvaluation_isIso_of_coherent_finiteTorDimension`: the
  evaluation morphism is an isomorphism in the second case.

## References

* [Stacks Project, Tag 0G4I](https://stacks.math.columbia.edu/tag/0G4I)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- A property of the opens of `X` **holds affine locally** when every point of `X` has an
affine open neighbourhood on which it holds. -/
def HoldsAffineLocally (P : Opens X → Prop) : Prop :=
  ∀ x : X, ∃ V : X.affineOpens, x ∈ (V : Opens X) ∧ P (V : Opens X)

/-- A property holding affine locally holds on a family of affine opens covering `X`. -/
theorem exists_cover_of_holdsAffineLocally (P : Opens X → Prop) (hP : HoldsAffineLocally X P) :
    ∃ (ι : Type u) (Y : ι → Opens X), (Opens.grothendieckTopology X).CoversTop Y ∧
      ∀ i, IsAffineOpen (Y i) ∧ P (Y i) := by
  refine ⟨{ V : Opens X // IsAffineOpen V ∧ P V }, fun p ↦ p.1, ?_, fun p ↦ p.2⟩
  rw [Opens.coversTop_iff]
  refine .mk <| eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨V, hxV, hPV⟩ := hP x
  exact Opens.mem_iSup.2 ⟨⟨V, V.2, hPV⟩, hxV⟩

/-- A property holding affine locally holds on a family of opens covering `X`. -/
private theorem exists_cover_of_holdsAffineLocally' (P : Opens X → Prop)
    (hP : HoldsAffineLocally X P) :
    ∃ (ι : Type u) (Y : ι → Opens X), (Opens.grothendieckTopology X).CoversTop Y ∧ ∀ i, P (Y i) :=
  let ⟨ι, Y, hY, h⟩ := exists_cover_of_holdsAffineLocally X P hP
  ⟨ι, Y, hY, fun i => (h i).2⟩

variable
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ N, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj N).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]

/-! ### Finiteness conditions -/

/-- An object of `D(O_X)` has **coherent cohomology** when every one of its cohomology sheaves
is a coherent `O_X`-module in the sense of [Stacks, Tag 01BV]. -/
def HasCoherentCohomology (E : DerivedCategory (StructureSheafModules X.sheaf)) : Prop :=
  ∀ i : ℤ, IsCoherent ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj E)

/-- An object of `D(O_X)` **has finite injective dimension over the open `V`** when its
restriction to the slice site over `V` has finite injective dimension ([Stacks, Tag 0A5S]) in the
derived category of `O_X|_V`-modules. -/
def HasFiniteInjectiveDimensionOverOpen
    (E : DerivedCategory (StructureSheafModules X.sheaf)) (V : Opens X) : Prop :=
  StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
    ((_root_.SheafOfModules.overFunctor.{u} (structureSheaf X.sheaf) V).mapDerivedCategory.obj E)

/-- An object `E` of `D(O_X)` **has finite tor dimension** when there is a finite range of
degrees outside which the derived tensor product of `E` with any `O_X`-module placed in degree
zero has vanishing cohomology. -/
def HasFiniteTorDimension (E : DerivedCategory (StructureSheafModules X.sheaf)) : Prop :=
  ∃ a b : ℤ, ∀ (N : StructureSheafModules X.sheaf) (i : ℤ), i ∉ Set.Icc a b →
    Limits.IsZero ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      (((derivedTensor X.sheaf).obj E).obj
        ((DerivedCategory.singleFunctor (StructureSheafModules X.sheaf) 0).obj N)))

/-! ### The two cases of the evaluation isomorphism -/

/-- The hypotheses of the first case on the triple `K`, `L`, `M`: all three lie in
`D_QCoh(O_X)`, `K` lies in `D^-_Coh(O_X)`, `L` lies in `D^+_Coh(O_X)`, and `M` has finite
injective dimension affine locally. -/
structure IsBoundedCoherentTriple
    (K L M : DerivedCategory (StructureSheafModules X.sheaf)) : Prop where
  /-- `K` lies in `D_QCoh(O_X)`. -/
  isDQCoh_K : Stacks.DerivedQCoh.IsDQCoh K
  /-- `L` lies in `D_QCoh(O_X)`. -/
  isDQCoh_L : Stacks.DerivedQCoh.IsDQCoh L
  /-- `M` lies in `D_QCoh(O_X)`. -/
  isDQCoh_M : Stacks.DerivedQCoh.IsDQCoh M
  /-- `K` is cohomologically bounded above. -/
  isBoundedAbove_K : DerivedCategoryB.IsBoundedAbove K
  /-- The cohomology sheaves of `K` are coherent; with the bound above, `K ∈ D^-_Coh(O_X)`. -/
  coherent_K : HasCoherentCohomology X K
  /-- `L` is cohomologically bounded below. -/
  isBoundedBelow_L : DerivedCategoryB.IsBoundedBelow L
  /-- The cohomology sheaves of `L` are coherent; with the bound below, `L ∈ D^+_Coh(O_X)`. -/
  coherent_L : HasCoherentCohomology X L
  /-- `M` has finite injective dimension affine locally. -/
  injectiveDimension_M : HoldsAffineLocally X (HasFiniteInjectiveDimensionOverOpen X M)

/-- The hypotheses of the second case on the triple `K`, `L`, `M`: all three lie in
`D_QCoh(O_X)`, `K` and `L` lie in `D_Coh(O_X)`, the object `RSheafHom(L, M)` has finite tor
dimension, and `L` and `M` have finite injective dimension affine locally, each on affine opens
of its own. -/
structure IsCoherentFiniteTorTriple
    (K L M : DerivedCategory (StructureSheafModules X.sheaf)) : Prop where
  /-- `K` lies in `D_QCoh(O_X)`. -/
  isDQCoh_K : Stacks.DerivedQCoh.IsDQCoh K
  /-- `L` lies in `D_QCoh(O_X)`. -/
  isDQCoh_L : Stacks.DerivedQCoh.IsDQCoh L
  /-- `M` lies in `D_QCoh(O_X)`. -/
  isDQCoh_M : Stacks.DerivedQCoh.IsDQCoh M
  /-- The cohomology sheaves of `K` are coherent, so `K ∈ D_Coh(O_X)`. -/
  coherent_K : HasCoherentCohomology X K
  /-- The cohomology sheaves of `L` are coherent, so `L ∈ D_Coh(O_X)`. -/
  coherent_L : HasCoherentCohomology X L
  /-- `RSheafHom(L, M)` has finite tor dimension. -/
  finiteTorDimension : HasFiniteTorDimension X
    (((derivedSheafHom X.sheaf).obj (op L)).obj M)
  /-- `L` has finite injective dimension affine locally. -/
  injectiveDimension_L : HoldsAffineLocally X (HasFiniteInjectiveDimensionOverOpen X L)
  /-- `M` has finite injective dimension affine locally. -/
  injectiveDimension_M : HoldsAffineLocally X (HasFiniteInjectiveDimensionOverOpen X M)

/-- Let `X` be a Noetherian scheme and let `K`, `L`, `M` be objects of `D_QCoh(O_X)` with
`K ∈ D^-_Coh(O_X)`, `L ∈ D^+_Coh(O_X)` and `M` of finite injective dimension affine locally. Then
the evaluation morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

of [Stacks, Tag 0A8U] is an isomorphism. -/
@[stacks 0G4I "case (1): on a Noetherian scheme, K bounded above with coherent cohomology, L \
  bounded below with coherent cohomology, all three in D_QCoh, M of finite injective dimension \
  affine locally"]
theorem derivedSheafHomEvaluation_isIso_of_boundedCoherent [IsNoetherian X]
    (K L M : DerivedCategory (StructureSheafModules X.sheaf))
    (h : IsBoundedCoherentTriple X K L M) :
    IsIso (derivedSheafHomEvaluation X.sheaf K L M) := by
  have hK : (ringedSite X.sheaf).IsPseudoCoherent K :=
    AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherent_ringedSite' X.toRingedSpace K
      ((isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨K, h.isDQCoh_K⟩).2
        ⟨h.isBoundedAbove_K, fun i => (h.coherent_K i).rootIsCoherent⟩)
  exact RingedSite.isIso_derivedSheafHomEvaluation_of_isPseudoCoherent (ringedSite X.sheaf) _ _
    K L M hK h.isBoundedBelow_L (exists_cover_of_holdsAffineLocally' X _
      h.injectiveDimension_M)

/-- Let `X` be a Noetherian scheme and let `K`, `L`, `M` be objects of `D_QCoh(O_X)` with `K`
and `L` in `D_Coh(O_X)`, with `RSheafHom(L, M)` of finite tor dimension, and with `L` and `M` of
finite injective dimension affine locally. Then the evaluation morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

of [Stacks, Tag 0A8U] is an isomorphism. -/
@[stacks 0G4I "case (2): on a Noetherian scheme, K and L with coherent cohomology, all three in \
  D_QCoh, RSheafHom(L, M) of finite tor dimension, L and M of finite injective dimension affine \
  locally"]
theorem derivedSheafHomEvaluation_isIso_of_coherent_finiteTorDimension [IsNoetherian X]
    (K L M : DerivedCategory (StructureSheafModules X.sheaf))
    (h : IsCoherentFiniteTorTriple X K L M) :
    IsIso (derivedSheafHomEvaluation X.sheaf K L M) := by
  have hK : ∀ N : ℤ, (ringedSite X.sheaf).IsPseudoCoherent
      ((DerivedCategory.TStructure.t.truncLE N).obj K) := by
    intro N
    have : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
      Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_containsZero X
    have hqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        ((DerivedCategory.TStructure.t.truncLE N).obj K) := fun i =>
      Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) K h.isDQCoh_K N i
    have hbdd : DerivedCategoryB.IsBoundedAbove ((DerivedCategory.TStructure.t.truncLE N).obj K) :=
      ⟨N, fun i hi => DerivedCategory.isZero_of_isLE _ N i hi⟩
    exact AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherent_ringedSite'
      X.toRingedSpace _
      ((isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨_, hqc⟩).2
        ⟨hbdd, fun i => (Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj
          (coherentModules X.ringCatSheaf) K h.coherent_K N i).rootIsCoherent⟩)
  obtain ⟨a, b, hab⟩ := h.finiteTorDimension
  have hE : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (canonicalDerivedTensorProduct (ringedSite X.sheaf))
      (((derivedSheafHom X.sheaf).obj (op L)).obj M) a := fun N i hi =>
    hab N i fun hi' => hi.not_ge hi'.1
  exact RingedSite.isIso_derivedSheafHomEvaluation_of_truncLE_isPseudoCoherent
    (ringedSite X.sheaf) _ _ K L M hK
    (exists_cover_of_holdsAffineLocally' X _ h.injectiveDimension_L)
    (exists_cover_of_holdsAffineLocally' X _ h.injectiveDimension_M) a hE

end Stacks.SheafOfModules

end
