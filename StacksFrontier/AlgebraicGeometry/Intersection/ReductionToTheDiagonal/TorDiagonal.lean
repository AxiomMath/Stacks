module

public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.DerivedDiagonal
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.CoefficientFunctors
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.Tor
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to the diagonal for Tor sheaves

Let `k` be a field, `f : X ⟶ Spec k` a separated scheme over `k` (for instance a nonsingular
variety), `pr₁, pr₂ : X ×_k X ⟶ X` the projections and `Δ` the diagonal. This file proves part (1)
of [Stacks, Tag 0B0T]: for `𝒪_X`-modules `F` and `G` with `G` quasi-coherent (in particular for
`F`, `G` coherent) there are canonical isomorphisms

`Tor_p^{𝒪_{X ×_k X}}(𝒪_Δ, pr₁^*F ⊗ pr₂^*G) ≅ Δ_* Tor_p^{𝒪_X}(F, G)`

for every `p`.

## Main definitions

* `Stacks.Intersection.Diagonal.singleTensorSinglePullbackIso`: **Tor independence**. For a flat
  morphism of ringed spaces `g : Z ⟶ X` and an `𝒪_Z`-module `B` such that `g^*(-) ⊗ B` is exact,
  `g^*F[0] ⊗^L B[0] ≅ (g^*F ⊗ B)[0]`, by the canonical map from the derived to the ordinary
  tensor product.
* `Stacks.Intersection.Diagonal.exteriorDerivedTensorSingleIso`: its instance
  `Lpr₁^*F[0] ⊗^L Lpr₂^*G[0] ≅ (pr₁^*F ⊗ pr₂^*G)[0]`.
* `Stacks.Intersection.Diagonal.torDiagonalIso`: **[Stacks, Tag 0B0T] part (1)**.

## Main results

* `Stacks.Intersection.Diagonal.isIso_toTensor_single_pullback`: the canonical map
  `g^*F[0] ⊗^L B[0] ⟶ Tot(g^*F[0] ⊗ B[0])` is invertible under the hypotheses above.
* `Stacks.Intersection.Diagonal.exactFunctor_pullbackFst_tensor`: `pr₁^*(-) ⊗ pr₂^*G` is exact for
  `G` quasi-coherent.

## Implementation notes

The source deduces (1) from (2) ("As (2) implies (1) the reader can skip the proof of (1)"), and
that is the route taken: `Tor_p(𝒪_Δ, E)` is `H^{-p}(𝒪_Δ[0] ⊗^L E[0])` ([Stacks, Tag 08BP],
`Stacks.Cohomology.tor`), the second isomorphism of part (2) turns
`𝒪_Δ[0] ⊗^L (Lpr₁^*F[0] ⊗^L Lpr₂^*G[0])` into `Δ_*(F[0] ⊗^L G[0])`, and `Δ_*` is exact so it
commutes with cohomology (`AlgebraicGeometry.derivedHomologyMapIso`).

What has to be added is the identification of `Lpr₁^*F[0] ⊗^L Lpr₂^*G[0]` with the ordinary
`(pr₁^*F ⊗ pr₂^*G)[0]` — the sheaf version of the source's remark that `Tot(F_• ⊗_k G_•)` resolves
`M ⊗_k N` "as it computes Tor groups over `k`". It is proved here as follows. Each `prᵢ` is flat,
so `Lprᵢ^*` is the termwise pullback on a module in degree zero. Choose a K-flat resolution
`P → F[0]`; then `pr₁^*P` is a K-flat resolution of `pr₁^*F[0]` ([Stacks, Tag 06YC]), so
`pr₁^*F[0] ⊗^L B[0]` is `Tot(pr₁^*P ⊗ B[0])`, which is `pr₁^*P ⊗ B` termwise. For
`B = pr₂^*G` the functor `pr₁^*(-) ⊗ pr₂^*G` is exact: `G` is flat over `Spec k`, so `pr₂^*G` is
flat over `X` along `pr₁` ([Stacks, Tag 01U8]), and tensoring the pullback with a module flat over
the base is exact ([Stacks, Tag 0GMU]); this is
`Stacks.AlgebraicGeometry.ModuleBaseChange.exact_totalCoefficients`. Hence `pr₁^*P ⊗ pr₂^*G` is
quasi-isomorphic to `pr₁^*F ⊗ pr₂^*G` in degree zero, and the canonical map is invertible.

*Hypotheses.* Nonsingularity is not used, and coherence of `F` and `G` only through the
quasi-coherence of `G`. The degree `p` ranges over `ℤ`, Tor being zero in negative degrees.

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
* [Stacks Project, Tag 08BP](https://stacks.math.columbia.edu/tag/08BP)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Intersection.Diagonal

attribute [local instance 10000] HasDerivedCategory.standard

section TorIndependence

variable {X Z : RingedSpace.{u, u}} (g : Z ⟶ X)
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport of invertibility of the canonical map `K ⊗^L B ⟶ Tot(K ⊗ B)` along a
quasi-isomorphism `K ⟶ K'` which stays a quasi-isomorphism after `- ⊗ B` is applied
termwise. -/
theorem isIso_toTensor_single_of_quasiIso
    {K K' : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) ℤ} (φ : K ⟶ K')
    (hφ : QuasiIso φ) (B : Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)
    (hrow : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) φ B))
    (hK : IsIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor K
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))) :
    IsIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor K'
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Z.sheaf
  let T := canonicalDerivedTensorProduct Z.sheaf
  let L := (HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)
    (ComplexShape.up ℤ) 0).obj B
  have htot : QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ)) := by
    have h2 : QuasiIso (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ) ≫
        (CochainComplex.KFlatBifunctor.totalSingleIso
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) K' B).hom) := by
      rw [CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) φ B]
      infer_instance
    exact (quasiIso_iff_comp_right _ _).1 h2
  have hQtot := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 htot
  have hQφ : IsIso (DerivedCategory.Q.map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).2 hφ
  have h3 : IsIso ((T.tensor.map (DerivedCategory.Q.map φ)).app (DerivedCategory.Q.obj L) ≫
      (T.tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map (𝟙 L)) ≫
      T.toTensor K' L) := by
    rw [T.toTensor_naturality φ (𝟙 L)]
    exact IsIso.comp_isIso' hK hQtot
  have h4 := IsIso.of_isIso_comp_left
    ((T.tensor.map (DerivedCategory.Q.map φ)).app (DerivedCategory.Q.obj L))
    ((T.tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map (𝟙 L)) ≫
      T.toTensor K' L)
  exact IsIso.of_isIso_comp_left
    ((T.tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map (𝟙 L))) _

/-- **Tor independence of a pulled-back module.** Let `g : Z ⟶ X` be a morphism of ringed spaces
with `g^*` exact and `B` an `𝒪_Z`-module with `g^*(-) ⊗ B` exact. For every `𝒪_X`-module `F` the
canonical map `g^*F[0] ⊗^L B[0] ⟶ Tot(g^*F[0] ⊗ B[0])` is an isomorphism. -/
theorem isIso_toTensor_single_pullback
    [PreservesFiniteLimits (modulePullback g)]
    (B : SheafOfModules.{u} (structureSheafRing Z))
    [PreservesFiniteLimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ((modulePullback g).obj F))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Z.sheaf
  obtain ⟨P, p, hP, -, hp, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj Z.sheaf B
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
      B).Additive :=
    Functor.flip_obj_additive (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) B
  have : (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B).Additive := by
    have : PreservesBinaryBiproducts (modulePullback g ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
        B).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let gc := (modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)
  have h0 : IsIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor (gc.obj P)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)) := by
    rw [(canonicalDerivedTensorProduct Z.sheaf).toTensor_eq_comparisonLeft (gc.obj P)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)
      (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional g P hP)]
    infer_instance
  have hrow : QuasiIso ((modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
        B).mapHomologicalComplex (ComplexShape.up ℤ) |>.map p) := inferInstance
  have : PreservesFiniteColimits (modulePullback g) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback g
  have : (modulePullback g).PreservesHomology := Functor.preservesHomologyOfExact _
  have hgp : QuasiIso (gc.map p) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology p (modulePullback g)
  have h1 := isIso_toTensor_single_of_quasiIso (gc.map p) hgp B hrow h0
  let e := (HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
    (ComplexShape.up ℤ) 0).app F
  have hrow' : QuasiIso (CochainComplex.KFlatBifunctor.rowComplexMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) e.hom B) := by
    have : IsIso (CochainComplex.KFlatBifunctor.rowComplexMap
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) e.hom B) :=
      Iso.isIso_hom ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj
        B).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e)
    exact quasiIso_of_isIso _
  exact isIso_toTensor_single_of_quasiIso e.hom (quasiIso_of_isIso e.hom) B hrow' h1

/-- The total tensor complex of [Stacks, Tag 06YU] is `HomologicalComplex.mapBifunctor` of the
tensor product of sheaves of modules, by definition. -/
def tensorComplexIsoMapBifunctorSingle (M B : Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B) ≅
    HomologicalComplex.mapBifunctor ((CochainComplex.singleFunctor _ 0).obj M)
      ((CochainComplex.singleFunctor _ 0).obj B)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ) :=
  Iso.refl _

/-- `HomologicalComplex.mapBifunctorSingleIso` for the tensor product of sheaves of modules, with
its target spelled through `HomologicalComplex.single`. -/
def mapBifunctorSheafTensorSingleIso (M B : Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) :
    HomologicalComplex.mapBifunctor ((CochainComplex.singleFunctor _ 0).obj M)
      ((CochainComplex.singleFunctor _ 0).obj B)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (ComplexShape.up ℤ) ≅
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj M).obj B) :=
  HomologicalComplex.mapBifunctorSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) M B

/-- `g^*F[0] ⊗^L B[0] ≅ (g^*F ⊗ B)[0]` when `g` is flat and `g^*(-) ⊗ B` is exact: the canonical
map from the derived to the ordinary tensor product, followed by the identification of the total
complex of two complexes concentrated in degree zero. -/
def singleTensorSinglePullbackIso
    [PreservesFiniteLimits (modulePullback g)]
    (B : SheafOfModules.{u} (structureSheafRing Z))
    [PreservesFiniteLimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    ((derivedTensorProductFunctor Z.sheaf).obj
        ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) 0).obj
          ((modulePullback g).obj F))).obj
        ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) 0).obj
          B) ≅
      (DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj
          ((modulePullback g).obj F)).obj B) :=
  @asIso _ _ _ _ _ (isIso_toTensor_single_pullback g B F) ≪≫
    (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)).mapIso
      (tensorComplexIsoMapBifunctorSingle _ _ ≪≫
        mapBifunctorSheafTensorSingleIso ((modulePullback g).obj F) B)

/-- The defining formula of `singleTensorSinglePullbackIso`: the canonical map from the derived to
the ordinary tensor product, followed by `Tot(M[0] ⊗ B[0]) ≅ (M ⊗ B)[0]`. -/
theorem singleTensorSinglePullbackIso_hom
    [PreservesFiniteLimits (modulePullback g)]
    (B : SheafOfModules.{u} (structureSheafRing Z))
    [PreservesFiniteLimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    [PreservesFiniteColimits (modulePullback g ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).flip.obj B)]
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (singleTensorSinglePullbackIso g B F).hom =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor _ _ ≫
        (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules Z.sheaf)).map
          (tensorComplexIsoMapBifunctorSingle _ _ ≪≫
            mapBifunctorSheafTensorSingleIso ((modulePullback g).obj F) B).hom :=
  rfl

end TorIndependence

section Tor

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Pullback of modules along the first projection of `X ×_k X` is exact, the projection being
flat. -/
instance preservesFiniteLimits_modulePullback_fst :
    PreservesFiniteLimits (modulePullback (pullback.fst f f).toLRSHom.toShHom) :=
  RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
    fun x => Flat.stalkMap _ x

/-- Pullback of modules along the second projection of `X ×_k X` is exact, the projection being
flat. -/
instance preservesFiniteLimits_modulePullback_snd :
    PreservesFiniteLimits (modulePullback (pullback.snd f f).toLRSHom.toShHom) :=
  RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
    fun x => Flat.stalkMap _ x

variable (G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [G.IsQuasicoherent]

/-- **`pr₁^*(-) ⊗ pr₂^*G` is exact** for a quasi-coherent `G`: every module is flat over the field,
so `pr₂^*G` is flat over `X` along `pr₁` ([Stacks, Tag 01U8]) and [Stacks, Tag 0GMU] applies. -/
theorem exactFunctor_pullbackFst_tensor :
    exactFunctor _ _ (modulePullback (pullback.fst f f).toLRSHom.toShHom ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (pullback f f).toRingedSpace.sheaf).flip.obj
        ((modulePullback (pullback.snd f f).toLRSHom.toShHom).obj G)) :=
  Stacks.AlgebraicGeometry.ModuleBaseChange.exact_totalCoefficients
    (IsPullback.of_hasPullback f f) G (isFlatOver_of_isField f G)

/-- For a flat morphism of ringed spaces `g`, `Lg^*(F[0]) ≅ (g^*F)[0]`. -/
def derivedPullbackSingleIsoOfFlat {Y W : RingedSpace.{u, u}} (g : W ⟶ Y)
    [PreservesFiniteLimits (modulePullback g)] (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePullback g).obj M) :=
  haveI : PreservesFiniteColimits (modulePullback g) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback g
  (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso g).app _ ≪≫
    ((modulePullback g).mapDerivedCategorySingleFunctor 0).app M

variable (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The exterior tensor product `pr₁^*F ⊗ pr₂^*G` of two `𝒪_X`-modules. -/
abbrev exteriorTensor (F G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing (pullback f f).toRingedSpace) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (pullback f f).toRingedSpace.sheaf).obj
    ((modulePullback (pullback.fst f f).toLRSHom.toShHom).obj F)).obj
    ((modulePullback (pullback.snd f f).toLRSHom.toShHom).obj G)

/-- **Tor independence of the two factors**: `Lpr₁^*F[0] ⊗^L Lpr₂^*G[0] ≅ (pr₁^*F ⊗ pr₂^*G)[0]`
for `G` quasi-coherent. -/
def exteriorDerivedTensorSingleIso :
    (exteriorDerivedTensor (pullback.fst f f).toLRSHom.toShHom
        (pullback.snd f f).toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor _ 0).obj F, (DerivedCategory.singleFunctor _ 0).obj G) ≅
      (DerivedCategory.singleFunctor _ 0).obj (exteriorTensor f F G) :=
  have hex := exactFunctor_pullbackFst_tensor f G
  haveI := ((exactFunctor_iff _).1 hex).1
  haveI := ((exactFunctor_iff _).1 hex).2
  ((derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).mapIso
      (derivedPullbackSingleIsoOfFlat (pullback.fst f f).toLRSHom.toShHom F)).app _ ≪≫
    ((derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).obj _).mapIso
      (derivedPullbackSingleIsoOfFlat (pullback.snd f f).toLRSHom.toShHom G) ≪≫
    singleTensorSinglePullbackIso (pullback.fst f f).toLRSHom.toShHom
      ((modulePullback (pullback.snd f f).toLRSHom.toShHom).obj G) F

variable [IsSeparated f]

/-- **[Stacks, Tag 0B0T], part (1).** Let `k` be a field and `f : X ⟶ Spec k` separated (for
instance a nonsingular variety), with projections `pr₁, pr₂` and diagonal `Δ`. For
`𝒪_X`-modules `F` and `G` with `G` quasi-coherent (for instance coherent) there are canonical
isomorphisms

`Tor_p^{𝒪_{X ×_k X}}(𝒪_Δ, pr₁^*F ⊗ pr₂^*G) ≅ Δ_* Tor_p^{𝒪_X}(F, G)`.

The isomorphism is `H^{-p}` of the composite of the Tor-independence isomorphism
`exteriorDerivedTensorSingleIso` (inverted, in the second factor) and the second isomorphism of
part (2), `diagonalTensorIso`, followed by the commutation of the exact functor `Δ_*` with
cohomology. -/
@[stacks 0B0T "(1)"]
def torDiagonalIso (p : ℤ) :
    Stacks.Cohomology.tor (pullback f f).toRingedSpace p (diagonalStructureModule f)
        (exteriorTensor f F G) ≅
      (modulePushforward (pullback.diagonal f).toLRSHom.toShHom).obj
        (Stacks.Cohomology.tor X.toRingedSpace p F G) :=
  (DerivedCategory.homologyFunctor _ (-p)).mapIso
      (((derivedTensorProductFunctor (pullback f f).toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor _ 0).obj (diagonalStructureModule f))).mapIso
          (exteriorDerivedTensorSingleIso f G F).symm ≪≫
        (diagonalTensorIso f).app
          ((DerivedCategory.singleFunctor _ 0).obj F, (DerivedCategory.singleFunctor _ 0).obj G)) ≪≫
    (AlgebraicGeometry.derivedHomologyMapIso
      (modulePushforward (pullback.diagonal f).toLRSHom.toShHom) _ (-p)).symm

end Tor

end Stacks.Intersection.Diagonal
