module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsPseudoCoherence
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of a tensor product: from perfect to pseudo-coherent

Let `A` be a ring, let `X` be a quasi-compact and quasi-separated scheme over `A` and let
`K ∈ D^-_QCoh(𝒪_X)`. If `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every perfect `E`,
then it is pseudo-coherent for every pseudo-coherent `E` ([Stacks, Tag 0CSH]).

## Main results

* `AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent`:
  [Stacks, Tag 0CSH], for `RΓ(X, E ⊗^𝐋 K)`.
* `AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent'`:
  the same for `RΓ(X, K ⊗^𝐋 E)`.
* `isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent_of_ringedSite`: the
  latter with the test objects perfect for the ringed site of opens ([Stacks, Tag 08G5]).
* `AlgebraicGeometry.exists_isLE_derivedGlobalSectionsOver_obj`: `A`-linear `RΓ(X, -)` has finite
  cohomological dimension on `D_QCoh(𝒪_X)` ([Stacks, Tag 08D5]).
* `AlgebraicGeometry.isLE_derivedTensor_obj_obj` and
  `AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj`: the derived tensor product
  adds upper bounds of cohomology and preserves quasi-coherence of cohomology ([Stacks, Tag 08DX]
  part (1)), at the standard model and in the spelling `Stacks.SheafOfModules.derivedTensor`.

## Implementation notes

**Spelling.** `D(𝒪_X)` is `DerivedCategory (StructureSheafModules X.sheaf)` at the standard model
`HasDerivedCategory.standard`, the derived tensor product is `Stacks.SheafOfModules.derivedTensor
X.sheaf` (the derived tensor product of [Stacks, Tag 06YU] on the ringed site of opens), `RΓ(X, -)`
is the `A`-linear `AlgebraicGeometry.derivedGlobalSectionsOver f` for the structure morphism
`f : X ⟶ Spec A`, perfectness is that of the ringed space `X` ([Stacks, Tag 08CM]) and
pseudo-coherence that of `RingedSpace.IsPseudoCoherent`; pseudo-coherence in `D(A)` is
`StacksDraft.PseudoCoherence.IsPseudoCoherent`. The standard model is the one at which
approximation by perfect complexes (`AlgebraicGeometry.HasApproximationByPerfectComplexes`) is
stated. The membership `K ∈ D^-_QCoh(𝒪_X)` is spelled out as quasi-coherence of every cohomology
sheaf together with vanishing above some degree.

**Instance arguments.** The sheafification and tensor-additivity instance arguments of the
statements are those `Stacks.SheafOfModules.derivedTensor` is stated under; all of them are found
by instance search for a scheme, so a consumer need not supply them. They are kept as binders
because the abelian structure that instance search finds on `StructureSheafModules X.sheaf`
without them is a different term from the one the derived tensor product was built with, and the
unification of the two exhausts the heartbeat budget.

**The proof** is the dévissage
`AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_obj_of_hasApproximationByPerfect`
applied to `G = (- ⊗^𝐋 K) ⋙ RΓ(X, -)`. Its exactness hypothesis comes from the exactness of the
derived tensor product in each variable (fields `exact_left`/`exact_right` of
`Stacks.SheafOfModules.DerivedTensorProduct`) and of `RΓ(X, -)`
(`AlgebraicGeometry.derivedGlobalSectionsOver_isTriangulated`); approximation by perfect complexes
is [Stacks, Tag 08ES], `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes`;
and the cohomological-dimension hypothesis with `d = b + N` is assembled from the three bounds
above. Quasi-coherence of the cohomology of a derived tensor product is available as
[Stacks, Tag 08DX] at the locally small model only
(`Stacks.Duality.isQuasicoherent_homology_derivedTensor`); it is moved to the standard model on
K-flat representatives, where the derived tensor product is the total tensor complex at either
model (`Stacks.Duality.isQuasicoherent_homology_totalTensorComplex`).

## References

* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
* [Stacks Project, Tag 08ES](https://stacks.math.columbia.edu/tag/08ES)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.SheafOfModules

universe u

/-! ### Quasi-coherence of a total tensor complex -/

namespace Stacks.Duality

/-- A property of objects closed under isomorphisms holds for the `j`-th cohomology of an object
of the derived category iff it holds for the `j`-th cohomology of any complex representing it. -/
private theorem prop_homology_iff_of_iso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (M : CochainComplex C ℤ) {K : DerivedCategory C} (e : DerivedCategory.Q.obj M ≅ K) (j : ℤ) :
    P ((DerivedCategory.homologyFunctor C j).obj K) ↔ P (HomologicalComplex.homology M j) :=
  let e' := (DerivedCategory.homologyFunctor C j).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors C j).app M
  ⟨P.prop_of_iso e', P.prop_of_iso e'.symm⟩

/-- **The total tensor complex of two K-flat complexes with quasi-coherent cohomology has
quasi-coherent cohomology.** This is [Stacks, Tag 08DX] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedTensor`, read on representatives: on K-flat
complexes the derived tensor product is the total tensor complex
(`Stacks.Duality.derivedTensorIsoQTensorComplex`), and the cohomology sheaves of the class of a
complex are those of the complex. The statement mentions no derived category, so it can be used
at any model of `D(𝒪_X)`. -/
theorem isQuasicoherent_homology_totalTensorComplex (X : AlgebraicGeometry.Scheme.{u})
    (P Q : TensorComplex X)
    (hP : KFlatComplex P) (hQ : KFlatComplex Q)
    (hPqc : ∀ i : ℤ,
      (HomologicalComplex.homology (@id (CochainComplex X.Modules ℤ) P) i).IsQuasicoherent)
    (hQqc : ∀ i : ℤ,
      (HomologicalComplex.homology (@id (CochainComplex X.Modules ℤ) Q) i).IsQuasicoherent)
    (i : ℤ) :
    (HomologicalComplex.homology (@id (CochainComplex X.Modules ℤ) (totalTensorComplex P Q))
      i).IsQuasicoherent := by
  let qc := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let K : quasiCoherentDerivedCategory X :=
    ⟨(DerivedCategory.Q.obj P : DerivedCategory X.Modules),
      fun j => (prop_homology_iff_of_iso qc P (Iso.refl _) j).2 (hPqc j)⟩
  let L : quasiCoherentDerivedCategory X :=
    ⟨(DerivedCategory.Q.obj Q : DerivedCategory X.Modules),
      fun j => (prop_homology_iff_of_iso qc Q (Iso.refl _) j).2 (hQqc j)⟩
  exact (prop_homology_iff_of_iso qc (totalTensorComplex P Q)
    (derivedTensorIsoQTensorComplex X K.obj L.obj P Q hP hQ (Iso.refl _) (Iso.refl _)).symm i).1
    (isQuasicoherent_homology_derivedTensor X K L i)

end Stacks.Duality

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose

/-! ### The derived tensor product of `D(𝒪_X)`, at the standard model -/

section Tensor

variable (X : Scheme.{u})
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- The derived tensor product `Stacks.SheafOfModules.derivedTensor X.sheaf` of the ringed site of
opens of `X`, read as a derived tensor product indexed by the structure sheaf: same bifunctor,
same comparisons with the total tensor complex. -/
abbrev siteDerivedTensorDatum :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf :=
  RingedSite.derivedTensorProductDatumOfSite (Stacks.SheafOfModules.ringedSite X.sheaf)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite X.sheaf))

/-- **The derived tensor product adds upper bounds of cohomology**: `K ⊗^𝐋 L` lies in
`D^{≤ a + b}` when `K` lies in `D^{≤ a}` and `L` in `D^{≤ b}`. -/
@[sga "6 I 2.16" "special case", sga "6 III 1.11" "(a), special case"]
theorem isLE_derivedTensor_obj_obj (K L : DerivedCategory (StructureSheafModules X.sheaf))
    (a b : ℤ) (hK : K.IsLE a) (hL : L.IsLE b) :
    (((derivedTensor X.sheaf).obj K).obj L).IsLE (a + b) := by
  have h : ∀ K' L' : Stacks.DerivedTensor.RingedSite.DerivedModules X.sheaf,
      K'.IsLE a → L'.IsLE b →
      (((siteDerivedTensorDatum X).tensor.obj K').obj L').IsLE (a + b) :=
    fun K' L' _ _ => Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct X.sheaf
      (siteDerivedTensorDatum X) K' L' a b
  exact h K L hK hL

/-- **A K-flat representative with quasi-coherent cohomology.** Every object `K` of `D(𝒪_X)` is
the class of a K-flat complex ([Stacks, Tag 06YS]), and if the cohomology sheaves of `K` are
quasi-coherent, so are those of the complex. -/
theorem exists_kFlatComplex_iso_of_isQuasicoherent
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      K).IsQuasicoherent) :
    ∃ P : CochainComplex (StructureSheafModules X.sheaf) ℤ,
      IsKFlat (Stacks.SheafOfModules.ringedSite X.sheaf).O P ∧
      (∀ j : ℤ, (HomologicalComplex.homology P j).IsQuasicoherent) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso
    (Stacks.SheafOfModules.ringedSite X.sheaf)
    ((DerivedCategory.Q (C := StructureSheafModules X.sheaf)).objPreimage K)
  have hpi := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := StructureSheafModules X.sheaf) p).2 hp
  let eP : (DerivedCategory.Q (C := StructureSheafModules X.sheaf)).obj P ≅ K :=
    asIso ((DerivedCategory.Q (C := StructureSheafModules X.sheaf)).map p) ≪≫
      (DerivedCategory.Q (C := StructureSheafModules X.sheaf)).objObjPreimageIso K
  exact ⟨P, hP, fun j => (Stacks.Duality.prop_homology_iff_of_iso
    (SheafOfModules.isQuasicoherent _) P eP j).1 (hK j), ⟨eP⟩⟩

/-- **On K-flat representatives the derived tensor product of the ringed site of opens is the
total tensor complex**, at the standard model: if `P` and `R` are K-flat complexes whose classes
are `K` and `L`, then `K ⊗^𝐋 L ≅ Q(Tot(P ⊗ R))`. -/
def derivedTensorObjObjIsoQTotal (K L : DerivedCategory (StructureSheafModules X.sheaf))
    (P R : CochainComplex (StructureSheafModules X.sheaf) ℤ)
    (hP : IsKFlat (Stacks.SheafOfModules.ringedSite X.sheaf).O P)
    (hR : IsKFlat (Stacks.SheafOfModules.ringedSite X.sheaf).O R)
    (eP : DerivedCategory.Q.obj P ≅ K) (eR : DerivedCategory.Q.obj R ≅ L) :
    ((derivedTensor X.sheaf).obj K).obj L ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj P |>.obj R) :=
  (((derivedTensor X.sheaf).mapIso eP).app L).symm ≪≫
    ((derivedTensor X.sheaf).obj (DerivedCategory.Q.obj P)).mapIso eR.symm ≪≫
    (canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite X.sheaf)).comparison P R hP hR

/-- **[Stacks, Tag 08DX] part (1) for the derived tensor product of the ringed site of opens, at
the standard model of `D(𝒪_X)`.** If `K` and `L` have quasi-coherent cohomology sheaves, so does
`K ⊗^𝐋 L`. Both factors are replaced by K-flat representatives ([Stacks, Tag 06YS]), on which the
derived tensor product is the total tensor complex, and
`Stacks.Duality.isQuasicoherent_homology_totalTensorComplex` applies. -/
theorem isQuasicoherent_homology_derivedTensor_obj_obj
    (K L : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      K).IsQuasicoherent)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      L).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      (((derivedTensor X.sheaf).obj K).obj L)).IsQuasicoherent := by
  obtain ⟨P, hP, hPqc, ⟨eP⟩⟩ := exists_kFlatComplex_iso_of_isQuasicoherent X K hK
  obtain ⟨R, hR, hRqc, ⟨eR⟩⟩ := exists_kFlatComplex_iso_of_isQuasicoherent X L hL
  exact (Stacks.Duality.prop_homology_iff_of_iso (SheafOfModules.isQuasicoherent _) _
    (derivedTensorObjObjIsoQTotal X K L P R hP hR eP eR).symm i).2
    (Stacks.Duality.isQuasicoherent_homology_totalTensorComplex X P R hP hR hPqc hRqc i)

end Tensor

/-! ### The cohomological dimension of `A`-linear derived global sections -/

section GlobalSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **`A`-linear derived global sections have finite cohomological dimension on
`D_QCoh(𝒪_X)`** ([Stacks, Tag 08D5] for the morphism to a point). For `X` quasi-compact and
quasi-separated there is an integer `N` such that `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` carries an object
with quasi-coherent cohomology lying in `D^{≤ d}` into `D^{≤ d + N}`.

Forgetting the `A`-module structure is exact and reflects zero objects, and it carries `A`-linear
derived global sections to the abelian-group-valued ones
(`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`), for which the
bound is [Stacks, Tag 08D4] part (3) at the uniform vanishing degree of
`AlgebraicGeometry.exists_isZero_rightDerivedPlus_globalSectionsGroup`. -/
@[ega "III 3.2.3" "more general"]
theorem exists_isLE_derivedGlobalSectionsOver_obj [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → ((derivedGlobalSectionsOver f).obj E).IsLE (d + N) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedPlus_globalSectionsGroup X
  refine ⟨(N : ℤ), fun E d hcoh hE => ?_⟩
  let T := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  let RGrp := ((globalSectionsGroup X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh W
  let αGrp := ((globalSectionsGroup X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh W
  have hbound : (RGrp.obj E).IsLE (d + (N : ℤ) - 1) :=
    isLE_rightDerivedFunctor_obj_addCommGrpCat X (globalSectionsGroup X) RGrp αGrp N hN E hcoh
      d hE
  let eT : derivedGlobalSectionsOver f ⋙ T.mapDerivedCategory ≅ RGrp :=
    Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
      (globalSectionsOver f) T
  rw [DerivedCategory.isLE_iff]
  intro m hm
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj (RGrp.obj E)) :=
    DerivedCategory.isZero_of_isLE _ (d + (N : ℤ) - 1) m (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
      (T.mapDerivedCategory.obj ((derivedGlobalSectionsOver f).obj E))) :=
    hz.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).mapIso (eT.app E))
  have hz'' : IsZero (T.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj
      ((derivedGlobalSectionsOver f).obj E))) :=
    hz'.of_iso ((T.mapDerivedCategoryHomologyIso m).app _).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hz'')

end GlobalSections

/-! ### From perfect to pseudo-coherent -/

section Main

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

omit [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
    [∀ (K₁ K₂ : HomologicalComplex
        (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
        (ComplexShape.up ℤ)] in
/-- **The dévissage of [Stacks, Tag 0CSH] for an exact functor out of `D(𝒪_X)` built from a
partial derived tensor product.** Let `F : D(𝒪_X) ⥤ D(𝒪_X)` be an exact functor carrying
`D^{≤ c}_QCoh` into `D^{≤ c + b}_QCoh` for every `c`. On a quasi-compact quasi-separated `X`, if
`RΓ(X, F(E))` is pseudo-coherent for every perfect `E`, it is pseudo-coherent for every
pseudo-coherent `E`. This is
`AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_obj_of_hasApproximationByPerfect` for
`G = F ⋙ RΓ(X, -)`, whose two inputs are [Stacks, Tag 08ES]
(`AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes`) and the bound
`exists_isLE_derivedGlobalSectionsOver_obj` on the cohomological dimension of `RΓ(X, -)`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_obj_of_isPseudoCoherent
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : DerivedCategory (StructureSheafModules X.sheaf) ⥤
      DerivedCategory (StructureSheafModules X.sheaf))
    [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]
    (b : ℤ)
    (hFqc : ∀ C : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
        C).IsQuasicoherent) →
      ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
        (F.obj C)).IsQuasicoherent)
    (hFle : ∀ (C : DerivedCategory (StructureSheafModules X.sheaf)) (c : ℤ), C.IsLE c →
      (F.obj C).IsLE (c + b))
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver f).obj (F.obj E)))
    (E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver f).obj (F.obj E)) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedGlobalSectionsOver_obj f
  let H : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
    derivedGlobalSectionsOver f
  let : H.CommShift ℤ := derivedGlobalSectionsOver_commShift f
  have : H.IsTriangulated := derivedGlobalSectionsOver_isTriangulated f
  refine PerfectApproximation.isPseudoCoherent_obj_of_hasApproximationByPerfect X
    (F ⋙ H) (b + N)
    (fun _ _ _ _ _ _ h => ⟨_, _, _, H.map_distinguished _ (F.map_distinguished _ h)⟩) ?_
    (PerfectApproximation.hasApproximationByPerfectComplexes X) hpc E hE
  intro C hCqc c hCvan i hi
  have hCle : C.IsLE (c - 1) := by
    rw [DerivedCategory.isLE_iff]
    exact fun j hj => hCvan j (by omega)
  have := hN (F.obj C) (c - 1 + b) (hFqc C hCqc) (hFle C (c - 1) hCle)
  exact DerivedCategory.isZero_of_isLE ((derivedGlobalSectionsOver f).obj (F.obj C))
    (c - 1 + b + N) i (by omega)

/-- **[Stacks, Tag 0CSH].** Let `A` be a ring, let `X` be a quasi-compact and quasi-separated
scheme over `A` (the structure morphism being `f : X ⟶ Spec A`), and let `K ∈ D^-_QCoh(𝒪_X)`,
i.e. `K` has quasi-coherent cohomology sheaves vanishing in all sufficiently large degrees. If
`RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every perfect `E` in `D(𝒪_X)`, then
`RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent in `D(A)` for every pseudo-coherent `E` in `D(𝒪_X)`.

The proof is the source's: by [Stacks, Tag 08ES] a pseudo-coherent `E` is approximated, in any
given degree, by a perfect `P ⟶ E` whose cone `C` has no cohomology from that degree on; tensoring
with `K` raises the vanishing bound by an upper bound `b` of the cohomology of `K` and keeps it in
`D_QCoh` ([Stacks, Tag 08DX]); `RΓ(X, -)` raises it by its cohomological dimension `N`
([Stacks, Tag 08D5]); so `RΓ(X, P ⊗^𝐋 K) ⟶ RΓ(X, E ⊗^𝐋 K)` is an isomorphism in high degrees and
the pseudo-coherence of its source passes to its target degree by degree. -/
@[stacks 0CSH]
theorem isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      K).IsQuasicoherent)
    (hKb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj K))
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K)))
    (E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj E).obj K)) := by
  obtain ⟨b, hb⟩ := hKb
  have hKle : K.IsLE b := by rwa [DerivedCategory.isLE_iff]
  exact isPseudoCoherent_derivedGlobalSectionsOver_obj_of_isPseudoCoherent f
    ((derivedTensor X.sheaf).flip.obj K)
    (hFs := (canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).commShift_left K)
    (hFt := (canonicalDerivedTensorProduct (Stacks.SheafOfModules.ringedSite X.sheaf)).exact_left K)
    b
    (fun C hC i => isQuasicoherent_homology_derivedTensor_obj_obj X C K hC hK i)
    (fun C c hC => isLE_derivedTensor_obj_obj X C K c b hC hKle) hpc E hE

/-- **[Stacks, Tag 0CSH], with the factors of the tensor product in the other order.** The same
statement for `RΓ(X, K ⊗^𝐋 E)`, the derived tensor product being symmetric: if
`RΓ(X, K ⊗^𝐋 E)` is pseudo-coherent in `D(A)` for every perfect `E`, then it is for every
pseudo-coherent `E`. The proof is that of
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent` with
the partial functor `K ⊗^𝐋 -` in place of `- ⊗^𝐋 K`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent'
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      K).IsQuasicoherent)
    (hKb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj K))
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)))
    (E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)) := by
  obtain ⟨b, hb⟩ := hKb
  have hKle : K.IsLE b := by rwa [DerivedCategory.isLE_iff]
  exact isPseudoCoherent_derivedGlobalSectionsOver_obj_of_isPseudoCoherent f
    ((derivedTensor X.sheaf).obj K)
    (hFs := (canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).commShift_right K)
    (hFt := (canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).exact_right K)
    b
    (fun C hC i => isQuasicoherent_homology_derivedTensor_obj_obj X K C hK hC i)
    (fun C c hC => by
      rw [add_comm c b]
      exact isLE_derivedTensor_obj_obj X K C b c hKle hC) hpc E hE

section Site

variable [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- **[Stacks, Tag 0CSH], with perfectness read on the ringed site of opens.** The statement of
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent'` with
the test objects `E` ranging over the objects of `D(𝒪_X)` that are perfect for the ringed site of
opens of `X` ([Stacks, Tag 08G5]) rather than for the ringed space ([Stacks, Tag 08CM]). The two
notions agree: a perfect object of the ringed space is perfect for the site
(`Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect`), which is the direction
needed to feed the hypothesis here to the ringed-space form. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent_of_ringedSite
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory (StructureSheafModules X.sheaf))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj
      K).IsQuasicoherent)
    (hKb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (StructureSheafModules X.sheaf) i).obj K))
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)))
    (E : DerivedCategory (StructureSheafModules X.sheaf))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E)) :=
  isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent' f K hK hKb
    (fun E' hE' => hpc E'
      (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E' hE'))
    E hE

end Site

end Main

end AlgebraicGeometry

end
