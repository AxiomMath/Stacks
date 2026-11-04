module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Duality.Sweep.NormalSheafAsSheafExt
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtComputation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomDegreeProjectionEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolution

/-!
# The right-derived sheaf Ext of two modules is the Ext sheaf of the derived internal Hom

Let `Y` be a ringed space and `F`, `G` sheaves of `𝒪_Y`-modules. Two definitions of the sheaf
Ext `𝓔xt^n_{𝒪_Y}(F, G)` are in use:

* `Stacks.RingedSpace.sheafExt Y F G n`, the `n`-th right derived functor of the internal Hom
  `𝓗om_{𝒪_Y}(F, -)` of [Stacks, Tag 03EN] evaluated at `G` — the definition [Stacks, Tag 0BQW]
  is formalized with;
* `Stacks.SheafOfModules.derivedSheafExt`, the `n`-th cohomology sheaf of the derived internal
  Hom `R𝓗om(F, G)` of [Stacks, Tag 08DH] — the definition of [Stacks, Tag 0BQP], which every
  other statement about Ext sheaves, [Stacks, Tag 0BQY] included, is phrased in.

This file identifies them, which is what allows [Stacks, Tag 0BQZ] to combine the two tags.

## Main definitions

* `Stacks.RingedSpace.sheafHomSingleInjectiveResolutionIso`: for an injective resolution `I` of
  `G`, the internal Hom complex out of `F` placed in degree zero into the `ℤ`-indexed resolution
  is the internal Hom functor applied degreewise to `I`, extended by zero.
* `Stacks.RingedSpace.sheafExtIsoDerivedSheafExt`: **the comparison**
  `sheafExt Y F G n ≅ derivedSheafExt (F[0]) (G[0]) n`.

## Implementation notes

The injective resolution is the one `CategoryTheory.Functor.rightDerived` uses,
`CategoryTheory.injectiveResolution G`, so no comparison of resolutions enters. Its `ℤ`-indexed
version `InjectiveResolution.cochainComplex` is a bounded below complex of injectives, hence
K-injective, and it computes the derived internal Hom by
`Stacks.SheafOfModules.derivedSheafHomComparison`. The internal Hom complex out of a complex
concentrated in degree zero has, in degree `m`, the single factor `𝓗om(F, I^m)`
(`AlgebraicGeometry.RingedSite.homDegreeProjection` at `q = 0`), and its differential is
postcomposition with the differential of `I`: by the Leibniz rule
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_differential`) the other summand involves the
differential of the source, which vanishes.

## References

* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
* [Stacks Project, Tag 0BQW](https://stacks.math.columbia.edu/tag/0BQW)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open HomologicalComplex Stacks.SheafOfModules.InternalHom

universe u

namespace Stacks.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F G : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier) Y.sheaf))

/-- The complex concentrated in degree zero on `F`. -/
abbrev singleZero : CochainComplex
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf)) ℤ :=
  (single _ (ComplexShape.up ℤ) 0).obj F

/-- The internal Hom functor out of `F`, applied degreewise to the `ℕ`-indexed injective
resolution of `G` that the right derived functor uses. -/
abbrev internalHomResolution : CochainComplex
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
        Y.sheaf)) ℕ :=
  ((internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
    F).mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution G).cocomplex

/-- The projection of the degree-`m` term of `SheafHom^•(F[0], I)` onto its only nonvanishing
factor `𝓗om(F, I^m)` is an isomorphism. -/
theorem isIso_homDegreeProjection_singleSource
    (I : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)) ℤ)
    (m : ℤ) :
    IsIso (RingedSite.homDegreeProjection (Stacks.SheafOfModules.ringedSite Y.sheaf)
      (singleZero Y F) I m 0) := by
  refine Stacks.Limits.isIso_fan_proj_of_isZero
    (RingedSite.homDegreeIsLimit (Stacks.SheafOfModules.ringedSite Y.sheaf) _ I m) 0
    fun q hq => RingedSite.internalHomSheaf_isZero_of_isZero _
      (isZero_single_obj_X (ComplexShape.up ℤ) 0 F (-q) (by omega))

/-- **The differential of `SheafHom^•(F[0], I)` read on the factor `𝓗om(F, I^m)` is
postcomposition with the differential of `I`.** By the Leibniz rule the other summand of the
differential precomposes with the differential of `F[0]`, which vanishes. -/
theorem sheafHomComplex_d_comp_homDegreeProjection_singleSource
    (I : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)) ℤ)
    (m : ℤ) :
    (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) (singleZero Y F)
        I).obj.d m (m + 1) ≫
      RingedSite.homDegreeProjection (Stacks.SheafOfModules.ringedSite Y.sheaf)
        (singleZero Y F) I (m + 1) 0 =
    RingedSite.homDegreeProjection (Stacks.SheafOfModules.ringedSite Y.sheaf)
        (singleZero Y F) I m 0 ≫
      RingedSite.internalHomPost (Stacks.SheafOfModules.ringedSite Y.sheaf)
        (I.d (m - 0) (m + 1 - 0)) := by
  let X := Stacks.SheafOfModules.ringedSite Y.sheaf
  let H := RingedSite.sheafHomComplex X (singleZero Y F) I
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun s => ?_))
  refine PresheafOfModules.hom_ext fun W => ?_
  ext x
  have hc : AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f (m + 1))
        ((H.obj.d m (m + 1)).val.app U s) =
      CochainComplex.HomComplex.δ m (m + 1)
        (AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f m) s) :=
    (congrArg (fun z => AddCommGrpCat.Hom.hom z s)
      ((H.sectionsIso U.unop).hom.comm m (m + 1))).symm
  have hdU : (RingedSite.restrictComplex X (singleZero Y F) U.unop).d (-0) (-0 + 1) = 0 := by
    change (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.unop).map
      ((singleZero Y F).d (-0) (-0 + 1)) = 0
    rw [single_obj_d, Functor.map_zero]
  have key : ∀ z : CochainComplex.HomComplex.Cochain
        (RingedSite.restrictComplex X (singleZero Y F) U.unop)
        (RingedSite.restrictComplex X I U.unop) m,
      (CochainComplex.HomComplex.δ m (m + 1) z).v (-0) (m + 1 - 0) (by omega) =
        z.v (-0) (m - 0) (by omega) ≫
          (RingedSite.restrictComplex X I U.unop).d (m - 0) (m + 1 - 0) := by
    intro z
    rw [CochainComplex.HomComplex.δ_v m (m + 1) rfl z (-0) (m + 1 - 0) (by omega) (m - 0)
      (-0 + 1) (by omega) rfl, hdU, zero_comp, smul_zero, add_zero]
  refine Eq.trans (congrArg
    (fun z : CochainComplex.HomComplex.Cochain
        (RingedSite.restrictComplex X (singleZero Y F) U.unop)
        (RingedSite.restrictComplex X I U.unop) (m + 1) =>
      ((z.v (-0) (m + 1 - 0) (by omega)).val.app W) x) hc) ?_
  refine Eq.trans (congrArg
    (fun φ : (RingedSite.restrictComplex X (singleZero Y F) U.unop).X (-0) ⟶
        (RingedSite.restrictComplex X I U.unop).X (m + 1 - 0) => (φ.val.app W) x)
    (key (AddCommGrpCat.Hom.hom ((H.sectionsIso U.unop).hom.f m) s))) ?_
  rfl

/-- The degree-`i` term of `SheafHom^•(F[0], I)` is `𝓗om(F, I^i)`. -/
def sheafHomSingleSourceXIso
    (I : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)) ℤ)
    (i : ℤ) :
    (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) (singleZero Y F)
        I).obj.X i ≅
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).obj (I.X i) :=
  haveI := isIso_homDegreeProjection_singleSource Y F I i
  asIso (RingedSite.homDegreeProjection (Stacks.SheafOfModules.ringedSite Y.sheaf)
      (singleZero Y F) I i 0) ≪≫
    (Iso.refl _ : RingedSite.internalHomSheaf (Stacks.SheafOfModules.ringedSite Y.sheaf)
        ((singleZero Y F).X (-0)) (I.X (i - 0)) ≅
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).obj (I.X (i - 0))) ≪≫
    (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      F).mapIso (I.XIsoOfEq (sub_zero i))

/-- The degreewise identification commutes with the differentials. -/
theorem sheafHomSingleSourceXIso_comm
    (I : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)) ℤ)
    (i j : ℤ) (hij : i + 1 = j) :
    (sheafHomSingleSourceXIso Y F I i).hom ≫
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
          F).map (I.d i j) =
      (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) (singleZero Y F)
          I).obj.d i j ≫ (sheafHomSingleSourceXIso Y F I j).hom := by
  subst hij
  have h := sheafHomComplex_d_comp_homDegreeProjection_singleSource Y F I i
  simp only [sheafHomSingleSourceXIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [reassoc_of% h]
  congr 1
  change (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      F).map (I.XIsoOfEq (sub_zero i)).hom ≫
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).map (I.d i (i + 1)) =
    (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
      F).map (I.d (i - 0) (i + 1 - 0)) ≫
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).map (I.XIsoOfEq (sub_zero (i + 1))).hom
  rw [← Functor.map_comp, ← Functor.map_comp, XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom]

/-- **The internal Hom complex out of a module placed in degree zero is the internal Hom functor
applied degreewise.** `SheafHom^•(F[0], I) ≅ 𝓗om(F, I^•)`. -/
def sheafHomSingleSourceIso
    (I : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology Y.carrier)
          Y.sheaf)) ℤ) :
    (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) (singleZero Y F)
        I).obj ≅
      ((internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf
        F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  (Hom.isoOfComponents (sheafHomSingleSourceXIso Y F I)
    (fun i j hij => sheafHomSingleSourceXIso_comm Y F I i j hij))

/-- **The comparison of the two sheaf Ext's.** The `n`-th right derived functor of the internal
Hom `𝓗om_{𝒪_Y}(F, -)` at `G`, which is the sheaf Ext of [Stacks, Tag 0BQW], is the `n`-th
cohomology sheaf of the derived internal Hom `R𝓗om(F, G)`, which is the Ext sheaf of
[Stacks, Tag 0BQP]. Both are computed by the injective resolution of `G` that the right derived
functor uses: on one side directly, on the other because that resolution, indexed by `ℤ`, is
K-injective and so computes the derived internal Hom as an ordinary internal Hom complex. -/
def sheafExtIsoDerivedSheafExt (n : ℕ) :
    Stacks.RingedSpace.sheafExt Y F G n ≅
      Stacks.SheafOfModules.derivedSheafExt Y.sheaf
        (DerivedCategory.Q.obj ((HomologicalComplex.single
          (Stacks.SheafOfModules.StructureSheafModules Y.sheaf) (ComplexShape.up ℤ) 0).obj F))
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) n :=
  haveI hK : (injectiveResolution G).cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  haveI : IsIso (DerivedCategory.Q.map (injectiveResolution G).ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  (injectiveResolution G).isoRightDerivedObj
      (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf F)
      n ≪≫
    ((internalHomResolution Y F G).extendHomologyIso ComplexShape.embeddingUpNat
      (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso
        (internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology Y.carrier) Y.sheaf F)
        (injectiveResolution G).cocomplex ComplexShape.embeddingUpNat ≪≫
      (sheafHomSingleSourceIso Y F (injectiveResolution G).cochainComplex).symm) ≪≫
    ((DerivedCategory.homologyFunctorFactors _ (n : ℤ)).app
      (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Y.sheaf) (singleZero Y F)
        (injectiveResolution G).cochainComplex).obj).symm ≪≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      (Stacks.SheafOfModules.derivedSheafHomComparison Y.sheaf (singleZero Y F)
        (injectiveResolution G).cochainComplex (hI := hK)).symm ≪≫
    Stacks.SheafOfModules.derivedSheafExtMapIso Y.sheaf (n : ℤ) (Iso.refl _)
      (asIso (DerivedCategory.Q.map (injectiveResolution G).ι')).symm

end Stacks.RingedSpace
