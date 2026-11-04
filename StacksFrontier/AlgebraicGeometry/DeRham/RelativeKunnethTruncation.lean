module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapUnbounded
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatCohomology
public import StacksFrontier.Algebra.Homology.StupidTruncationLE
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution

/-!
# The relative Künneth map at a locally bounded complex, by truncation

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes, let
`W = X ×_S Y` and `f = p ∘ a`. Let `F^•` on `X/S` and `G^•` on `Y/S` be complexes of
quasi-coherent modules whose differentials are differential operators of finite order, both
strictly bounded below. A family of maps

`Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^• ⟶ Rf_*Tot(F^• ⊠ G^•)`

natural in both complexes, such as the relative Künneth map of [Stacks, Tag 0G4B], is invertible
at a *locally bounded* `F^•` with terms flat over `a^{-1}𝒪_S` as soon as it is invertible at the
stupid truncations `σ^{≤N}` of both complexes, which have finitely many nonzero terms.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_of_isIso_stupidTrunc`: for any family of Künneth maps
  natural in both complexes, invertibility at every pair `(σ^{≤N}F^•, σ^{≤N}G^•)` gives
  invertibility at `(F^•, G^•)`.
* `Stacks.Cohomology.BoxKunneth.isGE_derivedTensor_derivedPushforward_obj`:
  `Ra_*F^• ⊗^𝐋_{𝒪_S} E` lies in degrees `≥ m + e` when `F^•` is locally bounded with flat
  quasi-coherent terms vanishing below `m`, and `E ∈ D_QCoh(𝒪_S)` lies in degrees `≥ e`.
* `Stacks.Cohomology.BoxKunneth.derivedCategoryB_derivedPushforward_obj_of_isStrictlyGE`:
  [Stacks, Tag 0FML] (2) for the unbounded derived direct image.

## References

* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.BoxKunneth

open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Cohomology of a morphism in a range, from a triangle -/

section Triangles

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- In a distinguished triangle whose first morphism is invertible on cohomology in every degree
`≤ M`, the third vertex is concentrated in degrees `≥ M`. -/
theorem isGE_obj₃_of_isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (M : ℤ)
    (h : ∀ i, i ≤ M → IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁)) :
    T.obj₃.IsGE M := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have := h i (by omega)
  have := h (i + 1) (by omega)
  have hz : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 inferInstance
  have hδ : DerivedCategory.HomologySequence.δ T i (i + 1) = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1 inferInstance
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_of_both_zeros hz hδ

variable (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]

/-- **A morphism of complexes which is invertible in every degree `≤ M`, followed by a
triangulated functor which does not lower degrees, is invertible on cohomology below `M - 1`.** -/
theorem isIso_homologyMap_map_Q_map_of_isIso_f
    (hF : ∀ (E : DerivedCategory C) (n : ℤ), E.IsGE n → (F.obj E).IsGE n)
    {A B : CochainComplex C ℤ} (g : A ⟶ B) (M : ℤ) (hg : ∀ n, n ≤ M → IsIso (g.f n))
    (d : ℤ) (hd : d < M - 1) :
    IsIso ((DerivedCategory.homologyFunctor D d).map (F.map (DerivedCategory.Q.map g))) := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map g)
  have hZ : Z.IsGE (M - 1) := by
    refine isGE_obj₃_of_isIso_homologyMap_mor₁ _ hT (M - 1) fun i hi ↦ ?_
    have : IsIso (HomologicalComplex.homologyMap g i) :=
      StacksDraft.TotalComplexQuasiIso.isIso_homologyMap_of_isIso_f g i (hg _ (by omega))
        (hg _ (by omega)) (hg _ (by omega))
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i) g).2 this
  exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ (F.mapTriangle.obj (Triangle.mk _ v w))
    (F.map_distinguished _ hT) d (M - 1) (hF Z (M - 1) hZ) hd

/-- **The quotient map of a short exact sequence of complexes, followed by a triangulated
functor, is invertible on cohomology below `m - 1`** as soon as the functor carries the kernel
into degrees `≥ m`. -/
theorem isIso_homologyMap_map_Q_map_g_of_isGE {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (m : ℤ) (hX : (F.obj (DerivedCategory.Q.obj S.X₁)).IsGE m) (d : ℤ)
    (hd : d < m - 1) :
    IsIso ((DerivedCategory.homologyFunctor D d).map (F.map (DerivedCategory.Q.map S.g))) := by
  have hT := F.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  have : ((F.obj (DerivedCategory.Q.obj S.X₁))⟦(1 : ℤ)⟧).IsGE (m - 1) :=
    DerivedCategory.TStructure.t.isGE_shift _ m 1 (m - 1) (by omega)
  exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ (rot_of_distTriang _ hT) d (m - 1)
    this hd

end Triangles

/-! ### Amplitude of `Ra_*F^• ⊗^𝐋 E` -/

section Amplitude

open Stacks.RelativeComplexPushforward
  (relativeComplexProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent)

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`Ra_*F^• ⊗^𝐋_{𝒪_S} E` lies in degrees `≥ m + e`** when `F^•` is a locally bounded
complex of flat `a^{-1}𝒪_S`-modules vanishing below `m`, with quasi-coherent terms, and `E` lies
in `D_QCoh(𝒪_S)` and in degrees `≥ e`. -/
theorem isGE_derivedTensor_derivedPushforward_obj [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ) (m : ℤ) [F.IsStrictlyGE m]
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (E : DerivedCategory (Modules S.toRingedSpace))
    (hE : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) E) (e : ℤ) [E.IsGE e] :
    (((derivedTensorProductFunctor.{u, u + 1} S.toRingedSpace.sheaf).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F))).obj E).IsGE (m + e) := by
  have : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback
      S.toRingedSpace f.base
  have : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback (inverseImageBaseProjection f)) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  have eIso := AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso
    (inverseImageBaseProjection f)
  obtain ⟨E₀, _, ⟨eE⟩⟩ := E.exists_iso_Q_obj_of_isGE e
  let P : CochainComplex (Modules (inverseImageBase f)) ℤ :=
    ((RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseProjection f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀
  have hkflat : Stacks.SheafOfModules.KFlat.KFlat (inverseImageBase f).sheaf F :=
    Stacks.Cohomology.LocallyBoundedKFlat.kFlat_of_isLocallyBounded_of_flat _ F hF hflat
  have ePull : (derivedPullback (inverseImageBaseProjection f)).obj E ≅
      DerivedCategory.Q.obj P :=
    (derivedPullback (inverseImageBaseProjection f)).mapIso eE ≪≫ eIso.app _ ≪≫
      (Functor.mapDerivedCategoryFactors (RingedSpaceModuleAdjunction.modulePullback
        (inverseImageBaseProjection f))).app E₀
  have eTensor := ((derivedTensorProductFunctor (inverseImageBase f).sheaf).obj
      (DerivedCategory.Q.obj F)).mapIso ePull ≪≫
    (canonicalDerivedTensorProduct (inverseImageBase f).sheaf).comparisonLeft F P hkflat
  have hP : CochainComplex.IsStrictlyGE P e := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (RingedSpaceModuleAdjunction.modulePullback
      (inverseImageBaseProjection f)).map_isZero (E₀.isZero_of_isStrictlyGE e i hi)
  have hT := Stacks.DerivedTensor.RingedSite.isStrictlyGE_mapBifunctor
    (R := (inverseImageBase f).sheaf) F P m e
  have hQ : (DerivedCategory.Q.obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
        P)).IsGE (m + e) := by
    have : CochainComplex.IsStrictlyGE
        (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj P)
        (m + e) := hT
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  have hInner := DerivedCategory.TStructure.t.isGE_of_iso eTensor.symm (m + e)
  have hPush := Stacks.SmallDerivedCategory.isGE_obj_of_isGE
    (RingedSpaceModuleAdjunction.modulePushforward (inverseImageBaseProjection f))
    (derivedPushforward (inverseImageBaseProjection f))
    (derivedPushforwardUnit (inverseImageBaseProjection f))
    (isIso_derivedPushforwardUnit_app_of_isKInjective (inverseImageBaseProjection f)) _ _
    hInner
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (relativeComplexProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent
      f E hE F hF M hM hFM).symm (m + e)

/-- **[Stacks, Tag 0FML] (2) for the unbounded derived direct image**: for `a` quasi-compact and
quasi-separated and `F^•` a strictly bounded below complex of `a^{-1}𝒪_S`-modules whose terms
are quasi-coherent `𝒪_X`-modules, `Ra_*F^•` lies in `D_QCoh(𝒪_S)`. -/
theorem derivedCategoryB_derivedPushforward_obj_of_isStrictlyGE [QuasiCompact f]
    [QuasiSeparated f] (F : CochainComplex (Modules (inverseImageBase f)) ℤ) (n : ℤ)
    [F.IsStrictlyGE n] (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj F)) := fun i ↦
  (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((boundedDerivedPushforwardIso (inverseImageBaseProjection f)).app
        (DerivedCategory.Plus.Q.obj ⟨F, n, inferInstance⟩)))
    (Stacks.RelativeComplexPushforward.derivedCategoryB_relativeDerivedPushforward f n F M hM
      hFM i)

end Amplitude

/-! ### The two stupid truncations of a complex, read in an abelian category -/

section Truncation

open HomologicalComplex ComplexShape

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [Abelian ℬ] (G : 𝒜 ⥤ ℬ) [G.PreservesZeroMorphisms] (K : CochainComplex 𝒜 ℤ) (N : ℤ)

/-- **The short exact sequence `0 ⟶ G(σ^{≥N+1}K) ⟶ G(K) ⟶ G(σ^{≤N}K) ⟶ 0`** of complexes in an
abelian category, for a functor `G` out of a preadditive category preserving zero morphisms. -/
def mapStupidTruncShortComplex : ShortComplex (CochainComplex ℬ ℤ) :=
  ShortComplex.mk ((G.mapHomologicalComplex (up ℤ)).map (K.ιStupidTrunc (embeddingUpIntGE (N + 1))))
    ((G.mapHomologicalComplex (up ℤ)).map (K.πStupidTrunc (embeddingUpIntLE N))) (by
      rw [← Functor.map_comp]
      have : K.ιStupidTrunc (embeddingUpIntGE (N + 1)) ≫ K.πStupidTrunc (embeddingUpIntLE N) =
          0 := by
        ext n
        by_cases hn : n ≤ N
        · exact (CochainComplex.isZero_of_isStrictlyGE _ (N + 1) n (by omega)).eq_of_src _ _
        · exact (CochainComplex.isZero_of_isStrictlyLE _ N n (by omega)).eq_of_tgt _ _
      rw [this, Functor.map_zero])

/-- The sequence `0 ⟶ G(σ^{≥N+1}K) ⟶ G(K) ⟶ G(σ^{≤N}K) ⟶ 0` is short exact. -/
theorem mapStupidTruncShortComplex_shortExact : (mapStupidTruncShortComplex G K N).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  let S := (mapStupidTruncShortComplex G K N).map (eval ℬ (up ℤ) n)
  change S.ShortExact
  by_cases hn : n ≤ N
  · apply (ShortComplex.Splitting.ofIsZeroOfIsIso S ?_ ?_).shortExact
    · exact G.map_isZero (CochainComplex.isZero_of_isStrictlyGE _ (N + 1) n (by omega))
    · change IsIso (G.map ((K.πStupidTrunc (embeddingUpIntLE N)).f n))
      have := StacksDraft.StupidTruncation.isIso_πStupidTruncLE_f K N n hn
      infer_instance
  · apply (ShortComplex.Splitting.ofIsIsoOfIsZero S ?_ ?_).shortExact
    · change IsIso (G.map ((K.ιStupidTrunc (embeddingUpIntGE (N + 1))).f n))
      rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K (N + 1) n (by omega)]
      infer_instance
    · exact G.map_isZero (CochainComplex.isZero_of_isStrictlyLE _ N n (by omega))

/-- Every term of a stupid truncation is either zero or the corresponding term of the complex. -/
theorem isZero_or_nonempty_iso_stupidTrunc_X {ι : Type*} {c : ComplexShape ι}
    (e : c.Embedding (up ℤ)) [e.IsRelIff] (i : ℤ) :
    IsZero ((K.stupidTrunc e).X i) ∨ Nonempty ((K.stupidTrunc e).X i ≅ K.X i) := by
  by_cases h : ∃ j, e.f j = i
  · exact Or.inr ⟨K.stupidTruncXIso e h.choose_spec⟩
  · exact Or.inl (K.isZero_stupidTrunc_X e i fun j hj ↦ h ⟨j, hj⟩)

end Truncation

/-! ### Truncating both complexes of a natural family of Künneth maps -/

section Core

open HomologicalComplex ComplexShape

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The derived direct image along a morphism of ringed spaces does not lower degrees. -/
theorem isGE_derivedPushforward_obj_of_isGE {Z W : RingedSpace.{u, u}} (g : Z ⟶ W)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) (n : ℤ) (hE : E.IsGE n) :
    ((derivedPushforward.{u, u + 1, u + 1} g).obj E).IsGE n :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (RingedSpaceModuleAdjunction.modulePushforward g)
    (derivedPushforward g) (derivedPushforwardUnit g)
    (isIso_derivedPushforwardUnit_app_of_isKInjective g) E n hE

/-- The source `Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^•` of the Künneth map of the box product. -/
abbrev boxKunnethSource (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    DerivedCategory (Modules S.toRingedSpace) :=
  ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K)))).obj
    ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
      (DerivedCategory.Q.obj (rightComplex b L)))

/-- The target `Rf_*Tot(F^• ⊠ G^•)` of the Künneth map of the box product, the total complex
being formed over `f^{-1}𝒪_S` with no boundedness condition. -/
abbrev boxKunnethTarget (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    DerivedCategory (Modules S.toRingedSpace) :=
  (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
    (DerivedCategory.Q.obj
      (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b) (ComplexShape.up ℤ)))

/-- A morphism of complexes of the box product, one factor fixed, is invertible in total degree
`k` as soon as the morphism of the other factor is invertible in every degree `j` for which the
fixed factor is nonzero in degree `k - j`. -/
theorem isIso_mapBifunctorMap_f
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ}
    (φ : K ⟶ K') (χ : L ⟶ L') (k : ℤ)
    (h : ∀ p q, p + q = k → (IsIso (φ.f p) ∧ IsIso (χ.f q)) ∨
      (IsZero (K.X p) ∧ IsZero (K'.X p)) ∨ (IsZero (L.X q) ∧ IsZero (L'.X q))) :
    IsIso ((HomologicalComplex.mapBifunctorMap φ χ (boxProductRelativeCurried a b)
      (ComplexShape.up ℤ)).f k) := by
  refine StacksDraft.TotalComplexQuasiIso.isIso_total_map_f _ k fun p q hpq ↦ ?_
  rcases h p q hpq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Functor.mapBifunctorHomologicalComplex_map_app_f_f,
      Functor.mapBifunctorHomologicalComplex_obj_map_f_f]
    exact IsIso.comp_isIso'
      (((boxProductRelativeCurried a b).mapIso (asIso (φ.f p))).app (L.X q)).isIso_hom
      (((boxProductRelativeCurried a b).obj (K'.X p)).mapIso (asIso (χ.f q))).isIso_hom
  · refine IsZero.isIso ?_ ?_ _
    · exact ((boxProductRelativeCurried a b).map_isZero h₁).obj _
    · exact ((boxProductRelativeCurried a b).map_isZero h₂).obj _
  · refine IsZero.isIso ?_ ?_ _
    · exact ((boxProductRelativeCurried a b).obj _).map_isZero h₁
    · exact ((boxProductRelativeCurried a b).obj _).map_isZero h₂

/-- A complex each of whose terms is zero or isomorphic to the corresponding term of a locally
bounded complex is locally bounded. -/
theorem isLocallyBounded_of_isZero_or_nonempty_iso {Z : RingedSpace.{u, u}}
    {F T : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded Z F)
    (h : ∀ i, IsZero (T.X i) ∨ Nonempty (T.X i ≅ F.X i)) :
    Stacks.SheafOfModules.OnSpace.IsLocallyBounded Z T := by
  intro x
  obtain ⟨U, hx, s, hs⟩ := hF x
  refine ⟨U, hx, s, fun i hi ↦ ?_⟩
  rcases h i with hz | he
  · exact Stacks.SheafOfModules.OnSpace.isZero_over_of_isZero Z hz U
  · obtain ⟨e⟩ := he
    exact (hs i hi).of_iso ((SheafOfModules.overFunctor _ U).mapIso e)

variable {a} in
/-- The complex of `a^{-1}𝒪_S`-modules underlying a stupid truncation of a locally bounded
complex with flat terms is locally bounded with flat terms. -/
theorem isLocallyBounded_and_isFlat_leftComplex_stupidTrunc
    {K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (up ℤ)) [e.IsRelIff] :
    Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a)
        (leftComplex a (K.stupidTrunc e)) ∧
      ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := (inverseImageBase a).sheaf) ((leftComplex a (K.stupidTrunc e)).X i) := by
  have h : ∀ i, IsZero ((leftComplex a (K.stupidTrunc e)).X i) ∨
      Nonempty ((leftComplex a (K.stupidTrunc e)).X i ≅ (leftComplex a K).X i) := fun i ↦ by
    rcases isZero_or_nonempty_iso_stupidTrunc_X K e i with hz | he
    · exact Or.inl ((toInverseImageModules a).map_isZero hz)
    · obtain ⟨e'⟩ := he
      exact Or.inr ⟨(toInverseImageModules a).mapIso e'⟩
  refine ⟨isLocallyBounded_of_isZero_or_nonempty_iso hK h, fun i ↦ ?_⟩
  rcases h i with hz | he
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero _ hz
  · obtain ⟨e'⟩ := he
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso _ e'.symm (hKflat i)

/-- A family of maps `Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^• ⟶ Rf_*Tot(F^• ⊠ G^•)`, one for each pair of
complexes. -/
abbrev KunnethFamily :=
  ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ),
    boxKunnethSource a b K L ⟶ boxKunnethTarget a b K L

/-- Naturality of a family of Künneth maps in the first complex. -/
def KunnethFamily.NaturalLeft (ψ : KunnethFamily a b) : Prop :=
  ∀ {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    (φ : K ⟶ K') (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ),
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules a).mapHomologicalComplex (up ℤ)).map φ)))).app
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ≫ ψ K' L =
      ψ K L ≫ (derivedPushforward.{u, u + 1, u + 1}
        (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
            (boxProductRelativeCurried a b) (up ℤ)))

/-- Naturality of a family of Künneth maps in the second complex. -/
def KunnethFamily.NaturalRight (ψ : KunnethFamily a b) : Prop :=
  ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (χ : L ⟶ L'),
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
          (DerivedCategory.Q.map
            (((toInverseImageModules b).mapHomologicalComplex (up ℤ)).map χ))) ≫ ψ K L' =
      ψ K L ≫ (derivedPushforward.{u, u + 1, u + 1}
        (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) χ
            (boxProductRelativeCurried a b) (up ℤ)))

variable {a b} [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]

/-- In a commutative square `s ≫ f' = f ≫ t`, the map `H f` is invertible as soon as `H s`,
`H f'` and `H t` are. -/
private theorem isIso_map_of_isIso_map_of_comm_sq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (H : 𝒞 ⥤ 𝒟) {A B A' B' : 𝒞} {f : A ⟶ B} {s : A ⟶ A'} {t : B ⟶ B'} {f' : A' ⟶ B'}
    (hs : IsIso (H.map s)) (h : IsIso (H.map f')) (ht : IsIso (H.map t))
    (sq : s ≫ f' = f ≫ t) : IsIso (H.map f) := by
  have e := congrArg H.map sq
  rw [H.map_comp, H.map_comp] at e
  have hc : IsIso (H.map f ≫ H.map t) := by
    rw [← e]
    exact IsIso.comp_isIso' hs h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ ht hc

/-- The derived direct image of a strictly `≥ n` complex on `Y/S` lies in `D_QCoh` and in degrees
`≥ n`. -/
private theorem derivedCategoryB_and_isGE_derivedPushforward_rightComplex
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (n : ℤ)
    [L.IsStrictlyGE n] :
    DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L))) ∧
    ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
      (DerivedCategory.Q.obj (rightComplex b L))).IsGE n :=
  ⟨derivedCategoryB_derivedPushforward_obj_of_isStrictlyGE b _ n (fun i ↦ (L.X i).module)
    (fun _ ↦ inferInstance) (fun _ ↦ Iso.refl _),
  isGE_derivedPushforward_obj_of_isGE _ _ n (by
    rw [DerivedCategory.isGE_Q_obj_iff]; infer_instance)⟩

/-- **Truncating the second complex does not change cohomology in degrees `< N + n₁ - 1`.** -/
theorem isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_right (ψ : KunnethFamily a b)
    (hψ : ψ.NaturalRight)
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ : ℤ) [K.IsStrictlyGE n₁]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (N d : ℤ) (hd : d < N + n₁ - 1)
    (h : IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map
      (ψ K (L.stupidTrunc (embeddingUpIntLE N))))) :
    IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map (ψ K L)) := by
  let H := DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d
  let T := canonicalDerivedTensorProduct.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)
  let A := (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
    (DerivedCategory.Q.obj (leftComplex a K))
  let L'' := L.stupidTrunc (embeddingUpIntGE (N + 1))
  let πL := L.πStupidTrunc (embeddingUpIntLE N)
  let g := inverseImageBaseProjection (pullback.fst a b ≫ a)
  let _ := derivedPushforwardCommShift (inverseImageBaseProjection b)
  have _ := derivedPushforward_isTriangulated (inverseImageBaseProjection b)
  let _ := derivedPushforwardCommShift g
  have _ := derivedPushforward_isTriangulated g
  let _ : (T.tensor.obj A).CommShift ℤ := T.commShift_right A
  have _ : (T.tensor.obj A).IsTriangulated := T.exact_right A
  have hL'' := derivedCategoryB_and_isGE_derivedPushforward_rightComplex L'' (N + 1)
  have := hL''.2
  have hs : IsIso (H.map ((T.tensor.obj A).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
        (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex (up ℤ)).map
          πL))))) :=
    isIso_homologyMap_map_Q_map_g_of_isGE
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b) ⋙ T.tensor.obj A)
      (mapStupidTruncShortComplex_shortExact (toInverseImageModules b) L N) (n₁ + (N + 1))
      (isGE_derivedTensor_derivedPushforward_obj a (leftComplex a K) n₁ hK hKflat
        (fun i ↦ (K.X i).module) (fun _ ↦ inferInstance) (fun _ ↦ Iso.refl _) _ hL''.1
        (N + 1)) d (by omega)
  have ht : IsIso (H.map ((derivedPushforward.{u, u + 1, u + 1} g).map
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) πL
        (boxProductRelativeCurried a b) (up ℤ))))) :=
    isIso_homologyMap_map_Q_map_of_isIso_f (derivedPushforward.{u, u + 1, u + 1} g)
      (isGE_derivedPushforward_obj_of_isGE g) _ (N + n₁) (fun k hk ↦
        isIso_mapBifunctorMap_f a b _ _ k fun p q hpq ↦ by
          by_cases hq : q ≤ N
          · exact Or.inl ⟨inferInstance,
              StacksDraft.StupidTruncation.isIso_πStupidTruncLE_f L N q hq⟩
          · exact Or.inr (Or.inl ⟨CochainComplex.isZero_of_isStrictlyGE _ n₁ p (by omega),
              CochainComplex.isZero_of_isStrictlyGE _ n₁ p (by omega)⟩)) d (by omega)
  exact isIso_map_of_isIso_map_of_comm_sq H hs h ht (hψ K πL)

/-- **Truncating the first complex does not change cohomology in degrees `< N + n₂ - 1`.** -/
theorem isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_left (ψ : KunnethFamily a b)
    (hψ : ψ.NaturalLeft)
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₂ : ℤ) [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (N d : ℤ) (hd : d < N + n₂ - 1)
    (h : IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map
      (ψ (K.stupidTrunc (embeddingUpIntLE N)) L))) :
    IsIso ((DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d).map (ψ K L)) := by
  let H := DerivedCategory.homologyFunctor (Modules S.toRingedSpace) d
  let T := canonicalDerivedTensorProduct.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)
  let E := (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
    (DerivedCategory.Q.obj (rightComplex b L))
  let K'' := K.stupidTrunc (embeddingUpIntGE (N + 1))
  let πK := K.πStupidTrunc (embeddingUpIntLE N)
  let g := inverseImageBaseProjection (pullback.fst a b ≫ a)
  let _ := derivedPushforwardCommShift (inverseImageBaseProjection a)
  have _ := derivedPushforward_isTriangulated (inverseImageBaseProjection a)
  let _ := derivedPushforwardCommShift g
  have _ := derivedPushforward_isTriangulated g
  let _ : (T.tensor.flip.obj E).CommShift ℤ := T.commShift_left E
  have _ : (T.tensor.flip.obj E).IsTriangulated := T.exact_left E
  have hK'' := isLocallyBounded_and_isFlat_leftComplex_stupidTrunc hK hKflat
    (embeddingUpIntGE (N + 1))
  have hL := derivedCategoryB_and_isGE_derivedPushforward_rightComplex L n₂
  have := hL.2
  have hs : IsIso (H.map ((T.tensor.flip.obj E).map
      ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
        (DerivedCategory.Q.map (((toInverseImageModules a).mapHomologicalComplex (up ℤ)).map
          πK))))) :=
    isIso_homologyMap_map_Q_map_g_of_isGE
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a) ⋙ T.tensor.flip.obj E)
      (mapStupidTruncShortComplex_shortExact (toInverseImageModules a) K N) ((N + 1) + n₂)
      (isGE_derivedTensor_derivedPushforward_obj a (leftComplex a K'') (N + 1) hK''.1 hK''.2
        (fun i ↦ (K''.X i).module) (fun _ ↦ inferInstance) (fun _ ↦ Iso.refl _) E hL.1 n₂)
      d (by omega)
  have ht : IsIso (H.map ((derivedPushforward.{u, u + 1, u + 1} g).map
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap πK (𝟙 L)
        (boxProductRelativeCurried a b) (up ℤ))))) :=
    isIso_homologyMap_map_Q_map_of_isIso_f (derivedPushforward.{u, u + 1, u + 1} g)
      (isGE_derivedPushforward_obj_of_isGE g) _ (N + n₂) (fun k hk ↦
        isIso_mapBifunctorMap_f a b _ _ k fun p q hpq ↦ by
          by_cases hp : p ≤ N
          · exact Or.inl ⟨StacksDraft.StupidTruncation.isIso_πStupidTruncLE_f K N p hp,
              inferInstance⟩
          · exact Or.inr (Or.inr ⟨CochainComplex.isZero_of_isStrictlyGE _ n₂ q (by omega),
              CochainComplex.isZero_of_isStrictlyGE _ n₂ q (by omega)⟩)) d (by omega)
  exact isIso_map_of_isIso_map_of_comm_sq H hs h ht (hψ πK L)

/-- **A natural family of Künneth maps is invertible at a locally bounded complex as soon as it
is invertible at its stupid truncations.** Let `ψ` be a family of maps
`Ra_*F^• ⊗^𝐋_{𝒪_S} Rb_*G^• ⟶ Rf_*Tot(F^• ⊠ G^•)`, natural in both complexes, for `a` and `b`
quasi-compact and quasi-separated. Let `F^•` be locally bounded with terms flat over
`a^{-1}𝒪_S`, and let both complexes be strictly bounded below. If `ψ` is invertible at
`(σ^{≤N}F^•, σ^{≤N}G^•)` for every `N`, then it is invertible at `(F^•, G^•)`. -/
theorem isIso_of_isIso_stupidTrunc (ψ : KunnethFamily a b) (hl : ψ.NaturalLeft)
    (hr : ψ.NaturalRight)
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (hB : ∀ N : ℤ, IsIso (ψ (K.stupidTrunc (embeddingUpIntLE N))
      (L.stupidTrunc (embeddingUpIntLE N)))) :
    IsIso (ψ K L) := by
  rw [DerivedCategory.isIso_iff]
  intro d
  let N : ℤ := max (d - n₁ + 2) (d - n₂ + 2)
  have hK' := isLocallyBounded_and_isFlat_leftComplex_stupidTrunc hK hKflat (embeddingUpIntLE N)
  refine isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_left ψ hl K L n₂ hK hKflat N d
    (by omega) ?_
  exact isIso_homologyMap_of_isIso_homologyMap_stupidTrunc_right ψ hr _ L n₁ hK'.1 hK'.2 N d
    (by omega) (Functor.map_isIso _ _)

end Core


end Stacks.Cohomology.BoxKunneth
