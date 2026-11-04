module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelIdentity
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ExternalTensorBox
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ScalarTwist
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.SpecFieldSplitting
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RegularPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalKernelTower
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentFunctorBounds
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.UniformBound
public import StacksFrontier.CategoryTheory.Triangulated.BoundedWindows

/-!
# A uniform bound for an exact functor on the coherent modules of a smooth proper scheme

Let `k` be a field, `X` a scheme proper and smooth over `k`, `Y` a quasi-compact scheme smooth
over `k`, and `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` an exact functor. Then there is an integer `m`
such that `F(𝓕)` has cohomology sheaves only in degrees `[-m, m]` for every coherent
`𝒪_X`-module `𝓕`.

This is the bound of [Stacks, Tag 0FZ8] for the homological functors `H^0 ∘ F`, which is how
[Stacks, Section 0G07] uses it, proved here unconditionally and directly from the diagonal:

* `𝒪_Δ` lies in `smd(add({ℰⱼ ⊠ 𝒢ⱼ}[-N, 0])^{⋆ (N + 1)})` in `D(𝒪_{X × X})`
  (`AlgebraicGeometry.exists_diagonalKernel_retractClosure_extensionProductIter`, from
  [Stacks, Tag 0FZ2], [Stacks, Tag 0FZ4] and [Stacks, Tag 0FX7]);
* the integral transform `N ↦ R pr_{2,*}(L pr_1^*𝓕 ⊗^𝐋 N)` is exact and takes `𝒪_Δ` to `𝓕`
  ([Stacks, Tag 0FYV], `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`), so `𝓕` lies in
  `smd(add({Φ(ℰⱼ ⊠ 𝒢ⱼ)}[-N, 0])^{⋆ (N + 1)})` by [Stacks, Tag 0FX5];
* `Φ(ℰ ⊠ 𝒢) = Lf^*Rf_*(𝓕 ⊗ ℰ) ⊗ 𝒢` (`AlgebraicGeometry.boxTransformMap`, [Stacks, Tag 08EU] and
  [Stacks, Tag 08IB]), and `Rf_*(𝓕 ⊗ ℰ)` is a bounded complex with coherent cohomology on
  `Spec k` concentrated in `[0, t]` for a `t` depending on `f` alone
  ([Stacks, Tag 08D5] and [Stacks, Tag 02O5]), hence a finite sum of shifts of `𝒪_{Spec k}`
  (`AlgebraicGeometry.specFieldSums_of_isGE_of_isLE`); so `Φ(ℰⱼ ⊠ 𝒢ⱼ) ∈ smd(add(𝒢ⱼ[0, t]))`;
* hence `𝓕 ∈ smd(add({𝒢ⱼ}[-N, t])^{⋆ (N + 1)})` with `N`, `t` and the `𝒢ⱼ` independent of `𝓕`,
  the membership can be read in `D_perf(𝒪_X)`, it is carried by `F` ([Stacks, Tag 0FX5]), and
  the window of `F` on the finitely many perfect objects `𝒢ⱼ` bounds the window on the tower
  ([Stacks, Tag 0FX8]).

## Main results

* `AlgebraicGeometry.exists_isZero_homology_perfectFunctor_obj_coherent`.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0FZ8](https://stacks.math.columbia.edu/tag/0FZ8)
* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
* [Stacks Project, Tag 0FX8](https://stacks.math.columbia.edu/tag/0FX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The two exact functors -/

section Functors

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

attribute [local instance] AlgebraicGeometry.commShift_pushforward
  AlgebraicGeometry.isTriangulated_pushforward

/-- `L pr_1^*M ⊗^𝐋 -` on `D(𝒪_{X ×_S Y})`, the first factor of the integral transform. -/
abbrev kernelTensorFactor (M : DerivedCategory X.Modules) :
    DerivedCategory (pullback f g).Modules ⥤ DerivedCategory (pullback f g).Modules :=
  (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
    ((fourierMukaiPullback f g).obj M)

/-- `L pr_1^*M ⊗^𝐋 -` commutes with the shift. -/
instance commShift_kernelTensorFactor (M : DerivedCategory X.Modules) :
    (kernelTensorFactor f g M).CommShift ℤ :=
  (canonicalDerivedTensorProduct (pullback f g).toRingedSpace.sheaf).commShift_right _

/-- `L pr_1^*M ⊗^𝐋 -` is exact. -/
instance isTriangulated_kernelTensorFactor (M : DerivedCategory X.Modules) :
    (kernelTensorFactor f g M).IsTriangulated :=
  (canonicalDerivedTensorProduct (pullback f g).toRingedSpace.sheaf).exact_right _

/-- The integral transform with a fixed argument commutes with the shift in the kernel. -/
instance commShift_kernelIntegralTransform (M : DerivedCategory X.Modules) :
    (kernelIntegralTransform f g M).CommShift ℤ :=
  inferInstanceAs ((kernelTensorFactor f g M ⋙ fourierMukaiPushforward f g).CommShift ℤ)

/-- The integral transform with a fixed argument is exact in the kernel. -/
instance isTriangulated_kernelIntegralTransform (M : DerivedCategory X.Modules) :
    (kernelIntegralTransform f g M).IsTriangulated :=
  inferInstanceAs ((kernelTensorFactor f g M ⋙ fourierMukaiPushforward f g).IsTriangulated)

end Functors

section Twist

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `- ⊗^𝐋 B` on `D(𝒪_X)`. -/
abbrev twistTensorFactor (B : DerivedCategory X.Modules) :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (derivedTensorProductFunctor X.toRingedSpace.sheaf).flip.obj B

/-- `- ⊗^𝐋 B` commutes with the shift. -/
instance commShift_twistTensorFactor (B : DerivedCategory X.Modules) :
    (twistTensorFactor B).CommShift ℤ :=
  (canonicalDerivedTensorProduct X.toRingedSpace.sheaf).commShift_left B

/-- `- ⊗^𝐋 B` is exact. -/
instance isTriangulated_twistTensorFactor (B : DerivedCategory X.Modules) :
    (twistTensorFactor B).IsTriangulated :=
  (canonicalDerivedTensorProduct X.toRingedSpace.sheaf).exact_left B

/-- The derived pullback `L f^*` commutes with the shift. -/
instance commShift_dpull : (dpull f).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := f.toLRSHom.toShHom)

/-- The derived pullback `L f^*` is exact. -/
instance isTriangulated_dpull : (dpull f).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated (f := f.toLRSHom.toShHom)

/-- `V ↦ L f^*V ⊗^𝐋 B`, from `D(𝒪_S)` to `D(𝒪_X)`. -/
abbrev pullbackTwist (B : DerivedCategory X.Modules) :
    DerivedCategory S.Modules ⥤ DerivedCategory X.Modules :=
  dpull f ⋙ twistTensorFactor B

/-- `L f^*𝒪_S[0] ⊗^𝐋 B ≅ B`. -/
def pullbackTwistUnitIso (B : DerivedCategory X.Modules) :
    (pullbackTwist f B).obj ((DerivedCategory.singleFunctor S.Modules 0).obj
      (SheafOfModules.unit S.ringCatSheaf)) ≅ B :=
  (unitTwistIso f).app B

end Twist

/-! ### The transform of an external tensor product -/

section Box

/-- `smd(add(B[a, b]))`: direct summands of finite direct sums of the objects `B[-p]`,
`p ∈ [a, b]`. -/
abbrev shiftSums {C : Type*} [Category C] [HasShift C ℤ] (B : C) (a b : ℤ) : ObjectProperty C :=
  (⨆ p ∈ Set.Icc a b, (ObjectProperty.singleton B).isoClosure.shift p
    ).binaryProductsClosure.retractClosure

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`L f^*(-) ⊗^𝐋 B` carries `smd(add(𝒪_{Spec k}[a, b]))` into `smd(add(B[a, b]))`**, being an
exact functor taking `𝒪_{Spec k}[0]` to `B` ([Stacks, Tag 0FX5] with no extension). -/
theorem pullbackTwist_mem_shiftSums (B : DerivedCategory X.Modules) {a b : ℤ}
    {V : DerivedCategory (Spec (.of k)).Modules} (hV : specFieldSums k a b V) :
    shiftSums B a b ((pullbackTwist f B).obj V) := by
  have h :=
    Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
      (pullbackTwist f B) (P := ObjectProperty.singleton
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)))
      (Q := (ObjectProperty.singleton B).isoClosure)
      (fun Z hZ => by
        obtain rfl := (ObjectProperty.singleton_iff _ _).1 hZ
        exact ⟨B, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨pullbackTwistUnitIso f B⟩⟩) a b 0
  simp only [extensionProductIter_zero, isoClosure_eq_self] at h
  exact h _ hV

/-- For `X` smooth over `k`, the first projection `X ×_k X ⟶ X` is flat on stalks. -/
theorem flat_stalk_fst [Smooth f] :
    AlgebraicGeometry.IsFlat (pullback.fst f f).toLRSHom.toShHom :=
  fun x => Flat.stalkMap (pullback.fst f f) x

/-- For `X` smooth over `k`, the second projection `X ×_k X ⟶ X` is flat on stalks. -/
theorem flat_stalk_snd [Smooth f] :
    AlgebraicGeometry.IsFlat (pullback.snd f f).toLRSHom.toShHom :=
  fun x => Flat.stalkMap (pullback.snd f f) x

/-- **The transform of an external tensor product lies in a window independent of the
argument.** For `X` proper and smooth over `k` there is `t` such that for every coherent `𝓕` and
all finite locally free `ℰ`, `𝒢` the object `R pr_{2,*}(L pr_1^*𝓕 ⊗^𝐋 (ℰ ⊠ 𝒢))` lies in
`smd(add(𝒢[0, t]))`: it is `Lf^*Rf_*(𝓕 ⊗ ℰ) ⊗ 𝒢` and `Rf_*(𝓕 ⊗ ℰ)` is a sum of shifts of
`𝒪_{Spec k}` in degrees `[0, t]`. -/
theorem exists_forall_kernelIntegralTransform_externalTensorProduct_mem [IsProper f] [Smooth f] :
    ∃ t : ℕ, ∀ (𝓕 : X.Modules) [𝓕.IsCoherent] (E G : X.Modules),
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E →
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G →
      shiftSums ((DerivedCategory.singleFunctor X.Modules 0).obj G) 0 t
        ((kernelIntegralTransform f f ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)).obj
          ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
            (externalTensorProduct f f E G))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedPushforward f
  refine ⟨N.toNat, fun 𝓕 h𝓕 E G hE hG => ?_⟩
  have := h𝓕
  have hEc : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X E
  have hGc : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X G
  have hqc (M : X.Modules) [M.IsCoherent] :
      IsQCohAll ((DerivedCategory.singleFunctor X.Modules 0).obj M) :=
    fun n => isQuasicoherent_homology_singleFunctor_obj X M
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1 n
  let M : X.Modules := (Stacks.Chow.twistFunctor E).obj 𝓕
  have hMc : M.IsCoherent :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace 𝓕 E h𝓕 hEc
  have hEflat := AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree E hE
  -- The chain of isomorphisms.
  have := isIso_boxTransformMap f f ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)
    ((DerivedCategory.singleFunctor X.Modules 0).obj E)
    ((DerivedCategory.singleFunctor X.Modules 0).obj G) (hqc 𝓕) (hqc E) (hqc G)
  let V := (dpush f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M)
  let e : (kernelIntegralTransform f f ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)).obj
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G)) ≅
      (pullbackTwist f ((DerivedCategory.singleFunctor X.Modules 0).obj G)).obj V :=
    (kernelIntegralTransform f f _).mapIso
        (derivedBoxSingleIso f f (flat_stalk_fst f) (flat_stalk_snd f) E G hG).symm ≪≫
      (asIso (boxTransformMap f f _ _ _)).symm ≪≫
      (pullbackTwist f _).mapIso ((dpush f).mapIso (dtenSingleIsoOfIsFlat 𝓕 E hEflat))
  refine (shiftSums _ 0 N.toNat).prop_of_iso e.symm (pullbackTwist_mem_shiftSums f _ ?_)
  -- `Rf_*(𝓕 ⊗ ℰ)` is a sum of shifts of `𝒪_{Spec k}` in degrees `[0, t]`.
  have hV0 : V.IsGE 0 :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f _ 0 inferInstance
  have hVt : V.IsLE N.toNat := (DerivedCategory.isLE_iff V _).2 fun i hi =>
    hN _ (hqc M) 0 inferInstance i (by omega)
  have hcoh :=
    open Stacks.AlgebraicGeometry.ProperSupportCoherent in
    derivedCategoryBBounded_derivedPushforward_of_properSupp
      f ((DerivedCategory.singleFunctor X.Modules 0).obj M)
      (TorFormula.isCoherent_homology_singleFunctor_obj X M hMc)
      (fun j => isProperOver_of_isProper f _) 0 0 inferInstance inferInstance
  exact specFieldSums_of_isGE_of_isLE V 0 N.toNat (by omega) hcoh.2

end Box

/-! ### The uniform tower and the bound -/

section Bound

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- The objects `𝒢ⱼ[0]`, `j ≤ N`, of `D(𝒪_X)`, up to isomorphism. -/
def singleFamily {X : Scheme.{u}} (N : ℕ) (G : ℕ → X.Modules) :
    ObjectProperty (DerivedCategory X.Modules) :=
  fun Z => ∃ j ≤ N, Nonempty (Z ≅ (DerivedCategory.singleFunctor X.Modules 0).obj (G j))

/-- **Every coherent module lies in one bounded tower.** For `X` proper and smooth over a field
there are `N`, `t` and finite locally free `𝒢₀, …, 𝒢_N` such that every coherent `𝓕` satisfies
`𝓕[0] ∈ smd(add({𝒢ⱼ[0]}[-N, t])^{⋆ (N + 1)})` in `D(𝒪_X)`. This is [Stacks, Tag 0FZ7] with its
inputs proved, for the finite family `{𝒢ⱼ}` in place of the single `⊕ⱼ 𝒢ⱼ`. -/
theorem exists_forall_coherent_retractClosure_extensionProductIter [IsProper f] [Smooth f] :
    ∃ (N t : ℕ) (G : ℕ → X.Modules),
      (∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (G j)) ∧
      ∀ (𝓕 : X.Modules) [𝓕.IsCoherent],
        ((⨆ i ∈ Set.Icc (-(N : ℤ)) (t : ℤ), (singleFamily N G).isoClosure.shift i
          ).binaryProductsClosure.extensionProductIter N).retractClosure
          ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  obtain ⟨N, E, G, hE, hG, hdiag⟩ := exists_diagonalKernel_retractClosure_extensionProductIter f
  obtain ⟨t, ht⟩ := exists_forall_kernelIntegralTransform_externalTensorProduct_mem f
  refine ⟨N, t, G, hG, fun 𝓕 h𝓕 => ?_⟩
  have := h𝓕
  let 𝒢 := singleFamily N G
  let Φ := kernelIntegralTransform f f ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)
  let Q := ((⨆ i ∈ Set.Icc (0 : ℤ) (t : ℤ), 𝒢.isoClosure.shift i).binaryProductsClosure
    ).retractClosure
  -- Each `Φ(ℰⱼ ⊠ 𝒢ⱼ)` lies in `smd(add(𝒢[0, t]))`.
  have hA : ∀ ⦃Z⦄, diagonalBoxes f N E G Z → Q (Φ.obj Z) := by
    rintro Z ⟨j, hj, ⟨e⟩⟩
    have hle : shiftSums ((DerivedCategory.singleFunctor X.Modules 0).obj (G j)) 0 t ≤ Q := by
      refine monotone_retractClosure (limitsClosure_monotone _
        (iSup₂_mono fun i _ => fun W hW => ?_))
      obtain ⟨W', hW', ⟨e'⟩⟩ := hW
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hW'
      exact ⟨_, ⟨j, hj, ⟨Iso.refl _⟩⟩, ⟨e'⟩⟩
    exact Q.prop_of_iso (Φ.mapIso e).symm (hle _ (ht 𝓕 (E j) (G j) (hE j) (hG j)))
  -- So `Φ(𝒪_Δ) ∈ smd(add(smd(add(𝒢[0, t]))[-N, 0])^{⋆ (N + 1)})` ([Stacks, Tag 0FX5]) ...
  have hB :=
    Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
      Φ hA (-(N : ℤ)) 0 N _ hdiag
  -- ... `⊆ smd(add(𝒢[-N, t])^{⋆ (N + 1)})`.
  have hC :=
    Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_retractClosure_le
      𝒢 0 t (-(N : ℤ)) 0 N _ hB
  simp only [zero_add, add_zero] at hC
  -- And `Φ(𝒪_Δ) ≅ 𝓕[0]` ([Stacks, Tag 0FYV]).
  obtain ⟨W, hW, ⟨r⟩⟩ := hC
  exact ⟨W, hW, ⟨(Retract.ofIso ((fourierMukaiDiagonalKernelIso f).app
    ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)).symm).trans r⟩⟩

/-- `H^0(K[i]) ≅ H^i(K)` for a perfect object `K`, read through the inclusion of `D_perf`. -/
def homologyZeroShiftPerfectIso {Y : Scheme.{u}} (W : PerfectDerivedCategory Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor Y.Modules 0).obj ((W⟦i⟧).obj) ≅
      (DerivedCategory.homologyFunctor Y.Modules i).obj W.obj :=
  (DerivedCategory.homologyFunctor Y.Modules 0).mapIso
      (((ObjectProperty.ι (fun K : DerivedCategory Y.Modules =>
        IsPerfect (X := Y.toRingedSpace) K)).commShiftIso i).app W) ≪≫
    ((DerivedCategory.homologyFunctor Y.Modules 0).shiftIso i 0 i (by omega)).app W.obj

/-- A perfect complex on a quasi-compact regular scheme has cohomology sheaves vanishing outside
some window `[-c, c]`. -/
private theorem exists_isZero_homology_of_isRegular {Y : Scheme.{u}} [CompactSpace Y]
    (hY : IsRegular Y) (K : PerfectDerivedCategory Y) :
    ∃ c : ℕ, ∀ i : ℤ, i ∉ Set.Icc (-(c : ℤ)) c →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj K.obj) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular Y hY _
      K.property
  refine ⟨a.natAbs + b.natAbs, fun i hi => ?_⟩
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · exact ha i (by omega)
  · exact hb i (by omega)

/-- If the cohomology sheaves of `F(W)` vanish outside `[a, b]` for every `W` in `E`, then those
of `F(Z)` vanish outside `[a + c, b + d]` for `Z` in `smd(add(E[c, d])^{⋆ (n + 1)})`. -/
private theorem isZero_homology_obj_of_retractClosure_extensionProductIter {X Y : Scheme.{u}}
    (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y) [F.CommShift ℤ] [F.IsTriangulated]
    (E : ObjectProperty (PerfectDerivedCategory X)) {a b : ℤ}
    (hE : ∀ ⦃W : PerfectDerivedCategory X⦄, E W → ∀ i ∉ Set.Icc a b,
      IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (F.obj W).obj))
    (c d : ℤ) (n : ℕ) {Z : PerfectDerivedCategory X}
    (hZ : ((⨆ j ∈ Set.Icc c d,
      E.isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure Z)
    {i : ℤ} (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (F.obj Z).obj) :=
  let H := F ⋙ ObjectProperty.ι (fun K : DerivedCategory Y.Modules =>
    IsPerfect (X := Y.toRingedSpace) K) ⋙ DerivedCategory.homologyFunctor Y.Modules 0
  have e (W : PerfectDerivedCategory X) (i : ℤ) : H.obj (W⟦i⟧) ≅
      (DerivedCategory.homologyFunctor Y.Modules i).obj (F.obj W).obj :=
    (DerivedCategory.homologyFunctor Y.Modules 0).mapIso
      ((ObjectProperty.ι _).mapIso (F.commShiftIso i |>.app W)) ≪≫ homologyZeroShiftPerfectIso _ i
  IsZero.of_iso (CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter H E
    (fun W hW i hi => IsZero.of_iso (hE hW i hi) (e W i)) c d n hZ hi) (e Z i).symm

/-- **A uniform bound for an exact functor on the coherent modules.** Let `k` be a field, `X` a
scheme proper and smooth over `k`, `Y` a quasi-compact scheme smooth over `k`, and
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` an exact functor. There is `m` such that for every coherent
`𝒪_X`-module `𝓕` the cohomology sheaves of `F(𝓕)` vanish outside `[-m, m]`.

This is the bound used in [Stacks, Section 0G07], namely [Stacks, Tag 0FZ8] for the homological
functors `H^0 ∘ F`, with the inputs of [Stacks, Tag 0FZ7] proved
(`AlgebraicGeometry.exists_forall_coherent_retractClosure_extensionProductIter`). -/
theorem exists_isZero_homology_perfectFunctor_obj_coherent [IsProper f] [Smooth f] [Smooth g]
    [CompactSpace Y] (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y) [F.CommShift ℤ]
    [F.IsTriangulated] :
    ∃ m : ℕ, ∀ (𝓕 : X.Modules), 𝓕.IsCoherent →
      ∀ (h𝓕 : IsPerfect (X := X.toRingedSpace) ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕))
        (i : ℤ), i ∉ Set.Icc (-(m : ℤ)) m →
          IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (F.obj ⟨_, h𝓕⟩).obj) := by
  obtain ⟨N, t, G, hG, htower⟩ := exists_forall_coherent_retractClosure_extensionProductIter f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX : IsRegular X := isRegular_of_smooth_over_field f
  have hGc : ∀ j, (G j).IsCoherent := fun j =>
    have := hG j
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X (G j)
  let P : ℕ → PerfectDerivedCategory X := fun j =>
    ⟨_, @isPerfect_single_of_isCoherent_of_isRegular X hX _ (G j) (hGc j)⟩
  -- The window of `F` on the finitely many `𝒢ⱼ`.
  choose c hc using fun j =>
    exists_isZero_homology_of_isRegular (isRegular_of_smooth_over_field g) (F.obj (P j))
  set C : ℕ := (Finset.range (N + 1)).sup c
  have hcC : ∀ j ≤ N, c j ≤ C := fun j hj =>
    Finset.le_sup (f := c) (Finset.mem_range.2 (by omega))
  refine ⟨C + N + t, fun 𝓕 h𝓕c h𝓕 i hi => ?_⟩
  have := h𝓕c
  -- The tower, read in `D_perf(𝒪_X)`.
  let E' : ObjectProperty (PerfectDerivedCategory X) := fun Z => ∃ j ≤ N, Nonempty (Z ≅ P j)
  have hle : singleFamily N G ≤ E'.map (ObjectProperty.ι _) := by
    rintro Z ⟨j, hj, ⟨e⟩⟩
    exact ⟨P j, ⟨j, hj, ⟨Iso.refl _⟩⟩, ⟨e.symm⟩⟩
  have hZ := Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_of_map_ι
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) E' (-(N : ℤ)) t N
    (Z := ⟨_, h𝓕⟩)
    (monotone_retractClosure (monotone_extensionProductIter (limitsClosure_monotone _
      (iSup₂_mono fun i _ => fun W hW => monotone_isoClosure hle _ hW)) N) _ (htower 𝓕))
  -- The window of `H^0` on the tower ([Stacks, Tag 0FX8]).
  refine isZero_homology_obj_of_retractClosure_extensionProductIter F E' (a := -(C : ℤ)) (b := C)
    ?_ (-(N : ℤ)) t N hZ (by
    simp only [Set.mem_Icc, not_and_or, not_le] at hi ⊢
    omega)
  rintro W ⟨j, hj, ⟨e⟩⟩ i hi
  refine IsZero.of_iso (hc j i fun h => hi ?_)
    ((DerivedCategory.homologyFunctor Y.Modules i).mapIso
      ((ObjectProperty.ι _).mapIso (F.mapIso e)))
  have := hcC j hj
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- A perfect complex on a quasi-compact regular scheme whose cohomology sheaves vanish outside
`[a, b]` lies in `smd(add(𝒞[a, b])^{⋆ (b - a)})` in `D_perf`, where `𝒞` is the class of coherent
modules placed in degree zero. -/
private theorem retractClosure_extensionProductIter_coherent_of_isZero_homology {X : Scheme.{u}}
    [CompactSpace X] (hX : IsRegular X) (Z : PerfectDerivedCategory X) {a b : ℤ} (hab : a ≤ b)
    (hZ : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj Z.obj)) :
    ((⨆ i ∈ Set.Icc a b, (ObjectProperty.isoClosure
      fun W : PerfectDerivedCategory X => ∃ (M : X.Modules) (_ : M.IsCoherent),
        Nonempty (W.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M)).shift i
      ).binaryProductsClosure.extensionProductIter (b - a).toNat).retractClosure Z := by
  let E' : ObjectProperty (PerfectDerivedCategory X) := fun W =>
    ∃ (M : X.Modules) (_ : M.IsCoherent),
      Nonempty (W.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M)
  have hcoh :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
      X hX _ Z.property).2
  have : Z.obj.IsGE a :=
    (DerivedCategory.isGE_iff _ a).2 fun i hi => hZ i fun h => absurd h.1 (by omega)
  have : Z.obj.IsLE b :=
    (DerivedCategory.isLE_iff _ b).2 fun i hi => hZ i fun h => absurd h.2 (by omega)
  -- [Stacks, Tag 0FX7] part (1), in `D(𝒪_X)`.
  have h7 :=
    (DerivedCategory.prop_retractClosure_extensionProductIter_of_prop_homology_and_of_prop_X
      (fun M : X.Modules => M.IsCoherent) hab).1 Z.obj (fun i _ =>
        le_retractClosure _ _ (le_limitsClosure _ _ _ (hcoh i)))
  have hshift : (⨆ i ∈ Set.Icc a b, ObjectProperty.map (fun M : X.Modules => M.IsCoherent)
      (DerivedCategory.singleFunctor X.Modules i)) ≤
      ⨆ i ∈ Set.Icc a b, (E'.map (ObjectProperty.ι _)).isoClosure.shift i := by
    refine iSup₂_le fun i hi => le_trans ?_ (le_iSup₂_of_le i hi le_rfl)
    rintro W ⟨M, hM, ⟨eW⟩⟩
    exact ⟨_, ⟨⟨_, @isPerfect_single_of_isCoherent_of_isRegular X hX _ M hM⟩,
        ⟨M, hM, ⟨Iso.refl _⟩⟩, ⟨Iso.refl _⟩⟩,
      ⟨(shiftFunctor (DerivedCategory X.Modules) i).mapIso eW.symm ≪≫
        ((DerivedCategory.singleFunctors X.Modules).shiftIso i 0 i (by omega)).app M⟩⟩
  exact Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_of_map_ι
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) E' a b
    (b - a).toNat (Z := Z)
    (monotone_retractClosure
      (monotone_extensionProductIter (limitsClosure_monotone _ hshift) _) _ h7)

/-- **The uniform bound for perfect complexes with cohomology in a range.** In the situation of
`AlgebraicGeometry.exists_isZero_homology_perfectFunctor_obj_coherent` there is `m` such that for
every perfect `Z` on `X` whose cohomology sheaves vanish outside `[a, b]` the cohomology sheaves
of `F(Z)` vanish outside `[a - m, b + m]`: the cohomology sheaves of `Z` are coherent, so `Z` is
an iterated extension of shifts of coherent modules ([Stacks, Tag 0FX7]), and [Stacks, Tag 0FX8]
propagates the window of `F` on the coherent modules. -/
theorem exists_isZero_homology_perfectFunctor_obj [IsProper f] [Smooth f] [Smooth g]
    [CompactSpace Y] (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y) [F.CommShift ℤ]
    [F.IsTriangulated] :
    ∃ m : ℕ, ∀ (Z : PerfectDerivedCategory X) (a b : ℤ), a ≤ b →
      (∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj Z.obj)) →
        ∀ i : ℤ, i ∉ Set.Icc (a - m) (b + m) →
          IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (F.obj Z).obj) := by
  obtain ⟨m, hm⟩ := exists_isZero_homology_perfectFunctor_obj_coherent f g F
  refine ⟨m, fun Z a b hab hZ i hi => ?_⟩
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX : IsRegular X := isRegular_of_smooth_over_field f
  -- The class of coherent modules placed in degree zero, inside `D_perf(𝒪_X)`.
  let E' : ObjectProperty (PerfectDerivedCategory X) := fun W =>
    ∃ (M : X.Modules) (_ : M.IsCoherent),
      Nonempty (W.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj M)
  have hZ' := retractClosure_extensionProductIter_coherent_of_isZero_homology hX Z hab hZ
  refine isZero_homology_obj_of_retractClosure_extensionProductIter F E' (a := -(m : ℤ)) (b := m)
    ?_ a b _ hZ' (by
    simp only [Set.mem_Icc, not_and_or, not_le] at hi ⊢
    omega)
  rintro W ⟨M, hM, ⟨e⟩⟩ i hi
  exact IsZero.of_iso (hm M hM (@isPerfect_single_of_isCoherent_of_isRegular X hX _ M hM) i hi)
    ((DerivedCategory.homologyFunctor Y.Modules i).mapIso ((ObjectProperty.ι _).mapIso
      (F.mapIso ((ObjectProperty.fullyFaithfulι _).preimageIso e))))

end Bound

end AlgebraicGeometry

end
