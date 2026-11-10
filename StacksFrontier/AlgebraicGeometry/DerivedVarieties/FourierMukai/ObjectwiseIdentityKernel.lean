module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelUnit
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.CaseIKernelVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedPushforwardImage
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.SupportedPushforwardReflect
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowLemmaGeneral
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DerivedStalkHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.InvertiblePushforwardSection
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelPerfect

/-!
# A kernel whose Fourier-Mukai functor is object-wise the identity

Let `K` be an algebraically closed field and `X` a smooth proper `K`-scheme. This file works
towards `AlgebraicGeometry.ObjectwiseIdentityKernelIsDiagonal K`: a perfect kernel `A` on
`X ×_K X` with `Φ_A(E) ≅ E` for every perfect `E` is the diagonal kernel `Δ_*𝒪_X`. That is
[Stacks, Tag 0G0E] with its hypothesis read object by object, which is what the reduction
`AlgebraicGeometry.derivedEquivalenceHasRelativeKernel_of_objectwise` of [Stacks, Tag 0G0Y]
consumes.

## The argument

1. For a `K`-point `x` with fibre `j_x : X ⟶ X ×_K X`, `y ↦ (x, y)`, of the first projection,
   `Φ_A(Rx_*𝒪) ≅ Lj_x^*A` (`AlgebraicGeometry.fourierMukaiPointIso`): base change
   ([Stacks, Tag 0E23]) along the cartesian square of `j_x`, the projection formula along the
   closed immersion `j_x`, and `j_x ≫ pr₂ = 𝟙`.
2. So `Lj_x^*A ≅ Rx_*𝒪` is supported at `x`, and Case I of [Stacks, Tag 0G0R] kills `A` near
   every closed point `(x, y)`, `y ≠ x`; by the Jacobson property all cohomology sheaves of `A`
   are supported on the diagonal
   (`AlgebraicGeometry.isZero_stalkHomology_of_notMem_range_diagonal`).
3. `R pr_{2,*}A ≅ Φ_A(𝒪_X) ≅ 𝒪_X` (`pushforwardSndIsoFourierMukaiUnit`). Over an affine open
   `V ⊆ X` the second projection `X ×_K V ⟶ V` is affine on the open `pr₁⁻¹V`, which contains the
   support of the restriction of `A`, and its derived direct image is
   `(R pr_{2,*}A)|_V ≅ 𝒪_V` ([Stacks, Tag 08IB], `restrictSndPushforwardIso`); direct image along
   a morphism affine over the support detects vanishing of cohomology, so `H^i(A) = 0` for
   `i ≠ 0` (`isZero_homology_of_ne_zero`).
4. So `A ≅ F[0]` with `F` coherent, supported on the diagonal, and
   `pr_{2,*}F ≅ R⁰pr_{2,*}F ≅ H⁰(R pr_{2,*}A) ≅ 𝒪_X` (`pushforwardSndIsoUnitOfIsoSingle`);
   [Stacks, Tag 0FZQ] with the section `Δ` of `pr₂` gives `F ≅ Δ_*𝒪_X`, and
   `A ≅ (Δ_*𝒪_X)[0] ≅ RΔ_*𝒪_X` (`nonempty_diagonalKernel_iso_of_forall_iso`).

Algebraic closedness is used only in step 2, to write every closed point of `X ×_K X` as a pair
of `K`-points. It is necessary: for `X = Spec L` with `L / K` a nontrivial Galois extension the
graph of `Spec σ`, `σ ≠ 1`, is a kernel whose functor is object-wise, not naturally, the
identity.

## Main results

* `AlgebraicGeometry.nonempty_diagonalKernel_iso_of_forall_iso` — the object-wise
  [Stacks, Tag 0G0E].
* `AlgebraicGeometry.objectwiseIdentityKernelIsDiagonal` — the same as the input
  `ObjectwiseIdentityKernelIsDiagonal K` of `derivedEquivalenceHasRelativeKernel_of_objectwise`.
* `AlgebraicGeometry.derivedEquivalenceHasRelativeKernel_of_objectwiseFourierMukai` — `hkernel`
  over an algebraically closed field from `ObjectwiseFourierMukaiOfEquivalence K` alone.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0FZQ](https://stacks.math.columbia.edu/tag/0FZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleFrobenius (derivedStructureSheaf)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Fibre

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _)

/-- The fibre `{x} × X` of the first projection over a `K`-point `x`: the morphism
`X ⟶ X ×_K X`, `y ↦ (x, y)`. -/
def pointFibreInclusion : X ⟶ pullback f f :=
  pullback.lift (f ≫ x) (𝟙 X) (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])

/-- The first coordinate of `pointFibreInclusion f x hx` is the constant map `f ≫ x`. -/
@[reassoc (attr := simp)]
lemma pointFibreInclusion_fst : pointFibreInclusion f x hx ≫ pullback.fst f f = f ≫ x :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pointFibreInclusion f x hx` is the identity of `X`. -/
@[reassoc (attr := simp)]
lemma pointFibreInclusion_snd : pointFibreInclusion f x hx ≫ pullback.snd f f = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- The square exhibiting `{x} × X` as the fibre of the first projection over `x`. -/
lemma isPullback_pointFibreInclusion :
    IsPullback (pointFibreInclusion f x hx) f (pullback.fst f f) x := by
  refine IsPullback.of_right ?_ (pointFibreInclusion_fst f x hx)
    (IsPullback.of_hasPullback f f).flip
  rw [pointFibreInclusion_snd, hx]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

include hx in
/-- A `K`-point `x` of `X` which is a section of `f` is a closed immersion. -/
lemma isClosedImmersion_point : IsClosedImmersion x :=
  isClosedImmersion_of_comp_eq_id f x hx

/-- The fibre inclusion `X ⟶ X ×_K X`, `y ↦ (x, y)`, is a closed immersion. -/
lemma isClosedImmersion_pointFibreInclusion : IsClosedImmersion (pointFibreInclusion f x hx) :=
  have := isClosedImmersion_point f x hx
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_pointFibreInclusion f x hx).flip inferInstance

/-- **The Fourier-Mukai transform of the skyscraper at a point is the restriction of the kernel
to the fibre over that point**: `Φ_A(Rx_*𝒪) ≅ Lj_x^*A` for `j_x : X ⟶ X ×_K X`,
`y ↦ (x, y)`. Base change along the cartesian square of `isPullback_pointFibreInclusion`
([Stacks, Tag 0E23], `pr₁` being flat), the projection formula along the closed immersion `j_x`,
and `j_x ≫ pr₂ = 𝟙`. -/
def fourierMukaiPointIso [Flat f] (A : DerivedCategory (pullback f f).Modules) :
    (fourierMukai f f A).obj ((dpush x).obj (derivedStructureSheaf (Spec (.of K)))) ≅
      (dpull (pointFibreInclusion f x hx)).obj A :=
  have := isClosedImmersion_point f x hx
  have := isClosedImmersion_pointFibreInclusion f x hx
  (fourierMukaiPushforward f f).mapIso
      ((fourierMukaiTensor f f A).mapIso
          ((Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso
              (isPullback_pointFibreInclusion f x hx)
              (torIndependent_of_flat_right _ _)).app _ ≪≫
            (dpush (pointFibreInclusion f x hx)).mapIso
              (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
                f.toLRSHom.toShHom)) ≪≫
        structPushforwardTensorIso (pointFibreInclusion f x hx) A) ≪≫
    (derivedPushforwardCompIso (pointFibreInclusion f x hx).toLRSHom.toShHom
        (pullback.snd f f).toLRSHom.toShHom).app _ ≪≫
    (eqToIso (congrArg (fun m : X.toRingedSpace ⟶ X.toRingedSpace => derivedPushforward m)
      (congrArg (fun m : X ⟶ X => m.toLRSHom.toShHom)
        (pointFibreInclusion_snd f x hx)))).app _ ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso
      X.toRingedSpace).app _

/-- The skyscraper at the `K`-point `x`, as `Rx_*𝒪_{Spec K}`. -/
abbrev pointSheaf : DerivedCategory X.Modules :=
  (dpush x).obj (derivedStructureSheaf (Spec (.of K)))

/-- `Rx_*𝒪 ≅ (x_*𝒪)[0]`, `x` being a closed immersion. -/
def pointSheafIso :
    pointSheaf x ≅ (DerivedCategory.singleFunctor X.Modules 0).obj
      ((Scheme.Modules.pushforward x).obj (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)) :=
  have := isClosedImmersion_point f x hx
  derivedPushforwardSingleIso x _

include hx in
/-- The skyscraper at a `K`-point is supported at that point. -/
lemma cohomologySupportedOn_pointSheaf :
    CohomologySupportedOn X.ringCatSheaf (Set.range x.base) (pointSheaf x) :=
  have := isClosedImmersion_point f x hx
  cohomologySupportedOn_derivedPushforward_of_range_subset x _
    x.isClosedEmbedding.isClosed_range subset_rfl (derivedPushforwardModules x)
    (derivedPushforwardModulesUnit x) _

omit x in
/-- A coherent module placed in degree zero on a smooth quasi-compact `K`-scheme is perfect. -/
lemma isPerfect_single_of_isCoherent [Smooth f] [CompactSpace X] (M : X.Modules)
    (hM : M.IsCoherent) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) := by
  have h := perfectInModules_eq_derivedCategoryBBounded X (isRegular_of_smooth_over_field f)
  change perfectInModules X _
  rw [h]
  exact derivedCategoryBBounded_singleFunctor_obj X M hM

include hx in
/-- The skyscraper at a `K`-point of a smooth scheme of finite type over `K` is perfect. -/
lemma isPerfect_pointSheaf [Smooth f] [QuasiCompact f] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) (pointSheaf x) := by
  have := isClosedImmersion_point f x hx
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : (SheafOfModules.unit (Spec (.of K)).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  exact ObjectProperty.prop_of_iso
    (fun K : DerivedCategory X.Modules => Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.toRingedSpace) K) (pointSheafIso f x hx).symm
    (isPerfect_single_of_isCoherent f _ (isCoherent_pushforward_of_isClosedImmersion x
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)))

omit x in
/-- The structure sheaf of a smooth scheme of finite type over `K` is perfect. -/
lemma isPerfect_derivedStructureSheaf [Smooth f] [QuasiCompact f] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (derivedStructureSheaf X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact isPerfect_single_of_isCoherent f _
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit

end Fibre

section Points

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- `x ≫ j_x = x ≫ Δ`: the fibre over `x` meets the diagonal in `(x, x)`. -/
lemma point_comp_pointFibreInclusion (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    x ≫ pointFibreInclusion f x hx = x ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp [reassoc_of% hx]

/-- **Over an algebraically closed field every closed point of `X ×_K X` lies on the fibre of
the first projection over a `K`-point**, at a closed point of that fibre. -/
lemma exists_pointFibreInclusion_eq [IsAlgClosed K] [LocallyOfFiniteType f] [IsSeparated f]
    (z : ↥(pullback f f)) (hz : IsClosed ({z} : Set ↥(pullback f f))) :
    ∃ (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : X), IsClosed ({y} : Set X) ∧
      (pointFibreInclusion f x hx).base y = z := by
  let p : pullback f f ⟶ Spec (.of K) := pullback.snd f f ≫ f
  let w := pointOfClosedPoint p z hz
  have hw : w ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z hz
  have hx : (w ≫ pullback.fst f f) ≫ f = 𝟙 _ := by
    rwa [Category.assoc, pullback.condition, ← Category.assoc]
  have hy : (w ≫ pullback.snd f f) ≫ f = 𝟙 _ := by rwa [Category.assoc]
  have hcomp : (w ≫ pullback.snd f f) ≫ pointFibreInclusion f _ hx = w := by
    apply pullback.hom_ext
    · have hy' : w ≫ pullback.snd f f ≫ f = 𝟙 _ := by rwa [← Category.assoc]
      simp only [Category.assoc, pointFibreInclusion_fst]
      exact (reassoc_of% hy') _
    · simp
  refine ⟨w ≫ pullback.fst f f, hx, (w ≫ pullback.snd f f).base (IsLocalRing.closedPoint K),
    ?_, ?_⟩
  · have := isClosedImmersion_point f _ hy
    convert (w ≫ pullback.snd f f).isClosedEmbedding.isClosed_range using 1
    ext a
    simp only [Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun h => ⟨IsLocalRing.closedPoint K, h.symm⟩,
      fun ⟨b, hb⟩ => by rw [← hb, Subsingleton.elim b (IsLocalRing.closedPoint K)]⟩
  · change ((w ≫ pullback.snd f f) ≫ pointFibreInclusion f _ hx).base
      (IsLocalRing.closedPoint K) = z
    rw [hcomp]
    exact pointOfClosedPoint_apply p z hz _

/-- **Off the diagonal, a kernel which is the identity on skyscrapers vanishes near every closed
point.** Let `K` be algebraically closed and `X` of finite type, separated and flat over `K`. If
`Φ_A(𝒪_x) ≅ 𝒪_x` for every `K`-point `x`, then every closed point of `X ×_K X` off the diagonal
has an open neighbourhood on which all cohomology sheaves of `A` vanish.

The closed point is `(x, y)` with `y ≠ x` closed (`exists_pointFibreInclusion_eq`); the restriction
of `A` to the fibre `{x} × X` is `Φ_A(𝒪_x) ≅ 𝒪_x` (`fourierMukaiPointIso`), supported at `x`, and
Case I of [Stacks, Tag 0G0R]
(`exists_mem_forall_isZero_stalkHomology_caseI_of_cohomologySupportedOn`) applies. -/
theorem exists_isZero_stalkHomology_of_notMem_range_diagonal [IsAlgClosed K]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [Flat f]
    (A : DerivedCategory (pullback f f).Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f f).toRingedSpace) A)
    (hΦ : ∀ (x : Spec (.of K) ⟶ X) (_ : x ≫ f = 𝟙 _),
      Nonempty ((fourierMukai f f A).obj (pointSheaf x) ≅ pointSheaf x))
    (z : ↥(pullback f f)) (hz : IsClosed ({z} : Set ↥(pullback f f)))
    (hzΔ : z ∉ Set.range (pullback.diagonal f).base) :
    ∃ U : TopologicalSpace.Opens (pullback f f).carrier, z ∈ U ∧ ∀ w : ↥(pullback f f), w ∈ U →
      ∀ n : ℤ, IsZero (SheafOfModules.stalkObj (pullback f f).ringCatSheaf w
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pullback f f).ringCatSheaf)
          n).obj A)) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_pointFibreInclusion_eq f z hz
  have := isClosedImmersion_pointFibreInclusion f x hx
  have : IsNoetherian (pullback f f) :=
    isNoetherian_of_locallyOfFiniteType (pullback.snd f f ≫ f)
  obtain ⟨eΦ⟩ := hΦ x hx
  have e : pointSheaf x ≅ (dpull (pointFibreInclusion f x hx)).obj A :=
    eΦ.symm ≪≫ fourierMukaiPointIso f x hx A
  have hyT : y ∉ Set.range x.base := by
    rintro ⟨a, rfl⟩
    apply hzΔ
    refine ⟨x.base a, ?_⟩
    change (x ≫ pullback.diagonal f).base a = (x ≫ pointFibreInclusion f x hx).base a
    rw [point_comp_pointFibreInclusion]
  have hT : CohomologySupportedOn X.ringCatSheaf (Set.range x.base)
      ((dpull (pointFibreInclusion f x hx)).obj A) :=
    @Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ X.ringCatSheaf
      (HasDerivedCategory.standard _) _ _ _ e (cohomologySupportedOn_pointSheaf f x hx)
  exact exists_mem_forall_isZero_stalkHomology_caseI_of_cohomologySupportedOn
    (pointFibreInclusion f x hx) y hy (Set.range x.base) hyT A hA hT

/-- **In a Jacobson space, a property holding on a neighbourhood of every closed point outside a
closed set holds at every point outside it.** -/
lemma _root_.JacobsonSpace.forall_notMem_of_forall_closedPoint {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {C : Set T} (hC : IsClosed C) (P : T → Prop)
    (h : ∀ z : T, IsClosed ({z} : Set T) → z ∉ C →
      ∃ U : Set T, IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, P w) :
    ∀ w : T, w ∉ C → P w := by
  let G : Set T := {w | ∃ U : Set T, IsOpen U ∧ w ∈ U ∧ ∀ v ∈ U, P v}
  have hG : IsOpen G := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨U, hU, hwU, hPU⟩
    exact ⟨U, fun v hv => ⟨U, hU, hv, hPU⟩, hU, hwU⟩
  have hempty : Cᶜ ∩ Gᶜ = ∅ := by
    by_contra hne
    obtain ⟨z, ⟨hzC, hzG⟩, hz⟩ := nonempty_inter_closedPoints
      (Set.nonempty_iff_ne_empty.2 hne)
      (hC.isOpen_compl.isLocallyClosed.inter hG.isClosed_compl.isLocallyClosed)
    exact hzG (h z hz hzC)
  intro w hw
  obtain ⟨U, -, hwU, hPU⟩ : w ∈ G := by
    by_contra hwG
    exact (Set.eq_empty_iff_forall_notMem.1 hempty) w ⟨hw, hwG⟩
  exact hPU w hwU

/-- **A kernel which is the identity on skyscrapers is supported on the diagonal.** Over an
algebraically closed field, if `Φ_A(𝒪_x) ≅ 𝒪_x` for every `K`-point `x`, then every cohomology
sheaf of `A` has vanishing stalks off the diagonal of `X ×_K X`. -/
theorem isZero_stalkHomology_of_notMem_range_diagonal [IsAlgClosed K]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [Flat f]
    (A : DerivedCategory (pullback f f).Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f f).toRingedSpace) A)
    (hΦ : ∀ (x : Spec (.of K) ⟶ X) (_ : x ≫ f = 𝟙 _),
      Nonempty ((fourierMukai f f A).obj (pointSheaf x) ≅ pointSheaf x))
    (w : ↥(pullback f f)) (hw : w ∉ Set.range (pullback.diagonal f).base) (n : ℤ) :
    IsZero (SheafOfModules.stalkObj (pullback f f).ringCatSheaf w
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pullback f f).ringCatSheaf)
        n).obj A)) := by
  have : JacobsonSpace ↥(pullback f f) := LocallyOfFiniteType.jacobsonSpace (pullback.snd f f ≫ f)
  refine JacobsonSpace.forall_notMem_of_forall_closedPoint
    (pullback.diagonal f).isClosedEmbedding.isClosed_range
    (fun w => ∀ n : ℤ, IsZero (SheafOfModules.stalkObj (pullback f f).ringCatSheaf w
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pullback f f).ringCatSheaf)
        n).obj A))) (fun z hz hzΔ => ?_) w hw n
  obtain ⟨U, hzU, hU⟩ := exists_isZero_stalkHomology_of_notMem_range_diagonal f A hA hΦ z hz hzΔ
  exact ⟨U, U.isOpen, hzU, hU⟩

end Points

/-! ### Restricting the second factor to an open -/

section Restriction

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (V : X.Opens)

/-- `X ×_K V ⟶ X ×_K X`, the part of `X ×_K X` over an open `V` of the second factor. -/
def restrictSndInclusion : pullback f (V.ι ≫ f) ⟶ pullback f f :=
  pullback.lift (pullback.fst f (V.ι ≫ f)) (pullback.snd f (V.ι ≫ f) ≫ V.ι)
    (by rw [pullback.condition, Category.assoc])

/-- The first coordinate of `restrictSndInclusion f V` is the first projection of `X ×_K V`. -/
@[reassoc (attr := simp)]
lemma restrictSndInclusion_fst :
    restrictSndInclusion f V ≫ pullback.fst f f = pullback.fst f (V.ι ≫ f) :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `restrictSndInclusion f V` is the second projection of `X ×_K V`
followed by the inclusion `V ⟶ X`. -/
@[reassoc (attr := simp)]
lemma restrictSndInclusion_snd :
    restrictSndInclusion f V ≫ pullback.snd f f = pullback.snd f (V.ι ≫ f) ≫ V.ι :=
  pullback.lift_snd _ _ _

/-- `X ×_K V` is the preimage of `V` under the second projection `X ×_K X ⟶ X`. -/
lemma isPullback_restrictSndInclusion :
    IsPullback (restrictSndInclusion f V) (pullback.snd f (V.ι ≫ f)) (pullback.snd f f) V.ι := by
  refine IsPullback.of_right ?_ (restrictSndInclusion_snd f V) (IsPullback.of_hasPullback f f)
  rw [restrictSndInclusion_fst]
  exact IsPullback.of_hasPullback f (V.ι ≫ f)

/-- The inclusion `X ×_K V ⟶ X ×_K X` is an open immersion. -/
instance isOpenImmersion_restrictSndInclusion : IsOpenImmersion (restrictSndInclusion f V) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_restrictSndInclusion f V).flip inferInstance

/-- **`R pr_{2,*}` commutes with restriction to an open of the second factor**, by
[Stacks, Tag 08IB] (`V ⟶ X` being flat). -/
def restrictSndPushforwardIso [QuasiCompact f] [QuasiSeparated f]
    (A : DerivedCategory (pullback f f).Modules) (hA : IsQCohAll A) :
    (dpull V.ι).obj ((dpush (pullback.snd f f)).obj A) ≅
      (dpush (pullback.snd f (V.ι ≫ f))).obj ((dpull (restrictSndInclusion f V)).obj A) :=
  have hsq := shHom_comp_eq (restrictSndInclusion_snd f V)
  have : IsIso ((dbaseChange (restrictSndInclusion f V) (pullback.snd f (V.ι ≫ f))
      (pullback.snd f f) V.ι hsq).app A) :=
    derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ (isPullback_restrictSndInclusion f V)
      inferInstance inferInstance (torIndependent_of_flat_right _ _) hsq A hA
  asIso ((dbaseChange (restrictSndInclusion f V) (pullback.snd f (V.ι ≫ f))
      (pullback.snd f f) V.ι hsq).app A)

/-- `R pr_{2,*}A ≅ Φ_A(𝒪_X)`. -/
def pushforwardSndIsoFourierMukaiUnit (A : DerivedCategory (pullback f f).Modules) :
    (dpush (pullback.snd f f)).obj A ≅ (fourierMukai f f A).obj (derivedStructureSheaf X) :=
  ((dpush (pullback.snd f f)).mapIso
    ((dtenR (pullback f f) A).mapIso
        (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
          (pullback.fst f f).toLRSHom.toShHom) ≪≫
      (Stacks.RingedSpace.derivedTensorLeftUnitorNatIso (pullback f f).toRingedSpace).app A)).symm

end Restriction

/-! ### Vanishing of the cohomology away from degree zero -/

section Degree

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The stalk of a sheaf of modules vanishes as a module exactly when it vanishes as a group. -/
lemma isZero_presheaf_stalk_of_isZero_stalkObj {W : Scheme.{u}} {M : W.Modules} {w : W}
    (h : IsZero (SheafOfModules.stalkObj W.ringCatSheaf w M)) :
    IsZero (TopCat.Presheaf.stalk (X := W) M.val.presheaf w) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact h

/-- Restricting to an open preserves vanishing of stalks of cohomology at the points of the
open. -/
lemma isZero_stalk_homology_restrict {W : Scheme.{u}} (O : W.Opens)
    (E : DerivedCategory W.Modules) (n : ℤ) (w : O)
    (h : IsZero (TopCat.Presheaf.stalk (X := W)
      ((DerivedCategory.homologyFunctor W.Modules n).obj E).val.presheaf (O.ι.base w))) :
    IsZero (TopCat.Presheaf.stalk (X := O.toScheme)
      ((DerivedCategory.homologyFunctor O.toScheme.Modules n).obj
        ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategory.obj E)).val.presheaf w) :=
  (h.of_iso ((Scheme.Modules.restrictStalkNatIso O.ι w).app
      ((DerivedCategory.homologyFunctor W.Modules n).obj E))).of_iso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (show O.toScheme from w)).mapIso
      ((Scheme.Modules.toPresheaf O.toScheme).mapIso
        (((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategoryHomologyIso n).app E)))

/-- **Derived pullback along an open immersion reflects vanishing of cohomology stalks**, one
degree at a time: the derived stalk of `Lg^*E` at `y` is the derived stalk of `E` at `g(y)` with
scalars extended along the stalk map, an isomorphism of rings, and restricting the scalars back
undoes that extension (`totalDerivedExtendRestrictScalarsSelfIso`). -/
lemma isZero_modulesStalk_homology_of_derivedPullback {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsOpenImmersion g] (y : Y) (E : DerivedCategory Z.Modules) (n : ℤ)
    (h : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj
      ((DerivedCategory.homologyFunctor Y.Modules n).obj ((dpull g).obj E)))) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z (g.base y)).obj
      ((DerivedCategory.homologyFunctor Z.Modules n).obj E)) := by
  let e : Z.presheaf.stalk (g.base y) ≃+* Y.presheaf.stalk y :=
    RingEquiv.ofBijective (g.stalkMap y).hom
      ((ConcreteCategory.isIso_iff_bijective (g.stalkMap y)).1 inferInstance)
  let D := (derivedStalkFunctor (g.base y)).obj E
  have h1 : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((derivedStalkFunctor y).obj ((dpull g).obj E))) :=
    h.of_iso ((derivedStalkCompHomologyIso y n).app _)
  have h2 : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        e.toRingHom).functor.obj D)) :=
    h1.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedPullbackStalkIso g y).app E).symm)
  have h3 : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          e.toRingHom).functor.obj D))) :=
    ((ModuleCat.restrictScalars.{u} e.toRingHom).map_isZero h2).of_iso
      (((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategoryCompHomologyFunctorIso
        n).app _)
  have h4 : IsZero ((DerivedCategory.homologyFunctor _ n).obj D) :=
    h3.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtendRestrictScalarsSelfIso.{u, u}
        e).app D).symm)
  exact h4.of_iso ((derivedStalkCompHomologyIso (g.base y) n).app E).symm

/-- **Over an affine open of the second factor, a kernel supported on the diagonal with
`Φ_A(𝒪_X) ≅ 𝒪_X` has no cohomology outside degree zero.** The second projection
`X ×_K V ⟶ V` is affine over `pr₁⁻¹V`, which contains the support, and
`R pr_{2,*}(A|_{X ×_K V}) ≅ (Φ_A(𝒪_X))|_V ≅ 𝒪_V`; direct image along a morphism affine over the
support detects vanishing of cohomology
(`isZero_homology_of_isZero_homology_derivedPushforward_of_supported`). -/
theorem isZero_homology_restrictSnd_of_ne_zero [QuasiCompact f] [IsSeparated f] [Flat f]
    (V : X.Opens) (hV : IsAffineOpen V) (A : DerivedCategory (pullback f f).Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f f).toRingedSpace) A)
    (hsupp : ∀ w : ↥(pullback f f), w ∉ Set.range (pullback.diagonal f).base → ∀ n : ℤ,
      IsZero (SheafOfModules.stalkObj (pullback f f).ringCatSheaf w
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pullback f f).ringCatSheaf)
          n).obj A)))
    (hΦ : Nonempty ((fourierMukai f f A).obj (derivedStructureSheaf X) ≅ derivedStructureSheaf X))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (pullback f (V.ι ≫ f)).Modules i).obj
      ((dpull (restrictSndInclusion f V)).obj A)) := by
  let ι := restrictSndInclusion f V
  let T : Set ↥(pullback f (V.ι ≫ f)) := ι.base ⁻¹' Set.range (pullback.diagonal f).base
  have hT : IsClosed T :=
    (pullback.diagonal f).isClosedEmbedding.isClosed_range.preimage ι.base.hom.continuous
  have hTU : T ⊆ (pullback.fst f (V.ι ≫ f) ⁻¹ᵁ V : Set ↥(pullback f (V.ι ≫ f))) := by
    rintro w ⟨a, ha⟩
    have hd : ∀ g : pullback f f ⟶ X, pullback.diagonal f ≫ g = 𝟙 X → g.base (ι.base w) = a :=
      fun g hg => by
        rw [← ha]
        exact congr($(hg).base a)
    have h1 : (pullback.fst f (V.ι ≫ f)).base w = a := by
      rw [← restrictSndInclusion_fst f V]
      exact hd _ (pullback.diagonal_fst f)
    have h3 : (pullback.snd f f).base (ι.base w) =
        V.ι.base ((pullback.snd f (V.ι ≫ f)).base w) := by
      change (ι ≫ pullback.snd f f).base w = _
      rw [restrictSndInclusion_snd]
      rfl
    change (pullback.fst f (V.ι ≫ f)).base w ∈ V
    rw [h1, ← hd _ (pullback.diagonal_snd f), h3]
    exact ((pullback.snd f (V.ι ≫ f)).base w).2
  have hE := cohomologySupportedOn_derivedPullback ι (Set.range (pullback.diagonal f).base) A
    (fun n w hw => isZero_presheaf_stalk_of_isZero_stalkObj (hsupp w hw n))
  have : IsAffineHom ((pullback.fst f (V.ι ≫ f) ⁻¹ᵁ V).ι ≫ pullback.snd f (V.ι ≫ f)) :=
    Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isAffineHom_ι_comp_pullback_snd f
      (V.ι ≫ f) hV
  open Stacks.AlgebraicGeometry.SupportedPushforwardReflect in
  refine
    isZero_homology_of_isZero_homology_derivedPushforward_of_supported
      (pullback.snd f (V.ι ≫ f)) (pullback.fst f (V.ι ≫ f) ⁻¹ᵁ V) hT hTU _ hE
      (isQCohAll_dpull _ (isQCohAll_of_isPerfect hA)) ?_
  obtain ⟨eΦ⟩ := hΦ
  have e : (dpush (pullback.snd f (V.ι ≫ f))).obj ((dpull ι).obj A) ≅
      derivedStructureSheaf V.toScheme :=
    (restrictSndPushforwardIso f V A (isQCohAll_of_isPerfect hA)).symm ≪≫
      (dpull V.ι).mapIso (pushforwardSndIsoFourierMukaiUnit f A ≪≫ eΦ) ≪≫
      Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso V.ι.toLRSHom.toShHom
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have hS : ∀ (M : V.toScheme.Modules), IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor V.toScheme.Modules 0).obj M)) := by
    intro M
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
  exact hS _

/-- A point of `X ×_K X` whose second coordinate lies in `V` lies in the image of `X ×_K V`. -/
lemma mem_range_restrictSndInclusion (V : X.Opens) (w : ↥(pullback f f))
    (hw : (pullback.snd f f).base w ∈ V) : w ∈ Set.range (restrictSndInclusion f V).base := by
  let h := isPullback_restrictSndInclusion f V
  obtain ⟨a, rfl⟩ : w ∈ Set.range (pullback.fst (pullback.snd f f) V.ι).base := by
    rwa [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
  refine ⟨h.isoPullback.inv.base a, ?_⟩
  rw [← h.isoPullback_inv_fst]
  rfl

/-- **A kernel supported on the diagonal with `Φ_A(𝒪_X) ≅ 𝒪_X` has no cohomology outside degree
zero.** Every point of `X ×_K X` lies over an affine open `V` of the second factor, over which
`isZero_homology_restrictSnd_of_ne_zero` applies; the open immersion `X ×_K V ⟶ X ×_K X`
reflects vanishing of cohomology stalks (`isZero_modulesStalk_homology_of_derivedPullback`). -/
theorem isZero_homology_of_ne_zero [QuasiCompact f] [IsSeparated f] [Flat f]
    (A : DerivedCategory (pullback f f).Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f f).toRingedSpace) A)
    (hsupp : ∀ w : ↥(pullback f f), w ∉ Set.range (pullback.diagonal f).base → ∀ n : ℤ,
      IsZero (SheafOfModules.stalkObj (pullback f f).ringCatSheaf w
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pullback f f).ringCatSheaf)
          n).obj A)))
    (hΦ : Nonempty ((fourierMukai f f A).obj (derivedStructureSheaf X) ≅ derivedStructureSheaf X))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (pullback f f).Modules i).obj A) := by
  refine Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero _ _
    fun w => ?_
  obtain ⟨V', ⟨V, hV, rfl⟩, hwV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd f f).base w)) isOpen_univ
  obtain ⟨w', rfl⟩ := mem_range_restrictSndInclusion f V w hwV
  have h := isZero_homology_restrictSnd_of_ne_zero f V hV A hA hsupp hΦ i hi
  exact (isZero_modulesStalkFunctor_obj_iff _ _).1
    (isZero_modulesStalk_homology_of_derivedPullback (restrictSndInclusion f V) w' A i
      (Functor.map_isZero _ h))

/-- **`pr_{2,*}F ≅ 𝒪_X` when `A ≅ F[0]` and `Φ_A(𝒪_X) ≅ 𝒪_X`**: `pr_{2,*}F` is `R⁰pr_{2,*}F`,
which is `H⁰(R pr_{2,*}(F[0])) ≅ H⁰(R pr_{2,*}A) ≅ H⁰(Φ_A(𝒪_X)) ≅ H⁰(𝒪_X[0])`
(`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`). -/
def pushforwardSndIsoUnitOfIsoSingle (A : DerivedCategory (pullback f f).Modules)
    (F : (pullback f f).Modules)
    (e : A ≅ (DerivedCategory.singleFunctor (pullback f f).Modules 0).obj F)
    (eΦ : (fourierMukai f f A).obj (derivedStructureSheaf X) ≅ derivedStructureSheaf X) :
    (Scheme.Modules.pushforward (pullback.snd f f)).obj F ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward (pullback.snd f f))).symm.app F ≪≫
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (Scheme.Modules.pushforward (pullback.snd f f))
      (derivedPushforwardModules (pullback.snd f f))
      (derivedPushforwardModulesUnit (pullback.snd f f))
      Stacks.Cohomology.Localization.enoughKInjectives 0).symm.app F) ≪≫
    (DerivedCategory.homologyFunctor X.Modules 0).mapIso
      ((dpush (pullback.snd f f)).mapIso e.symm ≪≫ pushforwardSndIsoFourierMukaiUnit f A ≪≫ eΦ) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _

end Degree

/-! ### The identification with the diagonal -/

section Main

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- A scheme smooth over a field is reduced: its stalks are regular, hence domains. -/
private lemma isReduced_of_smooth_over_field [Smooth f] : IsReduced X := by
  have hnormal : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have : IsDomain (X.presheaf.stalk x) := hnormal.stalk_isDomain x
    infer_instance
  exact isReduced_of_isReduced_stalk X

/-- **[Stacks, Tag 0G0E], object-wise, over an algebraically closed field.** Let `K` be
algebraically closed and `X` smooth and proper over `K`. A perfect kernel `A` on `X ×_K X` with
`Φ_A(E) ≅ E` for every perfect `E` is isomorphic to the diagonal kernel `Δ_*𝒪_X`.

The kernel is supported on the diagonal (`isZero_stalkHomology_of_notMem_range_diagonal`, from the
skyscrapers at the `K`-points), has cohomology in degree zero only (`isZero_homology_of_ne_zero`,
from `Φ_A(𝒪_X) ≅ 𝒪_X`), so it is a coherent module `F` in degree zero with `pr_{2,*}F ≅ 𝒪_X`
(`pushforwardSndIsoUnitOfIsoSingle`), and [Stacks, Tag 0FZQ] identifies `F` with `Δ_*𝒪_X`. -/
theorem nonempty_diagonalKernel_iso_of_forall_iso [IsAlgClosed K] [Smooth f] [IsProper f]
    (A : DerivedCategory (pullback f f).Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (pullback f f).toRingedSpace) A)
    (hΦ : ∀ E : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        Nonempty ((fourierMukai f f A).obj E ≅ E)) :
    Nonempty (diagonalKernel f ≅ A) := by
  have hO := hΦ _ (isPerfect_derivedStructureSheaf f)
  have hsupp := isZero_stalkHomology_of_notMem_range_diagonal f A hA
    fun x hx => hΦ _ (isPerfect_pointSheaf f x hx)
  have hdeg := isZero_homology_of_ne_zero f A hA hsupp hO
  have : A.IsGE 0 := (DerivedCategory.isGE_iff A 0).2 fun j hj => hdeg j (by omega)
  have : A.IsLE 0 := (DerivedCategory.isLE_iff A 0).2 fun j hj => hdeg j (by omega)
  obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A 0
  obtain ⟨eΦ⟩ := hO
  -- `F` is `H⁰(A)`
  let eF : F ≅ (DerivedCategory.homologyFunctor (pullback f f).Modules 0).obj A :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso e.symm
  have : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f f ≫ f)
  have hFc : F.IsCoherent := by
    have := isCoherent_homology_of_isPerfect' _ A hA 0
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso eF
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hFsupp : SheafOfModules.supp F ⊆ Set.range (pullback.diagonal f).base := by
    intro w hw
    by_contra hwΔ
    obtain ⟨a, ha⟩ := hw
    have h0 := isZero_presheaf_stalk_of_isZero_stalkObj (hsupp w hwΔ 0)
    have h1 := h0.of_iso ((TopCat.Presheaf.stalkFunctor _ w).mapIso
      ((SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _).mapIso eF))
    rw [AddCommGrpCat.isZero_iff_subsingleton] at h1
    exact ha (@Subsingleton.elim _ h1 _ _)
  have := isReduced_of_smooth_over_field f
  have ePush := pushforwardSndIsoUnitOfIsoSingle f A F e eΦ
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((Scheme.Modules.pushforward (pullback.snd f f)).obj F) :=
    have := Stacks.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.property
    (Stacks.SheafOfModules.isInvertible_of_iso X.presheaf X.ringCatSheaf.property
      ePush.symm).toAlgebraicGeometry
  obtain ⟨eΔ⟩ := Scheme.Modules.iso_pushforward_section_of_invertible_pushforward
    (pullback.snd f f)
    (pullback.diagonal f) (pullback.diagonal_snd f) F hFsupp
  exact ⟨derivedPushforwardSingleIso (pullback.diagonal f) _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.Modules.pushforward (pullback.diagonal f)).mapIso ePush.symm ≪≫ eΔ.symm) ≪≫
    e.symm⟩

/-- **`AlgebraicGeometry.ObjectwiseIdentityKernelIsDiagonal` over an algebraically closed
field.** -/
theorem objectwiseIdentityKernelIsDiagonal (K : Type u) [Field K] [IsAlgClosed K] :
    ObjectwiseIdentityKernelIsDiagonal K := by
  intro X f hs hp A hA hΦ
  exact nonempty_diagonalKernel_iso_of_forall_iso f A hA hΦ

/-- **The input `hkernel` of [Stacks, Tag 0G0Y] over an algebraically closed field, from the
object-wise form of Orlov's theorem alone.** -/
theorem derivedEquivalenceHasRelativeKernel_of_objectwiseFourierMukai (K : Type u) [Field K]
    [IsAlgClosed K] (hFM : ObjectwiseFourierMukaiOfEquivalence K) :
    DerivedEquivalenceHasRelativeKernel K :=
  derivedEquivalenceHasRelativeKernel_of_objectwise hFM (objectwiseIdentityKernelIsDiagonal K)

end Main

end AlgebraicGeometry
