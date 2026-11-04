module

public import StacksFrontier.AlgebraicGeometry.Curves.StableLocus.NodalConnectedLocus
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyAmpleDualizingLocus
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stable locus of genus `g` in a proper flat family of schemes is open

Let `T` be a Noetherian scheme and `π : Z ⟶ T` proper, flat and of finite presentation. There is
an open `W ⊆ T` such that a field-valued point `Spec K ⟶ T` lands in `W` exactly when the fibre
`Z_K` is a stable curve of genus `g` over `K`: its singularities are at-worst-nodal,
`dim(Z_K) = 1`, `K = H⁰(Z_K, 𝒪)`, its genus is `g` and its dualizing sheaf is ample — condition
(2)(c) of Stacks 0E76 together with the genus condition of Stacks 0E78. This is the openness of
`𝓜̄_g` in the stack of curves (Stacks 0E76, 0E78), for families whose total space is a scheme;
it is what the proof of the quasi-compactness of `𝓜̄_g` (Stacks 0E9B) uses.

`W` is cut out in four steps, each tested on the fibres over field-valued points: the nodal locus
(`AlgebraicGeometry.exists_opens_isAtWorstNodal_restrict_and_forall_mem_iff`), the locus of
geometrically connected fibres
(`AlgebraicGeometry.exists_opens_geometricallyConnected_restrict_and_forall_mem_iff`), the locus
where `χ(Z_t, 𝒪) = 1 - g` ([Stacks, Tag 0B9T]; with `H⁰ = K` this is the genus), and the locus
where the fibre dualizing sheaf is ample
(`Stacks.Duality.exists_opens_forall_mem_iff_isAmple_dualizingSheafOverField`, the openness of
Stacks 0E74).

## Main definitions

* `AlgebraicGeometry.IsStableCurveOfGenusOverField`: a proper scheme over a field is a stable
  curve of genus `g`.

## Main results

* `AlgebraicGeometry.exists_opens_forall_mem_iff_isStableCurveOfGenusOverField`.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0E9B](https://stacks.math.columbia.edu/tag/0E9B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A stable curve of genus `g` over a field.** A proper scheme `V` over a field `K` is a stable
curve of genus `g` when its singularities are at-worst-nodal, `dim(V) = 1`, `K = H⁰(V, 𝒪_V)`, its
genus is `g`, and its dualizing sheaf `ω_V` (invertible, `V` being a connected nodal curve) is
ample: condition (2)(c) of Stacks 0E76 with the genus of Stacks 0E78. The statement is condition
(c) of `AlgebraicGeometry.factors_moduliStableCurvesOfGenus_over_field_iff` for the object
`Over.mk fV`. -/
@[sga "7 I 5.1" "special case"]
def IsStableCurveOfGenusOverField (K : Type u) [Field K] {V : Scheme.{u}}
    (fV : V ⟶ Spec (CommRingCat.of K)) [IsProper fV] (g : ℕ) : Prop :=
  letI : (Over.mk fV).left.Over (Spec (.of K)) := ⟨(Over.mk fV).hom⟩
  haveI : IsProper ((Over.mk fV).left ↘ Spec (.of K)) := inferInstanceAs (IsProper fV)
  ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities K (Over.mk fV).left)
    (hdim1 : topologicalKrullDim (Over.mk fV).left = 1)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ ((Over.mk fV).left ↘ Spec (.of K)).appTop)),
    genus (Over.mk fV).hom = g ∧
      haveI := hH0
      haveI := connectedSpace_of_isIso_globalSections K ((Over.mk fV).left ↘ Spec (.of K))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K
        (Over.mk fV).left hdim1 hnodal
      Scheme.Modules.IsAmple (Over.mk fV).left
        (Stacks.Duality.dualizingSheafOverField ((Over.mk fV).left ↘ Spec (.of K)))

open ProperFlatFibreEulerCharacteristic in
/-- **`χ(V, 𝒪_V) = 1 - g(V)`** for a proper scheme of dimension at most one over a field with
`H⁰(V, 𝒪_V) = K`. -/
theorem eulerSum_unit_eq_one_sub_genus (K : Type u) [Field K] {V : Scheme.{u}}
    (fV : V ⟶ Spec (CommRingCat.of K)) [IsProper fV] (hdim : topologicalKrullDim V ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fV.appTop)] :
    eulerSum K fV (_root_.SheafOfModules.unit V.ringCatSheaf) = 1 - (genus fV : ℤ) := by
  have h₁ := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero K fV
    (_root_.SheafOfModules.unit V.ringCatSheaf)
    (fun m hm => isZero_cohomologyOverField_two_le K fV hdim _ m hm)
  unfold eulerSum
  rw [h₁, finrank_cohomologyOverField_unit_zero_eq_one fV,
    finrank_cohomologyOverField_one_unit_eq_genus K fV]
  push_cast
  ring

open ProperFlatFibreEulerCharacteristic in
/-- **The Euler characteristic of the structure sheaf at a field-valued point** of a proper flat
family is the Euler characteristic of the structure sheaf of the fibre there
([Stacks, Tag 0B9T]). -/
theorem fibreEulerCharacteristic_unit_eq_eulerSum {Z T V : Scheme.{u}} (π : Z ⟶ T) [IsProper π]
    [Flat π] [LocallyOfFinitePresentation π] {K : Type u} [Field K]
    {y : Spec (CommRingCat.of K) ⟶ T} {q : V ⟶ Z} {fV : V ⟶ Spec (CommRingCat.of K)}
    (sq : IsPullback q fV π y) :
    fibreEulerCharacteristic π (_root_.SheafOfModules.unit Z.ringCatSheaf)
        (y (IsLocalRing.closedPoint K)) =
      eulerSum K fV (_root_.SheafOfModules.unit V.ringCatSheaf) := by
  have hfp : FinitePresentation π := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible π
    (_root_.SheafOfModules.unit Z.ringCatSheaf) (Stacks.SheafOfModules.isInvertible_unit _ _)
  rw [fibreEulerCharacteristic_eq_chiDerivedFibre π hfp _ hOfp hOflat,
    chiDerivedFibre_eq_eulerSum π hfp _ hOfp hOflat K y q fV sq (IsLocalRing.closedPoint K)]
  exact eulerSum_congr K fV
    (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso q.toLRSHom.toShHom)

/-- **Restricting a field-point characterisation to an open of the base.** If membership of a
field-valued point of `U` in the open `U'` of `U` is tested by a condition `Q` on the fibre of
`π ∣_ U`, then membership of a field-valued point of `T` in the image of `U'` is tested by
landing in `U` and `Q` on the fibre of `π`. -/
theorem forall_mem_image_iff_of_forall_mem_iff {Z T : Scheme.{u}} (π : Z ⟶ T) (U : T.Opens)
    (U' : U.toScheme.Opens)
    (Q : ∀ (K : Type u) [Field K] {V : Scheme.{u}} (_ : V ⟶ Spec (CommRingCat.of K)), Prop)
    (hU' : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ U)
      (q : V ⟶ π ⁻¹ᵁ U) (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV (π ∣_ U) y →
      (y (IsLocalRing.closedPoint K) ∈ U' ↔ Q K fV)) :
    ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ T) (q : V ⟶ Z)
      (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV π y →
      (y (IsLocalRing.closedPoint K) ∈ U.ι ''ᵁ U' ↔
        y (IsLocalRing.closedPoint K) ∈ U ∧ Q K fV) := by
  intro K _ V y q fV sq
  have hU : y (IsLocalRing.closedPoint K) ∈ U.ι ''ᵁ U' → y (IsLocalRing.closedPoint K) ∈ U :=
    fun ⟨u, _, hyu⟩ => hyu ▸ u.2
  suffices H : y (IsLocalRing.closedPoint K) ∈ U →
      (y (IsLocalRing.closedPoint K) ∈ U.ι ''ᵁ U' ↔ Q K fV) from
    ⟨fun h => ⟨hU h, (H (hU h)).mp h⟩, fun ⟨hyU, hQ⟩ => (H hyU).mpr hQ⟩
  intro hyU
  obtain ⟨y', q', rfl, -, sq'⟩ := exists_isPullback_restrict_of_mem π U sq hyU
  rw [← hU' K V y' q' fV sq']
  exact U.ι.isOpenEmbedding.injective.mem_set_image

open ProperFlatFibreEulerCharacteristic in
/-- **The four fibre conditions make a stable curve of genus `g`.** A proper scheme `V` over a
field `K` is a stable curve of genus `g` exactly when it is at-worst-nodal of relative dimension
one over `K`, geometrically connected, with `χ(V, 𝒪_V) = 1 - g`, and with ample dualizing sheaf:
geometric connectedness of a proper geometrically reduced scheme is `K = H⁰(V, 𝒪_V)`
([Stacks, Tag 0FD2]), and then `χ(V, 𝒪_V) = 1 - g(V)`. -/
theorem isStableCurveOfGenusOverField_iff (K : Type u) [Field K] {V : Scheme.{u}}
    (fV : V ⟶ Spec (CommRingCat.of K)) [IsProper fV] (g : ℕ) :
    (IsAtWorstNodalOfRelativeDimensionOne fV ∧ GeometricallyConnected fV ∧
      eulerSum K fV (_root_.SheafOfModules.unit V.ringCatSheaf) = 1 - (g : ℤ) ∧
      ∃ _ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField fV),
        Stacks.Ample.IsAmple V (Stacks.Duality.dualizingSheafOverField fV)) ↔
      IsStableCurveOfGenusOverField K fV g := by
  let : V.Over (Spec (.of K)) := ⟨fV⟩
  have : IsProper (V ↘ Spec (.of K)) := ‹IsProper fV›
  have : LocallyOfFinitePresentation fV := inferInstance
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian fV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace fV
  have : IsNoetherian V := ⟨⟩
  constructor
  · rintro ⟨hnod, hgc, hχ, hinv, hamp⟩
    have : ConnectedSpace V := hgc.geometrically_connectedSpace (𝟙 _) (𝟙 V) fV
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
    have : Nonempty V := inferInstance
    obtain ⟨-, hdim, hnodal⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_of_field K fV).mp hnod
    have : GeometricallyReduced fV :=
      geometricallyReduced_of_isAtWorstNodalOfRelativeDimensionOne fV hnod
    have hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fV.appTop) :=
      (isIso_globalSections_iff_geometricallyConnected K fV).mpr hgc
    have hgen : genus fV = g := by
      have := eulerSum_unit_eq_one_sub_genus K fV hdim.le
      rw [hχ] at this
      exact_mod_cast (by omega : (genus fV : ℤ) = g)
    exact ⟨hnodal, hdim, hH0, hgen, (@Stacks.AmpleBridge.isAmple_iff_isAmple V _ hinv).mp hamp⟩
  · rintro ⟨hnodal, hdim, hH0, hgen, hamp⟩
    replace hnodal : Stacks.Curves.HasAtWorstNodalSingularities K V := hnodal
    replace hdim : topologicalKrullDim V = 1 := hdim
    replace hH0 : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fV.appTop) := hH0
    replace hgen : genus fV = g := hgen
    have := hH0
    have : ConnectedSpace V := connectedSpace_of_isIso_globalSections K fV
    have : Nonempty V := inferInstance
    have hnod : IsAtWorstNodalOfRelativeDimensionOne fV :=
      (isAtWorstNodalOfRelativeDimensionOne_iff_of_field K fV).mpr
        ⟨equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim, hdim, hnodal⟩
    have : GeometricallyReduced fV :=
      geometricallyReduced_of_isAtWorstNodalOfRelativeDimensionOne fV hnod
    have hgc := (isIso_globalSections_iff_geometricallyConnected K fV).mp hH0
    let hinv :=
      isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K V hdim hnodal
    refine ⟨hnod, hgc, ?_, hinv, (@Stacks.AmpleBridge.isAmple_iff_isAmple V _ hinv).mpr hamp⟩
    rw [eulerSum_unit_eq_one_sub_genus K fV hdim.le, hgen]

/-- **A stable curve of genus `g ≥ 2` has neither rational tails nor rational bridges**
(`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`): the fibre
condition of Stacks 0E75, and its genus is `g`. -/
theorem IsStableCurveOfGenusOverField.hasGenusTwoNoRationalTailNoRationalBridge {K : Type u}
    [Field K] {V : Scheme.{u}} {fV : V ⟶ Spec (CommRingCat.of K)} [IsProper fV] {g : ℕ}
    (hg : 2 ≤ g) (h : IsStableCurveOfGenusOverField K fV g) :
    HasGenusTwoNoRationalTailNoRationalBridge K fV ∧ genus fV = g := by
  obtain ⟨hnodal, hdim1, hH0, hgen, hamp⟩ := h
  let : V.Over (Spec (.of K)) := ⟨fV⟩
  have : IsProper (V ↘ Spec (.of K)) := ‹IsProper fV›
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (V ↘ Spec (.of K)).appTop) := hH0
  replace hgen : genus fV = g := hgen
  replace hdim1 : topologicalKrullDim V = 1 := hdim1
  replace hnodal : Stacks.Curves.HasAtWorstNodalSingularities K V := hnodal
  have hg' : 2 ≤ genus (V ↘ Spec (.of K)) := hgen ▸ hg
  obtain ⟨htail, hbridge⟩ :=
    (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim1 hnodal hg').2 (by exact hamp)
  exact ⟨⟨hg', htail, ‹IsProper fV›, hbridge⟩, hgen⟩

/-- Every proper field-valued fibre of an at-worst-nodal geometrically connected family has
invertible dualizing sheaf. -/
private theorem isInvertible_dualizingSheafOverField_of_isPullback {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) [hgc : GeometricallyConnected f]
    (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S) (g' : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f'] (sq : IsPullback g' f' f y) :
    SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f') := by
  have hnodX := IsAtWorstNodalOfRelativeDimensionOne.of_isPullback sq hf
  have : ConnectedSpace X' := hgc.geometrically_connectedSpace y g' f' sq
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper (X' ↘ Spec (.of K)) := ‹IsProper f'›
  obtain ⟨-, hdim, hnodal⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_of_field K f').mp hnodX
  exact isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K X' hdim hnodal

/-- The fibres of an at-worst-nodal family have local dimension one at every point. -/
private theorem topologicalKrullDimAt_fiber_eq_one_of_isAtWorstNodalOfRelativeDimensionOne
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsAtWorstNodalOfRelativeDimensionOne f) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, hlfp, hfib⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  obtain ⟨heq, hdim, -⟩ := hfib (f x) ⟨f.asFiber x⟩
  have hLFT : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback f _)
      inferInstance
  exact @Stacks.Curves.topologicalKrullDimAt_eq_one_of_equidimensional _ _ _
    (f.fiberToSpecResidueField (f x)) hLFT heq hdim _

/-- A proper at-worst-nodal geometrically connected family over a Noetherian base is
Cohen–Macaulay. -/
private theorem isCohenMacaulay_of_isAtWorstNodalOfRelativeDimensionOne {X S : Scheme.{u}}
    [IsNoetherian S] {f : X ⟶ S} [IsProper f] (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    [hgc : GeometricallyConnected f] :
    f.IsCohenMacaulay
      (Stacks.Duality.isLocallyNoetherian_fiber_left (Stacks.Duality.ftsHomToBase f)) := by
  obtain ⟨hflat, hlfp, hfib⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  refine (isCohenMacaulay_iff_flat_and_fibers f _).mpr ⟨hflat, fun s => ?_⟩
  have : ConnectedSpace (f.fiber s) := hgc.geometrically_connectedSpace _ _ _
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  obtain ⟨-, hdim, hnodal⟩ := hfib s inferInstance
  let : (f.fiber s).Over (Spec (.of (S.residueField s))) := ⟨f.fiberToSpecResidueField s⟩
  have : IsProper (f.fiber s ↘ Spec (.of (S.residueField s))) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback f _) inferInstance
  have := isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities _ _ hdim hnodal
  exact isCohenMacaulay_of_isGorenstein _

open ProperFlatFibreEulerCharacteristic in
/-- For a proper flat at-worst-nodal geometrically connected family of finite presentation over a
Noetherian base, the field-valued points whose fibre has `χ(𝒪) = 1 - g` and ample invertible
dualizing sheaf form an open. -/
private theorem exists_opens_forall_mem_iff_eulerSum_eq_and_isAmple_dualizingSheafOverField
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    [GeometricallyConnected f] (g : ℕ) :
    ∃ W : S.Opens, ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (q : V ⟶ X) (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV f y →
      (y (IsLocalRing.closedPoint K) ∈ W ↔
        eulerSum K fV (_root_.SheafOfModules.unit V.ringCatSheaf) = 1 - (g : ℤ) ∧
        ∃ hP : IsProper fV, ∃ _ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
          (@Stacks.Duality.dualizingSheafOverField K _ V fV hP),
          Stacks.Ample.IsAmple V (@Stacks.Duality.dualizingSheafOverField K _ V fV hP)) := by
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let O := _root_.SheafOfModules.unit X.ringCatSheaf
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible f O
    (Stacks.SheafOfModules.isInvertible_unit _ _)
  have hlc := isLocallyConstant_fibreEulerCharacteristic f hfp O hOfp hOflat
  let U₂ : S.Opens := ⟨fibreEulerCharacteristic f O ⁻¹' {1 - (g : ℤ)}, hlc.isOpen_fiber _⟩
  let π₂ := f ∣_ U₂
  have hnod₂ : IsAtWorstNodalOfRelativeDimensionOne π₂ :=
    IsAtWorstNodalOfRelativeDimensionOne.of_isPullback (isPullback_morphismRestrict f U₂).flip hf
  have : IsNoetherian U₂.toScheme := ⟨⟩
  obtain ⟨U₃, h₃⟩ :=
    Stacks.Duality.exists_opens_forall_mem_iff_isAmple_dualizingSheafOverField π₂
      (isCohenMacaulay_of_isAtWorstNodalOfRelativeDimensionOne hnod₂)
      (topologicalKrullDimAt_fiber_eq_one_of_isAtWorstNodalOfRelativeDimensionOne hnod₂)
      (isInvertible_dualizingSheafOverField_of_isPullback hnod₂)
  let Q₃ : ∀ (K : Type u) [Field K] {V : Scheme.{u}} (_ : V ⟶ Spec (CommRingCat.of K)), Prop :=
    fun K _ V fV => ∃ hP : IsProper fV,
      ∃ _ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        (@Stacks.Duality.dualizingSheafOverField K _ V fV hP),
        Stacks.Ample.IsAmple V (@Stacks.Duality.dualizingSheafOverField K _ V fV hP)
  have L₃ : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ U₂)
      (q : V ⟶ f ⁻¹ᵁ U₂) (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV π₂ y →
      (y (IsLocalRing.closedPoint K) ∈ U₃ ↔ Q₃ K fV) := by
    intro K _ V y q fV sq
    have hP : IsProper fV := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    rw [h₃ K V y q fV sq]
    exact ⟨fun h => ⟨hP, isInvertible_dualizingSheafOverField_of_isPullback hnod₂ K V y q fV sq, h⟩,
      fun ⟨_, _, h⟩ => h⟩
  refine ⟨U₂.ι ''ᵁ U₃, fun K _ V y q fV sq => ?_⟩
  rw [forall_mem_image_iff_of_forall_mem_iff f U₂ U₃ Q₃ L₃ K V y q fV sq]
  refine and_congr_left' ?_
  show fibreEulerCharacteristic f O _ = _ ↔ _
  rw [fibreEulerCharacteristic_unit_eq_eulerSum f sq]

open ProperFlatFibreEulerCharacteristic in
/-- **The stable locus of genus `g` of a proper flat family of schemes over a Noetherian base is
open.** For `π : Z ⟶ T` proper, flat and of finite presentation with `T` Noetherian there is an
open `W ⊆ T` such that a field-valued point `y : Spec K ⟶ T` lands in `W` exactly when the fibre
`fV : Z_K ⟶ Spec K` is a stable curve of genus `g`. -/
theorem exists_opens_forall_mem_iff_isStableCurveOfGenusOverField {Z T : Scheme.{u}}
    [IsNoetherian T] (π : Z ⟶ T) [IsProper π] [Flat π] [LocallyOfFinitePresentation π] (g : ℕ) :
    ∃ W : T.Opens, ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ T)
      (q : V ⟶ Z) (fV : V ⟶ Spec (CommRingCat.of K)) [IsProper fV], IsPullback q fV π y →
      (y (IsLocalRing.closedPoint K) ∈ W ↔ IsStableCurveOfGenusOverField K fV g) := by
  obtain ⟨U₀, hnod₀, h₀⟩ := exists_opens_isAtWorstNodal_restrict_and_forall_mem_iff π
  obtain ⟨U₁, hgc₁, h₁⟩ :=
    exists_opens_geometricallyConnected_restrict_and_forall_mem_iff (π ∣_ U₀) hnod₀
  let π₁ := (π ∣_ U₀) ∣_ U₁
  have hnod₁ : IsAtWorstNodalOfRelativeDimensionOne π₁ :=
    IsAtWorstNodalOfRelativeDimensionOne.of_isPullback
      (isPullback_morphismRestrict (π ∣_ U₀) U₁).flip hnod₀
  have : GeometricallyConnected π₁ := hgc₁
  have : IsNoetherian U₁.toScheme := ⟨⟩
  obtain ⟨W, hW⟩ :=
    exists_opens_forall_mem_iff_eulerSum_eq_and_isAmple_dualizingSheafOverField π₁ hnod₁ g
  let Q : ∀ (K : Type u) [Field K] {V : Scheme.{u}} (_ : V ⟶ Spec (CommRingCat.of K)), Prop :=
    fun K _ V fV => eulerSum K fV (_root_.SheafOfModules.unit V.ringCatSheaf) = 1 - (g : ℤ) ∧
      ∃ hP : IsProper fV, ∃ _ : SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
        (@Stacks.Duality.dualizingSheafOverField K _ V fV hP),
        Stacks.Ample.IsAmple V (@Stacks.Duality.dualizingSheafOverField K _ V fV hP)
  have L₁ : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ U₀)
      (q : V ⟶ π ⁻¹ᵁ U₀) (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV (π ∣_ U₀) y →
      (y (IsLocalRing.closedPoint K) ∈ U₁.ι ''ᵁ W ↔ GeometricallyConnected fV ∧ Q K fV) := by
    intro K _ V y q fV sq
    rw [forall_mem_image_iff_of_forall_mem_iff (π ∣_ U₀) U₁ W Q hW K V y q fV sq,
      h₁ K V y q fV sq]
  refine ⟨U₀.ι ''ᵁ (U₁.ι ''ᵁ W), fun K _ V y q fV _ sq => ?_⟩
  rw [forall_mem_image_iff_of_forall_mem_iff π U₀ (U₁.ι ''ᵁ W)
      (fun K _ V fV => GeometricallyConnected fV ∧ Q K fV) L₁ K V y q fV sq,
    h₀ K V y q fV sq, ← isStableCurveOfGenusOverField_iff]
  exact ⟨fun ⟨h0, h1, h2, _, h3, h4⟩ => ⟨h0, h1, h2, h3, h4⟩,
    fun ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, ‹_›, h3, h4⟩⟩

end AlgebraicGeometry

end
